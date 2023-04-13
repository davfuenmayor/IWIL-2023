theory "topology-compactness"
  imports Main
begin

(*Override Sledgehammer and Nitpick default params*)
declare[[smt_timeout=30]]
sledgehammer_params[isar_proof=false,max_facts=20]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3, atoms=a b c d]


section \<open>Background Theory\<close>

(*Sets are encoded as characteristic functions/predicates (i.e. functions with a 'bool' codomain)*)
type_synonym 'a \<sigma> = \<open>'a \<Rightarrow> bool\<close>
(*Relations are encoded as set-valued functions*)
type_synonym ('a,'b)\<rho> = \<open>'a \<Rightarrow>'b \<sigma>\<close>
(*Convenient type constructor for unary set-operators (allowing for some restricted two-sortedness).*)
type_synonym ('a,'b)\<O> = "('a \<sigma>,'b)\<rho>" (**i.e. 'a \<sigma> \<Rightarrow> 'b \<sigma>*)

(*We define the image and preimage (aka. inverse image) set-operators for functions.
 We read the term "(pre)imageFun f X z" as "z is the (pre)image of X under f". *)
definition imageFun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a,'b)\<O>" ("\<lbrakk>_ _\<rbrakk>") (*suggestive notation for partial application*)
  where "imageFun  f \<equiv> \<lambda>A. \<lambda>b. \<exists>a. (f a) = b \<and> A a"
definition preimageFun::"('a \<Rightarrow> 'b) \<Rightarrow> ('b,'a)\<O>" ("\<lbrakk>_ _\<rbrakk>\<inverse>")
  where "preimageFun f \<equiv> \<lambda>B. \<lambda>a. B (f a)"

(**Predicate for indicating that a map is one-one/injective (or onto) wrt. its domain (and codomain)*)
abbreviation one2one::"'a \<sigma> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  where "one2one A f \<equiv> \<forall>x y. A x \<and> A y \<and> (f x) = (f y) \<longrightarrow> x = y"
abbreviation onto::"'a \<sigma> \<Rightarrow> 'b \<sigma> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "onto A B f \<equiv> \<forall>b. B b \<longrightarrow> (\<exists>a. A a \<and> (f a) = b)"

(**Predicate for indicating that a function maps a set to another.*)
abbreviation map::"'a \<sigma> \<Rightarrow> 'b \<sigma> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  where "map A B f \<equiv> \<forall>a. A a \<longrightarrow> B (f a)"
abbreviation "embedding A B f \<equiv> map A B f \<and> one2one A f"
abbreviation "bijective A B f \<equiv> embedding A B f \<and> onto A B f"

(*When notions of embedding and bijection collapse for all (endo)maps in a set, it is called finite*)
definition finite::"'a \<sigma> \<Rightarrow> bool"
  where "finite S \<equiv> \<forall>f. embedding S S f \<longrightarrow> onto S S f"

(*A set S can be closed under a unary resp. binary function (\<phi>/1 resp. \<xi>/2)*)
definition set_closed1::"('a \<Rightarrow> 'a) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-closed")
  where "\<phi>-closed S \<equiv> \<forall>x. S x \<longrightarrow> S(\<phi> x)"
definition set_closed2::"('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-closed")
  where "\<xi>-closed S \<equiv> \<forall>x y. S x \<and> S y \<longrightarrow> S(\<xi> x y)"
(*Closure under a binary function can be reduced to closure under a unary function via partial application*)
lemma set_closed2_def2: "\<xi>-closed S = (\<forall>x. S x \<longrightarrow> (\<xi> x)-closed S)"
  unfolding set_closed1_def set_closed2_def by blast

(*Analogously, we say that an element is 'closed' wrt. unary function \<phi> when it is one of its fixed points*)
definition elem_closed::"('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" ("_-closed")
  where "\<phi>-closed x \<equiv> (\<phi> x) = x"
(*This too can be reduced to closure (under the function \<phi>) of the corresponding singleton set*)
lemma elem_closed_def2: "\<phi>-closed x = \<phi>-closed(\<lambda>y. y = x)" by (simp add: elem_closed_def set_closed1_def)

(*We introduce below some operations on sets which endow them with a Boolean algebra structure.*)

definition univ::"'a \<sigma>" ("\<UU>")
  where "\<UU> \<equiv> \<lambda>x. True"
definition empty::"'a \<sigma>" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<lambda>x. False"
definition compl::"'a \<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<midarrow>") (*or type: ('a,'a)\<O> *)
  where \<open>\<^bold>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>
definition inter::"'a \<sigma> \<Rightarrow> 'a \<sigma> \<Rightarrow> 'a \<sigma>" (infixr "\<^bold>\<inter>" 54) 
  where "A \<^bold>\<inter> B \<equiv> \<lambda>x. A x \<and> B x"
definition union::"'a \<sigma> \<Rightarrow> 'a \<sigma> \<Rightarrow> 'a \<sigma>" (infixr "\<^bold>\<union>" 53) 
  where "A \<^bold>\<union> B \<equiv> \<lambda>x. A x \<or> B x"
(*Union and intersection can be generalized to the infinitary case (i.e. operating on arbitrary sets of sets)*)
definition biginter::"('a \<sigma>)\<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<Inter>") 
  where "\<^bold>\<Inter>S \<equiv> \<lambda>x. \<forall>A. S A \<longrightarrow> A x"
definition bigunion:: "('a \<sigma>)\<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<Union>") 
  where "\<^bold>\<Union>S \<equiv> \<lambda>x. \<exists>A. S A  \<and>  A x"

lemma deMorgan1: "\<forall>A B. \<^bold>\<midarrow>(A \<^bold>\<inter> B) = (\<^bold>\<midarrow>A \<^bold>\<union> \<^bold>\<midarrow>B)" by (simp add: compl_def inter_def union_def)
lemma deMorgan2: "\<forall>A B. \<^bold>\<midarrow>(A \<^bold>\<union> B) = (\<^bold>\<midarrow>A \<^bold>\<inter> \<^bold>\<midarrow>B)" by (simp add: compl_def inter_def union_def)
lemma bigDeMorgan1: "\<forall>S. \<^bold>\<midarrow>(\<^bold>\<Inter> S) = \<^bold>\<Union>\<lbrakk>\<^bold>\<midarrow> S\<rbrakk>" unfolding biginter_def bigunion_def compl_def imageFun_def by metis
lemma bigDeMorgan2: "\<forall>S. \<^bold>\<midarrow>(\<^bold>\<Union> S) = \<^bold>\<Inter>\<lbrakk>\<^bold>\<midarrow> S\<rbrakk>" unfolding biginter_def bigunion_def compl_def imageFun_def by metis

(*The algebra of sets is ordered wrt. standard subset relation*)
definition subset::"('a \<sigma>,'a \<sigma>)\<rho>" (infixr "\<^bold>\<subseteq>" 51) 
  where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"


section \<open>Basic Theory of Compactness\<close>

(*The following property of a collection of sets says that there exists a pair of them that covers a given set X*)
definition BCP  ("BCP|\<^sub>_ _"[90]) (* read as 'binary cover property' *)
  where "BCP|\<^sub>X S \<equiv> \<exists>A B. S A \<and> S B \<and> (X \<^bold>\<subseteq> A \<^bold>\<union> B)"

(*The following property of a collection of sets says that there exists a finite subcollection that covers X*)
definition FCP  ("FCP|\<^sub>_ _"[90]) (* read as 'finite cover property' *)
  where "FCP|\<^sub>X S \<equiv> \<exists>D. (\<exists>A. D A) \<and> D \<^bold>\<subseteq> S \<and> finite D \<and> (X \<^bold>\<subseteq> \<^bold>\<Union>D)"

(*Recall that open sets are the fixed-points of the dual of the closure operator (i.e. the interior)*)
abbreviation "dual \<phi> \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"
abbreviation elem_open::"('a,'a)\<O> \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-open") 
  where "\<C>-open x \<equiv> (dual \<C>)-closed x"

(*Using the relativized definitions above we can define compactness for sets/subspaces using the FCP
   (as in 'every open cover has a finite subcover')*)
definition compactSet::"('a,'a)\<O> \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-compactSet")
  where "\<C>-compactSet X \<equiv> \<forall>S. S \<^bold>\<subseteq> \<C>-open \<longrightarrow> (X \<^bold>\<subseteq> \<^bold>\<Union>S) \<longrightarrow> FCP|\<^sub>X S"

(**An alternative (arguably simpler) candidate definition can be stated as follows*)
abbreviation "union_gen S \<equiv> \<^bold>\<Inter>(\<lambda>X. (\<^bold>\<union>)-closed X \<and> S \<^bold>\<subseteq> X)"
definition compactSet'::"('a,'a)\<O> \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-compactSet''")
  where "\<C>-compactSet' X \<equiv> \<forall>S. S \<^bold>\<subseteq> \<C>-open \<longrightarrow> (X \<^bold>\<subseteq> \<^bold>\<Union>S) \<longrightarrow> BCP|\<^sub>X (union_gen S)"

(*The equivalence of both definitions follows from the following (hard to fully automate) lemma*)
lemma FCP_BCP_bridge: "FCP|\<^sub>X S = BCP|\<^sub>X (union_gen S)" 
  unfolding FCP_def BCP_def sorry (*TODO: manual proof pending*)

lemma compactSet_equiv: "\<C>-compactSet = \<C>-compactSet'" 
  unfolding compactSet_def compactSet'_def by (simp add: FCP_BCP_bridge)


section \<open>An illustrative problem in topology\<close>

(*A common classroom example asks: "show that the continuous image of a compact set is compact".
  Let's start by introducing some required definitions.*)

(**The mapping f:'u\<Rightarrow>'v is continuous if its direct image distributes (increasingly) over the closure*)
definition continuous::"('u \<sigma> \<Rightarrow> 'u \<sigma>) \<Rightarrow> ('v \<sigma> \<Rightarrow> 'v \<sigma>) \<Rightarrow> (('u \<Rightarrow> 'v))\<sigma>" ("_,_-continuous")
  where "\<C>\<^sub>1,\<C>\<^sub>2-continuous f = (\<forall>U. \<lbrakk>f (\<C>\<^sub>1 U)\<rbrakk> \<^bold>\<subseteq> \<C>\<^sub>2 \<lbrakk>f U\<rbrakk>)"

(**Continuity also has alternative definitions in terms closed and open sets. For instance, this one
  says that the mapping \<phi>:'u\<Rightarrow>'v is continuous iff the inverse image of every open set is open*)
definition continuous'::"('u \<sigma> \<Rightarrow> 'u \<sigma>) \<Rightarrow> ('v \<sigma> \<Rightarrow> 'v \<sigma>) \<Rightarrow> ('u \<Rightarrow> 'v) \<Rightarrow> bool" ("_,_-continuous''")
  where "\<C>\<^sub>1,\<C>\<^sub>2-continuous' f \<equiv> \<forall>V. \<C>\<^sub>2-open V \<longrightarrow> \<C>\<^sub>1-open \<lbrakk>f V\<rbrakk>\<inverse>"

(*Let us now introduce the usual (topological) constraints on closure operators*)
abbreviation "MONO \<C> \<equiv> \<forall>A B. A \<^bold>\<subseteq> B \<longrightarrow> \<C> A \<^bold>\<subseteq> \<C> B"
abbreviation "ADDI \<C> \<equiv> \<forall>A B. \<C> (A \<^bold>\<union> B) = (\<C> A \<^bold>\<union> \<C> B)"
abbreviation "EXPN \<C>  \<equiv> \<forall>A. A \<^bold>\<subseteq> \<C> A"
abbreviation "NORM \<C>  \<equiv> \<C> \<emptyset> = \<emptyset>"
abbreviation "IDEM \<C>  \<equiv> \<forall>A. (\<C> A) = \<C>(\<C> A)"
abbreviation "Hull \<C> \<equiv> MONO \<C> \<and> EXPN \<C> \<and> IDEM \<C>"
abbreviation "Closure \<C> \<equiv> Hull \<C> \<and> ADDI \<C> \<and> NORM \<C>"

(**The two definitions above are equivalent already when the operators \<C>\<^sub>1,\<C>\<^sub>2 are Hull-closures*)
lemma Continuous_equiv: assumes "Hull \<C>\<^sub>1" and "Hull \<C>\<^sub>2" 
                        shows "\<C>\<^sub>1,\<C>\<^sub>2-continuous f = \<C>\<^sub>1,\<C>\<^sub>2-continuous' f" 
  sorry (*TODO: manual proof pending*)


(*Now we can formalize and (try to) prove the conjecture: "the continuous image of a compact set is compact".*)
lemma assumes "Closure \<C>\<^sub>1" and "Closure \<C>\<^sub>2" (*note that these conditions can probably be weakened*)
      shows "\<C>\<^sub>1,\<C>\<^sub>2-continuous f \<longrightarrow> (\<forall>X. \<C>\<^sub>1-compactSet X \<longrightarrow> \<C>\<^sub>2-compactSet \<lbrakk>f X\<rbrakk>)" 
  oops (*Exercise: prove automatically under minimal conditions (adding cut-lemmata/definitions on demand)*)

end