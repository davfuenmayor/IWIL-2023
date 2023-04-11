theory "topology-compactness"
  imports Main
begin

(*Override Sledgehammer and Nitpick default params*)
declare[[smt_timeout=30]]
sledgehammer_params[isar_proof=false,max_facts=20]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3, atoms=a b c d]


(*Sets are encoded as characteristic functions/predicates (i.e. functions with a 'bool' codomain)*)
type_synonym 'a \<sigma> = \<open>'a \<Rightarrow> bool\<close>
(*Relations are encoded as set-valued functions*)
type_synonym ('a,'b)\<rho> = \<open>'a \<Rightarrow>'b \<sigma>\<close>
(*Convenient type constructors for unary & binary set-operators (allowing for some restricted two-sortedness).*)
type_synonym ('a,'b)\<O> = "('a \<sigma>,'b)\<rho>" (**i.e. 'a \<sigma> \<Rightarrow> 'b \<sigma>*)

(*Given a function, we define the well-known "image" set-operator (and its less-known dual).
  We can also read the term "(d)imageFun f A b" as "b is the (dual)image of A under f". *)
definition  imageFun::"('a \<Rightarrow> 'b) \<Rightarrow> ('a \<sigma>,'b)\<rho>" ("\<lbrakk>_ _\<rbrakk>") (*suggestive notation for partial application*)
  where "imageFun  f \<equiv> \<lambda>A. \<lambda>b. \<exists>a. (f a) = b \<and> A a"

abbreviation one2one::"'a \<sigma> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  where "one2one A f \<equiv> \<forall>x y. A x \<and> A y \<and> (f x) = (f y) \<longrightarrow> x = y"
abbreviation onto::"'a \<sigma> \<Rightarrow> 'b \<sigma> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "onto A B f \<equiv> \<forall>b. B b \<longrightarrow> (\<exists>a. A a \<and> (f a) = b)"

(**Predicate for indicating that a function maps a set into/onto another.*)
abbreviation map::"'a \<sigma> \<Rightarrow> 'b \<sigma> \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  where "map A B f \<equiv> \<forall>a. A a \<longrightarrow> B (f a)"
abbreviation (input) "embedding A B f \<equiv> map A B f \<and> one2one A f"

(*When notions of embedding and bijection collapse for all (endo)maps in a set, it is called finite*)
definition finite::"'a \<sigma> \<Rightarrow> bool"
  where "finite S \<equiv> \<forall>f. embedding S S f \<longrightarrow> onto S S f"

(*We introduce below some operations on sets which endow them with a Boolean algebra structure.*)

(*Two important 0-ary operations (aka. 'constants'). The "universal" and the "empty" set.*)
definition univ::"'a \<sigma>" ("\<UU>")
  where "\<UU> \<equiv> \<lambda>x. True"
definition empty::"'a \<sigma>" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<lambda>x. False"

(*Set complement is a unary operation*)
definition compl::"'a \<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<midarrow>") (*or type: ('a \<sigma>, 'a)\<rho> *)
  where \<open>\<^bold>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>

(*We can also define some binary operations on sets *)
definition inter::"'a \<sigma> \<Rightarrow> 'a \<sigma> \<Rightarrow> 'a \<sigma>" (infixr "\<^bold>\<inter>" 54) 
  where "A \<^bold>\<inter> B \<equiv> \<lambda>x. A x \<and> B x"
definition union::"'a \<sigma> \<Rightarrow> 'a \<sigma> \<Rightarrow> 'a \<sigma>" (infixr "\<^bold>\<union>" 53) 
  where "A \<^bold>\<union> B \<equiv> \<lambda>x. A x \<or> B x"

lemma deMorgan1: "\<forall>A B. \<^bold>\<midarrow>(A \<^bold>\<inter> B) = (\<^bold>\<midarrow>A \<^bold>\<union> \<^bold>\<midarrow>B)" by (simp add: compl_def inter_def union_def)
lemma deMorgan2: "\<forall>A B. \<^bold>\<midarrow>(A \<^bold>\<union> B) = (\<^bold>\<midarrow>A \<^bold>\<inter> \<^bold>\<midarrow>B)" by (simp add: compl_def inter_def union_def)

(*Union and intersection can be generalized to the infinitary case (i.e. operating on arbitrary sets of sets)*)
definition biginter::"('a \<sigma>)\<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<Inter>") 
  where "\<^bold>\<Inter>S \<equiv> \<lambda>x. \<forall>A. S A \<longrightarrow> A x"
definition bigunion:: "('a \<sigma>)\<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<Union>") 
  where "\<^bold>\<Union>S \<equiv> \<lambda>x. \<exists>A. S A  \<and>  A x"

lemma bigDeMorgan1: "\<forall>S. \<^bold>\<midarrow>(\<^bold>\<Inter> S) = \<^bold>\<Union>\<lbrakk>\<^bold>\<midarrow> S\<rbrakk>" 
  unfolding biginter_def bigunion_def compl_def imageFun_def by metis
lemma bigDeMorgan2: "\<forall>S. \<^bold>\<midarrow>(\<^bold>\<Union> S) = \<^bold>\<Inter>\<lbrakk>\<^bold>\<midarrow> S\<rbrakk>"
  unfolding biginter_def bigunion_def compl_def imageFun_def by metis

(*The algebra of sets is ordered wrt. standard subset relation*)
definition subset::"('a \<sigma>,'a \<sigma>)\<rho>" (infixr "\<^bold>\<subseteq>" 51) 
  where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"

(**Morphism condition for unary set-operators*)
abbreviation (input) morph1_sub::"('a,'a)\<O> \<Rightarrow> ('b,'b)\<O> \<Rightarrow> (('a,'b)\<O>)\<sigma>" ("_,_-MORPH\<^sup>\<subseteq>")
  where "\<psi>,\<upsilon>-MORPH\<^sup>\<subseteq> \<phi> \<equiv> \<forall>A. \<phi>(\<psi> A) \<^bold>\<subseteq> \<upsilon>(\<phi> A)"

(**The mapping f:'u\<Rightarrow>'v is continuous if its direct image distributes (increasingly) over the closure*)
abbreviation (input) Continuous::"('u \<sigma> \<Rightarrow> 'u \<sigma>) \<Rightarrow> ('v \<sigma> \<Rightarrow> 'v \<sigma>) \<Rightarrow> (('u \<Rightarrow> 'v))\<sigma>" ("_,_-continuous")
  where "\<psi>,\<nu>-continuous f \<equiv> \<psi>,\<nu>-MORPH\<^sup>\<subseteq> (imageFun f)"

lemma "\<psi>,\<nu>-continuous f = (\<forall>U. \<lbrakk>f (\<psi> U)\<rbrakk> \<^bold>\<subseteq> \<nu> \<lbrakk>f U\<rbrakk>)" ..

(*The following property of a collection of sets says that there exists a pair of them that covers a given set X*)
definition BCP_rel  ("BCP|\<^sub>_") (* read as 'binary cover property' *)
  where "BCP|\<^sub>X S \<equiv> \<exists>A B. S A \<and> S B \<and> (X \<^bold>\<subseteq> A \<^bold>\<union> B)"

(*The following property of a collection of sets says that there exists a finite subcollection that covers X*)
definition FCP_rel  ("FCP|\<^sub>_") (* read as 'finite cover property' *)
  where "FCP|\<^sub>X S \<equiv> \<exists>D. (\<exists>A. D A) \<and> D \<^bold>\<subseteq> S \<and> finite D \<and> (X \<^bold>\<subseteq> \<^bold>\<Union>D)"

(*The 'dual' of a unary operator*)
abbreviation op_dual::"('a,'a)\<O> \<Rightarrow> ('a,'a)\<O>" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"

definition fixpoint::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma>)\<sigma>" ("fp") 
  where "fp \<phi> \<equiv> \<lambda>X. \<phi> X = X"

(*Closed (open) sets are the fixed-points of (the dual of) a given closure operator*)
abbreviation closedset ("Cl[_]") where "Cl[\<C>] \<equiv> fp \<C>"
abbreviation openset ("Op[_]") where "Op[\<C>] \<equiv> fp (\<C>\<^sup>d)"

(*Using the relativized definitions above we can define compactness for sets/subspaces*)

(**The definition of compactness using the FCP (as in 'every open cover has a finite subcover')*)
definition compactSet::"('a,'a)\<O> \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("compactSet[_]")
  where "compactSet[\<C>] X \<equiv> \<forall>S. S \<^bold>\<subseteq> Op[\<C>] \<longrightarrow> (X \<^bold>\<subseteq> \<^bold>\<Union>S) \<longrightarrow> FCP|\<^sub>X S"

(**A simplified definition using the (simpler) BCP (i.e. FCP for the binary case)*)
abbreviation compactSet2::"('a,'a)\<O> \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("compactSet\<^sub>2[_]")
  where "compactSet\<^sub>2[\<C>] X \<equiv> \<forall>S. S \<^bold>\<subseteq> Op[\<C>] \<longrightarrow> (X \<^bold>\<subseteq> \<^bold>\<Union>S) \<longrightarrow> BCP|\<^sub>X S"

(*Both definitions above are not in general equivalent (but nitpick cannot give us a counterexample) *)
lemma "compactSet[\<C>] X \<longleftrightarrow> compactSet\<^sub>2[\<C>] X" (*nitpick*) oops

(*The issue is that the FCP and the BCP properties are not in general equivalent (but again nitpick cannot tell us)*)
lemma "FCP|\<^sub>X S \<longleftrightarrow> BCP|\<^sub>X S" (*nitpick*) oops

(*The equivalence between FCP and BCP holds in fact for those collections of sets that are closed under union*)
abbreviation "union_closed S \<equiv> \<forall>X Y. S X \<and> S Y \<longrightarrow> S(X \<^bold>\<union> Y)"
lemma "union_closed S \<Longrightarrow>  FCP|\<^sub>X S \<longleftrightarrow> BCP|\<^sub>X S" oops (*TODO: prove*)


(*A common classroom example for illustration: "the continuous image of a compact set is compact"
 We first try to prove this without constraining the involved closure operators:*)

(*Using the FCP-based definition we cannot obtain countermodels to the (false!) conjecture below*)
lemma "C\<^sub>1,C\<^sub>2-continuous f \<Longrightarrow> \<forall>X. compactSet[C\<^sub>1] X \<longrightarrow> compactSet[C\<^sub>2] \<lbrakk>f X\<rbrakk>" (*nitpick*) oops

(*Using the BCP based definition we can in fact obtain countermodels by nitpick*)
lemma "C\<^sub>1,C\<^sub>2-continuous f \<Longrightarrow> \<forall>X. compactSet\<^sub>2[C\<^sub>1] X \<longrightarrow> compactSet\<^sub>2[C\<^sub>2] \<lbrakk>f X\<rbrakk>" nitpick oops


(*For the sake of illustration let us now introduce a concrete topology (using preimage operators) *)

abbreviation preimage::"('a,'b)\<rho> \<Rightarrow> ('b,'a)\<O>"
  where "preimage R  \<equiv> \<lambda>B. \<lambda>a. \<exists>b. R a b \<and> B b"

typedecl i (*type for possible worlds*)
consts R\<^sub>1::"(i,i)\<rho>" (*the accessibility relation*)
consts R\<^sub>2::"(i,i)\<rho>" (*the accessibility relation*)

(*As defined above, \<C>\<^sub>1 and \<C>\<^sub>2 give rise to 'hull' closure operators (which are not idempotent in general)*)
abbreviation "\<C>\<^sub>1 \<equiv> preimage R\<^sub>1"
abbreviation "\<C>\<^sub>2 \<equiv> preimage R\<^sub>2"

lemma "union_closed Op[\<C>\<^sub>1]" nitpick oops (*counterexample*)

(*The variant using FUP does not show any countermodel (since they are all infinite)*)
lemma "\<C>\<^sub>1,\<C>\<^sub>2-continuous f \<Longrightarrow> \<forall>X. compactSet[\<C>\<^sub>1] X \<longrightarrow> compactSet[\<C>\<^sub>2] \<lbrakk>f X\<rbrakk>" (*nitpick*) oops
(*The variant using BUP shows in fact (finite) countermodels*)
lemma "\<C>\<^sub>1,\<C>\<^sub>2-continuous f \<Longrightarrow> \<forall>X. compactSet\<^sub>2[\<C>\<^sub>1] X \<longrightarrow> compactSet\<^sub>2[\<C>\<^sub>2] \<lbrakk>f X\<rbrakk>" nitpick oops

abbreviation \<open>reflexive R \<equiv> \<forall>a. R a a\<close>
abbreviation \<open>transitive R \<equiv> (\<forall>a b c. R a c \<and> R c b \<longrightarrow> R a b)\<close>
abbreviation "preorder R \<equiv> reflexive R \<and> transitive R"

lemma assumes "reflexive R\<^sub>1" shows "union_closed Op[\<C>\<^sub>1]" oops (*TODO: prove*)

(*Nitpick cannot find any countermodels to the conjecture below (which is in fact a theorem) *)
lemma assumes "preorder R\<^sub>1" and "preorder R\<^sub>2" (*with these assumptions \<C>\<^sub>1 & \<C>\<^sub>2 give rise to Alexandrov topologies*)
  shows "\<C>\<^sub>1,\<C>\<^sub>2-continuous f \<Longrightarrow> \<forall>X. compactSet\<^sub>2[\<C>\<^sub>1] X \<longrightarrow> compactSet\<^sub>2[\<C>\<^sub>2] \<lbrakk>f X\<rbrakk>"
  (*nitpick*) oops (*TODO: prove*)

end