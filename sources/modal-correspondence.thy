theory "modal-correspondence"
  imports Main
begin

section \<open>A toy background theory\<close> (*skip on first read*)

(*Sets are encoded as characteristic functions/predicates (i.e. functions with a 'bool' codomain)*)
type_synonym 'a \<sigma> = \<open>'a \<Rightarrow> bool\<close>
(*Relations are encoded as set-valued functions*)
type_synonym ('a,'b)\<rho> = \<open>'a \<Rightarrow>'b \<sigma>\<close>
(*Convenient type constructors for unary & binary set-operators (allowing for some restricted two-sortedness).*)
type_synonym ('a,'b)\<O> = "('a \<sigma>,'b)\<rho>" (**i.e. 'a \<sigma> \<Rightarrow> 'b \<sigma>*)
type_synonym ('a,'b)\<O>\<^sub>2 = "'a \<sigma> \<Rightarrow> ('a,'b)\<O>" (**i.e. 'a \<sigma> \<Rightarrow> a \<sigma> \<Rightarrow> 'b \<sigma>*)


(*General functions naturally feature a monoidal structure with function composition as the fundamental
  binary operation and the identity function as the unit (i.e. a zero-ary operation or 'constant').*)
abbreviation (input) fcomp'::"('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<^bold>\<circ>" 75)
  where "\<psi> \<^bold>\<circ> \<phi> \<equiv> \<lambda>x. \<psi>(\<phi> x)"
abbreviation (input) fid :: "('a \<Rightarrow> 'a)" ("ID") 
  where "ID \<equiv> \<lambda>x. x"

(*We say that \<phi> below is a morphism wrt. some (pair of) zero-ary, unary, or binary function(s)*)
abbreviation (input) morph0::"'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)\<sigma>" ("_,_-MORPH")
  where "A,B-MORPH \<phi> \<equiv> \<phi> A = B"
abbreviation morph1::"('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<sigma>" ("_,_-MORPH")
  where "\<psi>,\<upsilon>-MORPH \<phi> \<equiv> \<forall>A. \<phi>(\<psi> A) = \<upsilon>(\<phi> A)"
abbreviation morph2::"('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<sigma>" ("_,_-MORPH")
  where "\<xi>,\<delta>-MORPH \<phi> \<equiv> \<forall>A B. \<phi>(\<xi> A B) = \<delta> (\<phi> A) (\<phi> B)"

(*In the case of (curried) binary functions, we introduce a convenient unary operation: transposition. 
 'Transposing' a binary function corresponds to swapping its arguments/parameters.
 In the case of relations this corresponds to the notions of converse (aka. inverse, reverse) relation.*)
abbreviation (input) transpose::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" ("(_)\<Zcat>" [90])
  where \<open>f\<Zcat> \<equiv> \<lambda>a b. f b a\<close>

(*Relations, as functions, also exhibit a monoidal structure. For instance, they can also be composed.*)
definition rcomp::"('b,'c)\<rho> \<Rightarrow> ('a,'b)\<rho> \<Rightarrow> ('a,'c)\<rho>" (infixl "\<^bold>\<circ>\<^sup>r" 75)
  where "T \<^bold>\<circ>\<^sup>r R \<equiv> \<lambda>a c. \<exists>b. R a b \<and> T b c"
(*Equality plays the role of identity/unit elements (one identity for each type)*)
abbreviation (input) rid :: "('a,'a)\<rho>" ("ID\<^sup>r") 
  where "ID\<^sup>r \<equiv> (=)"

(*The following definition of relation embedding generalizes the well-known notion of order-embedding.*)
abbreviation rel_embedding::"('a,'a)\<rho> \<Rightarrow> ('b,'b)\<rho> \<Rightarrow> ('a \<Rightarrow>'b) \<Rightarrow> bool" ("_,_-EMBD")
  where "\<rho>1,\<rho>2-EMBD \<phi> \<equiv> \<forall>A B. (\<rho>1 A B) \<longleftrightarrow> (\<rho>2 (\<phi> A) (\<phi> B))"

(*The algebra of sets is ordered by the standard subset relation, as defined below.*)
definition subset::"('a \<sigma>,'a \<sigma>)\<rho>" (infixr "\<^bold>\<subseteq>" 51) 
  where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"
(*The algebra of relations is also an ordered algebra. We define the standard relation-inclusion relation
  also by drawing upon the corresponding set counterparts.*)
abbreviation subsetR::"(('a,'b)\<rho>,('a,'b)\<rho>)\<rho>" (infixr "\<^bold>\<subseteq>\<^sup>r" 51) 
  where "R \<^bold>\<subseteq>\<^sup>r T \<equiv> \<forall>a. R a \<^bold>\<subseteq> T a"

(*We can say of two unary operators \<phi> and \<psi> that they form an "adjoint" or "residuated" pair (notation: \<phi> \<stileturn> \<psi>).
 When \<phi> \<stileturn> \<psi> we say that \<phi> (\<psi>) is the left (right) "adjoint" or "residue" to \<psi> (\<phi>).*)
abbreviation Residuation::"(('a,'b)\<O>,('b,'a)\<O>)\<rho>" ("_\<stileturn>_")
  where "\<phi> \<stileturn> \<psi> \<equiv> \<forall>A B. \<phi> A \<^bold>\<subseteq> B \<longleftrightarrow> A \<^bold>\<subseteq> \<psi> B"

(*Given a relation R we can define the unary operators image and preimage (aka. inverse-image), 
 in an analogous fashion as in the case of functions. These operators come in dual pairs as shown.*)
definition image::"('a,'b)\<rho> \<Rightarrow> ('a,'b)\<O>"  
  where "image R     \<equiv> \<lambda>A. \<lambda>b. \<exists>a. R a b \<and> A a"
definition preimage::"('a,'b)\<rho> \<Rightarrow> ('b,'a)\<O>"
  where "preimage R  \<equiv> \<lambda>B. \<lambda>a. \<exists>b. R a b \<and> B b"
definition dimage::"('a,'b)\<rho> \<Rightarrow> ('a,'b)\<O>" (*dual image*)
  where "dimage R    \<equiv> \<lambda>A. \<lambda>b. \<forall>a. R a b \<longrightarrow> A a"
definition dpreimage::"('a,'b)\<rho> \<Rightarrow> ('b,'a)\<O>"  (*dual preimage*)
  where "dpreimage R \<equiv> \<lambda>B. \<lambda>a. \<forall>b. R a b \<longrightarrow> B b"

(*The (dual-)image of a relation corresponds to the (dual-)preimage of its converse and vice versa*)
lemma image_transp:  "image R = preimage R\<Zcat>" unfolding image_def preimage_def ..
lemma dimage_transp: "dimage R = dpreimage R\<Zcat>" unfolding dimage_def dpreimage_def ..

(*The operators above are in fact (dual) order-embeddings wrt. (converse) relation order*)
lemma preimage_order: "(\<^bold>\<subseteq>\<^sup>r),(\<^bold>\<subseteq>\<^sup>r)-EMBD preimage" unfolding preimage_def subset_def by force
lemma image_order: "(\<^bold>\<subseteq>\<^sup>r),(\<^bold>\<subseteq>\<^sup>r)-EMBD image" unfolding image_def subset_def by force
lemma dual_preimage_order: "(\<^bold>\<subseteq>\<^sup>r),(\<^bold>\<subseteq>\<^sup>r)\<Zcat>-EMBD dpreimage" unfolding dpreimage_def subset_def by metis
lemma dual_image_order: "(\<^bold>\<subseteq>\<^sup>r),(\<^bold>\<subseteq>\<^sup>r)\<Zcat>-EMBD dimage" unfolding dimage_def subset_def by blast

(*Moreover, they are (dual) monoid-homomorphisms (from the monoid of relations to the monoid of operators)*)
lemma image_id:    "ID\<^sup>r,ID-MORPH image" unfolding image_def by simp
lemma preimage_id: "ID\<^sup>r,ID-MORPH preimage" unfolding preimage_def by simp
lemma dimage_id: "ID\<^sup>r,ID-MORPH dimage" unfolding dimage_def by simp
lemma dpreimage_id: "ID\<^sup>r,ID-MORPH dpreimage" unfolding dpreimage_def by simp
lemma image_comp:    "(\<^bold>\<circ>\<^sup>r),(\<^bold>\<circ>)-MORPH image" unfolding image_def by (metis (no_types, opaque_lifting) rcomp_def)
lemma preimage_comp: "(\<^bold>\<circ>\<^sup>r),(\<^bold>\<circ>)\<Zcat>-MORPH preimage" unfolding preimage_def by (metis (no_types, opaque_lifting) rcomp_def)
lemma dimage_comp: "(\<^bold>\<circ>\<^sup>r),(\<^bold>\<circ>)-MORPH dimage" unfolding dimage_def by (metis (no_types, opaque_lifting) rcomp_def)
lemma dpreimage_comp: "(\<^bold>\<circ>\<^sup>r),(\<^bold>\<circ>)\<Zcat>-MORPH dpreimage" unfolding dpreimage_def by (metis (no_types, opaque_lifting) rcomp_def)

(*Interestingly, operators derived from relations form residuated pairs as shown below: *)
lemma residuation1: "image R \<stileturn> dpreimage R" by (smt (verit, del_insts) subset_def dpreimage_def image_def)
lemma residuation2: "preimage R \<stileturn> dimage R" by (smt (verit) subset_def dimage_def preimage_def)


section \<open>Automating modal correspondences\<close>

(*Let us introduce some properties of relations*)
definition \<open>reflexive R \<equiv> \<forall>a. R a a\<close>
definition \<open>symmetric R \<equiv> \<forall>a b. R a b \<longrightarrow> R b a\<close> 
definition \<open>transitive R \<equiv> (\<forall>a b c. R a c \<and> R c b \<longrightarrow> R a b)\<close>
definition \<open>dense R \<equiv> \<forall>a b. R a b \<longrightarrow> (\<exists>c. R a c \<and> R c b)\<close> 
definition \<open>euclidean R \<equiv> \<forall>a b c. R c a \<and> R c b \<longrightarrow> R a b\<close> 

(*The key to automatically proving correspondences between conditions on relations and their respective
  unary operations lies on the following alternative relational-algebraic definitions*)
lemma reflexive_reldef: \<open>reflexive R = ID\<^sup>r \<^bold>\<subseteq>\<^sup>r R\<close> by (simp add: subset_def reflexive_def)
lemma symmetric_reldef: \<open>symmetric R = (R\<Zcat> \<^bold>\<subseteq>\<^sup>r R)\<close> by (metis (full_types) subset_def symmetric_def)
lemma euclidean_reldef: \<open>euclidean R = (R \<^bold>\<circ>\<^sup>r R\<Zcat> \<^bold>\<subseteq>\<^sup>r R)\<close> by (simp add: subset_def euclidean_def rcomp_def)
lemma transitive_reldef: \<open>transitive R = (R \<^bold>\<circ>\<^sup>r R \<^bold>\<subseteq>\<^sup>r R)\<close> by (simp add: subset_def rcomp_def transitive_def)
lemma dense_reldef: \<open>dense R = (R \<^bold>\<subseteq>\<^sup>r R \<^bold>\<circ>\<^sup>r R)\<close> by (simp add: subset_def dense_def rcomp_def)


(*For the sake of illustration let us now introduce a shallow embedding of a normal modal logic:*)
typedecl i (*type for possible worlds*)
consts R::"(i,i)\<rho>" (*the accessibility relation*)

(*Boolean logical connectives*)
abbreviation compl::"(i,i)\<O>" ("\<^bold>\<midarrow>") (*or type: ('a \<sigma>, 'a)\<rho> *)
  where \<open>\<^bold>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>
abbreviation mand::"(i,i)\<O>\<^sub>2" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>x. A x \<and> B x"
abbreviation mor::"(i,i)\<O>\<^sub>2" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>x. A x \<or> B x"
definition mimpl::"(i,i)\<O>\<^sub>2" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>x. A x \<longrightarrow> B x" (** note that (set-)implication is made a definition*)
(*Modal operators*)
abbreviation box::"(i,i)\<O>" ("\<^bold>\<box>_"[80])
  where "\<^bold>\<box>A \<equiv> dpreimage R A"
abbreviation dia::"(i,i)\<O>" ("\<^bold>\<diamond>_"[80])
  where "\<^bold>\<diamond>A \<equiv> preimage R A"

(*Definition of modal validity: truth in all worlds*)
definition valid ("\<lfloor>_\<rfloor>")
  where "\<lfloor>F\<rfloor> \<equiv> \<forall>w. F w"

(*The following lemma is an algebraic-variant of the Deduction Theorem for modal logics.*)
lemma ADT: "\<lfloor>A \<^bold>\<rightarrow> B\<rfloor> = (A \<^bold>\<subseteq> B)" by (simp add: mimpl_def subset_def valid_def)


(*Let us now prove automatically several well-known modal correspondences. Observe how ATPs (via sledgehammer)
  manage to find the right definitions in the background theory, by cleverly exploiting the lemma 'ADT'
 and the 'XY_reldef' family of (definitional) lemmata.*)

lemma refl_corresp:  "reflexive R \<longleftrightarrow> (\<forall>P. \<lfloor>P \<^bold>\<rightarrow> \<^bold>\<diamond>P\<rfloor>)"
  by (metis ADT preimage_id preimage_order reflexive_reldef)
lemma refl_corresp': "reflexive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<box>P \<^bold>\<rightarrow> P\<rfloor>)"
  by (metis ADT dpreimage_id dual_preimage_order reflexive_reldef)

lemma symm_corresp: "symmetric R \<longleftrightarrow> (\<forall>P. \<lfloor>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>P\<rfloor>)"
  by (metis ADT image_transp preimage_order residuation1 symmetric_reldef)
lemma symm_corresp': "symmetric R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<diamond>\<^bold>\<box>P \<^bold>\<rightarrow> P\<rfloor>)"
  by (metis ADT dimage_transp dual_preimage_order residuation2 symmetric_reldef)

lemma trans_corresp:  "transitive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<diamond>\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^bold>\<diamond>P\<rfloor>)"
  by (metis ADT preimage_comp preimage_order transitive_reldef)
lemma trans_corresp': "transitive R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<box>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>P\<rfloor>)"
  by (metis ADT dpreimage_comp dual_preimage_order transitive_reldef)

lemma dense_corresp: "dense R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<box>\<^bold>\<box>P \<^bold>\<rightarrow> \<^bold>\<box>P\<rfloor>)"
  by (metis ADT dense_reldef dpreimage_comp dual_preimage_order)
lemma dense_corresp': "dense R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<diamond>P\<rfloor>)"
  by (metis ADT dense_reldef preimage_comp preimage_order)

lemma euclidean_corresp: "euclidean R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<diamond>P \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>P\<rfloor>)"
  by (smt (verit, ccfv_SIG) ADT euclidean_reldef image_transp preimage_comp preimage_order residuation1)
lemma euclidean_corresp': "euclidean R \<longleftrightarrow> (\<forall>P. \<lfloor>\<^bold>\<diamond>\<^bold>\<box>P \<^bold>\<rightarrow> \<^bold>\<box>P\<rfloor>)"
  by (smt (verit, del_insts) ADT dimage_transp dpreimage_comp dual_preimage_order euclidean_reldef residuation2)


section \<open>Lemmon-Scott schema\<close>

(*Exercise: formalize and prove the Lemmon-Scott schema (cf. SEP article on modal logic:
    https://plato.stanford.edu/entries/logic-modal/#GenAxi)*)


end
