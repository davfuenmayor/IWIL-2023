theory BCIgen imports Main
begin

section \<open>A toy background theory\<close> (*skip on first read*)

(*Sets are encoded as characteristic functions/predicates (i.e. functions with a 'bool' codomain)*)
type_synonym 'a \<sigma> = \<open>'a \<Rightarrow> bool\<close>

(*Standard subset relation*)
definition subset::"'a \<sigma> \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" (infixr "\<^bold>\<subseteq>" 51) 
  where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"

(*The infimum (i.e. big-intersection) of a set of sets*)
definition Infimum:: "('a \<sigma>)\<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<Inter>")
  where "\<^bold>\<Inter>S \<equiv> \<lambda>z. (\<forall>X. S X \<longrightarrow> X z)"

(*A set S can be closed under a zero-ary, unary, or binary operation (\<chi>/0, \<phi>/1, or \<xi>/2 resp.)*)
abbreviation (input) op0_closed::"'a  \<Rightarrow> 'a \<sigma>  \<Rightarrow> bool" ("_-closed\<^sub>0") 
  where "\<chi>-closed\<^sub>0 \<equiv> \<lambda>S. S \<chi>" (*just for illustration, not really useful as a definition *)
definition op1_closed::"('a \<Rightarrow> 'a) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-closed\<^sub>1")
  where "\<phi>-closed\<^sub>1 \<equiv> \<lambda>S. \<forall>x. S x \<longrightarrow> S(\<phi> x)"
definition op2_closed::"('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-closed\<^sub>2")
  where "\<xi>-closed\<^sub>2 \<equiv> \<lambda>S. \<forall>x y. S x \<and> S y \<longrightarrow> S(\<xi> x y)"

(*Closure under a binary operation can be reduced to closure under a unary operation via partial application*)
lemma op2_closed_def2: "\<xi>-closed\<^sub>2 = (\<lambda>S. (\<forall>x. S x \<longrightarrow> (\<xi> x)-closed\<^sub>1 S))"
  unfolding op1_closed_def op2_closed_def by blast

(*Convenient abbreviation to say that the set S is a (sub)algebra wrt. to the operations \<chi>/0, \<phi>/1*)
definition "subAlg \<chi> \<phi> \<equiv> \<lambda>S. (\<chi>-closed\<^sub>0 S) \<and> (\<phi>-closed\<^sub>1 S)" (*i.e. (\<chi>-closed\<^sub>0 S) \<and> (\<phi>-closed\<^sub>1 S)*)

(*The set of elements denoted by terms of the form \<phi>\<^sup>n\<chi>. Let's call them 'inductive(ly generated) sets'*)
definition "indAlg \<chi> \<phi> \<equiv> \<^bold>\<Inter>(subAlg \<chi> \<phi>)"

(*Convenient shorthand for composing unary with binary functions*)
abbreviation (input) fcomp12::"('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'c)" (infixr "\<circ>\<^sub>1\<^sub>2" 75) 
  where "\<phi> \<circ>\<^sub>1\<^sub>2 \<xi> \<equiv> \<lambda>x y. \<phi>(\<xi> x y)"


section \<open>Encoding BCI problem\<close>

(*For each model, the semantic domain \<D>\<^sup>i can be seen as the carrier of an algebra \<A> = <\<D>\<^sup>i,e/0,s/1>*)
typedecl i 
consts e :: "i"  (*zero-ary operation*)
       s :: "i\<Rightarrow>i"  (*unary operation*)

(*The first three axioms axiomatize (via equations!) a binary operation 'f' in terms of 'e' and 's'*)
abbreviation (input) "A1 f \<equiv> \<forall>x. f x e = s e"
abbreviation (input) "A2 f \<equiv> \<forall>y. f e (s y) = s (s (f e y))"
abbreviation (input) "A3 f \<equiv> \<forall>x y. f (s x) (s y) = f x (f (s x) y)"

(*The final two axioms constrain a given set 'd' as a subuniverse (subalgebra) of \<A> (= <\<D>\<^sup>i,e/0,s/1>)*)
abbreviation (input) "A4 d \<equiv> d e"
abbreviation (input) "A5 d \<equiv> \<forall>x. d x \<longrightarrow> d (s x)"

(*Observe that the last two axioms correspond to the definition of a <e,s>-subalgebra of \<A>*)
lemma "(A4 d \<and> A5 d) = (subAlg e s) d"  unfolding  op1_closed_def subAlg_def ..

(*Boolos original problem basically asks whether, for an arbitrary <e,s>-subalgebra 'd', the image under 'f'
 (as axiomatized with A1-A3) of two particular elements (denoted by the terms of the form 's\<^sup>ne') is in 'd'*)
theorem BCI: "A1 f \<Longrightarrow> A2 f \<Longrightarrow> A3 f \<Longrightarrow> \<forall>d. (A4 d \<and> A5 d) \<longrightarrow> d (f (s(s(s(s e)))) (s(s(s(s e)))))"
  (*sledgehammer*) oops (*not solvable automatically yet*)


section \<open>A generalized BCI problem\<close>

(*Let us introduce a convenient shorthand notation for the (inductively generated) set N of all elements
 that are denoted by terms of the form s\<^sup>ne (for some arbitrary n). This is the smallest <e,s>-subalgebra.*)
abbreviation "N \<equiv> indAlg e s"

(*A natural generalization of Boolos' problem asks whether the image under 'f' of any two elements 
 belonging to N (i.e. denoted by terms of the form 's\<^sup>ne') belongs again to N. In other words, we want
 to find out whether axioms A1-A3 constrain 'f' in such a way that N is closed under 'f'.*)
lemma BCIgen: "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> f-closed\<^sub>2 N" oops (*no automatic proof...yet*)

(*First of all, note that the axioms A1-A3 don't guarantee that N is closed under the unary
  operation (f x) for any arbitrary x in the domain...*)
lemma "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> (\<forall>x. (f x)-closed\<^sub>1 N)" nitpick oops (*countermodel found*)
(*...but only for those x that belong in fact to the (inductive) set N...*)
lemma "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> (\<forall>x. N x \<longrightarrow> (f x)-closed\<^sub>1 N)" oops
(*...or equivalently*)
lemma "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> N  \<^bold>\<subseteq> (\<lambda>x. (f x)-closed\<^sub>1 N)" oops (*still difficult to prove automatically*)

(*Recall that when we want to show that a set contains an inductively generated set it suffices to show
  that it is a (sub)algebra wrt. the corresponding signature (the other direction does not hold though!)*)
lemma "(subAlg \<chi> \<phi>) S \<longrightarrow> (indAlg \<chi> \<phi>) \<^bold>\<subseteq> S" by (metis (full_types) Infimum_def indAlg_def subset_def)
lemma "(indAlg \<chi> \<phi>) \<^bold>\<subseteq> S \<longrightarrow> (subAlg \<chi> \<phi>) S" nitpick oops (*countermodel*)

(*Thus we see that our result holds if we manage to prove the following (slightly more general) statement:*)
lemma BCIgen: "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> (subAlg e s) (\<lambda>x. (f x)-closed\<^sub>1 N)"
  unfolding subAlg_def apply auto oops (*unfolds definition of subalgebra and obtains subgoals*)

(*which, after unfolding definitions, divides into two subgoals (using minimal sets of assumptions)*)
lemma BCIgen_base: "A1 f \<and> A2 f \<longrightarrow> (f e)-closed\<^sub>1 N" oops (*still not proven automatically*)
lemma BCIgen_induct: "A1 f \<and> A3 f \<longrightarrow> s-closed\<^sub>1 (\<lambda>x. (f x)-closed\<^sub>1 N)" oops (*still not proven automatically*)

(*As it happens, proving the two lemmata above requires the following (monomorphic!) definition:*)
definition p:: "(i \<Rightarrow> i \<Rightarrow> i) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool" (*we need to enforce the type for the definition to be useful*)
  where "p f \<equiv> N \<circ>\<^sub>1\<^sub>2 f" (*\<lambda>x y. N (f x y)*)

(*We can now prove the 'base' case...*)
lemma BCIgen_base: "A1 f \<and> A2 f \<longrightarrow> (f e)-closed\<^sub>1 N"
  by (smt (verit) Infimum_def indAlg_def op1_closed_def p_def subAlg_def)
(*...as well as the 'inductive' case*)
lemma BCIgen_induct: "A1 f \<and> A3 f \<longrightarrow> s-closed\<^sub>1 (\<lambda>x. (f x)-closed\<^sub>1 N)"
  by (smt (verit, best) Infimum_def indAlg_def op1_closed_def p_def subAlg_def)

(*So we can now finally prove what we set out to*)
lemma BCIgen: "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> f-closed\<^sub>2 N" 
  by (metis (mono_tags, lifting) Infimum_def BCIgen_base indAlg_def BCIgen_induct op2_closed_def2 subAlg_def)

(*Interestingly, ATPs can automatically detect that BCI follows from the (cut) lemma above!*)
theorem BCI: "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> (\<forall>d. (A4 d \<and> A5 d) \<longrightarrow> d (f (s(s(s(s e)))) (s(s(s(s e))))))"
  by (smt (z3) BCIgen Infimum_def indAlg_def op1_closed_def op2_closed_def2 subAlg_def)

(*The main benefit of proving Boolos problem automatically via a suitable cut-lemma (BCIgen) is that 
 we are now in a position to repeat the previous experiment using other axiom sets (e.g. axiomatizing 
 other Ackermann-style functions or hyper-operators). *)

end