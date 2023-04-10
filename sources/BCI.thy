theory BCI imports Main
begin

section \<open>A toy background theory\<close> (*skip on first read*)

(*Sets are encoded as characteristic functions/predicates (i.e. functions with a 'bool' codomain)*)
type_synonym 'a \<sigma> = \<open>'a \<Rightarrow> bool\<close>

(*The infimum (i.e. big-intersection) of a set of sets*)
definition Infimum:: "('a \<sigma>)\<sigma> \<Rightarrow> 'a \<sigma>" ("\<^bold>\<Inter>")
  where "\<^bold>\<Inter>S \<equiv> \<lambda>z. (\<forall>X. S X \<longrightarrow> X z)"

(*A set S can be closed under a zero-ary, unary, or binary operation (\<chi>/0, \<phi>/1, or \<xi>/2 resp.)*)
abbreviation (input) op0_closed::"'a  \<Rightarrow> 'a \<sigma>  \<Rightarrow> bool" ("_-closed\<^sub>0") 
  where "\<chi>-closed\<^sub>0 \<equiv> \<lambda>S. S \<chi>" (*just for illustration, not really useful as a definition *)
definition op1_closed::"('a \<Rightarrow> 'a) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("_-closed\<^sub>1")
  where "\<phi>-closed\<^sub>1 \<equiv> \<lambda>S. \<forall>x. S x \<longrightarrow> S(\<phi> x)"

(*Convenient abbreviation to say that the set S is a (sub)algebra wrt. to the operations \<chi>/0, \<phi>/1*)
abbreviation "subAlg \<chi> \<phi> \<equiv> \<lambda>S. (\<chi>-closed\<^sub>0 S) \<and> (\<phi>-closed\<^sub>1 S)" (*i.e. (\<chi>-closed\<^sub>0 S) \<and> (\<phi>-closed\<^sub>1 S)*)

(*The set of elements denoted by terms of the form \<phi>\<^sup>n\<chi>. Let's call them 'inductive(ly generated) sets'*)
abbreviation "indAlg \<chi> \<phi> \<equiv> \<^bold>\<Inter>(subAlg \<chi> \<phi>)"

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

(*Boolos problem corresponds to asking whether, for an arbitrary <e,s>-subalgebra 'd', the image under 'f'
 (as axiomatized with A1-A3) of two particular elements (denoted by the terms of the form 's\<^sup>ne') is in 'd'*)
theorem BCI: "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> (\<forall>d. (A4 d \<and> A5 d) \<longrightarrow> d (f (s(s(s(s e)))) (s(s(s(s e))))))"
  (*sledgehammer*) oops (*not solvable automatically*)


section \<open>Solving the BCI problem fully automatically\<close>

(*Let us introduce a convenient shorthand notation for the (inductively generated) set N of all elements
 that are denoted by terms of the form s\<^sup>ne (for some arbitrary n). This is the smallest <e,s>-subalgebra.*)
abbreviation "N \<equiv> indAlg e s"
(*Let us introduce the following (monomorphic!) definition:*)
definition p:: "(i \<Rightarrow> i \<Rightarrow> i) \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> bool)"
  where "p f \<equiv> N \<circ>\<^sub>1\<^sub>2 f"

(*In previous work it has been shown that the above definition 'p' makes Boolos' problem solvable automatically*)
theorem BCI: "A1 f \<and> A2 f \<and> A3 f \<longrightarrow> (\<forall>d. (A4 d \<and> A5 d) \<longrightarrow> d (f (s(s(s(s e)))) (s(s(s(s e))))))"
  (*sledgehammer*) by (smt (z3) Infimum_def op1_closed_def p_def)

end