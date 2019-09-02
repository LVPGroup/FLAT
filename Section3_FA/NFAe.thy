text\<open>
Formal Languages and Automata Theory (FLAT)
according to the book with same name (2nd version) by Zongli Jiang
created by Yongwang Zhao (zhaoyw@buaa.edu.cn)
School of Computer Science and Engineering, Beihang University, Beijing, China
\<close>

section\<open>3. Finite Automaton\<close>

subsection\<open>3.4: nondeterministic finite automaton with \<epsilon>\<close>

theory NFAe
imports NFA
begin

subsubsection\<open>definition 3-9: NFA with \<epsilon>\<close>

type_synonym ('a,'s)nfae = "('a option,'s)nfa"

abbreviation
  eps :: "('a,'s)nfae \<Rightarrow> ('s \<times> 's)set" where
  "eps A \<equiv> step A None"

primrec steps :: "('a,'s)nfae \<Rightarrow> 'a list \<Rightarrow> ('s \<times> 's)set" where
"steps A [] = (eps A)\<^sup>*" |
"steps A (a#w) = (eps A)\<^sup>* O step A (Some a) O steps A w"

(*
primrec delta :: "('a,'s)nfae \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set"
  where
"delta A [] s = (eps A)\<^sup>* `` {s}"
| "delta A (a#w) s = lift(delta A w) (lift(next A (Some a)) ((eps A)\<^sup>* `` {s}))"
*)

lemma steps_epsclosure[simp]: "(eps A)\<^sup>* O steps A w = steps A w"
by (cases w) (simp_all add: O_assoc[symmetric])

lemma in_steps_epsclosure:
  "\<lbrakk> (p,q) \<in> (eps A)\<^sup>*; (q,r) \<in> steps A w \<rbrakk> \<Longrightarrow> (p,r) \<in> steps A w"
apply(rule steps_epsclosure[THEN equalityE])
apply blast
done

lemma epsclosure_steps: "steps A w O (eps A)\<^sup>* = steps A w"
apply(induct w)
 apply simp
apply(simp add:O_assoc)
done

lemma in_epsclosure_steps:
  "\<lbrakk> (p,q) \<in> steps A w; (q,r) \<in> (eps A)\<^sup>* \<rbrakk> \<Longrightarrow> (p,r) \<in> steps A w"
apply(rule epsclosure_steps[THEN equalityE])
apply blast
done

lemma steps_append[simp]:  "steps A (v@w) = steps A v  O  steps A w"
by(induct v)(simp_all add:O_assoc[symmetric])

lemma in_steps_append[iff]:
  "(p,r) \<in> steps A (v@w) = ((p,r) \<in> (steps A v O steps A w))"
apply(rule steps_append[THEN equalityE])
apply blast
done

subsubsection\<open>definition 3-10: accepted language\<close>
definition
 accepts :: "('a,'s)nfae \<Rightarrow> 'a list \<Rightarrow> bool" where
"accepts A w = (\<exists>q. (q0 A,q) \<in> steps A w \<and> q \<in> F A)"

definition NFAeLang :: "('a,'s)nfae \<Rightarrow> 'a lang"
  where "NFAeLang m \<equiv> {x. accepts m x}"


(* Equivalence of steps and delta
* Use "(\<exists>x \<in> f ` A. P x) = (\<exists>a\<in>A. P(f x))" ?? *
Goal "\<forall>p. (p,q) : steps A w = (q : delta A w p)";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [comp_def,step_def]) 1);
by (Blast_tac 1);
qed_spec_mp "steps_equiv_delta";
*)

end
