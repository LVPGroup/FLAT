section\<open>2.Grammar\<close>

theory grammar
  imports Main
begin

subsection\<open>2.2 formal definition\<close>

subsubsection\<open>definition 2-1\<close>
abbreviation "l_prod p \<equiv> fst p"
abbreviation "r_prod p \<equiv> snd p"

consts isvar :: "'a \<Rightarrow> bool"

locale Grammar =
  fixes V :: "'a set"
  fixes T :: "'a set"
  fixes P :: "('a list \<times> 'a list) set"
  fixes S :: 'a

  fixes isvar :: "'a \<Rightarrow> bool"
  fixes isterminal :: "'a \<Rightarrow> bool"
  assumes "isterminal a \<equiv> \<not> (isvar a)"
  assumes "V \<noteq> {}"
  assumes "T \<noteq> {}"
  assumes "P \<noteq> {}"
  assumes "\<forall>v\<in>V. isvar v"
  assumes "\<forall>t\<in>T. isterminal t"
  assumes "\<forall>p\<in>P. l_prod p \<noteq> [] \<and> (\<exists>i<length (l_prod p). isvar ((l_prod p)!i))"
  assumes "isvar S"
begin

lemma "V \<inter> T = {}"
  by (metis Grammar_axioms Grammar_def disjoint_iff_not_equal)
end 

subsubsection\<open>examples\<close>

locale example0

begin

datatype V1 = A | B | C | S | a | b | c
fun isvar1 :: "V1 \<Rightarrow> bool"
  where "isvar1 A = True" | "isvar1 B = True" | "isvar1 C = True" | "isvar1 S = True" | "isvar1 _ = False"

definition isterminal1 :: "V1 \<Rightarrow> bool"
  where "isterminal1 v \<equiv> \<not>isvar1 v"

interpretation Grammar 
"{A,B,C,S}" 
"{a,b,c}" 
"{([A,B], [a,a,A])}"
S
isvar1
"isterminal1"
  apply(rule Grammar.intro) apply(simp add:isterminal1_def)+ 
  by auto

end

print_dependencies Grammar

subsubsection \<open>definition 2-2\<close>
context Grammar
begin

inductive_set derive_set :: "('a list \<times> 'a list) set"
  and derive :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" 
  and derives :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" 
  where
    "derive x y \<equiv> (x,y) \<in> derive_set"
  | "derives x y \<equiv> (x,y) \<in> derive_set\<^sup>*"
  | r_drvset: "\<exists>p\<in>P. \<alpha> = l_prod p \<and> \<beta> = r_prod p \<Longrightarrow> (\<gamma>@\<alpha>@\<delta>,\<gamma>@\<beta>@\<delta>)\<in>derive_set"

inductive_set reduce_set :: "('a list \<times> 'a list) set"
and reduce :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
and reduces :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
    "reduce x y \<equiv> (x,y) \<in> reduce_set"
  | "reduces x y \<equiv> (x,y) \<in> reduce_set\<^sup>*"
  | r_redset: "\<exists>p\<in>P. \<alpha> = l_prod p \<and> \<beta> = r_prod p \<Longrightarrow> (\<gamma>@\<beta>@\<delta>,\<gamma>@\<alpha>@\<delta>)\<in>reduce_set"

lemma "derive x y = reduce y x" 
  apply(rule iffI) 
    apply(rule derive_set.cases) apply simp
  using reduce_set.r_redset apply auto[1]

  apply(rule reduce_set.cases)
  apply simp
  using derive_set.r_drvset by auto

lemma "derives x y = reduces y x" sorry

end

subsubsection\<open>examples\<close>

context example0
begin

interpretation g1: Grammar 
"{A}" 
"{a}" 
"{([A], [a]),([A],[a,A])}"
A
isvar1
"isterminal1"
  apply(rule Grammar.intro) apply(simp add:isterminal1_def)+ done

lemma "g1.derive [A] [a]"
  using g1.r_drvset[where \<alpha>="[A]" and \<gamma> = "[]" and \<delta>="[]" and \<beta>="[a]"] by simp

lemma "g1.derive [A,A,a,a,A,A,A] [a,A,a,a,A,A,A]"
  using g1.r_drvset[where \<alpha>="[A]" and \<gamma> = "[]" and \<delta>="[A, a, a, A, A, A]" and \<beta>="[a]"] by simp


end

context Grammar
begin

definition allterminals :: "'a list \<Rightarrow> bool"
  where "allterminals w \<equiv> (\<forall>i<length w. isterminal (w!i))"

(* after interpretation, we propage the function ``derives'' to the theory. 
here we use local.derives to refer to the definition inner the locale. *)

subsubsection\<open>definition 2-4\<close>
definition sentence_form :: "'a list \<Rightarrow> bool"
  where "sentence_form w \<equiv> (derives [S] w)"

subsubsection\<open>definition 2-3\<close>

definition Lang :: "'a list set"
  where "Lang \<equiv> {w. sentence_form w \<and> allterminals w}"

definition sentence :: "'a list \<Rightarrow> bool"
  where "sentence w \<equiv> (w\<in>Lang)"

end

subsection\<open>2.3 construct syntax\<close>

subsubsection\<open>definition 2-5\<close>
thm Grammar.Lang_def
thm Grammar.intro

locale GrammarEquiv
  fixes 
begin
interpretation g1: Grammar
  sorry

thm g1.Lang_def

end

end
