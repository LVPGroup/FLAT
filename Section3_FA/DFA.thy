text\<open>
Formal Languages and Automata Theory (FLAT)
according to the book with same name (2nd version) by Zongli Jiang
created by Yongwang Zhao (zhaoyw@buaa.edu.cn)
School of Computer Science and Engineering, Beihang University, Beijing, China
\<close>

section\<open>3. Finite Automaton\<close>

subsection\<open>3.2: finite automaton\<close>

theory DFA
imports AutoProj
begin

subsubsection\<open>definition 3-1 finite automaton\<close>

text\<open>
M = <Q,\<Sigma>,\<delta>,q0,F>
Q: states, represented as 's
\<Sigma>: input alphabet, represented as 'a
\<delta>: transition function
q0: initial state
F: final states
dfa defined as below is a triple <q0,\<delta>,F>
\<close>
type_synonym ('a,'s)dfa = "'s \<times> ('a \<Rightarrow> 's \<Rightarrow> 's) \<times> ('s set)"

abbreviation "q0 \<equiv> start"
abbreviation "\<delta> \<equiv> next"
abbreviation "F \<equiv> fin"

definition
 foldl2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
"foldl2 f xs a = foldl (\<lambda>a b. f b a) a xs"

text\<open>
extend the \<delta>: \<Sigma> \<times> Q \<times> Q to \<delta>': \<Sigma>* \<times> Q \<times> Q
\<close>
definition
 \<delta>' :: "('a,'s)dfa \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's" where
"\<delta>' A = foldl2 (\<delta> A)"

subsubsection\<open>definition 3-2: accepted language\<close>

definition
 accepts :: "('a,'s)dfa \<Rightarrow> 'a list \<Rightarrow> bool" where
"accepts A w \<equiv> (\<delta>' A w (q0 A)) \<in> F A"

type_synonym 'a lang = "'a list set"

definition DFALang :: "('a,'s)dfa \<Rightarrow> 'a lang"
  where "DFALang m \<equiv> {x. accepts m x}"


lemma [simp]: "foldl2 f [] a = a \<and> foldl2 f (x#xs) a = foldl2 f xs (f x a)"
by(simp add:foldl2_def)

lemma delta_Nil[simp]: "\<delta>' A [] s = s"
by(simp add:\<delta>'_def)

lemma delta_Cons[simp]: "\<delta>' A (a#w) s = \<delta>' A w (\<delta> A a s)"
by(simp add:\<delta>'_def)

lemma delta_append[simp]:
 "\<And>q ys. \<delta>' A (xs@ys) q = \<delta>' A ys (\<delta>' A xs q)"
by(induct xs) simp_all


subsubsection\<open>definition 3-3: FA equivalence\<close>
definition DFAEquiv :: "('a,'s)dfa \<Rightarrow> ('a,'s)dfa \<Rightarrow> bool"
  where "DFAEquiv m1 m2 \<equiv> DFALang m1 = DFALang m2"

subsubsection\<open>definition 3-5: instantaneous description (ID)\<close>

type_synonym ('a,'s) IDType = "'a list \<times> 's \<times> 'a list"

fun ID :: "('a,'s)dfa \<Rightarrow> ('a,'s) IDType \<Rightarrow> bool"
  where "ID m (x,q,y) = (\<delta>' m x (q0 m) = q)"

inductive_set IDtran_set :: "('a,'s)dfa \<Rightarrow> (('a,'s) IDType \<times> ('a,'s) IDType) set"
and IDtran :: "('a,'s)dfa \<Rightarrow> ('a,'s) IDType \<Rightarrow> ('a,'s) IDType \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto> _" [80,80,80] 81)
  for M :: "('a,'s)dfa"
  where "M \<turnstile> x \<leadsto> y \<equiv> (x,y) \<in> IDtran_set M"
  | "\<lbrakk>ID M (x,q,a#y); (\<delta> M) a q = p \<rbrakk> \<Longrightarrow> ((x,q,a#y),(x@[a],p,y)) \<in> IDtran_set M"

text\<open>
a transition from an ID, the target is an ID too.
\<close>
lemma id_tran2_id: "\<lbrakk> ID M (x,q,y); M \<turnstile> (x,q,y) \<leadsto> (x',q',y') \<rbrakk> \<Longrightarrow> ID M (x',q',y')"
  apply(rule IDtran_set.cases) apply fast
  by auto


inductive nIDtrans :: "('a,'s)dfa \<Rightarrow> ('a,'s) IDType \<Rightarrow> nat \<Rightarrow> ('a,'s) IDType \<Rightarrow> bool" 
("_ \<turnstile> _ \<midarrow>_\<leadsto> _" [80,80,80,80] 81)
  where tran0: "g \<turnstile> x \<midarrow>0\<leadsto> x" |
        trann: "\<exists>r. g \<turnstile> x \<midarrow>n\<leadsto> r \<and> g \<turnstile> r \<leadsto> y \<Longrightarrow> g \<turnstile> x \<midarrow>(n+1)\<leadsto> y"

definition IDtrans :: "('a,'s)dfa \<Rightarrow> ('a,'s) IDType \<Rightarrow> ('a,'s) IDType \<Rightarrow> bool" ("_ \<turnstile> _ \<midarrow>*\<leadsto> _" [80,80,80] 81)
  where "IDtrans g x y \<equiv> (\<exists>n. g \<turnstile> x \<midarrow>n\<leadsto> y)"

definition IDtrans1 :: "('a,'s)dfa \<Rightarrow> ('a,'s) IDType \<Rightarrow> ('a,'s) IDType \<Rightarrow> bool" ("_ \<turnstile> _ \<midarrow>+\<leadsto> _" [80,80,80] 81)
  where "IDtrans1 g x y \<equiv> (\<exists>n>0. g \<turnstile> x \<midarrow>n\<leadsto> y)"

lemma id_trans2_id: "\<lbrakk> ID M (x,q,y); M \<turnstile> (x,q,y) \<midarrow>n\<leadsto> (x',q',y') \<rbrakk> \<Longrightarrow> ID M (x',q',y')"
  apply(induct n arbitrary: x q y x' q' y') using nIDtrans.cases
  apply (metis add.commute less_one not_add_less1) 
  apply(rule nIDtrans.cases) apply blast+ 
  using id_tran2_id
  by (metis Suc_eq_plus1 Suc_inject prod_cases3) 

subsubsection\<open>definition 3-6\<close>

definition aset :: "('a,'s)dfa \<Rightarrow> 's \<Rightarrow> 'a list set"
  where "aset M q \<equiv> {x. \<delta>' M x (q0 M) = q}"


end
