text\<open>
Formal Languages and Automata Theory (FLAT)
according to the book with same name (2nd version) by Zongli Jiang
created by Yongwang Zhao (zhaoyw@buaa.edu.cn)
School of Computer Science and Engineering, Beihang University, Beijing, China
\<close>

section\<open>3. Finite Automaton\<close>

subsection\<open>3.4: nondeterministic finite automaton with \<epsilon>\<close>

theory NFAe_NFA_eq
  imports NFAe DFA
begin


subsubsection\<open>equivalence of DFA and NFAe\<close>

definition
 nfae2dfa :: "('a,'s)nfae \<Rightarrow> ('a,'s set)dfa" where
"nfae2dfa A = ({q0 A},
              \<lambda>a Q. \<Union>(\<delta> A (Some a) ` ((eps A)\<^sup>* `` Q)),
              {Q. \<exists>p \<in> (eps A)\<^sup>* `` Q. p \<in> F A})"


(*** Direct equivalence of NFAe and DFA ***)

lemma espclosure_DFA_delta_is_steps:
 "\<And>Q. (eps A)\<^sup>* `` (DFA.\<delta>' (nfae2dfa A) w Q) = steps A w `` Q"
apply (induct w)
 apply(simp)
apply (simp add: step_def nfae2dfa_def)
apply (blast)
done

lemma NFAe_DFA_equiv:
  "DFA.accepts (nfae2dfa A) w = NFAe.accepts A w"
proof -
  have "\<And>Q. Q \<in> F (nfae2dfa A) = (\<exists>q \<in> (eps A)\<^sup>* `` Q. q \<in> F A)"
    by(simp add:nfae2dfa_def)
  thus ?thesis
    apply(simp add:espclosure_DFA_delta_is_steps NFAe.accepts_def DFA.accepts_def)
    apply(simp add:nfae2dfa_def)
    apply blast
    done
qed

subsubsection\<open>equivalence of NFAe and NFA\<close>
definition
 nfae2nfa :: "('a,'s)nfae \<Rightarrow> ('a list,'s)nfa" where
"nfae2nfa A \<equiv> (q0 A, \<lambda>as q. NFAe.steps A as `` {q}, 
                if (\<exists>q\<in>F A. (q0 A,q) \<in> eps A) then F A \<union> {q0 A} else F A)"

lemma NFA_delta_is_lift_NFAe_delta:
 "NFA.steps (nfae2nfa A) w `` Q = NFAe.steps A (concat w) `` Q"
  apply (induct w arbitrary:Q) apply(simp add:nfae2nfa_def) sorry

lemma NFAe_NFA_equiv:
  "NFAe.accepts A (concat w) = NFA.accepts (nfae2nfa A) w"
  apply (simp add: DFA.accepts_def NFA.accepts_def NFA_delta_is_lift_NFAe_delta)
  apply (simp add: nfae2nfa_def) sorry


end
