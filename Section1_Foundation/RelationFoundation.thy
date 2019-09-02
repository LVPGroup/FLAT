(*
Isabelle/HOL source for lectures of Set Theory
created by Yongwang ZHAO
School of Computer Science and Engineering, Beihang University, China
zhaoyw@buaa.edu.cn
*)

theory RelationFoundation
imports Main HOL.Real

begin

declare [[smt_timeout = 60]]

chapter {* chapter 6. Relation *}

section {* section 6.1: relation and its properties *}

subsection {* definition 6.1 *}

type_synonym ('a, 'b) Relation = "('a \<times> 'b) set"

type_synonym Nat_Relation = "(nat \<times> nat) set"

consts Rel_A :: "('a, 'b) Relation"

lemma "{x::'a. True} = UNIV" by auto
lemma "{x::'b. True} = UNIV" by auto
lemma "Rel_A \<subseteq> UNIV \<times> UNIV" by auto

lemma "\<forall>x y. (x,y) \<in> Rel_A \<or> (x,y) \<notin> Rel_A" 
  by auto

subsection {* example 6.1 *}

datatype Teacher = x1 | y1 | z1
datatype Student = a1 | b1 | c1 | d1

definition "T_S \<equiv> {(x1,a1), (x1,b1), (y1,b1), (z1,b1), (z1,d1)}"
  
definition real_lg :: "(real,real) Relation"
  where "real_lg \<equiv> {(x,y). x > y}"

definition real_S :: "(real,real) Relation"
  where "real_S \<equiv> {(x,y). y = x\<^sup>2}"

subsection {* predicate representation of relation *}

definition Rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) Relation"
  where "Rel P \<equiv> {(x,y). P x y}"

lemma "\<forall>x y. P x y \<longleftrightarrow> (x,y)\<in>Rel P" 
  by (simp add:Rel_def)

subsection {* definition 6.2 *}

thm DomainI
lemma "Domain R = {x. \<exists>y. (x,y)\<in>R}"
  unfolding Domain_def by auto

thm RangeI 
lemma "Range R = {y. \<exists>x. (x,y)\<in>R}"
  unfolding Range_def by auto

lemma "Domain Rel_A \<subseteq> {x::'a. True}" by auto
lemma "Range Rel_A \<subseteq> {x::'b. True}" by auto

definition "U_x X \<equiv> {(x, y). x\<in>X \<and> y\<in>X}"

definition "I_x X \<equiv> {(x, y). x\<in>X \<and> y\<in>X \<and> x = y}"

subsection {* example 6.2 *}

value "U_x {0::int,1,2}" 

(* value "I_x {0::int,1,2}" *)
lemma "I_x {0::int,1,2} = {(0,0),(1,1),(2,2)}"
  unfolding I_x_def by force

subsection {* definition 6.3 *}

thm reflp_def

thm irreflp_def

thm symp_def

thm antisym_def

thm transp_def

thm Id_def

subsection {* example 6.5 *}

thm Relation.refl_Id

lemma "\<not> (irrefl Id)"
  by (simp add: irrefl_def)  

thm Relation.sym_Id

thm Relation.antisym_Id

thm Relation.trans_Id

definition int_less_eq :: "(int,int) Relation"
  where "int_less_eq \<equiv> {(x,y). x \<le> y}"

lemma "refl int_less_eq" 
  by (simp add:int_less_eq_def refl_on_def)

lemma "\<not>(irrefl int_less_eq)"
  by (simp add:int_less_eq_def irrefl_def)

lemma "antisym int_less_eq"
  by (simp add:int_less_eq_def antisym_def)

lemma "\<not> (sym int_less_eq)" 
  unfolding int_less_eq_def sym_def 
    proof -
      have "(0::int) < (1::int)" by auto 
      have "(0::int, 1::int) \<in> {(x, y). x \<le> y}" by auto
      moreover
      have "(1::int, 0::int) \<notin> {(x, y). x \<le> y}" by auto
      ultimately have "\<exists>(x::int) (y::int). (x, y) \<in> {(x, y). x \<le> y} \<and> (y, x) \<notin> {(x, y). x \<le> y}" 
        by blast
      then show "\<not> (\<forall>(x::int) (y::int). (x, y) \<in> {(x, y). x \<le> y} \<longrightarrow> (y, x) \<in> {(x, y). x \<le> y})" 
        by auto
    qed

lemma "trans int_less_eq" 
  by (simp add:int_less_eq_def trans_def)

definition int_less :: "(int,int) Relation"
  where "int_less \<equiv> {(x,y). x < y}"

lemma "irrefl int_less" 
  by (simp add:int_less_def irrefl_def)

lemma "\<not> (refl int_less)"
  by (simp add:int_less_def refl_on_def)

lemma "antisym int_less"
  by (simp add:int_less_def antisym_def)

lemma "\<not> (sym int_less)" 
  unfolding int_less_def sym_def 
    proof -
      have "(0::int) < (1::int)" by auto 
      have "(0::int, 1::int) \<in> {(x, y). x < y}" by auto
      moreover
      have "(1::int, 0::int) \<notin> {(x, y). x < y}" by auto
      ultimately have "\<exists>(x::int) (y::int). (x, y) \<in> {(x, y). x < y} \<and> (y, x) \<notin> {(x, y). x < y}" 
        by blast
      then show "\<not> (\<forall>(x::int) (y::int). (x, y) \<in> {(x, y). x < y} \<longrightarrow> (y, x) \<in> {(x, y). x < y})" 
        by auto
    qed

lemma "trans int_less" 
  by (simp add:int_less_def trans_def)

section {* section 6.2: relation operation*}

subsection {* definition 6.4 *}

lemma "(x,y)\<in>(R \<inter> S) = ((x,y)\<in>R \<and> (x,y)\<in>S)"
  by auto

lemma "(x,y)\<in>(R \<union> S) = ((x,y)\<in>R \<or> (x,y)\<in>S)"
  by auto

lemma "(x,y)\<in>(R - S) = ((x,y)\<in>R \<and> \<not> (x,y)\<in>S)"
  by auto

lemma "(x,y)\<in>(- R) = (\<not> (x,y)\<in>R)"
  by auto

subsection {* example 6.6 *}

definition R1 :: "(int,int) Relation"
  where "R1 \<equiv> {(1,3),(3,1),(2,4),(4,2)}"

definition S1 :: "(int,int) Relation"
  where "S1 \<equiv> {(1,4),(4,1)}"

value "R1 \<union> S1"

value "R1 \<inter> S1"

value "R1 - S1"

value "{1,2,3,4}\<times>{1,2,3,4} - R1"

subsection {* definition 6.5 *}

thm Relation.relcomp_unfold

subsection {* theorem 6.1 *}

thm Relation.O_assoc

lemma "(R O S) O P = R O (S O P)"
  proof -
    have "\<forall>x w. (x,w)\<in>(R O S) O P \<longleftrightarrow> (\<exists>z. (x,z)\<in> R O S \<and> (z,w)\<in>P)" by auto
    then have "\<forall>x w. (x,w)\<in>(R O S) O P \<longleftrightarrow> (\<exists>z y. (x,y)\<in> R \<and> (y,z)\<in>S \<and> (z,w)\<in>P)" by auto
    then have "\<forall>x w. (x,w)\<in>(R O S) O P \<longleftrightarrow> (\<exists>y. (x,y)\<in> R \<and> (\<exists>z. (y,z)\<in>S \<and> (z,w)\<in>P))" by auto
    then have "\<forall>x w. (x,w)\<in>(R O S) O P \<longleftrightarrow> (\<exists>y. (x,y)\<in> R \<and> (y,w)\<in>S O P)" by auto
    then have "\<forall>x w. (x,w)\<in>(R O S) O P \<longleftrightarrow> (x,w)\<in>R O (S O P)" by auto
    then show ?thesis by auto
  qed

subsection {* example 6.7 *}

definition R2 :: "(int,int) Relation"
  where "R2 \<equiv> {(1,2),(3,4),(2,2)}"

definition S2 :: "(int,int) Relation"
  where "S2 \<equiv> {(4,2),(2,5),(3,1),(1,3)}"

value "R2 O S2"
value "S2 O R2"
value "(R2 O S2) O R2"
value "R2 O ( S2 O R2)"
value "R2 O R2"
value "S2 O S2"
value "R2 O R2 O R2"

subsection {* example 6.8 *}

definition R3 :: "(int,int) Relation"
  where "R3 \<equiv> {(x, y). y = 2 * x}"

definition S3 :: "(int,int) Relation"
  where "S3 \<equiv> {(x, y). y = 7 * x}"

lemma "R3 O S3 = {(x,y). y = 14 * x}" 
  proof -
    have "\<forall>x y. (x,y)\<in>R3 O S3 \<longleftrightarrow> (\<exists>z. (x,z)\<in>R3 \<and> (z,y)\<in>S3)" by auto
    then have "\<forall>x y. (x,y)\<in>R3 O S3 \<longleftrightarrow> (x,2*x)\<in>R3 \<and> (2*x,y)\<in>S3" 
      by (simp add: R3_def S3_def) 
    then have "\<forall>x y. (x,y)\<in>R3 O S3 \<longleftrightarrow> y = 14 * x" 
      by (simp add: R3_def S3_def) 
    then show ?thesis by auto
  qed

lemma R3_lm1: "R3 O R3 = {(x,y). y = 4 * x}" apply(simp add:R3_def) by auto
(* please prove it by youself *)

lemma "R3 O R3 O R3 = {(x,y). y = 8 * x}" using R3_lm1 by(simp add:R3_def, auto)

lemma "R3 O S3 O R3 = {(x,y). y = 28 * x}" 
apply(rule subst[where t="S3 O R3" and s = "{(x,y). y = 14 * x}"]) 
apply(simp add:R3_def S3_def) apply auto[1]
by(simp add:R3_def,auto)

subsection {* definition 6.6 *}

primrec R_n :: "('a, 'a) Relation \<Rightarrow> nat \<Rightarrow> ('a, 'a) Relation" ("_\<^sup>_" [81] 80)
  where R_n_zero: "R\<^sup>0 = Id" |
        R_n_suc: "R_n R (Suc n) = R O (R\<^sup>n)"

lemma R_m_n : "\<forall>R m n. R\<^sup>m O R\<^sup>n = R_n R (m+n)"
  proof -
  {
    fix R m
    have "\<forall>n. R\<^sup>m O R\<^sup>n = R_n R (m+n)"
      proof(induct m)
        case 0
        show ?case by simp
      next
        case (Suc k)
        assume p: "\<forall>n. R\<^sup>k O R\<^sup>n = R_n R (k + n)"
        show ?case 
          proof
            fix n
            have "R_n R (Suc k) O R\<^sup>n = R O (R_n R k) O R\<^sup>n" 
              using R_n_suc by auto
            with p have "R_n R (Suc k) O R\<^sup>n = R O (R_n R (k+n))" by auto
            then show "R_n R (Suc k) O R\<^sup>n = R_n R (Suc k + n)" using R_n_suc by auto
          qed
      qed
  }
  then show ?thesis by blast
  qed

lemma "(R\<^sup>m)\<^sup>n = R_n R (m*n)" sorry
(* please prove it by youself *)

subsection {* definition 6.7 *}

thm Relation.converse_unfold

lemma "(R\<inverse>)\<inverse> = R"
  using Relation.converse_converse by simp

subsection {* theorem 6.2 *}

thm Relation.converse_relcomp

lemma "(R O S)\<inverse> = S\<inverse> O R\<inverse>" 
  proof -
    have "\<forall>x y. (x,y)\<in>(R O S)\<inverse> \<longleftrightarrow> (y,x)\<in>(R O S)" by auto
    then have "\<forall>x y. (x,y)\<in>(R O S)\<inverse> \<longleftrightarrow> (\<exists>z. (y,z)\<in>R \<and> (z,x)\<in>S)" by auto
    then have "\<forall>x y. (x,y)\<in>(R O S)\<inverse> \<longleftrightarrow> (\<exists>z. (z,y)\<in>R\<inverse> \<and> (x,z)\<in>S\<inverse>)" by auto
    then have "\<forall>x y. (x,y)\<in>(R O S)\<inverse> \<longleftrightarrow> (x,y)\<in>S\<inverse> O R\<inverse>" by auto
    then show ?thesis by auto
  qed

subsection {* definition 6.8 *}

(* reflexive closure*)
inductive_set reflcl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(r(_))" [1000] 999)
  for R :: "('a \<times> 'a) set"
where
  R_reflcl:      "(a, b) \<in> R \<Longrightarrow> (a, b) \<in> r(R)"
| R_into_reflcl: "(a, a) \<in> r(R)"

(* transitive closure*)
inductive_set trancl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(t(_))" [1000] 999)
  for R :: "('a \<times> 'a) set"
where
  R_into_trancl: "(a, b) \<in> R \<Longrightarrow> (a, b) \<in> t(R)"
| R_trancl:      "(a, b) \<in> t(R) \<Longrightarrow> (b, c) \<in> R \<Longrightarrow> (a, c) \<in> t(R)" 
  (* R_trancl: "(a, b) \<in> R \<Longrightarrow> (b, c) \<in> t(R) \<Longrightarrow> (a, c) \<in> t(R)" *)

(* symmetric closure*)
inductive_set symcl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(s(_))" [1000] 999)
  for R :: "('a \<times> 'a) set"
where
  R_symcl:      "(a, b) \<in> R \<Longrightarrow> (a, b) \<in> s(R)"
| R_into_symcl: "(a, b) \<in> R \<Longrightarrow> (b, a) \<in> s(R)"

(* the set R is contained in r(R) *)
lemma reflcl_cl: "R \<subseteq> r(R)" 
  using R_reflcl subrelI by fastforce 

(* the set R is contained in t(R) *)
lemma trancl_cl: "R \<subseteq> t(R)" 
  using R_trancl by (simp add: subrelI trancl.R_into_trancl)  

(* the set R is contained in s(R) *)
lemma symcl_cl: "R \<subseteq> s(R)"
   using R_symcl subrelI by fastforce 

(* reflexive closure is reflexive*)
lemma "refl (r(R))"
  using R_into_reflcl reflp_def reflp_refl_eq by force 

(* symmetric closure is symmetric*)
lemma "sym (s(R))"
  using R_into_symcl R_symcl
    by (simp add: sym_def symcl.simps)  

(* transitive closure is transitive*)
lemma "trans (t(R))"
   sorry
(* please prove it on paper by youself *)

lemma "refl R \<Longrightarrow> r(R) = R"
  proof -
    assume p: "refl R"
    have "R \<subseteq> r(R)" using reflcl_cl by auto
    moreover
    have "r(R) \<subseteq> R"
      proof -
        {
          fix a b
          assume a0: "(a, b)\<in>r(R)"
          then have "(a, b)\<in>R" 
            apply(rule reflcl.cases) 
            apply simp
            by (meson UNIV_I p refl_onD)
        }
        then have "\<forall>z. z\<in>r(R) \<longrightarrow> z\<in>R" by auto
        then show ?thesis by auto
      qed
    ultimately show ?thesis by auto
  qed
   

lemma "sym R \<Longrightarrow> s(R) = R"
  proof -
    assume p: "sym R"
    have "R \<subseteq> s(R)" using symcl_cl by auto
    moreover
    have "s(R) \<subseteq> R"
      proof -
        {
          fix a b
          assume a0: "(a, b)\<in>s(R)"
          then have "(a, b)\<in>R" 
            apply(rule symcl.cases)
            apply simp
            by (meson p symE)
        }
        then have "\<forall>z. z\<in>s(R) \<longrightarrow> z\<in>R" by auto
        then show ?thesis by auto
      qed
    ultimately show ?thesis by auto
  qed

lemma "trans R \<Longrightarrow> t(R) = R" sorry
(* please prove it on paper by youself *)


lemma "\<lbrakk>R \<subseteq> S; refl S\<rbrakk> \<Longrightarrow> r(R) \<subseteq> S"
  (* by (metis UNIV_I refl_on_def reflcl.simps subrelI subsetCE) *)
  proof -
    assume p1: "R \<subseteq> S"
      and  p2: "refl S"
    {
      fix a b
      assume "(a,b)\<in>r(R)"
      then have "(a,b)\<in>S"
        apply(rule reflcl.cases)
        using p1 apply blast
        using p2 by (meson UNIV_I refl_onD)       
        
    }
    then show "r(R) \<subseteq> S" by auto
  qed

lemma "\<lbrakk>R \<subseteq> S; sym S\<rbrakk> \<Longrightarrow> s(R) \<subseteq> S"
  (* by (meson subrelI subsetCE symE symcl.cases) *)
  proof -
    assume p1: "R \<subseteq> S"
      and  p2: "sym S"
    {
      fix a b
      assume "(a,b)\<in>s(R)"
      then have "(a,b)\<in>S"
        apply(rule symcl.cases)
        using p1 apply auto[1]
        using p1 p2 by (meson subsetCE symE)
    }
    then show "s(R) \<subseteq> S" by auto
  qed

lemma tR_trans_S: "\<lbrakk>R \<subseteq> S; trans S\<rbrakk> \<Longrightarrow> t(R) \<subseteq> S" sorry
(* please prove it on paper by youself *)
(*
  proof -
    assume p1: "R \<subseteq> S"
      and  p2: "trans S"
    {
      fix a b
      assume "(a,b)\<in>t(R)"
      then have "(a,b)\<in>S"
        apply(rule trancl.cases)
        using p1 apply auto[1]
        
        using p1 p2 apply (meson subsetCE symE)
        using p1 by auto
    }
    then show "s(R) \<subseteq> S" by auto
  qed
*)

subsection {* theorem 6.3 *}

lemma "r(R) = R \<union> Id" 
  proof -
    have "\<forall>x. x\<in>r(R) \<longrightarrow> x\<in>(R \<union> Id)"
      proof -
      {
        fix x
        assume p0: "x\<in>r(R)"
        then obtain a and b where a1: "x = (a,b)"
          by fastforce 
        have "x\<in>(R \<union> Id)"
          apply(rule reflcl.cases)
          using p0 a1 by simp+
      }
      then show ?thesis by auto
      qed
    moreover
    have "\<forall>x. x\<in>(R \<union> Id) \<longrightarrow> x\<in>r(R)"
      proof -
      {
        fix x
        assume p0: "x\<in>(R \<union> Id)"
        then obtain a and b where a1: "x = (a,b)"
          by fastforce 
        from p0 have "x\<in>r(R)"
          proof 
            assume "x\<in>R"
            then show "x\<in>r(R)" using R_reflcl a1 by auto
          next
            assume "x:Id"
            then show "x\<in>r(R)" using R_into_reflcl a1 by auto
          qed
       }
      then show ?thesis by auto
      qed
    ultimately show ?thesis by auto
  qed

thm sym_conv_converse_eq

lemma "sym R = (R = R\<inverse>)"
  proof - 
    {
      assume p: "sym R"
      then have "\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (y,x)\<in>R"
        by (meson symE)
      then have "\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (x,y)\<in>R\<inverse>" by simp
      then have "R = R\<inverse>" by auto
    }
    moreover
    {
      assume "R = R\<inverse>"
      then have "\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (x,y)\<in>R\<inverse>" by auto
      then have "\<forall>x y. (x,y)\<in>R \<longrightarrow> (y,x)\<in>R" by simp
      then have "sym R" by (simp add:sym_def)
    }
    ultimately show ?thesis by auto
  qed

subsubsection {* theorem 6.4 *}

lemma "s(R) = R \<union> R\<inverse>" 
  proof -
    have "\<forall>x\<in>s(R). x\<in>R \<union> R\<inverse>"
      proof
        fix x
        assume p: "x\<in>s(R)"
        then obtain a and b where a1: "x=(a,b)" by fastforce
        show "x\<in>R \<union> R\<inverse>"
          apply(rule symcl.cases)
          using p a1 by simp+
      qed
    moreover
    have "\<forall>x\<in>R \<union> R\<inverse>. x\<in>s(R)"
      proof
        fix x
        assume p: "x\<in>R \<union> R\<inverse>"
        then obtain a and b where a1: "x=(a,b)" by fastforce
        from p show "x\<in>s(R)"
          proof
            assume "x\<in>R"
            then show "x\<in>s(R)" using R_symcl a1 by auto
          next
            assume "x\<in>R\<inverse>"
            then show "x\<in>s(R)" using R_into_symcl a1 by auto
          qed
      qed
    ultimately show ?thesis by auto
  qed

subsubsection {* theorem 6.5 *}

(* declare [[ show_types = true ]] *)

lemma U_R_trans: "trans (\<Union>n\<in>{0<..}. R\<^sup>n)"
  proof -
  {
    fix x y z
    let ?U = "\<Union>n\<in>{0<..}. R\<^sup>n"
    assume a1: "(x,y)\<in>?U"
      and  a2: "(y,z)\<in>?U"
    from a1 have "\<exists>m>0. (x,y)\<in>R\<^sup>m"
      by blast
    then obtain m where a3: "m > 0 \<and> (x,y)\<in>R\<^sup>m" by auto
    
    from a2 have "\<exists>k>0. ((y,z)\<in>R\<^sup>k)" by blast
    then obtain k where a4: "k > 0 \<and> (y,z)\<in>R\<^sup>k" by auto

    from a3 a4 have "(x,z)\<in>R_n R (m+k)" 
      using R_m_n relcomp.relcompI by fastforce 
    with a3 a4 have "(x,z)\<in>?U" by blast
  }
  then show ?thesis by (meson transI)
  qed

lemma "\<forall>(R::('d,'d) Relation). t(R) = (\<Union>n\<in>{0<..}. R\<^sup>n)"
  proof -
    have "\<forall>n>0. \<forall>(R::('d,'d) Relation). (R\<^sup>n) \<subseteq> t(R)"
      proof -
      {
        fix n
        assume p: "(n::nat) > 0"
        then have "\<forall>(R::('d,'d) Relation). (R\<^sup>n) \<subseteq> t(R)" 
          proof(induct n)
            case 0 show ?case using "0.prems" by auto  
          next
            case (Suc m)
            assume a0: "0 < (m::nat) \<Longrightarrow> \<forall>(R::('d,'d) Relation). (R\<^sup>m) \<subseteq> t(R)"
              and  a1: "0 < Suc m"
            show ?case
              proof(cases "m = 0")
                assume b0: "m = 0"
                have "\<forall>R. R\<subseteq>t(R)" using R_into_trancl by auto
                with b0 show ?thesis by auto
              next
                assume b0: "m \<noteq> 0"
                then have b1: "m > 0" by auto
                with a0 have b2: "\<forall>(R::('d,'d) Relation). (R\<^sup>m) \<subseteq> t(R)" by simp
                have "\<forall>(R::('d,'d) Relation). (R\<^sup>m) O R \<subseteq> t(R)"
                  proof -
                  {
                    fix R
                    from b2 have "(R\<^sup>m) \<subseteq> t(R::('d,'d) Relation)" by simp 
                    then have "(R\<^sup>m) O R \<subseteq> t(R)" using R_trancl
                      by (smt relcomp.cases set_mp subrelI)
                  }
                  then show ?thesis by auto
                  qed
                then show ?thesis 
                  using R_n_suc R_m_n b1 by (metis Nat.add_0_right R_O_Id R_n.simps(1) add_Suc_right) 
              qed
          qed              
      }
      then show ?thesis by auto
      qed
    then have "\<forall>(R::('d,'d) Relation). (\<Union>n\<in>{0<..}. R\<^sup>n) \<subseteq> t(R)" by blast
    moreover
    {
      fix R
      have "(R::('d,'d) Relation) = R\<^sup>1" 
        using R_n_zero R_n_suc by simp
      then have "(R::('d,'d) Relation) \<subseteq> (\<Union>n\<in>{0<..}. R\<^sup>n)" by blast
      then have "t((R::('d,'d) Relation)) \<subseteq> (\<Union>n\<in>{0<..}. R\<^sup>n)"
        using U_R_trans[of R] tR_trans_S[of R "\<Union>n\<in>{0<..}. R\<^sup>n"] by blast
    }        
    ultimately show ?thesis by fast
  qed

lemma "\<lbrakk>card X = n; R \<subseteq> X \<times> X\<rbrakk> \<Longrightarrow> t(R) = (\<Union>i\<in>{1..n}. R\<^sup>i)" sorry


subsection {* example 6.9 *}

definition "R4 \<equiv> {(''a'', ''b''), (''b'', ''c''), (''c'', ''a'')}"

lemma "R_n (R4) 2 = R4 O R4" 
  using R_n_suc R_n_zero by (simp add: numeral_2_eq_2) 

value "R4 O R4" 
value "R4 O R4 O R4" 
value "R4 O R4 O R4 O R4"

section {* Order relation *}

subsection {* definition 6.9*}

definition Partial_Order_Set :: "'d set \<Rightarrow> ('d,'d) Relation \<Rightarrow> bool" ("\<langle>_, \<le> _\<rangle>")
  where "Partial_Order_Set P R \<equiv> refl_on P R \<and> trans R \<and> antisym R"

lemma "\<langle>P, \<le> R\<rangle> \<Longrightarrow> Domain R = P"
  unfolding Partial_Order_Set_def refl_on_def using DomainI by blast

lemma "\<langle>P, \<le> R\<rangle> \<Longrightarrow> \<langle>P, \<le> R\<inverse>\<rangle> " 
  unfolding Partial_Order_Set_def by force

subsection {* definition 6.10 *} 

definition Total_Order_Set :: "'d set \<Rightarrow> ('d,'d) Relation \<Rightarrow> bool" ("\<langle>_, \<le>* _\<rangle>")
  where "Total_Order_Set P R \<equiv> \<langle>P, \<le> R\<rangle> \<and> (\<forall>x y. x\<in>P \<and> y\<in>P \<longrightarrow> (x, y)\<in>R \<or> (y, x)\<in>R)"

lemma "\<langle>P, \<le>* R\<rangle> \<Longrightarrow> \<langle>P, \<le> R\<rangle> " 
  unfolding Partial_Order_Set_def Total_Order_Set_def
    by blast

subsection {* definition 6.11 *}

definition Strict_Partial_Order_Set :: "'d set \<Rightarrow> ('d, 'd) Relation \<Rightarrow> bool" ("\<langle>_, < _\<rangle>")
  where "Strict_Partial_Order_Set P R \<equiv> R \<subseteq> P \<times> P \<and> trans R \<and> irrefl R"

(* 
why we did not define antisym in Strict_Partial_Order_Set? 
because antisym is implied by trans and irrefl
*)
lemma "trans R \<and> irrefl R \<Longrightarrow> antisym R"
  unfolding trans_def irrefl_def antisym_def by blast

(*
lemma "Domain R = P \<Longrightarrow> R \<in> \<langle>-, <\<rangle> \<Longrightarrow> (R \<union> Id) \<in> \<langle>P, \<le>\<rangle>"
*)

(*
lemma "R \<in> \<langle>-, <\<rangle> \<and> S\<in>\<langle>P, \<le>\<rangle> \<Longrightarrow> R = S - Id"  
*)

subsection {* examples of definition 6.11 *}

definition "less_eq_real \<equiv> {(x::real,y). x \<le> y}"
definition "greater_eq_real \<equiv> {(x::real,y). x \<ge> y} "
definition "less_real \<equiv> {(x::real,y). x < y}"
definition "greater_real \<equiv> {(x::real,y). x > y} "

lemma less_eq_real_partial_order: "\<langle>UNIV, \<le> less_eq_real\<rangle> "
  proof -
    have "trans less_eq_real" using less_eq_real_def trans_def
      by (smt case_prodD case_prodI mem_Collect_eq)  
    moreover
    have "antisym less_eq_real" using less_eq_real_def antisym_def
      by (smt case_prod_conv mem_Collect_eq)
    moreover
    have "refl_on UNIV less_eq_real" using less_eq_real_def refl_on_def
      UNIV_I case_prodI mem_Collect_eq mem_Sigma_iff subrelI by fastforce
    ultimately show ?thesis by (simp add:Partial_Order_Set_def)
  qed

lemma "\<langle>UNIV, \<le>* less_eq_real\<rangle>"
  proof - 
    have "\<forall>x y. (x, y)\<in>less_eq_real \<or> (y, x)\<in>less_eq_real"
      by (smt less_eq_real_def mem_Collect_eq old.prod.case) 
    with less_eq_real_partial_order show ?thesis by (simp add:Total_Order_Set_def)
  qed

lemma greater_eq_real_partial_order: "\<langle>UNIV, \<le> greater_eq_real\<rangle>"
  proof -
    have "trans greater_eq_real" using greater_eq_real_def trans_def
      by (smt case_prodD case_prodI mem_Collect_eq)  
    moreover
    have "antisym greater_eq_real" using greater_eq_real_def antisym_def
      by (smt case_prod_conv mem_Collect_eq)
    moreover
    have "refl_on UNIV greater_eq_real" using greater_eq_real_def refl_on_def
      UNIV_I case_prodI mem_Collect_eq mem_Sigma_iff subrelI by fastforce
    ultimately show ?thesis by (simp add:Partial_Order_Set_def)
  qed

lemma "\<langle>UNIV, \<le>* greater_eq_real\<rangle>"
  proof - 
    have "\<forall>x y. (x, y)\<in>greater_eq_real \<or> (y, x)\<in>greater_eq_real"
      by (smt greater_eq_real_def mem_Collect_eq old.prod.case) 
    with greater_eq_real_partial_order show ?thesis by (simp add:Total_Order_Set_def)
  qed

lemma "\<langle>UNIV, < less_real\<rangle>"
  proof -
    have "trans less_real" using less_real_def trans_def
      by (smt case_prodD case_prodI mem_Collect_eq)  
    moreover
    have "irrefl less_real" using less_real_def irrefl_def
      by (smt case_prod_conv mem_Collect_eq)
    ultimately show ?thesis by (simp add:Strict_Partial_Order_Set_def)
  qed

lemma "\<langle>UNIV, < greater_real\<rangle>"
  proof -
    have "trans greater_real" using greater_real_def trans_def[of greater_real]
      by (smt case_prodD case_prodI mem_Collect_eq)  
    moreover
    have "irrefl greater_real" using greater_real_def irrefl_def
      by (smt case_prod_conv mem_Collect_eq)
    ultimately show ?thesis by (simp add:Strict_Partial_Order_Set_def)
  qed

definition "subset_eq_rel \<equiv> {(x,y). x \<subseteq> y} "

(* it is not correct. Domain of subset_eq_rel is UNIV, not P *)
lemma "\<langle>P, \<le> subset_eq_rel\<rangle>" sorry

definition "subset_eq_powp_rel P \<equiv> {(x,y). x\<in>Pow P \<and> y\<in>Pow P \<and> x \<subseteq> y}"
definition "subset_powp_rel P \<equiv> {(x,y). x\<in>Pow P \<and> y\<in>Pow P \<and> x \<subset> y} "

lemma "\<langle>Pow P, \<le> (subset_eq_powp_rel P)\<rangle>"
  proof -
    have "trans (subset_eq_powp_rel P)" 
      using subset_eq_powp_rel_def[of P] trans_def[of "(subset_eq_powp_rel P)"] by fastforce
    moreover
    have "antisym (subset_eq_powp_rel P)" 
      using subset_eq_powp_rel_def[of P] antisym_def[of "(subset_eq_powp_rel P)"] by fastforce
    moreover
    have "refl_on (Pow P) (subset_eq_powp_rel P)" 
      using subset_eq_powp_rel_def[of P] refl_on_def[of "Pow P" "(subset_eq_powp_rel P)"] by force
    ultimately show ?thesis by (simp add:Partial_Order_Set_def)
  qed

lemma "\<langle>Pow P, < (subset_powp_rel P)\<rangle>"
  proof -
    have "trans (subset_powp_rel P)" 
      using subset_powp_rel_def[of P] trans_def[of "subset_powp_rel P"] by fastforce 
    moreover
    have "irrefl (subset_powp_rel P)" 
      using subset_powp_rel_def[of P] irrefl_def[of "subset_powp_rel P"] by fastforce
    ultimately show ?thesis 
      unfolding Strict_Partial_Order_Set_def subset_powp_rel_def by auto
  qed

subsection {* definition 6.12, 6.13 *}
(* maximal, minimal, least and greatest elements *)
(*  supremum: least upper bound  or join *)
(*  infimum: greatest lower bound or meet *) 

definition greatest :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "greatest R B \<equiv> {b. b \<in> B \<and> (\<forall>b' \<in> B. (b', b) \<in> R)}" 

definition least :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "least R B \<equiv> {b. b \<in> B \<and> (\<forall>b' \<in> B. (b, b') \<in> R)}" 

definition maximal :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "maximal R B \<equiv> {b. b \<in> B \<and> \<not>(\<exists>b' \<in> B. b \<noteq> b' \<and> (b, b') \<in> R)}" 

definition minimal :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "minimal R B \<equiv> {b. b \<in> B \<and> \<not>(\<exists>b' \<in> B. b \<noteq> b' \<and> (b', b) \<in> R)}" 

definition upperbound :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "upperbound R B \<equiv> {b. (\<forall>b' \<in> B. (b', b) \<in> R)}" 

definition lowerbound :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "lowerbound R B \<equiv> {b. (\<forall>b' \<in> B. (b, b') \<in> R)}"

(*  supremum: least upper bound  or join *)
definition supremum :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "supremum R B \<equiv> {b. \<forall>b'\<in>upperbound R B. (b,b') \<in> R}"

(*  infimum: greatest lower bound or meet *) 
definition infimum :: "('a, 'a) Relation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "infimum R B \<equiv> {b. \<forall>b'\<in>lowerbound R B. (b',b) \<in> R}"


(* at most one greatest element *)
lemma grtst_one_most: "\<langle>A, \<le> R\<rangle> \<Longrightarrow> \<forall>x y. x \<in> greatest R B \<and> y \<in> greatest R B \<longrightarrow> x = y"
  proof -
    assume p0: "\<langle>A, \<le> R\<rangle>"
    {
      fix x y
      assume p2: "x \<in> greatest R B \<and> y \<in> greatest R B"
      from p2 have "x \<in> B \<and> (\<forall>b' \<in> B. (b', x) \<in> R)" by (simp add:greatest_def)
      moreover
      from p2 have "y \<in> B \<and> (\<forall>b' \<in> B. (b', y) \<in> R)" by (simp add:greatest_def)
      ultimately have "(x,y)\<in>R \<and> (y,x)\<in>R"  by auto
      moreover
      from p0 have "antisym R" by (simp add:Partial_Order_Set_def)
      ultimately have "x = y" by (simp add:antisym_def)
    }
    then show ?thesis by auto
  qed

(* at most one least element *)
lemma least_one_most: "\<langle>A, \<le> R\<rangle> \<Longrightarrow> \<forall>x y. x \<in> least R B \<and> y \<in> least R B \<longrightarrow> x = y"
  proof -
    assume p0: "\<langle>A, \<le> R\<rangle>"
    {
      fix x y
      assume p2: "x \<in> least R B \<and> y \<in> least R B"
      from p2 have "x \<in> B \<and> (\<forall>b' \<in> B. (x, b') \<in> R)" by (simp add:least_def)
      moreover
      from p2 have "y \<in> B \<and> (\<forall>b' \<in> B. (y, b') \<in> R)" by (simp add:least_def)
      ultimately have "(x,y)\<in>R \<and> (y,x)\<in>R" by auto
      moreover
      from p0 have "antisym R" by (simp add:Partial_Order_Set_def)
      ultimately have "x = y" by (simp add:antisym_def)
    }
    then show ?thesis by auto
  qed

(* greatest implies maximal *)
lemma poset_grst_eq_max: "\<langle>A, \<le> R\<rangle> \<and> greatest R B \<noteq> {} \<Longrightarrow> greatest R B = maximal R B"
  proof -
    assume p0: "\<langle>A, \<le> R\<rangle> \<and> greatest R B \<noteq> {}"
    then obtain b where "b \<in> greatest R B" by blast
    with grtst_one_most p0 have a0: "{b} = greatest R B"
      using singleton_iff subsetI subset_singletonD by blast 
    then have a1: "b \<in> B \<and> (\<forall>b' \<in> B. (b', b) \<in> R)" unfolding greatest_def by blast

    from p0 have a2: "antisym R" by (simp add:Partial_Order_Set_def)
    
    with a1 have "b \<in> maximal R B" unfolding maximal_def antisym_def by blast
    
    with a1 a2 have "{b} = maximal R B" unfolding maximal_def antisym_def by blast
    with a0 show "greatest R B = maximal R B" by simp
  qed
  
(* least implies minimal *)
lemma poset_least_eq_min: "\<langle>A, \<le> R\<rangle> \<and> least R B \<noteq> {} \<Longrightarrow> least R B = minimal R B"
  proof -
    assume p0: "\<langle>A, \<le> R\<rangle> \<and> least R B \<noteq> {}"
    then obtain b where "b \<in> least R B" by blast
    with least_one_most p0 have a0: "{b} = least R B"
      using singleton_iff subsetI subset_singletonD by blast 
    then have a1: "b \<in> B \<and> (\<forall>b' \<in> B. (b, b') \<in> R)" unfolding least_def by blast

    from p0 have a2: "antisym R" by (simp add:Partial_Order_Set_def)
    
    with a1 have "b \<in> minimal R B" unfolding minimal_def antisym_def by blast
    
    with a1 a2 have "{b} = minimal R B" unfolding minimal_def antisym_def by blast
    with a0 show "least R B = minimal R B" by simp
  qed


subsection {* definition 6.14 *}

definition Well_Order_Set :: "'d set \<Rightarrow> ('d,'d) Relation \<Rightarrow> bool" ("\<langle>_, \<lessapprox> _\<rangle>")
  where "Well_Order_Set P R \<equiv> \<langle>P,\<le> R\<rangle> \<and> (\<forall>A. A\<subseteq>P \<and> A \<noteq> {}  \<longrightarrow> least R A \<noteq> {})"

(* *)
lemma A_wo_has_least: "\<langle>P, \<lessapprox> R\<rangle> \<Longrightarrow> (\<forall>A. A \<subseteq> P \<and> A \<noteq> {} \<longrightarrow> (\<exists>y\<in>A. \<forall>x\<in>A. (y,x)\<in>R))"
  proof -
    assume p0: "\<langle>P, \<lessapprox> R\<rangle>"
    then have p1: "\<langle>P,\<le> R\<rangle> \<and> (\<forall>A. A \<subseteq> P \<and> A \<noteq> {} \<longrightarrow> least R A \<noteq> {})" 
      by (simp add: Well_Order_Set_def)
    
    {
      fix A
      assume a0: "A\<subseteq>P \<and> A \<noteq> {}"
      with p1 have a1: "least R A \<noteq> {}" by auto

      from p1 have "\<forall>x y. x \<in> least R A \<and> y \<in> least R A \<longrightarrow> x = y"
        using least_one_most by metis

      with a1 have "\<exists>y. least R A = {y}" by fastforce

      then obtain y where "least R A = {y}" by auto
      then have "y \<in> A \<and> (\<forall>b' \<in> A. (y, b') \<in> R)" unfolding least_def by blast
      then have "\<exists>y\<in>A. \<forall>x\<in>A. (y,x)\<in>R" by auto
    }
    then show ?thesis by auto
  qed

(* well order set is total order set*)
lemma "\<langle>P, \<lessapprox> R\<rangle> \<Longrightarrow> \<langle>P, \<le>* R\<rangle>"
  proof -
    assume "\<langle>P, \<lessapprox> R\<rangle>"
    then have p1: "\<langle>P,\<le> R\<rangle> \<and> (\<forall>A. A\<subseteq>P \<and> A \<noteq> {}  \<longrightarrow> least R A \<noteq> {})" 
      by (simp add: Well_Order_Set_def)
      
    {
      fix x y
      assume a0: "x\<in>P \<and> y\<in>P"
      let ?A = "{x,y}"
      from a0 have "?A\<subseteq>P" by auto
      with p1 have a1: "least R ?A \<noteq> {}" by blast
      from p1 have "\<forall>x y. x \<in> least R ?A \<and> y \<in> least R ?A \<longrightarrow> x = y"
        using least_one_most by metis
      with a1 have "\<exists>y. least R ?A = {y}" by fastforce
      then obtain y1 where "least R ?A = {y1}" by auto
      then have a2: "y1 \<in> ?A \<and> (\<forall>b' \<in> ?A. (y1, b') \<in> R)" unfolding least_def by blast
      then have "x = y1 \<or> y = y1" by blast
      then have "(x, y)\<in>R \<or> (y, x)\<in>R" 
        proof
          assume "x = y1"
          with a2 show "(x, y) \<in> R \<or> (y, x) \<in> R" by blast
        next
          assume "y = y1"
          with a2 show "(x, y) \<in> R \<or> (y, x) \<in> R" by blast
        qed
    }
    then have "\<forall>x y. x\<in>P \<and> y\<in>P \<longrightarrow> (x, y)\<in>R \<or> (y, x)\<in>R" by auto
    with p1 show ?thesis by (simp add:Total_Order_Set_def)
  qed


section {* section 6.4 equivalent relation, partition, and others *}

subsection {* definition 6.15 *}

definition "Set_Cover S A \<equiv> ((\<forall>B\<in>A. B \<noteq> {}) \<and> Union A = S)"

subsection {* definition 6.16 *}

definition "Set_Partition S A \<equiv> Set_Cover S A \<and> (\<forall>x y. x\<in>A \<and> y\<in>A \<and> x \<noteq> y \<longrightarrow> x \<inter> y = {})"

subsection {* example 6.16 *}

lemma lmaa:  "Set_Cover {1::int,2,3} {{1,2},{2,3}}"
  unfolding Set_Cover_def by blast

lemma lmcc: "Set_Partition {1::int,2,3} {{1},{2,3}}"
  unfolding Set_Partition_def Set_Cover_def by force

lemma lmdd: "Set_Partition {1::int,2,3} {{1,2,3}}"
  unfolding Set_Partition_def Set_Cover_def by force

lemma lmee: "Set_Partition {1::int,2,3} {{1},{2},{3}}"
  unfolding Set_Partition_def Set_Cover_def by force

lemma lmff:  "Set_Cover {1::int,2,3} {{1}, {1,2},{2,3}}"
  unfolding Set_Cover_def by blast

subsection {* example 6.17 *}

definition "NatSet = {x::int. x \<ge> 0}"

definition "E1 = {x::int. x \<ge> 0 \<and> x mod 2 = 0}"

definition "O1 = {x::int. x \<ge> 0 \<and> x mod 2 \<noteq> 0}"

lemma exm617_lm1: "Union {E1, O1} = NatSet"
  proof -
    have "Union {E1, O1} = {x::int. x \<ge> 0}"
      unfolding E1_def O1_def by force
    then show ?thesis unfolding NatSet_def by simp
  qed

lemma exm617_lm2: "Set_Cover NatSet {E1, O1}"
    apply(simp add: Set_Cover_def)
    apply(rule conjI)
    apply(simp add: E1_def) apply fastforce
    apply(rule conjI)
    apply(simp add: O1_def) apply presburger 
    using exm617_lm1 by simp

lemma "Set_Partition NatSet {E1, O1}" 
  apply(simp add: Set_Partition_def)
  apply(rule conjI)
  using exm617_lm2 apply simp
  apply(rule allI)+
  apply(rule impI)
  unfolding NatSet_def E1_def O1_def 
  by fastforce

subsection {* definition 6.17 *}

thm equiv_def

lemma "equiv A R \<Longrightarrow> Domain R = A"
  unfolding equiv_def refl_on_def by force

subsection {* equiv with mod *}

definition "ModR X m \<equiv> {(x::int,y::int). x\<in>X \<and> y\<in>X \<and> x mod m = y mod m}"

lemma "equiv X (ModR X m)" 
  proof -
    have "refl_on X (ModR X m)"
      unfolding refl_on_def ModR_def by fastforce
    moreover
    have "sym (ModR X m)"
      unfolding sym_def ModR_def by fastforce
    moreover
    have "trans (ModR X m)" 
      unfolding trans_def ModR_def by fastforce
    ultimately show ?thesis by (simp add:equiv_def)
  qed

subsection {* definition 6.18 *}

definition "Set_x X R x \<equiv> {y. y\<in>X \<and> (x,y)\<in>R}"

lemma def618_lm11: "equiv X R \<and> x\<in>X \<Longrightarrow> x\<in>Set_x X R x"
  unfolding equiv_def refl_on_def Set_x_def by fastforce

lemma def618_lm12: "equiv X R \<and> x\<in>X \<Longrightarrow> Set_x X R x \<noteq> {}"  
  using def618_lm11 by fastforce

lemma def618_lm2: "equiv X R \<and> x\<in>X \<and> y\<in>X \<Longrightarrow> (Set_x X R x = Set_x X R y) \<longleftrightarrow> (x,y)\<in>R"
  proof -
    assume p0: "equiv X R \<and> x\<in>X \<and> y\<in>X"

    {
      assume a0: "Set_x X R x = Set_x X R y"
      from p0 have "x\<in>Set_x X R x" using def618_lm11 by fastforce
      moreover
      from p0 have "y\<in>Set_x X R y" using def618_lm11 by fastforce
      ultimately have "(x,y)\<in>R"  using a0 unfolding Set_x_def by fastforce
    }
    moreover
    {
      assume a0: "(x,y)\<in>R"
      with p0 have a1: "(y,x)\<in>R" 
        unfolding equiv_def sym_def by fastforce

      {
        fix a
        assume "a\<in>Set_x X R  x"
        with p0 a1 have "a\<in>Set_x X R y"
          unfolding Set_x_def equiv_def trans_def
            using mem_Collect_eq by blast 
      }
      moreover
      {
        fix a
        assume "a\<in>Set_x X R y"
        then have "(y,a)\<in>R"
          unfolding Set_x_def by auto
        with p0 a0 have "a\<in>Set_x X R x"
          unfolding Set_x_def equiv_def trans_def
            by (metis (no_types, lifting) CollectI refl_onD2) 
      }
      ultimately have "Set_x X R x = Set_x X R y" by auto
    }
    ultimately show ?thesis by auto
  qed

lemma def618_lm3: "equiv X R \<and> x\<in>X \<and> y\<in>X \<and> (x,y)\<notin>R \<Longrightarrow> Set_x X R x \<inter> Set_x X R y = {}"
  proof -
    assume p0: "equiv X R \<and> x\<in>X \<and> y\<in>X \<and> (x,y)\<notin>R"

    {
      assume a0: "Set_x X R x \<inter> Set_x X R y \<noteq> {}"
      then obtain tt where "tt \<in> Set_x X R x \<and> tt \<in> Set_x X R y" by auto
      then have "(x,tt)\<in>R \<and> (y,tt)\<in>R"
        unfolding Set_x_def by auto
      moreover
      with p0 have "(tt,y)\<in>R" unfolding equiv_def sym_def by fastforce
      ultimately have "(x,y)\<in>R" using p0
        unfolding equiv_def sym_def refl_on_def trans_def by meson
   
      with p0 have False by simp
    }
    then show ?thesis by auto
 qed

lemma def618_lm4: "equiv X R \<Longrightarrow> (\<Union>x\<in>X. Set_x X R x) = X" 
  proof -
    assume p0: "equiv X R"
    have "\<forall>x. x\<in>X \<longrightarrow> Set_x X R x \<subseteq> X"
      apply(rule allI)
      apply(rule impI)
      unfolding Set_x_def by auto
    then have g1: "(\<Union>x\<in>X. Set_x X R x) \<subseteq> X" by auto

    from p0 have "\<forall>x. x\<in>X \<longrightarrow> x\<in>Set_x X R x" 
      using def618_lm11 by fastforce
    then have g2: "X \<subseteq> (\<Union>x\<in>X. Set_x X R x)" by auto

    from g1 g2 show ?thesis by auto
  qed

subsection {* theorem 6.8 *}

(* the set of equiv class *)
definition "Equiv_Set X R \<equiv> {S. \<exists>x\<in>X. S = Set_x X R x}"

lemma thm6_8: "equiv X R \<Longrightarrow> Set_Partition X (Equiv_Set X R)" 
  proof -
    assume p0: "equiv X R"
    let ?A = "{S. \<exists>x\<in>X. S = Set_x X R x}"
    from p0 have "(\<Union>x\<in>X. Set_x X R x) = X" using def618_lm4 by auto
    moreover
    have "(\<Union>x\<in>X. Set_x X R x) = Union ?A" by fastforce
    ultimately have "Union ?A = X" by simp
    moreover from p0 have "\<forall>B\<in>{S. \<exists>x\<in>X. S = Set_x X R x}. B \<noteq> {}" using def618_lm12 by fastforce
    ultimately have g1: "Set_Cover X ?A" unfolding Set_Cover_def by auto

    {
      fix A B
      assume a0: "A\<in>?A \<and> B\<in>?A \<and> A \<noteq> B"
      moreover
      then obtain x where a1: "x\<in>X \<and> Set_x X R x = A" by auto
      moreover
      from a0 obtain y where a2: "y\<in>X \<and> Set_x X R y = B" by auto
      ultimately have "(x,y)\<notin>R" 
        using p0 def618_lm2 by (metis (no_types, lifting)) 

      with p0 a1 a2 have "A \<inter> B = {}" using def618_lm3 by fastforce
    }
    then have g2: "\<forall>A B. A\<in>?A \<and> B\<in>?A \<and> A \<noteq> B \<longrightarrow> A \<inter> B = {}" by auto
   
    from g1 g2 show ?thesis unfolding Set_Partition_def Equiv_Set_def by simp
  qed


subsection {* example 6.20 *}

definition "ID X \<equiv> {p. \<exists>x. x\<in>X \<and> p = (x, x)}"
definition "U X \<equiv> {p. \<exists>x y. x\<in>X \<and> y\<in>X \<and> p = (x,y)}"

lemma equiv_id_lm: "equiv X (ID X)"
  unfolding equiv_def ID_def
  apply(rule conjI)
  unfolding refl_on_def apply force
  apply(rule conjI)
  unfolding sym_def apply force
  unfolding trans_def by force

lemma equiv_u_lm: "equiv X (U X)"
  unfolding equiv_def U_def
  apply(rule conjI)
  unfolding refl_on_def apply force
  apply(rule conjI)
  unfolding sym_def apply force
  unfolding trans_def by force

lemma "X \<noteq> {} \<Longrightarrow> Equiv_Set X (U X) = {X}" 
  proof -
    assume p0: "X \<noteq> {}"
    let ?R = "U X"
    have a1: "equiv X ?R" using equiv_u_lm by auto

    {
      fix x y
      assume b0: "x\<in>X \<and> y\<in>X"
      then have "(x,y)\<in> ?R" unfolding U_def by fastforce
      with b0 a1 have "Set_x X ?R x = Set_x X ?R y" 
        using def618_lm2 by fastforce
    }
    then have a2: "\<forall>x y. x\<in>X \<and> y\<in>X \<longrightarrow> Set_x X ?R x = Set_x X ?R y"  by auto
    from p0 obtain x1 where a3: "x1\<in>X" by auto
    with a2 have a4: "\<forall>x\<in>X. Set_x X ?R x = Set_x X ?R x1" by blast

    {
      fix a
      assume "a\<in>(\<Union>x\<in>X. Set_x X ?R x)"
      then obtain y1 where "y1\<in>X \<and> a\<in>Set_x X ?R y1" by auto
      with a4 have "a\<in>Set_x X ?R x1" by blast
    }
    moreover
    {
      fix a
      assume "a\<in>Set_x X ?R x1"
      with a3 have "a\<in>(\<Union>x\<in>X. Set_x X ?R x)"
          using UN_I \<open>\<And>thesis. (\<And>x1. x1 \<in> X \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by force
    }
    ultimately have "(\<Union>x\<in>X. Set_x X ?R x) = Set_x X ?R x1" by blast

    with a1 a4 have a5: "\<forall>x\<in>X. Set_x X ?R x = X" using def618_lm4 by fastforce

    {
      fix a
      assume "a\<in>Equiv_Set X (U X)"
      then obtain x2 where "x2\<in>X \<and> a = Set_x X ?R x2" unfolding Equiv_Set_def by auto
      with a5 have "a\<in>{X}" by auto
    }
    moreover
    {
      fix a
      assume "a\<in>{X}"
      with a3 a5 a4 have "a\<in>Equiv_Set X (U X)" 
        unfolding Equiv_Set_def by blast
    }
    ultimately show ?thesis by auto
  qed

lemma "X \<noteq> {} \<Longrightarrow> Equiv_Set X (ID X) = {p. \<exists>x\<in>X. p = {x}}" sorry
(* please prove it by youself *)

subsection {* theorem 6.9 *} 
    
lemma "Set_Partition X C \<and> (\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (\<exists>c\<in>C. x\<in>c \<and> y\<in>c)) \<Longrightarrow> equiv X R" 
  proof -
    assume p0: "Set_Partition X C \<and> (\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (\<exists>c\<in>C. x\<in>c \<and> y\<in>c))"
    
    have g1: "refl_on X R" 
      unfolding refl_on_def apply(rule conjI)
      proof -
        {
          fix x y
          assume "(x,y)\<in>R"
          with p0 have "\<exists>c\<in>C. x\<in>c \<and> y\<in>c" by auto
          then obtain c where "c\<in>C \<and> x\<in>c \<and> y\<in>c" by auto
          with p0 have "(x,y)\<in>X \<times> X" 
            unfolding Set_Partition_def Set_Cover_def by fastforce
        }
        then show "R \<subseteq> X \<times> X" by auto
      next
        {
          fix x
          assume "x\<in>X"
          with p0 have "\<exists>c\<in>C. x\<in>c" 
            unfolding Set_Partition_def Set_Cover_def by fastforce
          with p0 have "(x, x) \<in> R" by auto
        }
        then show "\<forall>x\<in>X. (x, x) \<in> R"  by auto
      qed

    {
      fix x y
      assume "(x, y) \<in> R"
      with p0 have "\<exists>c\<in>C. x \<in> c \<and> y \<in> c" by auto
      with p0 have "(y, x) \<in> R" by auto
    }
    then have g2: "sym R"
      unfolding sym_def by auto
          
    {
      fix x y z
      assume a1: "(x, y) \<in> R"
        and  a2: "(y, z) \<in> R"
      from p0 a1 have "\<exists>c\<in>C. x \<in> c \<and> y \<in> c" by auto
      then obtain c1 where a3: "c1\<in>C \<and> x \<in> c1 \<and> y \<in> c1" by auto

      from p0 a2 have "\<exists>c\<in>C. y \<in> c \<and> z \<in> c" by auto
      then obtain c2 where a4: "c2\<in>C \<and> y \<in> c2 \<and> z \<in> c2" by auto
      
      from a3 a4 have "c1 \<inter> c2 \<noteq> {}" by auto
      with p0 a3 a4 have "c1 = c2" 
        unfolding Set_Partition_def Set_Cover_def by auto
      with p0 a3 a4 have "(x, z) \<in> R" by auto
    }
    then have g3: "trans R"
      unfolding trans_def by blast

    from g1 g2 g3 show ?thesis unfolding equiv_def by auto
  qed

lemma "Set_Partition X C \<and> R = (\<Union>c\<in>C. (c \<times> c)) \<Longrightarrow> (\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (\<exists>c\<in>C. x\<in>c \<and> y\<in>c))"
  proof -
    assume p0: "Set_Partition X C \<and> R = (\<Union>c\<in>C. (c \<times> c))"
    
    {
      fix x y
      {
        assume "(x,y)\<in>R"
        with p0 have "\<exists>c\<in>C. x\<in>c \<and> y\<in>c" by auto
      }
      moreover
      {
        assume "\<exists>c\<in>C. x\<in>c \<and> y\<in>c"
        then obtain c where "c\<in>C \<and> x\<in>c \<and> y\<in>c" by auto
        with p0 have "(x,y)\<in>R" by auto
      }
      ultimately have "(x,y)\<in>R \<longleftrightarrow> (\<exists>c\<in>C. x\<in>c \<and> y\<in>c)" by auto
    }
    then show ?thesis by auto
  qed

lemma "Set_Partition X C \<and> (\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (\<exists>c\<in>C. x\<in>c \<and> y\<in>c)) \<Longrightarrow> R = (\<Union>c\<in>C. (c \<times> c))"
  proof -
    assume p0: "Set_Partition X C \<and> (\<forall>x y. (x,y)\<in>R \<longleftrightarrow> (\<exists>c\<in>C. x\<in>c \<and> y\<in>c))"
    
    {
      fix x y
      assume "(x,y)\<in>R"
      with p0 have "\<exists>c\<in>C. x\<in>c \<and> y\<in>c" by auto
      then have "(x,y)\<in>(\<Union>c\<in>C. (c \<times> c))" by auto
    }
    then have g1: "\<forall>x y. (x,y)\<in>R \<longrightarrow> (x,y)\<in>(\<Union>c\<in>C. (c \<times> c))" by auto
    
    {
      fix x y
      assume "(x,y)\<in>(\<Union>c\<in>C. (c \<times> c))"
      then have "\<exists>c\<in>C. (x,y)\<in>c\<times>c" by auto
      with p0 have "(x,y)\<in>R" by auto
    }
    then have g2: "\<forall>x y. (x,y)\<in>(\<Union>c\<in>C. (c \<times> c)) \<longrightarrow> (x,y)\<in>R" by auto

    from g1 g2 show ?thesis by fastforce
  qed
  

end