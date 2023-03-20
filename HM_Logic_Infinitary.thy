theory HM_Logic_Infinitary
  imports 
    Weak_Relations
begin

section \<open>Infinitary Hennessy-Milner Logic\<close>

datatype ('a,'x)HML_formula =
  HML_true 
| HML_conj \<open>'x set\<close> \<open>'x \<Rightarrow> ('a,'x)HML_formula\<close>  (\<open>AND _ _\<close>)
| HML_neg \<open>('a,'x)HML_formula\<close>                  (\<open>~_\<close> [20] 60)
| HML_poss \<open>'a\<close> \<open>('a,'x)HML_formula\<close>            (\<open>\<langle>_\<rangle>_\<close> [60] 60)

term \<open>\<langle>\<tau>\<rangle>\<langle>1\<rangle>\<langle>2\<rangle>\<langle>a\<rangle> ((\<lambda> x. \<langle>2\<rangle>x) C)\<close>

subsection \<open>Satisfaction Relation\<close>

context lts_tau
begin

function satisfies :: \<open>'s \<Rightarrow> ('a, 's) HML_formula \<Rightarrow> bool\<close> 
  (\<open>_ \<Turnstile> _\<close> [50, 50] 50)
  where
    \<open>(p \<Turnstile> HML_true) = True\<close> 
  | \<open>(p \<Turnstile> HML_conj I F) = (\<forall> i \<in> I. p \<Turnstile> (F i))\<close> 
  | \<open>(p \<Turnstile> HML_neg \<phi>) = (\<not> p \<Turnstile> \<phi>)\<close>
  | \<open>(p \<Turnstile> HML_poss \<alpha> \<phi>) = (\<exists> p'. ((tau \<alpha> \<and> p \<longmapsto>* tau p') \<or> (\<not> tau \<alpha> \<and> p \<longmapsto>\<alpha> p')) \<and> p' \<Turnstile> \<phi>)\<close>
  using HML_formula.exhaust by (auto, blast)

inductive_set HML_wf_rel :: \<open>('s \<times> ('a, 's) HML_formula) rel\<close> 
  where
    \<open>\<phi> = F i \<and> i \<in> I \<Longrightarrow> ((p, \<phi>), (p, HML_conj I F)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p, HML_neg \<phi>)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p', HML_poss \<alpha> \<phi>)) \<in> HML_wf_rel\<close>

lemma HML_wf_rel_is_wf: \<open>wf HML_wf_rel\<close> 
  unfolding wf_def
proof (safe)
  fix P::\<open>'s \<times> ('a, 's) HML_formula \<Rightarrow> bool\<close> and t::\<open>'s \<times> ('a, 's) HML_formula\<close>
  obtain p \<phi> where \<open>t = (p, \<phi>)\<close> by force
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HML_wf_rel \<longrightarrow> P y) \<longrightarrow> P x\<close>
  hence \<open>P (p, \<phi>)\<close>
    apply (induct \<phi> arbitrary: p)
    apply (metis HML_formula.ctr_transfer(1) HML_formula.distinct(3) HML_formula.distinct(5) HML_formula.rel_distinct(2) HML_wf_relp.cases HML_wf_relp_HML_wf_rel_eq surj_pair)
    apply (smt (verit) HML_formula.distinct(10) HML_formula.distinct(7) HML_formula.inject(1) HML_wf_rel_def UNIV_I case_prodE' image_eqI HML_wf_rel.cases mem_Collect_eq split_conv)
    apply (smt (verit, ccfv_threshold) HML_formula.distinct(11) HML_formula.distinct(7) HML_formula.inject(2) case_prodI2 case_prod_curry HML_wf_rel.cases HML_wf_rel_def)
    apply (smt (verit, del_insts) HML_formula.distinct(3,5,9,11)  HML_formula.inject(3) HML_wf_rel.cases case_prodD case_prodE' HML_wf_rel_def mem_Collect_eq)
    done
  thus \<open>P t\<close> using \<open>t = (p, \<phi>)\<close> by simp
qed

termination satisfies using HML_wf_rel_is_wf 
  by (standard, (simp add: HML_wf_rel.intros)+)


inductive_set HML_direct_subformulas :: \<open>(('a, 's) HML_formula) rel\<close>
  where
    \<open>\<phi> = F i \<and> i \<in> I \<Longrightarrow> (\<phi>, HML_conj I F) \<in> HML_direct_subformulas\<close> 
  | \<open>(\<phi>, HML_neg \<phi>) \<in> HML_direct_subformulas\<close> 
  | \<open>(\<phi>, HML_poss \<alpha> \<phi>) \<in> HML_direct_subformulas\<close>


lemma HML_direct_subformulas_wf: \<open>wf HML_direct_subformulas\<close> 
  unfolding wf_def
proof (safe)
  fix P x
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HML_direct_subformulas \<longrightarrow> P y) \<longrightarrow> P x\<close>
  thus \<open>P x\<close>
    apply (induct, auto)
    using HML_direct_subformulas.simps apply blast
    apply (metis HML_direct_subformulas.cases HML_formula.distinct(7) HML_formula.distinct(9) HML_formula.inject(1) range_eqI)
    apply (metis HML_direct_subformulas.simps HML_formula.distinct(11) HML_formula.distinct(7) HML_formula.inject(2))
    by (metis HML_direct_subformulas.simps HML_formula.distinct(11) HML_formula.distinct(9) HML_formula.inject(3))
qed

definition HML_subformulas where \<open>HML_subformulas \<equiv> (HML_direct_subformulas)\<^sup>+\<close>

lemma HML_subformulas_wf: \<open>wf HML_subformulas\<close>
  using HML_direct_subformulas_wf HML_subformulas_def wf_trancl
  by fastforce

lemma conj_only_depends_on_indexset:
  assumes \<open>\<forall>i\<in>I. f1 i = f2 i\<close>
  shows \<open>(p \<Turnstile> HML_conj I f1) = (p \<Turnstile> HML_conj I f2)\<close>
  using assms by auto

subsection \<open>Distinguishing Formulas\<close>

definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>HML_equivalent p q 
    \<equiv> (\<forall> \<phi>::('a, 's) HML_formula. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

lemma distinguishing_formula:
  assumes \<open>\<not> HML_equivalent p q\<close>
  shows \<open>\<exists> \<phi>. p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close>
  using assms  satisfies.simps(3) unfolding HML_equivalent_def 
  by blast

lemma HML_equivalent_symm:
  assumes \<open>HML_equivalent p q\<close>
  shows \<open>HML_equivalent q p\<close>
  using HML_equivalent_def assms by presburger

end \<comment> \<open>of \<open>context lts\<close>\<close>
end \<comment> \<open>of \<open>theory\<close>\<close>