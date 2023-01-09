theory HM_Logic_infinitary
  imports 
    Weak_Relations
begin

chapter \<open>Infinitary Hennessy-Milner Logic\<close>

datatype ('a,'x)HML_formula =
  HML_true 
| HML_conj \<open>'x set\<close> \<open>'x \<Rightarrow> ('a,'x)HML_formula\<close> 
| HML_neg \<open>('a,'x)HML_formula\<close> 
| HML_poss \<open>'a\<close> \<open>('a,'x)HML_formula\<close> 

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
proof (rule allI, rule impI, rule allI)
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

subsection \<open>Weak-NOR HML\<close>

definition HML_weaknor ::
  \<open>'x set \<Rightarrow> ('x \<Rightarrow> ('a,'x)HML_formula) \<Rightarrow> ('a,'x)HML_formula\<close>
  where \<open>HML_weaknor I F = HML_poss \<tau> (HML_conj I (\<lambda>f. HML_neg (F f)))\<close>





end \<comment> \<open>of \<open>context lts\<close>\<close>
end \<comment> \<open>of \<open>theory\<close>\<close>