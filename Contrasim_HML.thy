theory Contrasim_HML
  imports
    Contrasimulation
    HM_Logic_Infinitary
begin

context lts_tau
begin

subsection \<open>Weak-NOR HML\<close>

definition HML_weaknor ::
  \<open>'x set \<Rightarrow> ('x \<Rightarrow> ('a,'x)HML_formula) \<Rightarrow> ('a,'x)HML_formula\<close>
  where \<open>HML_weaknor I F = HML_poss \<tau> (HML_conj I (\<lambda>f. HML_neg (F f)))\<close>

definition HML_weaknot ::
  \<open>('a,'x)HML_formula \<Rightarrow> ('a,'x)HML_formula\<close>
  where \<open>HML_weaknot \<phi> = HML_weaknor {undefined} (\<lambda>i. \<phi>)\<close>

inductive_set HML_weak_formulas :: \<open>('a,'x)HML_formula set\<close> where
  Base: \<open>HML_weaknor {} (\<lambda>i. HML_true) \<in> HML_weak_formulas\<close> |
  Obs: \<open>\<phi> \<in> HML_weak_formulas \<Longrightarrow> (\<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) \<in> HML_weak_formulas\<close> |
  Conj: \<open>(\<And>i. i \<in> I \<Longrightarrow> F i \<in> HML_weak_formulas) \<Longrightarrow> HML_weaknor I F \<in> HML_weak_formulas\<close>

thm HML_weak_formulas.induct

lemma backwards_truth:
  assumes
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>p \<longmapsto>* tau  p'\<close>
    \<open>p' \<Turnstile> \<phi>\<close>
  shows
    \<open>p \<Turnstile> \<phi>\<close>
  using assms apply (cases)
    apply (metis emptyE lts_tau.HML_weaknor_def lts_tau.satisfies.simps(4) lts_tau.tau_tau satisfies.simps(2))
  using satisfies.simps(4) steps_concat tau_tau apply blast
  by (smt (z3) HML_weaknor_def satisfies.simps(4) steps_concat tau_tau)

lemma all_states_sat_empty_conj:
  shows \<open>\<forall>q. q \<Turnstile> (HML_weaknor {} (\<lambda>i. HML_true))\<close>
proof - 
  have \<open>\<forall>q F. q \<Turnstile> (HML_conj {} (\<lambda>f. HML_neg (F f)))\<close> by auto
  thus ?thesis                     
    by (metis HML_formula.distinct(9, 11)
        HML_formula.inject(3) HML_weaknor_def satisfies.elims(3) step_tau_refl tau_def)
qed 

lemma tau_a_obs_implies_delay_step: 
  assumes \<open>p  \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close>
  shows \<open>\<exists>p'. p =\<rhd>a p' \<and> p' \<Turnstile> \<phi>\<close>
proof - 
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p'' \<and> p'' \<Turnstile> \<langle>a\<rangle>\<phi>\<close> using assms by auto
  thus ?thesis using satisfies.simps(4) steps_concat tau_tau by blast
qed

lemma delay_step_implies_tau_a_obs: 
  assumes 
    \<open>p =\<rhd>a p'\<close>
    \<open>p' \<Turnstile> \<phi>\<close>
  shows \<open>p  \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close>
proof - 
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p''\<close> and \<open>p'' \<Rightarrow>^a p'\<close> using assms steps.refl tau_tau by blast
  thus ?thesis by (metis assms(1,2) lts_tau.satisfies.simps(4) lts_tau.tau_tau)
qed


lemma contrasim_implies_HML_weak_equivalent:
  assumes
    \<open>(\<phi>, \<psi>) \<in> HML_subformulas \<or> \<phi> = \<psi>\<close>
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>p \<Turnstile> \<phi>\<close>
    \<open>p \<sqsubseteq>c q\<close>
  shows \<open>q \<Turnstile> \<phi>\<close>
  using HML_subformulas_wf assms
proof (induct arbitrary: p q)
  case (less \<phi>)
  from \<open>\<phi> \<in> HML_weak_formulas\<close> show ?case
  proof (cases)
    case Base
    then show ?thesis 
      unfolding HML_weaknor_def
      using lts.steps.simps satisfies.elims(3) tau_tau by fastforce
  next
    case (Obs \<phi>' a)
    with \<open>p \<Turnstile> \<phi>\<close> obtain p' where p'_spec: \<open>p =\<rhd>a p'\<close> \<open>p' \<Turnstile> \<phi>'\<close>
      by (metis satisfies.simps(4) steps_concat tau_tau)
    with \<open>p \<sqsubseteq>c q\<close> obtain q' where q'_spec: \<open>q  =\<rhd>a q'\<close> \<open>q' \<sqsubseteq>c p'\<close>
      using contrasim_step_weaker_than_seq unfolding contrasim_step_def
      sorry
    from \<open>\<phi>' \<in> HML_weak_formulas\<close> show ?thesis proof cases
      case Base
      then have \<open>q' \<Turnstile> \<phi>'\<close>
        unfolding HML_weaknor_def
        using lts.steps.simps satisfies.elims(3) tau_tau by fastforce
      with q'_spec(1) \<open>\<phi> = \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>'\<close> show ?thesis
        using step_tau_refl tau_def by auto
    next
      case (Obs \<phi> a)
      then show ?thesis sorry
    next
      case (Conj I F)
      then show ?thesis sorry
    qed
  next
    case (Conj I F)
    then show ?thesis sorry
  qed
  oops

(*
lemma contrasim_implies_HML_weak_equivalent:
  assumes
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>p \<Turnstile> \<phi>\<close>
    \<open>\<exists>q'. q' \<longmapsto>* tau q \<and> p \<sqsubseteq>c q'\<close>
  shows \<open>\<exists>q'. q' \<longmapsto>* tau q \<and> q' \<Turnstile> \<phi>\<close>
  using assms
proof (induct arbitrary: p q rule: HML_weak_formulas.induct)
  case Base
  then show ?case
    unfolding HML_weaknor_def
    using contrasim_coupled  by (auto)
next
  case (Obs \<phi> a p q)
  then obtain p' where p'_spec: \<open>p =\<rhd>a p'\<close> \<open>p' \<Turnstile> \<phi>\<close>
    by (metis satisfies.simps(4) steps_concat tau_tau)
  from Obs obtain q' where \<open>q' \<longmapsto>* tau q\<close> \<open>p \<sqsubseteq>c q'\<close> by blast
  with p'_spec obtain q'' where \<open>q' \<Rightarrow>^a q''\<close> \<open>q'' \<sqsubseteq>c p'\<close>
    using contrasim_step_weaker_than_seq unfolding contrasim_step_def
    by (smt (verit) step_tau_refl tau_tau)
  then obtain p'' where  \<open>p' \<longmapsto>* tau p''\<close> \<open>p'' \<sqsubseteq>c q''\<close>
    using contrasim_coupled
    by blast
  then show ?case
next
  case (Conj I F)
  then show ?case sorry
qed
*)

end \<comment> \<open>of \<open>context lts\<close>\<close>
end \<comment> \<open>of \<open>theory\<close>\<close>