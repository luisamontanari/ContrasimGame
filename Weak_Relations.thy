
subsection \<open>Weak Simulation\<close>

theory Weak_Relations
imports
  Weak_Transition_Systems
  Strong_Relations
begin

context lts_tau
begin

definition weak_simulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>weak_simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<Rightarrow>^a q')))\<close>

text \<open>Note: Isabelle won't finish the proofs needed for the introduction of the following
  coinductive predicate if it unfolds the abbreviation of @{text \<open>\<Rightarrow>^\<close>}. Therefore we use
  @{text \<open>\<Rightarrow>^^\<close>} as a barrier. There is no mathematical purpose in this.\<close>

definition weak_step_tau2 :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<Rightarrow>^^ _  _" [70, 70, 70] 80)
where [simp]:
  \<open>(p \<Rightarrow>^^ a q) \<equiv> p \<Rightarrow>^a q\<close>

coinductive greatest_weak_simulation :: 
  \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
where
  \<open>(\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> (\<exists> q'. greatest_weak_simulation p' q' \<and> (q \<Rightarrow>^^ a q')))
  \<Longrightarrow> greatest_weak_simulation p q\<close>
  
lemma weak_sim_ruleformat:
assumes \<open>weak_simulation R\<close>
  and \<open>R p q\<close>
shows
  \<open>p \<longmapsto>a p' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<Rightarrow>a q'))\<close>
  \<open>p \<longmapsto>a p' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>* tau q'))\<close>
  using assms unfolding weak_simulation_def by (blast+)

abbreviation weakly_simulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>ws  _" [60, 60] 65)
  where \<open>weakly_simulated_by p q \<equiv> \<exists> R . weak_simulation R \<and> R p q\<close>

lemma weaksim_greatest:
  shows \<open>weak_simulation (\<lambda> p q . p \<sqsubseteq>ws q)\<close>
  unfolding weak_simulation_def
  by (metis (no_types, lifting))


lemma gws_is_weak_simulation:
  shows \<open>weak_simulation greatest_weak_simulation\<close>
  unfolding weak_simulation_def
proof safe
  fix p q p' a
  assume ih:
    \<open>greatest_weak_simulation p q\<close>
    \<open>p \<longmapsto>a  p'\<close>
  hence \<open>(\<forall>x xa. p \<longmapsto>x xa \<longrightarrow> (\<exists>q'. q \<Rightarrow>^^ x  q' \<and> greatest_weak_simulation xa q'))\<close>
    by (meson greatest_weak_simulation.simps)
  then obtain q' where \<open>q \<Rightarrow>^^ a  q' \<and> greatest_weak_simulation p' q'\<close> using ih by blast
  thus \<open>\<exists>q'. greatest_weak_simulation p' q' \<and> q \<Rightarrow>^a  q'\<close>
    unfolding weak_step_tau2_def by blast
qed

lemma weakly_sim_by_implies_gws:
  assumes \<open>p \<sqsubseteq>ws q\<close>
  shows \<open>greatest_weak_simulation p q\<close>
  using assms
proof (coinduct, simp del: weak_step_tau2_def, safe)
  fix x1 x2 R a xa
  assume ih: \<open>weak_simulation R\<close> \<open>R x1 x2\<close> \<open>x1 \<longmapsto>a  xa\<close>
  then obtain q' where \<open>x2 \<Rightarrow>^^ a  q'\<close> \<open>R xa q'\<close>
    unfolding weak_simulation_def weak_step_tau2_def by blast
  thus \<open>\<exists>q'. (xa \<sqsubseteq>ws  q' \<or> greatest_weak_simulation xa q') \<and> x2 \<Rightarrow>^^ a  q'\<close>
    using ih by blast
qed

lemma gws_eq_weakly_sim_by:
  shows \<open>p \<sqsubseteq>ws q = greatest_weak_simulation p q\<close>
  using weakly_sim_by_implies_gws gws_is_weak_simulation by blast

lemma steps_retain_weak_sim:
assumes 
  \<open>weak_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<longmapsto>*A  p'\<close>
  \<open>\<And> a . tau a \<Longrightarrow> A a\<close>
shows \<open>\<exists>q'. R p' q' \<and> q \<longmapsto>*A  q'\<close>
  using assms(3,2,4) proof (induct)
  case (refl p' A)
  hence \<open>R p' q  \<and> q \<longmapsto>* A  q\<close> using assms(2) steps.refl by simp
  then show ?case by blast
next
  case (step p A p' a p'')
  then obtain q' where q': \<open>R p' q'\<close> \<open>q \<longmapsto>* A  q'\<close> by blast
  obtain q'' where q'':
    \<open>R p'' q''\<close> \<open>(\<not> tau a \<longrightarrow> q' \<Rightarrow>a  q'') \<and> (tau a \<longrightarrow> q' \<longmapsto>* tau  q'')\<close>
    using `weak_simulation R` q'(1) step(3) unfolding weak_simulation_def by blast
  have \<open>q' \<longmapsto>* A  q''\<close>
    using q''(2) steps_spec[of q'] step(4) step(6) weak_steps[of q' a q''] by blast
  hence \<open>q \<longmapsto>* A  q''\<close> using steps_concat[OF _ q'(2)] by blast
  thus ?case using q''(1) by blast
qed

lemma weak_sim_weak_premise:
  \<open>weak_simulation R =
    (\<forall> p q . R p q \<longrightarrow> 
      (\<forall> p' a. p \<Rightarrow>^a p' \<longrightarrow> (\<exists> q'. R p' q' \<and> q \<Rightarrow>^a q')))\<close>
proof 
  assume \<open>\<forall> p q . R p q \<longrightarrow> (\<forall>p' a. p \<Rightarrow>^a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'))\<close>
  thus \<open>weak_simulation R\<close>
    unfolding weak_simulation_def using step_weak_step_tau by simp
next
  assume ws: \<open>weak_simulation R\<close>
  show \<open>\<forall>p q. R p q \<longrightarrow> (\<forall>p' a. p \<Rightarrow>^a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'))\<close>
  proof safe
    fix p q p' a pq1 pq2
    assume case_assms:
      \<open>R p q\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain q' where q'_def: \<open>q \<longmapsto>* tau  q'\<close> \<open>R pq1 q'\<close>
      using steps_retain_weak_sim[OF ws] by blast
    then moreover obtain q'' where q''_def: \<open>R pq2 q''\<close> \<open>q' \<Rightarrow>^a  q''\<close>
      using ws case_assms(3) unfolding weak_simulation_def by blast
    then moreover obtain q''' where q''_def: \<open>R p' q'''\<close> \<open>q'' \<longmapsto>* tau  q'''\<close>
      using case_assms(4) steps_retain_weak_sim[OF ws] by blast
    ultimately show \<open>\<exists> q'''. R p' q''' \<and> q \<Rightarrow>^a  q'''\<close> using weak_step_extend by blast
  next
    fix p q p' a
    assume
      \<open>R p q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>\<nexists>q'. R p' q' \<and> q \<Rightarrow>^a  q'\<close>
      \<open>tau a\<close>
    thus \<open>False\<close>
      using steps_retain_weak_sim[OF ws] by blast
  next
    \<comment>\<open>case identical to first case\<close>
    fix p q p' a pq1 pq2
    assume case_assms:
      \<open>R p q\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain q' where q'_def: \<open>q \<longmapsto>* tau  q'\<close> \<open>R pq1 q'\<close>
      using steps_retain_weak_sim[OF ws] by blast
    then moreover obtain q'' where q''_def: \<open>R pq2 q''\<close> \<open>q' \<Rightarrow>^a  q''\<close>
      using ws case_assms(3) unfolding weak_simulation_def by blast
    then moreover obtain q''' where q''_def: \<open>R p' q'''\<close> \<open>q'' \<longmapsto>* tau  q'''\<close>
      using case_assms(4) steps_retain_weak_sim[OF ws] by blast
    ultimately show \<open>\<exists> q'''. R p' q''' \<and> q \<Rightarrow>^a  q'''\<close> using weak_step_extend by blast
  qed
qed

lemma weak_sim_enabled_subs:
  assumes
    \<open>p \<sqsubseteq>ws q\<close>
    \<open>weak_enabled p a\<close>
    \<open>\<not> tau a\<close>
  shows \<open>weak_enabled q a\<close>
proof-
  obtain p' where p'_spec: \<open>p \<Rightarrow>a p'\<close>
    using \<open>weak_enabled p a\<close> weak_enabled_step by blast
  obtain R where \<open>R p q\<close> \<open>weak_simulation R\<close> using assms(1) by blast
  then obtain q' where \<open>q \<Rightarrow>^a q'\<close>
    unfolding weak_sim_weak_premise using weak_step_impl_weak_tau[OF p'_spec] by blast
  thus ?thesis using weak_enabled_step assms(3) by blast
qed

lemma weak_sim_union_cl:
  assumes
    \<open>weak_simulation RA\<close>
    \<open>weak_simulation RB\<close>
  shows
    \<open>weak_simulation (\<lambda> p q. RA p q \<or> RB p q)\<close>
  using assms unfolding weak_simulation_def by blast

lemma weak_sim_remove_dead_state:
  assumes
    \<open>weak_simulation R\<close>
    \<open>\<And> a p . \<not> step d a p \<and> \<not> step p a d\<close>
  shows
    \<open>weak_simulation (\<lambda> p q . R p q \<and> q \<noteq> d)\<close>
  unfolding weak_simulation_def
proof safe
  fix p q p' a
  assume
    \<open>R p q\<close>
    \<open>q \<noteq> d\<close>
    \<open>p \<longmapsto>a  p'\<close>
  then obtain q' where \<open>R p' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
    using assms(1) unfolding weak_simulation_def by blast
  moreover hence \<open>q' \<noteq> d\<close>
    using assms(2) `q \<noteq> d` by (metis steps.cases)
  ultimately show \<open>\<exists>q'. (R p' q' \<and> q' \<noteq> d) \<and> q \<Rightarrow>^a  q'\<close> by blast
qed

lemma weak_sim_tau_step:
  \<open>weak_simulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)\<close>
  unfolding weak_simulation_def
  using lts.steps.simps by metis

lemma weak_sim_trans_constructive:
  fixes R1 R2
  defines
    \<open>R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)\<close>
  assumes
    R1_def: \<open>weak_simulation R1\<close> \<open>R1 p pq\<close> and
    R2_def: \<open>weak_simulation R2\<close> \<open>R2 pq q\<close>
  shows
    \<open>R p q\<close> \<open>weak_simulation R\<close>
proof-
  show \<open>R p q\<close> unfolding R_def using R1_def(2) R2_def(2) by blast
next
  show \<open>weak_simulation R\<close>
    unfolding weak_sim_weak_premise R_def
  proof (safe)
    fix p q pq p' a pq1 pq2
    assume
      \<open>R1 p pq\<close>
      \<open>R2 pq q\<close>
      \<open>\<not> tau a\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    thus \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      using R1_def(1) R2_def(1) unfolding weak_sim_weak_premise by blast
  next
    fix p q pq p' a
    assume
      \<open>R1 p pq\<close>
      \<open>R2 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>\<nexists>q'.(\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q')\<and> q \<Rightarrow>^a  q'\<close>
      \<open>tau a\<close>
    thus \<open>False\<close>
      using R1_def(1) R2_def(1) unfolding weak_sim_weak_premise by blast
  next
    fix p q pq p' a pq1 pq2
    assume 
      \<open>R1 p pq\<close>
      \<open>R2 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain pq' q' where \<open>R1 p' pq'\<close> \<open>pq \<Rightarrow>^a  pq'\<close> \<open>R2 pq' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
      using R1_def(1) R2_def(1) assms(3) unfolding weak_sim_weak_premise by blast
    thus \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      by blast
  next
    fix p q pq p' a pq1 pq2
    assume sa:
      \<open>R2 p pq\<close>
      \<open>R1 pq q\<close>
      \<open>\<not> tau a\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain pq' q'  where \<open>R2 p' pq'\<close> \<open>pq \<Rightarrow>^a  pq'\<close> \<open>R1 pq' q'\<close> \<open>q \<Rightarrow>^a  q'\<close>
      using R2_def(1) R1_def(1) unfolding weak_sim_weak_premise by blast
    thus \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      by blast
  next
    fix p q pq p' a
    assume
      \<open>R2 p pq\<close>
      \<open>R1 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>\<nexists>q'.(\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q')\<and> q \<Rightarrow>^a  q'\<close>
      \<open>tau a\<close>
    thus \<open>False\<close>
      using R1_def(1) R2_def(1) weak_step_tau_tau[OF `p \<longmapsto>* tau  p'` tau_tau]
      unfolding weak_sim_weak_premise by (metis (no_types, lifting))
  next
    fix p q pq p' a pq1 pq2
    assume sa:
      \<open>R2 p pq\<close>
      \<open>R1 pq q\<close>
      \<open>p \<longmapsto>* tau  p'\<close>
      \<open>p \<longmapsto>* tau  pq1\<close>
      \<open>pq1 \<longmapsto>a  pq2\<close>
      \<open>pq2 \<longmapsto>* tau  p'\<close>
    then obtain pq'  where \<open>R2 p' pq'\<close> \<open>pq \<Rightarrow>^a  pq'\<close>
      using R1_def(1) R2_def(1) weak_step_impl_weak_tau[of p a p']
      unfolding weak_sim_weak_premise by blast
    moreover then obtain q' where \<open>R1 pq' q'\<close> \<open>q \<Rightarrow>^a  q'\<close> 
      using R1_def(1) sa(2) unfolding weak_sim_weak_premise by blast
    ultimately show \<open>\<exists>q'. (\<exists>pq. R1 p' pq \<and> R2 pq q' \<or> R2 p' pq \<and> R1 pq q') \<and> q \<Rightarrow>^a  q'\<close>
      by blast
  qed
qed

lemma weak_sim_trans:
  assumes
    \<open>p \<sqsubseteq>ws pq\<close>
    \<open>pq \<sqsubseteq>ws q\<close>
  shows
    \<open>p \<sqsubseteq>ws q\<close>
  using assms(1,2)
proof -
  obtain R1 R2  where  \<open>weak_simulation R1\<close> \<open>R1 p pq\<close> \<open>weak_simulation R2\<close> \<open>R2 pq q\<close>
    using assms(1,2) by blast
  thus ?thesis
    using weak_sim_trans_constructive tau_tau
    by blast
qed

subsection \<open>Weak Bisimulation\<close>

definition weak_bisimulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>weak_bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> (\<exists> q'. R p' q'
      \<and> (q \<Rightarrow>^a q'))) \<and>
    (\<forall> q' a. q \<longmapsto>a q' \<longrightarrow> (\<exists> p'. R p' q'
      \<and> ( p \<Rightarrow>^a p')))\<close>
  
lemma weak_bisim_ruleformat:
assumes \<open>weak_bisimulation R\<close>
  and \<open>R p q\<close>
shows
  \<open>p \<longmapsto>a p' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<Rightarrow>a q'))\<close>
  \<open>p \<longmapsto>a p' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>* tau q'))\<close>
  \<open>q \<longmapsto>a q' \<Longrightarrow> \<not>tau a \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<Rightarrow>a p'))\<close>
  \<open>q \<longmapsto>a q' \<Longrightarrow>  tau a \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<longmapsto>* tau p'))\<close>
  using assms unfolding weak_bisimulation_def by (blast+)
  
definition tau_weak_bisimulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow>  bool) \<Rightarrow>  bool\<close>
where
  \<open>tau_weak_bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<Rightarrow>a q'))) \<and>
    (\<forall> q' a. q \<longmapsto>a q' \<longrightarrow> 
      (\<exists> p'. R p' q' \<and> (p \<Rightarrow>a p')))\<close>

lemma weak_bisim_implies_tau_weak_bisim:
  assumes
    \<open>tau_weak_bisimulation R\<close>
  shows
    \<open>weak_bisimulation R\<close>
unfolding weak_bisimulation_def proof (safe)
  fix p q p' a
  assume \<open>R p q\<close> \<open>p \<longmapsto>a  p'\<close>
  thus \<open>\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q')\<close>
    using assms weak_steps[of q a _ tau] unfolding tau_weak_bisimulation_def by blast
next
  fix p q q' a
  assume \<open>R p q\<close> \<open>q \<longmapsto>a  q'\<close>
  thus \<open>\<exists>p'. R p' q' \<and> (p \<Rightarrow>^a  p')\<close>
    using assms weak_steps[of p a _ tau] unfolding tau_weak_bisimulation_def by blast
qed

lemma weak_bisim_invert:
  assumes
    \<open>weak_bisimulation R\<close>
  shows
    \<open>weak_bisimulation (\<lambda> p q. R q p)\<close>
using assms unfolding weak_bisimulation_def by auto
  
lemma bisim_weak_bisim:
  assumes \<open>bisimulation R\<close>
  shows \<open>weak_bisimulation R\<close>
  unfolding weak_bisimulation_def
proof (clarify, rule)
  fix p q
  assume R: \<open>R p q\<close>
  show \<open>\<forall>p' a. p \<longmapsto>a  p' \<longrightarrow> (\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q'))\<close>
  proof (clarify)
    fix p' a
    assume p'a: \<open>p \<longmapsto>a  p'\<close>
    have
      \<open>\<not> tau a \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<Rightarrow>a  q')\<close>
      \<open>(tau a \<longrightarrow> (\<exists>q'. R p' q' \<and> q \<longmapsto>* tau  q'))\<close> 
      using bisim_ruleformat(1)[OF assms R p'a] step_weak_step step_weak_step_tau by auto
    thus \<open>\<exists>q'. R p' q' \<and> (q \<Rightarrow>^a  q')\<close> by blast
  qed
next 
  fix p q
  assume R: \<open>R p q\<close>
  have \<open>\<forall>q' a. q \<longmapsto>a  q' \<longrightarrow> (\<not> tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<Rightarrow>a  p'))
     \<and> (tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>* tau  p'))\<close>
  proof (clarify)
    fix q' a
    assume q'a: \<open>q \<longmapsto>a  q'\<close>
    show
      \<open>(\<not> tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<Rightarrow>a  p')) \<and>
      (tau a \<longrightarrow> (\<exists>p'. R p' q' \<and> p \<longmapsto>* tau  p'))\<close> 
      using bisim_ruleformat(2)[OF assms R q'a] step_weak_step
        step_weak_step_tau steps_one_step by auto
  qed
  thus \<open>\<forall>q' a. q \<longmapsto>a  q' \<longrightarrow> (\<exists>p'. R p' q' \<and> (p \<Rightarrow>^a  p'))\<close> by blast
qed
  
lemma weak_bisim_weak_sim:  
shows
  \<open>weak_bisimulation R = (weak_simulation R \<and> weak_simulation (\<lambda> p q . R q p))\<close>
unfolding weak_bisimulation_def weak_simulation_def by auto

lemma steps_retain_weak_bisim:
  assumes 
    \<open>weak_bisimulation R\<close>
    \<open>R p q\<close>
    \<open>p \<longmapsto>*A  p'\<close>
    \<open>\<And> a . tau a \<Longrightarrow> A a\<close>
  shows \<open>\<exists>q'. R p' q' \<and> q \<longmapsto>*A  q'\<close>
    using assms weak_bisim_weak_sim steps_retain_weak_sim
    by auto
  
lemma weak_bisim_union:
  assumes
    \<open>weak_bisimulation R1\<close>
    \<open>weak_bisimulation R2\<close>
  shows
    \<open>weak_bisimulation (\<lambda> p q . R1 p q \<or> R2 p q)\<close>
  using assms unfolding weak_bisimulation_def by blast

subsection \<open>Delay Simulation\<close>

definition delay_simulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>delay_simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (tau a \<longrightarrow> R p' q) \<and>
      (\<not>tau a \<longrightarrow> (\<exists> q'. R p' q'\<and> (q =\<rhd>a q'))))\<close>

lemma delay_simulation_implies_weak_simulation:
  assumes
    \<open>delay_simulation R\<close>
  shows
    \<open>weak_simulation R\<close>
  using assms weak_step_delay_implies_weak_tau steps.refl
  unfolding delay_simulation_def weak_simulation_def by blast

end \<comment>\<open>context @{locale lts_tau}\<close>
  
subsection \<open>Similarity ignores \<open>\<tau>\<close>-sinks\<close>
  
lemma simulation_tau_sink_1:
  fixes
    step sink \<tau> R
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p\<close>
    \<open>lts_tau.weak_simulation step \<tau> R\<close>
  shows
    \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink \<or> R p q)\<close>
proof -
  let ?tau = \<open>(lts_tau.tau \<tau>)\<close>
  let ?tauEx = \<open>\<tau>\<close>
  show ?thesis unfolding lts_tau.weak_simulation_def
  proof safe
    fix p q p' a
    assume \<open>step2 sink a p'\<close>
    hence \<open>p' = sink\<close> \<open>a = \<tau>\<close>
      using assms(2) unfolding step2_def by auto
    thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and> 
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2 
        \<and> lts.steps step2 pq2 ?tau q'))\<close>
      using lts_tau.step_tau_refl[of \<tau> step2 q] lts.steps.refl[of step2 q ?tau]  by auto
  next
    fix p q p' a
    assume \<open>step2 p a p'\<close> \<open>R p q\<close>
    have step_impl_step2: \<open>\<And> p1 a p2 . step p1 a p2 \<Longrightarrow> step2 p1 a p2\<close>
      unfolding step2_def by blast
    have \<open>(p \<noteq> sink \<and> a = ?tauEx \<and> p' = sink) \<or> step p a p'\<close>
      using `step2 p a p'` unfolding step2_def .
    thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
        \<and> lts.steps step2 pq2 ?tau q'))\<close>
    proof safe
      show \<open>\<exists>q'. (sink = sink \<or> R sink q') \<and>
           (?tau ?tauEx \<longrightarrow> lts.steps step2 q ?tau q') \<and>
           (\<not> ?tau ?tauEx \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1
            \<and> step2 pq1 ?tauEx pq2 \<and> lts.steps step2 pq2 ?tau q'))\<close>
        using lts.steps.refl[of step2 q ?tau] assms(1) by (meson lts_tau.tau_tau)
    next
      assume \<open>step p a p'\<close>
      then obtain q' where q'_def:
        \<open>R p' q' \<and>
        (?tau a \<longrightarrow> lts.steps step q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> lts.steps step pq2 ?tau q'))\<close>
        using assms(3) `R p q` unfolding lts_tau.weak_simulation_def by blast
      hence \<open>(p' = sink \<or> R p' q') \<and>
        (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
          \<and> lts.steps step2 pq2 ?tau q'))\<close>
        using lts_impl_steps[of step _ _ _ step2] step_impl_step2 by blast
      thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
        (?tau a \<longrightarrow> lts.steps step2 q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. lts.steps step2 q ?tau pq1 \<and> step2 pq1 a pq2
          \<and> lts.steps step2 pq2 ?tau q'))\<close>
        by blast
    qed
  qed
qed
  
lemma simulation_tau_sink_2:
  fixes
    step sink R \<tau>
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p \<and> \<not> step p a sink\<close>
    \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink \<or> R p q)\<close>
    \<open>\<And> p' q' q . (p' = sink \<or> R p' q') 
      \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'  \<longrightarrow> (p' = sink \<or> R p' q)\<close>
  shows
    \<open>lts_tau.weak_simulation step \<tau> (\<lambda> p q. p = sink \<or> R p q)\<close>
proof -
  let ?tau = \<open>(lts_tau.tau \<tau>)\<close>
  let ?tauEx = \<open>\<tau>\<close>
  let ?steps = \<open>lts.steps\<close>
  show ?thesis
    unfolding lts_tau.weak_simulation_def
  proof safe
    fix p q p' a
    assume
      \<open>step sink a p'\<close>
    hence False using assms(2) by blast
    thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> ?steps step q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> ?steps step pq2 ?tau q'))\<close> ..
  next
    fix p q p' a
    assume \<open>R p q\<close> \<open>step p a p'\<close>
    hence not_sink: \<open>p \<noteq> sink\<close> \<open>p' \<noteq> sink\<close>
      using assms(2)[of a p] assms(2)[of a p'] by auto
    have \<open>step2 p a p'\<close> using `step p a p'` unfolding step2_def by blast
    then obtain q' where q'_def:
      \<open>p' = sink \<or> R p' q'\<close>
      \<open>?tau a \<longrightarrow> ?steps step2 q ?tau q'\<close>  
      \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step2 q ?tau pq1 \<and> step2 pq1 a pq2 
        \<and> ?steps step2 pq2 ?tau q')\<close>
      using assms(3) `R p q` unfolding lts_tau.weak_simulation_def by blast
    hence outer_goal_a: \<open>R p' q'\<close> using not_sink by blast
    show \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and>
      (?tau a \<longrightarrow> ?steps step q ?tau q') \<and>
      (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> ?steps step pq2 ?tau q'))\<close>
    proof (cases \<open>q' = sink\<close>)
      assume \<open>q' = sink\<close>
      then obtain q'' where q''_def:
        \<open>?tau a \<longrightarrow> (?steps step q ?tau q'' \<and> ?steps step2 q'' ?tau q')\<close>
        \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1. ?steps step2 q ?tau pq1 \<and> step pq1 a q''
          \<and> ?steps step2 q'' ?tau q')\<close>
        using q'_def(2,3) assms(1) step2_def lts_tau.step_tau_refl[of \<tau>]
          lts_tau.tau_tau[of \<tau>] by metis
      hence \<open>q'' = sink \<longrightarrow> q = sink\<close>
        using assms(2) unfolding step2_def by (metis lts.steps.cases)
      have \<open>?steps step2 q'' ?tau q'\<close> using q''_def by auto
      hence \<open>p' = sink \<or> R p' q''\<close> using  q'_def(1) assms(4)[of p' q' q''] by blast
      moreover have \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
        \<and> ?steps step pq2 ?tau q'')\<close>
      proof
        assume \<open>\<not> ?tau a\<close>
        hence \<open>q \<noteq> sink\<close> using q'_def by (metis assms(2) lts.steps_left step2_def)
        hence \<open>q'' \<noteq> sink\<close> using `q'' = sink \<longrightarrow> q = sink` by simp
        obtain pq1 where pq1_def:
            \<open>?steps step2 q ?tau pq1\<close> \<open>step pq1 a q''\<close> \<open>?steps step2 q'' ?tau q'\<close>
          using q''_def(2) `\<not> ?tau a` by blast
        hence \<open>pq1 \<noteq> sink\<close> using `q'' \<noteq> sink` assms(2) by blast
        hence \<open>?steps step q ?tau pq1\<close> using `q \<noteq> sink` `?steps step2 q ?tau pq1`
        proof (induct rule: lts.steps.induct[OF `?steps step2 q ?tau pq1`])
          case (1 p af)
          then show ?case using lts.steps.refl[of step p af] by blast
        next
          case (2 p af q1 a q)
          hence \<open>q1 \<noteq> sink\<close> \<open>step q1 a q\<close> using assms(2) unfolding step2_def by auto
          moreover hence \<open>?steps step p af q1\<close> using 2 by blast 
          ultimately show ?case using 2(4) by (meson lts.step)
        qed
        thus
          \<open>\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2 \<and> ?steps step pq2 ?tau q''\<close>
          using pq1_def(2) lts.steps.refl[of step q'' ?tau] by blast
      qed
      ultimately show \<open>\<exists>q''. (p' = sink \<or> R p' q'') \<and>
           (?tau a \<longrightarrow> ?steps step q ?tau q'') \<and>
           (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
            \<and> ?steps step pq2 ?tau q''))\<close>
        using q''_def(1) q'_def(1) by auto
    next
      assume not_sink_q': \<open>q' \<noteq> sink\<close>
      have outer_goal_b: \<open>?tau a \<longrightarrow> ?steps step q ?tau q'\<close>
        using q'_def(2) not_sink_q' unfolding step2_def
      proof (safe)
        assume i:
          \<open>q' \<noteq> sink\<close> \<open>?tau a\<close>
          \<open>?steps (\<lambda>p1 a p2.  p1 \<noteq> sink \<and> a = ?tauEx \<and> p2 = sink \<or> step p1 a p2) q ?tau q'\<close>
        thus \<open>?steps step q ?tau q'\<close>
        proof (induct rule: lts.steps.induct[OF i(3)])
          case (1 p af)
          then show ?case using lts.steps.refl[of _ p af] by auto
        next
          case (2 p af q1 a q)
          hence \<open>step q1 a q\<close> by blast
          moreover have \<open>?steps step p af q1\<close> using 2 assms(2) by blast
          ultimately show ?case using `af a` lts.step[of step p af q1 a q] by blast
        qed
      qed
      have outer_goal_c:
          \<open>\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> ?steps step pq2 ?tau q')\<close>
        using q'_def(3)
      proof safe
        fix pq1 pq2
        assume subassms:
          \<open>\<not> ?tau a\<close>
          \<open>?steps step2 q ?tau pq1\<close>
          \<open>step2 pq1 a pq2\<close>
          \<open>?steps step2 pq2 ?tau q'\<close>
        have \<open>pq2 \<noteq> sink\<close> 
          using subassms(4) assms(2) not_sink_q' lts.steps_loop
          unfolding step2_def by (metis (mono_tags, lifting))
        have  goal_c: \<open>?steps step pq2 ?tau q'\<close>
          using subassms(4) not_sink_q' unfolding step2_def
        proof (induct rule:lts.steps.induct[OF subassms(4)])
          case (1 p af) show ?case using lts.steps.refl by assumption
        next
          case (2 p af q1 a q)
          hence \<open>step q1 a q\<close> unfolding step2_def by simp
          moreover hence \<open>q1 \<noteq> sink\<close> using assms(2) by blast
          ultimately have \<open>?steps step p af q1\<close> using 2 unfolding step2_def by auto
          thus ?case using `step q1 a q` 2(4) lts.step[of step p af q1 a q] by blast
        qed
        have goal_b: \<open>step pq1 a pq2\<close>
          using `pq2 \<noteq> sink` subassms(3) unfolding step2_def by blast
        hence \<open>pq1 \<noteq> sink\<close> using assms(2) by blast
        hence goal_a: \<open>?steps step q ?tau pq1\<close>
          using subassms(4) unfolding step2_def
        proof (induct rule:lts.steps.induct[OF subassms(2)])
          case (1 p af) show ?case using lts.steps.refl by assumption
        next
          case (2 p af q1 a q)
          hence \<open>step q1 a q\<close> unfolding step2_def by simp
          moreover hence \<open>q1 \<noteq> sink\<close> using assms(2) by blast
          ultimately have \<open>?steps step p af q1\<close> using 2 unfolding step2_def by auto
          thus ?case using `step q1 a q` 2(4) lts.step[of step p af q1 a q] by blast
        qed
        thus
          \<open>\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2 \<and> ?steps step pq2 ?tau q'\<close>
          using goal_b goal_c by auto
      qed
      thus \<open>\<exists>q'. (p' = sink \<or> R p' q') \<and> (?tau a \<longrightarrow> ?steps step q ?tau q') \<and>
        (\<not> ?tau a \<longrightarrow> (\<exists>pq1 pq2. ?steps step q ?tau pq1 \<and> step pq1 a pq2
          \<and> ?steps step pq2 ?tau q'))\<close>
        using outer_goal_a outer_goal_b by auto
    qed
  qed
qed

lemma simulation_sink_invariant:
  fixes
    step sink \<tau> R
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a =  \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p \<and> \<not> step p a sink\<close>
  shows \<open>lts_tau.weakly_simulated_by step2 \<tau> p q = lts_tau.weakly_simulated_by step \<tau> p q\<close>
proof (rule)
  have sink_sim_min: \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda> p q. p = sink)\<close>
    unfolding lts_tau.weak_simulation_def step2_def using assms(2)
    by (meson lts.steps.simps)
  define R where \<open>R \<equiv> lts_tau.weakly_simulated_by step2 \<tau>\<close>
  have weak_sim_R: \<open>lts_tau.weak_simulation step2 \<tau> R\<close>
    using lts_tau.weaksim_greatest[of step2 \<tau>] unfolding R_def by blast
  have R_contains_inv_tau_closure:
    \<open>R = (\<lambda>p1 q1. R p1 q1 \<or> lts.steps step2 q1 (lts_tau.tau \<tau>) p1)\<close> unfolding R_def
  proof (rule, rule, rule, simp)
    fix p q
    assume
      \<open>(\<exists>R. lts_tau.weak_simulation step2 \<tau>  R \<and> R p q) \<or>
       (lts.steps step2 q (lts_tau.tau \<tau>) p)\<close>
    thus \<open>\<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q\<close>
      using weak_sim_R
            lts_tau.weak_sim_tau_step[of step2 \<open>\<tau>\<close>]
            lts_tau.weak_sim_union_cl[of step2 \<open>\<tau>\<close>] by blast
  qed
  assume Rpq: \<open>R p q\<close>
  have \<open>\<And> p' q' q . R p' q' \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'  \<longrightarrow> R p' q\<close>
    using R_contains_inv_tau_closure lts_tau.weak_sim_trans[of step2 \<open>\<tau>\<close> _ _ _] R_def assms(2)
    by meson
  hence closed_R:
      \<open>\<And> p' q' q . (p' = sink \<or> R p' q') \<and> lts.steps step2 q (lts_tau.tau \<tau>) q'
         \<longrightarrow> (p' = sink \<or> R p' q)\<close>
    using weak_sim_R sink_sim_min lts_tau.weak_sim_union_cl by blast
  have \<open>lts_tau.weak_simulation step2 \<tau> (\<lambda>p q. p = sink \<or> R p q)\<close>
    using weak_sim_R sink_sim_min lts_tau.weak_sim_union_cl[of step2 \<tau>] by blast
  hence \<open>lts_tau.weak_simulation step \<tau> (\<lambda>p q. p = sink \<or> R p q)\<close>
    using  simulation_tau_sink_2[of step sink \<tau> R] assms(2) closed_R
    unfolding step2_def by blast
  thus \<open>\<exists>R. lts_tau.weak_simulation step \<tau> R \<and> R p q\<close>
    using Rpq weak_sim_R by blast
next
  show \<open>\<exists>R. lts_tau.weak_simulation step \<tau> R \<and> R p q \<Longrightarrow>
        \<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q\<close>
  proof clarify
    fix R
    assume
      \<open>lts_tau.weak_simulation step \<tau> R\<close>
      \<open>R p q\<close>
    hence \<open>lts_tau.weak_simulation
      (\<lambda>p1 a p2. p1 \<noteq> sink \<and> a = \<tau> \<and> p2 = sink \<or> step p1 a p2) \<tau> (\<lambda>p q. p = sink \<or> R p q)\<close>
      using simulation_tau_sink_1[of step sink \<tau> R] assms(2) unfolding step2_def by auto
    thus \<open>\<exists>R. lts_tau.weak_simulation step2 \<tau> R \<and> R p q\<close>
      using `R p q` unfolding step2_def by blast
  qed
qed

end