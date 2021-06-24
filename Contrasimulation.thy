section \<open>Contrasimulation\<close>

theory Contrasimulation
imports
  Weak_Relations
begin

context lts_tau
begin

subsection \<open>Definition of Contrasimulation\<close>

definition contrasim ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>contrasim R \<equiv> \<forall> p q p' A . (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<and> R p q \<and> (p \<Rightarrow>$ A p') \<longrightarrow>
    (\<exists> q'. (q \<Rightarrow>$ A q') \<and> R q' p')\<close>

lemma contrasim_simpler_def:
  shows \<open>contrasim R =
    (\<forall> p q p' A . R p q \<and> (p \<Rightarrow>$ A p') \<longrightarrow> (\<exists> q'. (q \<Rightarrow>$ A q') \<and> R q' p'))\<close>
proof -
  have \<open>\<And>A. \<forall>a\<in>set (filter (\<lambda>a. a \<noteq> \<tau>) A). a \<noteq> \<tau>\<close> by auto
  then show ?thesis
    unfolding contrasim_def
    using word_steps_ignore_tau_addition word_steps_ignore_tau_removal
    by metis
qed
abbreviation contrasimulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>c  _" [60, 60] 65)
  where \<open>contrasimulated_by p q \<equiv> \<exists> R . contrasim R \<and> R p q\<close>

lemma contrasim_preorder_is_contrasim:
  shows \<open>contrasim (\<lambda> p q . p \<sqsubseteq>c q)\<close>
  unfolding contrasim_def
  by metis

lemma contrasim_preorder_is_greatest:
  assumes \<open>contrasim R\<close>
  shows \<open>\<And> p q. R p q \<Longrightarrow> p \<sqsubseteq>c q\<close>
  using assms by auto

lemma contrasim_tau_step:
  \<open>contrasim (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)\<close>
  unfolding contrasim_def
  using steps.simps tau_tau tau_word_concat
  by metis

lemma contrasim_trans_constructive:
  fixes R1 R2
  defines
    \<open>R \<equiv> \<lambda> p q . \<exists> pq . (R1 p pq \<and> R2 pq q) \<or> (R2 p pq \<and> R1 pq q)\<close>
  assumes
    R1_def: \<open>contrasim R1\<close> \<open>R1 p pq\<close> and
    R2_def: \<open>contrasim R2\<close> \<open>R2 pq q\<close>
  shows
    \<open>R p q\<close> \<open>contrasim R\<close>
  using assms(2,3,4,5) unfolding R_def contrasim_def by metis+

lemma contrasim_trans:
  assumes
    \<open>p \<sqsubseteq>c pq\<close>
    \<open>pq \<sqsubseteq>c q\<close>
  shows
    \<open>p \<sqsubseteq>c q\<close>
  using assms contrasim_trans_constructive by blast

lemma contrasim_refl:
  shows
    \<open>p \<sqsubseteq>c p\<close>
  using contrasim_tau_step steps.refl by blast

lemma contrasim_coupled:
  assumes
    \<open>contrasim R\<close>
    \<open>R p q\<close>
  shows
    \<open>\<exists> q'. q \<longmapsto>* tau q' \<and> R q' p\<close>
  using assms steps.refl[of p tau] weak_step_seq.simps(1)
  unfolding contrasim_simpler_def by blast

lemma contrasim_taufree_symm:
  assumes
    \<open>contrasim R\<close>
    \<open>R p q\<close>
    \<open>stable_state q\<close>
  shows
    \<open>R q p\<close>
  using contrasim_coupled assms stable_tauclosure_only_loop by blast

lemma symm_contrasim_is_weak_bisim:
  assumes
    \<open>contrasim R\<close>
    \<open>\<And> p q. R p q \<Longrightarrow> R q p\<close>
  shows
    \<open>weak_bisimulation R\<close>
  using assms unfolding contrasim_simpler_def weak_sim_word weak_bisim_weak_sim by blast

lemma contrasim_weakest_bisim:
  assumes
    \<open>contrasim R\<close>
    \<open>\<And> p q a. p \<longmapsto> a q \<Longrightarrow> \<not> tau a\<close>
  shows
    \<open>bisimulation R\<close>
  using assms contrasim_taufree_symm symm_contrasim_is_weak_bisim weak_bisim_taufree_strong
  by blast

lemma symm_weak_sim_is_contrasim:
  assumes
    \<open>weak_simulation R\<close>
    \<open>\<And> p q. R p q \<Longrightarrow> R q p\<close>
  shows
    \<open>contrasim R\<close>
  using assms unfolding contrasim_simpler_def weak_sim_word by blast

subsection \<open>Intermediate Relation Mimicking Contrasim\<close>

definition F :: "(('s \<Rightarrow> ('s set) \<Rightarrow> bool)) \<Rightarrow> ('s \<Rightarrow> ('s set) \<Rightarrow> bool)" where 
\<open>F R p' Q' \<equiv> \<exists>p Q A. R p Q \<and> p \<Rightarrow>$A p' \<and> (\<forall>a \<in> set A. a \<noteq> \<tau>) \<and> Q' = (dsuccs_seq_rec (rev A) Q)\<close>

definition set_type :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> ('s set) \<Rightarrow> bool)" where 
\<open>set_type R p Q \<equiv> \<exists>q. R p q \<and> Q = {q}\<close>

lemma R_is_in_F_of_R : 
  assumes \<open>R p Q\<close>
  shows \<open>F R p Q\<close>
proof -
  have Q_cond: \<open>Q = dsuccs_seq_rec (rev []) Q\<close>  by simp 
  have p_cond: \<open>p \<Rightarrow>$[] p\<close> using steps.simps weak_step_seq.simps(1) by blast 
  thus \<open>F R p Q\<close> using Q_cond F_def \<open>R p Q\<close>
    by (metis bex_empty empty_set tau_tau)
qed

lemma F_of_C_guarantees_tau_succ:
  assumes 
    \<open>contrasim C\<close>
    \<open>F (set_type C) p Q\<close>
    \<open>p \<Rightarrow>^\<tau> p'\<close>
  shows \<open>\<exists>q'. q' \<in> (weak_tau_succs Q) \<and> F (set_type C) q' {p'}\<close>
proof -
  obtain p0 Q0 A q0
      where \<open>(set_type C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> \<open>Q0 = {q0}\<close> 
        and Q_def: \<open>Q = (dsuccs_seq_rec (rev A) Q0)\<close> 
      using F_def assms set_type_def by metis
  hence \<open>C p0 q0\<close> using set_type_def by auto 
  have \<open>p0 \<Rightarrow>$(A@[\<tau>]) p'\<close> using \<open>p0 \<Rightarrow>$A p\<close>  \<open>p \<Rightarrow>^\<tau>  p'\<close> rev_seq_step_concat by auto
  hence word: \<open>p0 \<Rightarrow>$A p'\<close> 
    by (metis \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> app_tau_taufree_list tau_def weak_step_over_tau)
  then obtain q' where \<open>q0 \<Rightarrow>$A q'\<close> \<open>C q' p'\<close> 
    using assms contrasim_def[of \<open>C\<close>] \<open>C p0 q0\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> by blast
  hence \<open>(set_type C) q' {p'}\<close> using set_type_def by auto
  hence inF: \<open>F (set_type C) q' {p'}\<close> using R_is_in_F_of_R  by auto
  have \<open>q' \<in> weak_tau_succs (dsuccs_seq_rec (rev A) Q0)\<close> 
    using \<open>Q0 = {q0}\<close> \<open>q0 \<Rightarrow>$ A q'\<close>
    by (simp add: word_reachable_implies_in_dsuccs) 
  hence \<open>q' \<in> weak_tau_succs Q\<close> using Q_def by simp 
  thus \<open>\<exists>q'. q' \<in> weak_tau_succs Q \<and> F (set_type C) q' {p'}\<close> using inF by auto
qed

lemma F_of_C_guarantees_action_succ :
 assumes 
    \<open>contrasim C\<close>
    \<open>F (set_type C) p Q\<close>
    \<open>p =\<rhd>a p'\<close>
    \<open>a \<noteq> \<tau>\<close>
  shows \<open>dsuccs a Q \<noteq> {}  \<and> F (set_type C) p' (dsuccs a Q)\<close>
proof -
  obtain p0 Q0 A q0
    where \<open>(set_type C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>Q0 = {q0}\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> 
      and Q_def: \<open>Q = (dsuccs_seq_rec (rev A) Q0)\<close> 
    using F_def assms set_type_def by metis
  then obtain CS where CS_def: \<open>contrasim CS \<and> CS p0 q0\<close> 
    using assms set_type_def by (metis singleton_inject) 
  have notau: \<open>\<forall>a \<in> set (A@[a]). a \<noteq> \<tau>\<close> 
    using \<open>a \<noteq> \<tau>\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> by auto
  have  \<open>p \<Rightarrow>a  p'\<close> using assms(3,4) steps.refl tau_def by auto 
  hence word: \<open>p0 \<Rightarrow>$(A@[a]) p'\<close>
    using \<open>p0 \<Rightarrow>$A p\<close>  rev_seq_step_concat
    by (meson steps.step steps_concat)
  then obtain q' where \<open>q0 \<Rightarrow>$(A@[a]) q' \<and> CS q' p'\<close> 
    using CS_def contrasim_def[of \<open>CS\<close>] notau
    by fastforce
  hence \<open>q' \<in> weak_tau_succs (dsuccs_seq_rec (rev (A@[a])) {q0})\<close> 
    using word_reachable_implies_in_dsuccs by blast
  then obtain q1 where in_dsuccs: \<open>q1 \<in> dsuccs_seq_rec (rev (A@[a])) {q0}\<close> \<open>q1 \<Rightarrow>^\<tau> q'\<close>
    using weak_tau_succs_def[of \<open>dsuccs_seq_rec (rev (A@[a])) {q0}\<close>] by auto
  hence \<open>q1 \<in> dsuccs_seq_rec (a#(rev A)) {q0}\<close> by auto
  hence \<open>q1 \<in> dsuccs a (dsuccs_seq_rec (rev A) {q0})\<close>  by auto
  hence notempty: \<open>q1 \<in> dsuccs a Q\<close> using Q_def \<open>Q0 = {q0}\<close> by auto
  have \<open>F (set_type C) p' (dsuccs a Q)\<close> 
    using in_dsuccs word F_def[of \<open>(set_type C)\<close>] \<open>(set_type C) p0 Q0\<close> 
      \<open>Q0 = {q0}\<close> Q_def notau simp_dsuccs_seq_rev by meson
  with notempty show ?thesis by auto
qed

end
end
