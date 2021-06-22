subsection \<open>Contrasimulation\<close>

theory Contrasimulation
imports
  Weak_Relations
begin

context lts_tau
begin

definition contrasim ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>contrasim R \<equiv> \<forall> p q p' A . (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<and> R p q \<and> (p \<Rightarrow>$ A p') \<longrightarrow>
    (\<exists> q'. (q \<Rightarrow>$ A q') \<and> R q' p')\<close>

definition ZR :: "(('s \<Rightarrow> ('s set) \<Rightarrow> bool)) \<Rightarrow> ('s \<Rightarrow> ('s set) \<Rightarrow> bool)" where 
\<open>ZR R p' Q' \<equiv> \<exists>p Q A. R p Q \<and> p \<Rightarrow>$A p' \<and> (\<forall>a \<in> set A. a \<noteq> \<tau>) \<and> Q' = (dsuccs_seq_rec (rev A) Q)\<close>

definition set_type :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> ('s set) \<Rightarrow> bool)" where 
\<open>set_type R p Q \<equiv> \<exists>q. R p q \<and> Q = {q}\<close>

lemma R_is_in_ZR : 
  assumes \<open>R p Q\<close>
  shows \<open>ZR R p Q\<close>
proof -
  have Q_cond: \<open>Q = dsuccs_seq_rec (rev []) Q\<close>  by simp 
  have p_cond: \<open>p \<Rightarrow>$[] p\<close> using steps.simps weak_step_seq.simps(1) by blast 
  thus \<open>ZR R p Q\<close> using Q_cond ZR_def \<open>R p Q\<close>
    by (metis bex_empty empty_set tau_tau)
qed

lemma ZR_C_guarantees_tau_succ : 
  assumes 
    \<open>contrasim C\<close>
    \<open>ZR (set_type C) p Q\<close>
    \<open>p \<Rightarrow>^\<tau> p'\<close>
  shows \<open>\<exists>q'. q' \<in> (weak_tau_succs Q) \<and> ZR (set_type C) q' {p'}\<close>
proof -
  obtain p0 Q0 A q0
      where \<open>(set_type C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> \<open>Q0 = {q0}\<close> 
        and Q_def: \<open>Q = (dsuccs_seq_rec (rev A) Q0)\<close> 
      using ZR_def assms set_type_def by metis
  hence \<open>C p0 q0\<close> using set_type_def by auto 
  have \<open>p0 \<Rightarrow>$(A@[\<tau>]) p'\<close> using \<open>p0 \<Rightarrow>$A p\<close>  \<open>p \<Rightarrow>^\<tau>  p'\<close> rev_seq_step_concat by auto
  hence word: \<open>p0 \<Rightarrow>$A p'\<close> 
    by (metis \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> app_tau_taufree_list tau_def weak_step_over_tau)
  then obtain q' where \<open>q0 \<Rightarrow>$A q'\<close> \<open>C q' p'\<close> 
    using assms contrasim_def[of \<open>C\<close>] \<open>C p0 q0\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> by blast
  hence \<open>(set_type C) q' {p'}\<close> using set_type_def by auto
  hence inZR: \<open>ZR (set_type C) q' {p'}\<close> using R_is_in_ZR  by auto
  have \<open>q' \<in> weak_tau_succs (dsuccs_seq_rec (rev A) Q0)\<close> 
    using \<open>Q0 = {q0}\<close> \<open>q0 \<Rightarrow>$ A q'\<close>
    by (simp add: word_reachable_implies_in_dsuccs) 
  hence \<open>q' \<in> weak_tau_succs Q\<close> using Q_def by simp 
  thus \<open>\<exists>q'. q' \<in> weak_tau_succs Q \<and> ZR (set_type C) q' {p'}\<close> using inZR by auto
qed

lemma ZR_C_guarantees_action_succ :
 assumes 
    \<open>contrasim C\<close>
    \<open>ZR (set_type C) p Q\<close>
    \<open>p =\<rhd>a p'\<close>
    \<open>a \<noteq> \<tau>\<close>
  shows \<open>dsuccs a Q \<noteq> {}  \<and> ZR (set_type C) p' (dsuccs a Q)\<close>
proof -
  obtain p0 Q0 A q0
    where \<open>(set_type C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>Q0 = {q0}\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> 
      and Q_def: \<open>Q = (dsuccs_seq_rec (rev A) Q0)\<close> 
    using ZR_def assms set_type_def by metis
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
  have \<open>ZR (set_type C) p' (dsuccs a Q)\<close> 
    using in_dsuccs word ZR_def[of \<open>(set_type C)\<close>] \<open>(set_type C) p0 Q0\<close> 
      \<open>Q0 = {q0}\<close> Q_def notau simp_dsuccs_seq_rev by meson
  with notempty show ?thesis by auto
qed

end
end