subsection \<open>Montanari Weak Relations\<close>

theory Montanari_Weak_Relations
imports
  Weak_Transition_Systems
  Weak_Relations_modified
  Montanari_Weak_Transition_Systems
begin

context lts_tau
begin

definition contrasim ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>contrasim R \<equiv> \<forall> p q p' A . (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<and> R p q \<and> (p \<Rightarrow>$ A p') \<longrightarrow>
    (\<exists> q'. (q \<Rightarrow>$ A q') \<and> R q' p')\<close>

definition ZR :: "(('s \<Rightarrow> ('s set) \<Rightarrow> bool)) \<Rightarrow> ('s \<Rightarrow> ('s set) \<Rightarrow> bool)" where 
\<open>ZR R p' Q' \<equiv> \<exists>p Q A. R p Q \<and> p \<Rightarrow>$A p' \<and> (\<forall>a \<in> set A. a \<noteq> \<tau>) \<and> Q' = (succs_seq_rec (rev A) Q)\<close>

definition set_type :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> ('s set) \<Rightarrow> bool)" where 
\<open>set_type R p Q \<equiv> \<exists>q. R p q \<and> Q = {q}\<close>

lemma R_is_in_ZR : 
  assumes \<open>R p Q\<close>
  shows \<open>ZR R p Q\<close>
proof -
  have Q_cond: \<open>Q = succs_seq_rec (rev []) Q\<close>  by simp 
  have p_cond: \<open>p \<Rightarrow>$[] p\<close> using steps.simps weak_step_seq.simps(1) by blast 
  thus \<open>ZR R p Q\<close> using Q_cond ZR_def \<open>R p Q\<close>
    by (metis bex_empty empty_set tau_tau)
qed

lemma ZR_C_guarantees_tau_succ : 
  assumes 
    \<open>contrasim C\<close>
    \<open>ZR (set_type C) p Q\<close>
    \<open>p \<Rightarrow>^\<tau> p'\<close>
  shows \<open>\<exists>q'. q' \<in> (succs \<tau> Q) \<and> ZR (set_type C) q' {p'}\<close>
proof -
  obtain p0 Q0 A q0
      where \<open>(set_type C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> \<open>Q0 = {q0}\<close> 
        and Q_def: \<open>Q = (succs_seq_rec (rev A) Q0)\<close> 
      using ZR_def assms set_type_def by metis
  hence \<open>C p0 q0\<close> using set_type_def by auto 
  have \<open>p0 \<Rightarrow>$(A@[\<tau>]) p'\<close> using \<open>p0 \<Rightarrow>$A p\<close>  \<open>p \<Rightarrow>^\<tau>  p'\<close> rev_seq_step_concat by auto
  hence word: \<open>p0 \<Rightarrow>$A p'\<close> 
    by (metis \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> app_tau_taufree_list tau_def weak_step_over_tau)
  then obtain q' where \<open>q0 \<Rightarrow>$A q'\<close> \<open>C q' p'\<close> 
    using assms contrasim_def[of \<open>C\<close>] \<open>C p0 q0\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau>\<close> by blast
  hence \<open>(set_type C) q' {p'}\<close> using set_type_def by auto
  hence inZR: \<open>ZR (set_type C) q' {p'}\<close> using R_is_in_ZR  by auto
  have \<open>q' \<in> succs \<tau> Q\<close>
  proof (cases \<open>A = []\<close>)
    case True
    hence \<open>q0 \<Rightarrow>^\<tau> q'\<close> using \<open>q0 \<Rightarrow>$A q'\<close> by auto
    hence \<open>q' \<in> succs \<tau> {q0}\<close> using succs_def by simp
    hence \<open>q' \<in> succs \<tau> Q0\<close>  using \<open>Q0 = {q0}\<close>  by simp       
    thus \<open>q' \<in> succs \<tau> Q\<close>  using Q_def by (simp add: True) 
  next
    case False
    hence \<open>q' \<in> succs_seq_rec (rev A) Q0\<close> 
      using \<open>Q0 = {q0}\<close> \<open>q0 \<Rightarrow>$ A q'\<close>
      by (simp add: word_reachable_implies_in_s) 
    hence \<open>q' \<in> Q\<close> using Q_def by auto
    hence \<open>\<exists>q \<in> Q. q \<Rightarrow>^\<tau> q'\<close> using \<open>q' \<in> Q\<close> steps.refl by auto
    thus \<open>q' \<in> succs \<tau> Q\<close>using succs_def by simp
  qed
  thus \<open>\<exists>q'. q' \<in> succs \<tau> Q \<and> ZR (set_type C) q' {p'}\<close> using inZR by auto
qed

lemma ZR_C_guarantees_action_succ :
 assumes 
    \<open>contrasim C\<close>
    \<open>ZR (set_type C) p Q\<close>
    \<open>p \<Rightarrow>a p'\<close>
    \<open>a \<noteq> \<tau>\<close>
  shows \<open>succs a Q \<noteq> {}  \<and> ZR (set_type C) p' (succs a Q)\<close>
proof -
  obtain p0 Q0 A q0
    where \<open>(set_type C) p0 Q0\<close> \<open>p0 \<Rightarrow>$A p\<close> \<open>Q0 = {q0}\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> and Q_def: \<open>Q = (succs_seq_rec (rev A) Q0)\<close> 
    using ZR_def assms set_type_def by metis
  then obtain CS where CS_def: \<open>contrasim CS \<and> CS p0 q0\<close> 
    using assms set_type_def by (metis singleton_inject) 
  have notau: \<open>\<forall>a \<in> set (A@[a]). a \<noteq> \<tau>\<close> 
    using \<open>a \<noteq> \<tau>\<close> \<open>\<forall>a \<in> set A. a \<noteq> \<tau> \<close> by auto
  have word: \<open>p0 \<Rightarrow>$(A@[a]) p'\<close>
    using \<open>p0 \<Rightarrow>$A p\<close>  \<open>p \<Rightarrow>a  p'\<close> rev_seq_step_concat
    by (meson steps.step steps_concat)
  then obtain q' where \<open>q0 \<Rightarrow>$(A@[a]) q' \<and> CS q' p'\<close> 
    using CS_def contrasim_def[of \<open>CS\<close>] notau
    by fastforce
  hence in_succs: \<open>q' \<in> (succs_seq_rec (rev (A@[a])) {q0})\<close> 
    using word_reachable_implies_in_s by blast
  hence \<open>q' \<in> (succs_seq_rec (a#(rev A)) {q0})\<close>
    by (metis rev_eq_Cons_iff rev_rev_ident)
  hence \<open>q' \<in> succs a (succs_seq_rec (rev A) {q0})\<close> by auto
  hence notempty: \<open>q' \<in> succs a Q\<close> using Q_def \<open>Q0 = {q0}\<close>  by auto
  have \<open>ZR (set_type C) p' (succs a Q)\<close> 
    using in_succs word ZR_def[of \<open>(set_type C)\<close>] \<open>(set_type C) p0 Q0\<close> 
      \<open>Q0 = {q0}\<close> Q_def simp_succs_seq_rev notau
    by meson
  with notempty show \<open>succs a Q \<noteq> {} \<and> ZR (set_type C) p' (succs a Q)\<close> by auto
qed

end
end
