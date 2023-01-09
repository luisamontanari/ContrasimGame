section \<open>Tau Sink Proofs\<close>

theory Tau_Sink_Contrasim
imports
  Coupled_Simulation
begin

context lts_tau
begin

definition trace_simulation ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>trace_simulation R  \<equiv> \<forall> p q p' A . (\<forall> a \<in> set(A). a \<noteq> \<tau>) 
  \<and> R p q \<and> p \<Rightarrow>$ A p' \<longrightarrow> (\<exists> q'. q \<Rightarrow>$ A q')\<close>

lemma contrasim_implies_trace_sim:
  assumes \<open>contrasim R\<close>
  shows \<open>trace_simulation R\<close>
by (metis assms contrasim_simpler_def trace_simulation_def) 

definition tau_sink ::
  \<open>'s \<Rightarrow> bool\<close>
where
  \<open>tau_sink p  \<equiv> \<forall>a. \<nexists>p'. p \<longmapsto>a p'\<close>

lemma tau_sink_has_no_weak_transitions: 
  assumes 
    \<open>tau_sink sink\<close>
  shows \<open>\<nexists>s'. s' \<noteq> sink \<and> sink \<Rightarrow>^a s'\<close>
proof - 
  have  \<open>\<nexists>s' . sink \<longmapsto>a s'\<close> using tau_sink_def assms(1) by auto
  show ?thesis by (metis assms lts_tau.tau_sink_def stable_tauclosure_only_loop) 
qed

lemma tau_sink_has_no_word_transitions: 
  assumes 
    \<open>tau_sink sink\<close>
    \<open>A \<noteq> []\<close>
    \<open>\<forall> a \<in> set(A). a \<noteq> \<tau>\<close>
  shows \<open>\<nexists>s'. sink \<Rightarrow>$A s'\<close>
proof - 
  obtain a where \<open>\<exists>B. A = a#B\<close> using assms(2) list.exhaust_sel by auto
  hence \<open>\<nexists>s' . sink \<Rightarrow>^a s'\<close>
    by (metis assms(1, 3) list.set_intros(1) lts_tau.tau_def tau_sink_def tau_sink_has_no_weak_transitions)
  thus ?thesis using \<open>\<exists>B. A = a#B\<close> by fastforce
qed

lemma tau_sink_contrasimulates_all_states:
fixes A :: " 'a list"
  assumes 
    \<open>tau_sink sink\<close>
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows 
    \<open>\<forall> p. sink \<sqsubseteq>c p\<close>
proof (cases A)
  case Nil
  hence empty_word: \<open>sink \<Rightarrow>$A sink\<close> by (simp add: steps.refl)
  have \<open>\<forall>p. p \<Rightarrow>$A sink\<close> using assms(2) Nil by auto
  have \<open>sink \<sqsubseteq>c sink\<close> using contrasim_tau_step empty_word Nil by auto 
  show ?thesis using assms(2) contrasim_tau_step by auto 
next
  case Cons
  hence \<open>\<nexists>s'. (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<and> sink \<Rightarrow>$A s'\<close>
    using assms(1) tau_sink_has_no_word_transitions by fastforce
  show ?thesis using assms(2) contrasim_tau_step by auto 
qed

lemma tau_sink_coupled_simulates_all_states:
  assumes 
    \<open>tau_sink sink\<close>
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows 
    \<open>sink \<sqsubseteq>cs p\<close> 
  by (simp add: assms(1, 2) coupledsim_refl tau_sink_def coupledsim_step)  

lemma tau_sink_trace_sim_contrasim:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
    \<open>\<And> p . R sink p\<close>
    \<open>trace_simulation R\<close>
  shows
    \<open>contrasim R\<close>
 unfolding contrasim_def
proof clarify
  fix p q p' A
  assume \<open>R p q\<close> \<open>p \<Rightarrow>$A  p'\<close> \<open>\<forall> a \<in> set(A). a \<noteq> \<tau>\<close>
  hence \<open>\<exists>q'. q \<Rightarrow>$A  q'\<close>
    using assms(3) unfolding trace_simulation_def by blast
  hence \<open>q \<Rightarrow>$A  sink\<close>
    using assms(1) tau_tau word_tau_concat by blast
  thus \<open>\<exists>q'. q \<Rightarrow>$ A  q' \<and> R q' p'\<close>
    using assms(2) by auto
qed

end 
end
