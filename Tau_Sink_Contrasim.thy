section \<open>Tau Sink Proofs\<close>

theory Tau_Sink_Contrasim
imports
  Weak_Relations
  Contrasimulation
begin


(*----------start import from coupled_simulation.thy------------------*)
context lts_tau
begin

definition coupled_simulation ::
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>coupled_simulation R  \<equiv> \<forall> p q . 
    R p q \<longrightarrow> 
      (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
        (\<exists> q'. R p' q' \<and> q \<Rightarrow>^a q')) \<and>
      (\<exists> q'. q \<longmapsto>*tau q' \<and> R q' p)\<close>

abbreviation coupled_simulated_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>cs  _" [60, 60] 65)
  where \<open>coupled_simulated_by p q \<equiv> \<exists> R . coupled_simulation R \<and> R p q\<close>

lemma coupledsim_step_gla17:
  \<open>coupled_simulation (\<lambda> p1 q1 . q1 \<longmapsto>* tau p1)\<close>
  unfolding coupled_simulation_def
  using lts.steps.simps by metis

corollary coupledsim_step:
  assumes
    \<open>p \<longmapsto>* tau  q\<close>
  shows
    \<open>q \<sqsubseteq>cs p\<close>
  using assms coupledsim_step_gla17 by auto

lemma coupledsim_refl:
  \<open>p \<sqsubseteq>cs p\<close>
  using coupledsim_step steps.refl by auto

text \<open>If there is a sink every state can reach via tau steps, then weak simulation implies
  (and thus coincides with) coupled simulation.\<close>
lemma tau_sink_sim_coupledsim:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
    \<open>\<And> p . R sink p\<close>
    \<open>weak_simulation R\<close>
  shows
    \<open>coupled_simulation R\<close>
  unfolding coupled_simulation_def
proof safe
  show \<open> \<And>p q p' a. R p q \<Longrightarrow> p \<longmapsto>a  p' \<Longrightarrow> \<exists>q'. R p' q' \<and> q \<Rightarrow>^a  q'\<close>
    using assms(3) unfolding weak_simulation_def by blast
next
  fix p q
  assume \<open>R p q\<close>
  hence \<open>q \<longmapsto>* tau sink \<and> R sink p\<close>
    using assms(1,2) by blast
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p\<close> by blast
qed


(*----------end import from coupled_simulation.thy------------------*)

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
proof -
  have \<open>\<And>p q p' A. R p q \<and> p \<Rightarrow>$A  p' \<and>  (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<Longrightarrow> \<exists>q'. q \<Rightarrow>$A  q'\<close>
    using assms(3) unfolding trace_simulation_def by blast
  hence \<open>\<And>p q p' A. R p q \<and> p \<Rightarrow>$A  p' \<and>  (\<forall> a \<in> set(A). a \<noteq> \<tau>) \<Longrightarrow> q \<Rightarrow>$A  sink\<close> 
    using assms(1) by (meson lts_tau.tau_tau lts_tau.word_tau_concat)
  thus \<open>\<forall>p q p' A. (\<forall>a\<in>set A. a \<noteq> \<tau>) \<and> R p q \<and> p \<Rightarrow>$ A  p' \<longrightarrow> (\<exists>q'. q \<Rightarrow>$ A  q' \<and> R q' p')\<close>
    using assms(2) by fastforce
qed


(* nicer proof, but something's wrong with the proof state

lemma tau_sink_trace_sim_contrasim2:
  assumes
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
    \<open>\<And> p . R sink p\<close>
    \<open>trace_simulation R\<close>
  shows
    \<open>contrasim R\<close>
 unfolding contrasim_def
proof -
  fix p q p' A assume \<open>R p q \<and> p \<Rightarrow>$A  p' \<and>  (\<forall> a \<in> set(A). a \<noteq> \<tau>)\<close>
  hence \<open>\<exists>q'. q \<Rightarrow>$A  q'\<close>
    using assms(3) unfolding trace_simulation_def by blast
  hence \<open>q \<Rightarrow>$A  sink\<close> using assms(1) by (metis lts_tau.word_tau_concat tau_tau)
  thus \<open>\<exists>q'. q \<Rightarrow>$ A  q' \<and> R q' p'\<close> using assms(2) by auto
qed
*)


end 
end
