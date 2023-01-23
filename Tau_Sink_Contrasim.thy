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

abbreviation weakly_trace_included_by :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<sqsubseteq>T  _" [60, 60] 65)
  where \<open>weakly_trace_included_by p q \<equiv> \<exists> R . trace_simulation R \<and> R p q\<close>

lemma contrasim_implies_trace_sim:
  assumes \<open>contrasim R\<close>
  shows \<open>trace_simulation R\<close>
by (metis assms contrasim_simpler_def trace_simulation_def) 

definition tau_sink ::
  \<open>'s \<Rightarrow> bool\<close>
where
  \<open>tau_sink p  \<equiv> \<forall>a. a = \<tau> \<or> (\<nexists>p'. p \<Rightarrow>a p')\<close>

lemma tau_sink_has_no_weak_act_transitions: 
  assumes 
    \<open>tau_sink sink\<close>
  shows \<open>\<nexists>s'. s' \<noteq> sink \<and> sink \<Rightarrow>^a s' \<and> a \<noteq> \<tau>\<close>
proof - 
  have  \<open>\<nexists>s' . sink \<Rightarrow>a s' \<and> a \<noteq> \<tau>\<close> using tau_sink_def assms(1) by auto
  thus ?thesis using tau_def by blast
qed

lemma tau_sink_has_no_word_transitions: 
  assumes 
    \<open>tau_sink sink\<close>
    \<open>A \<noteq> []\<close>
    \<open>\<forall> a \<in> set(A). a \<noteq> \<tau>\<close>
  shows \<open>\<nexists>s'. sink \<Rightarrow>$A s'\<close>
proof - 
  obtain a where \<open>\<exists>B. A = a#B\<close> using assms(2) list.exhaust_sel by auto
  hence \<open>\<nexists>s' . sink \<Rightarrow>^a s'\<close> by (metis assms(1,3) list.set_intros(1) lts_tau.tau_def tau_sink_def)
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

lemma tau_sink_trace_includes_all_states:
  assumes 
    \<open>tau_sink sink\<close>
    \<open>\<And> p . (p \<longmapsto>* tau sink)\<close>
  shows 
    \<open>sink \<sqsubseteq>T p\<close>
  by (metis assms(2) contrasim_tau_step lts_tau.contrasim_implies_trace_sim) 


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

lemma trace_preorder_sink_invariant:
  fixes
    step sink R
  defines
    \<open>step2 \<equiv> \<lambda> p1 a p2 . (p1 \<noteq> sink \<and> a =  \<tau> \<and> p2 = sink) \<or> step p1 a p2\<close>
  assumes
    \<open>\<And> a p . \<not> step sink a p \<and> \<not> step p a sink\<close>
  shows \<open>lts_tau.weakly_trace_included_by step2 \<tau> p q = lts_tau.weakly_trace_included_by step \<tau> p q\<close>
proof - 
  let ?tau = \<open>(lts_tau.tau \<tau>)\<close>
  let ?steps = \<open>lts.steps\<close>
  {
    fix A
    have \<open>\<forall>p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> lts_tau.weak_step_seq step2 \<tau> p A p' 
    \<longrightarrow> (\<exists>p''. lts_tau.weak_step_seq step \<tau> p A p''
    \<and> lts_tau.weak_step_tau step2 \<tau> p'' \<tau> p')\<close>
    proof(clarify, induct A rule: rev_induct)
      case Nil
      hence \<open>lts_tau.weak_step_tau step \<tau> p \<tau> p\<close>
        by (simp add: lts_tau.step_tau_refl) 
      thus ?case
        by (metis Nil.prems(2) lts_tau.tau_tau lts_tau.weak_step_seq.simps(1)) 
    next
      case (snoc a A)
      hence not_in_set: \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> by force 
      then obtain p01 where 
        \<open>lts_tau.weak_step_seq step2 \<tau> p A p01\<close> and
        p01_def2: \<open>lts_tau.weak_step_tau step2 \<tau> p01 a p'\<close>
        using snoc by (metis lts_tau.rev_seq_split) 
      then obtain p02 where p02_def: 
        \<open>lts_tau.weak_step_seq step \<tau> p A p02\<close> 
        \<open>lts_tau.weak_step_tau step2 \<tau> p02 \<tau> p01\<close>
        using snoc.hyps[of p p01] snoc.prems(1) not_in_set by auto
      hence \<open>lts_tau.weak_step_tau step2 \<tau> p02 a p'\<close> using p01_def2 lts_tau.step_tau_concat tau_tau
        by metis
      then obtain p03 p04 where 
        tau1: \<open>lts_tau.weak_step_tau step2 \<tau> p02 \<tau> p03\<close> and
        a_step2: \<open>lts.step step2 p03 a p04\<close> and
        tau2: \<open>lts_tau.weak_step_tau step2 \<tau> p04 \<tau> p'\<close>
        using snoc.prems(1) tau_def by auto 
      hence \<open>p04 \<noteq> sink\<close> using assms snoc.prems(1) by force
      hence a_step: \<open>lts.step step p03 a p04\<close> using a_step2 assms by auto
      have notsinkp03: \<open>p03 \<noteq> sink\<close> using a_step2 assms snoc.prems(1) by force
      have \<open>lts.steps step2 p02 (lts_tau.tau \<tau>) p03\<close> using tau1 by simp 

      hence \<open>?steps step p02 tau p03\<close> using notsinkp03
      proof (induct rule: lts.steps.induct[OF `?steps step2 p02 ?tau  p03`])
        case (1 p A)
        thus ?case by (simp add: lts.refl)
      next
        case (2 p A q1 a q)
        hence \<open>q1 \<noteq> sink\<close> using assms(2) step2_def by blast 
        thus ?case using 2 lts.step step2_def by metis
      qed 
      hence \<open>lts_tau.weak_step_tau step \<tau> p02 \<tau> p03\<close> by simp 
      hence \<open>lts_tau.weak_step_tau step \<tau> p02 a p04\<close> using a_step
        by (metis lts.step lts_tau.step_tau_refl tau_tau) 
      hence \<open>lts_tau.weak_step_seq step \<tau> p (A@[a]) p04\<close>
        using lts_tau.rev_seq_step_concat p02_def(1) by fastforce 
      thus ?case using tau2 by auto
    qed
  }
  hence step2_to_step: \<open>\<forall>A p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> lts_tau.weak_step_seq step2 \<tau> p A p' 
    \<longrightarrow> (\<exists>p''. lts_tau.weak_step_seq step \<tau> p A p'')\<close>
    by fastforce

  have step_to_step2:  \<open>\<forall>A p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> lts_tau.weak_step_seq step \<tau> p A p' 
    \<longrightarrow> lts_tau.weak_step_seq step2 \<tau> p A p'\<close>
  proof
    fix A
    show \<open>\<forall>p p'. (\<forall> a \<in> set(A). a \<noteq> \<tau>)
    \<and> lts_tau.weak_step_seq step \<tau> p A p' 
    \<longrightarrow> lts_tau.weak_step_seq step2 \<tau> p A p'\<close>
    proof(clarify, induct A rule: list.induct)
      case Nil
      assume \<open>lts_tau.weak_step_seq step \<tau> p [] p'\<close>
      hence tau_step: \<open>lts_tau.weak_step_tau step \<tau> p \<tau> p'\<close>
        by (simp add: lts_tau.weak_step_seq.simps(1))
      hence \<open>lts_tau.weak_step_tau step2 \<tau> p \<tau> p'\<close>
        using lts_impl_steps step2_def by force 
      thus ?case by (simp add: lts_tau.weak_step_seq.simps(1)) 
    next
      case (Cons x xs)
      then obtain p1 where p1_def: \<open>lts_tau.weak_step_tau step \<tau> p x p1\<close> 
      \<open>lts_tau.weak_step_seq step \<tau> p1 xs p'\<close>
        by (metis (mono_tags, lifting) lts_tau.weak_step_seq.simps(2))
      hence IH: \<open>lts_tau.weak_step_seq step2 \<tau> p1 xs p'\<close> using Cons by auto
      then obtain p01 p02 where \<open>lts_tau.weak_step_tau step \<tau> p \<tau> p01\<close> and
        strong: \<open>lts.step step p01 x p02\<close> and
        p02_weak: \<open>lts_tau.weak_step_tau step \<tau> p02 \<tau> p1\<close>
        using Cons.prems(1) p1_def tau_def by auto
      hence tau1: \<open>lts_tau.weak_step_tau step2 \<tau> p \<tau> p01\<close> 
        using lts_impl_steps step2_def by force 
      have \<open>lts_tau.weak_step_tau step2 \<tau> p02 \<tau> p1\<close> 
        using p02_weak lts_impl_steps step2_def by force 
      hence \<open>lts_tau.weak_step_tau step2 \<tau> p x p1\<close> 
        using tau1 strong step2_def Cons.prems(1) tau_def by auto 
      thus \<open>lts_tau.weak_step_seq step2 \<tau> p (x#xs) p'\<close> 
        using IH lts_tau.weak_step_seq_def[of step2 \<tau>] by auto
    qed
  qed

  show ?thesis
  proof (rule)
    assume \<open>\<exists>R. lts_tau.trace_simulation step2 \<tau> R \<and> R p q\<close>
    then obtain R where weak_sim_R: \<open>lts_tau.trace_simulation step2 \<tau> R\<close>
      and Rpq: \<open>R p q\<close>
      by blast
    have \<open>lts_tau.trace_simulation step \<tau> R\<close>
      unfolding lts_tau.trace_simulation_def
    proof clarify
      fix p q p' A
      assume subassms: 
        \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
        \<open>R p q\<close>
        \<open>lts_tau.weak_step_seq step \<tau> p A p'\<close>
      hence \<open>(\<forall>a\<in>set A. a \<noteq> \<tau>) \<and>
       lts_tau.weak_step_seq step2 \<tau> p A p' \<longrightarrow>
       (\<exists>q'. lts_tau.weak_step_seq step2 \<tau> q A q')\<close> 
        using weak_sim_R 
        unfolding lts_tau.trace_simulation_def by simp
      hence \<open>(\<forall>a\<in>set A. a \<noteq> \<tau>) \<and>
       lts_tau.weak_step_seq step \<tau> p A p' \<longrightarrow>
       (\<exists>q'. lts_tau.weak_step_seq step \<tau> q A q')\<close>
        using step2_to_step step_to_step2
        by auto
      thus "\<exists>q'. lts_tau.weak_step_seq step \<tau> q A q'"
        by (simp add: subassms)
    qed
    thus \<open>\<exists>R. lts_tau.trace_simulation step \<tau> R \<and> R p q\<close>
      using Rpq by auto
  next 
    assume \<open>\<exists>R. lts_tau.trace_simulation step \<tau> R \<and> R p q\<close>
    then obtain R where weak_sim_R: \<open>lts_tau.trace_simulation step \<tau> R\<close>
      and Rpq: \<open>R p q\<close>
      by blast
    have \<open>lts_tau.trace_simulation step2 \<tau> R\<close> 
      unfolding lts_tau.trace_simulation_def
    proof clarify
      fix p q p' A
      assume subassms: 
        \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
        \<open>R p q\<close>
        \<open>lts_tau.weak_step_seq step2 \<tau> p A p'\<close>
      thus \<open>\<exists>q'. lts_tau.weak_step_seq step2 \<tau> q A q'\<close>
        using step2_to_step step_to_step2
        by (metis (full_types) lts_tau.trace_simulation_def weak_sim_R)
    qed
    thus \<open>\<exists>R. lts_tau.trace_simulation step2 \<tau> R \<and> R p q\<close> using Rpq by auto
  qed
qed

end 
end
