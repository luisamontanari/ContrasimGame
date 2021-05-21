subsection \<open>Transition Systems with Silent Steps\<close>

theory Weak_Transition_Systems
  imports Transition_Systems
begin                

locale lts_tau = lts trans for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> + fixes
  \<tau> :: \<open>'a\<close> begin
  
definition tau :: \<open>'a \<Rightarrow> bool\<close> where \<open>tau a \<equiv> (a = \<tau>)\<close>

lemma tau_tau[simp]: \<open>tau \<tau>\<close> unfolding tau_def by simp

abbreviation weak_step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<Rightarrow>_  _" [70, 70, 70] 80)
where
  \<open>(p \<Rightarrow>a q) \<equiv> (\<exists> pq1 pq2. 
    p \<longmapsto>* tau pq1 \<and>
    pq1 \<longmapsto>a   pq2 \<and>
    pq2 \<longmapsto>* tau q)\<close>

lemma step_weak_step:
  assumes \<open>p \<longmapsto>a p'\<close>
   shows   \<open>p \<Rightarrow>a p'\<close>
   using assms steps.refl by auto
    
abbreviation weak_step_tau :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<Rightarrow>^_  _" [70, 70, 70] 80)
where
  \<open>(p \<Rightarrow>^a q) \<equiv>
    (tau a \<longrightarrow> p \<longmapsto>* tau q) \<and>
    (\<not>tau a \<longrightarrow> p \<Rightarrow>a q)\<close>

abbreviation weak_step_delay :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ =\<rhd> _  _" [70, 70, 70] 80)
where
  \<open>(p =\<rhd>a q) \<equiv> 
    (tau a \<longrightarrow> p \<longmapsto>* tau q) \<and>
    (\<not>tau a \<longrightarrow>  (\<exists> pq.
      p \<longmapsto>* tau pq \<and>
      pq \<longmapsto>a   q))\<close>

lemma weak_step_delay_implies_weak_tau:
  assumes \<open>p =\<rhd>a p'\<close>
  shows \<open>p \<Rightarrow>^a p'\<close>
  using assms steps.refl[of p' tau] by blast

lemma weak_step_delay_left:
  assumes
    \<open>\<not> p0 \<longmapsto>a p1\<close>
    \<open>p0 =\<rhd>a p1\<close>
    \<open>\<not>tau a\<close>
  shows
    \<open>\<exists> p0' t. tau t \<and> p0 \<longmapsto>t p0' \<and> p0' =\<rhd>a p1\<close>
  using assms steps_left by metis

primrec weak_step_seq :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<Rightarrow>$ _  _" [70, 70, 70] 80)
  where
    \<open>weak_step_seq p0 [] p1 = p0 \<longmapsto>* tau p1\<close>
  | \<open>weak_step_seq p0 (a#A) p1 = (\<exists> p01 . p0 \<Rightarrow>^a p01 \<and> weak_step_seq p01 A p1)\<close>

lemma step_weak_step_tau:
  assumes \<open>p \<longmapsto>a p'\<close>
  shows   \<open>p \<Rightarrow>^a p'\<close>
  using step_weak_step[OF assms] steps_one_step[OF assms]
  by blast
    
lemma step_tau_refl:
  shows   \<open>p \<Rightarrow>^\<tau> p\<close>
  using steps.refl[of p tau]
  by simp
    
lemma weak_step_tau_weak_step[simp]:
  assumes \<open>p \<Rightarrow>^a p'\<close> \<open>\<not> tau a\<close>
  shows   \<open>p \<Rightarrow>a p'\<close>
  using assms by auto
  
lemma weak_steps:
  assumes
    \<open>p \<Rightarrow>a  p'\<close>
    \<open>\<And> a . tau a \<Longrightarrow> A a\<close>
    \<open>A a\<close>
  shows
    \<open>p \<longmapsto>* A  p'\<close>
proof -
  obtain pp pp' where pp:
    \<open>p \<longmapsto>* tau pp\<close> \<open>pp \<longmapsto>a  pp'\<close> \<open>pp' \<longmapsto>* tau p'\<close>
     using assms(1) by blast
  then have cascade:
    \<open>p \<longmapsto>* A pp\<close> \<open>pp \<longmapsto>* A  pp'\<close> \<open>pp' \<longmapsto>* A p'\<close>
     using steps_one_step steps_spec assms(2,3) by auto
  have \<open>p \<longmapsto>* A pp'\<close> using steps_concat[OF cascade(2) cascade(1)] .
  show ?thesis using steps_concat[OF cascade(3) `p \<longmapsto>* A  pp'`] .
qed
  
lemma weak_step_impl_weak_tau:
  assumes
    \<open>p \<Rightarrow>a p'\<close>
  shows
    \<open>p \<Rightarrow>^a p'\<close>
  using assms weak_steps[OF assms, of tau] by auto
  
lemma weak_impl_strong_step:
  assumes
    \<open>p \<Rightarrow>a  p''\<close>
  shows
    \<open>(\<exists> a' p' . tau a' \<and> p \<longmapsto>a'  p') \<or> (\<exists> p' . p \<longmapsto>a  p')\<close>
proof  -
  from assms obtain pq1 pq2 where pq12:
    \<open>p \<longmapsto>* tau pq1\<close>
     \<open>pq1 \<longmapsto>a   pq2\<close>
     \<open>pq2 \<longmapsto>* tau p''\<close> by blast
  show ?thesis
  proof (cases \<open>p = pq1\<close>)
    case True
    then show ?thesis using pq12 by blast
  next
    case False
    then show ?thesis using pq12 steps_left[of p pq1 tau] by blast
  qed
qed
  
lemma weak_step_extend:
  assumes 
    \<open>p1 \<longmapsto>* tau p2\<close>
    \<open>p2 \<Rightarrow>^a p3\<close>
    \<open>p3 \<longmapsto>* tau p4\<close>
  shows
    \<open>p1 \<Rightarrow>^a p4\<close>
  using assms steps_concat by blast
    
lemma weak_step_tau_tau:
  assumes 
    \<open>p1 \<longmapsto>* tau p2\<close>
    \<open>tau a\<close>
  shows
    \<open>p1 \<Rightarrow>^a p2\<close>
  using assms by blast

lemma weak_single_step[iff]: 
  \<open>p \<Rightarrow>$ [a] p' \<longleftrightarrow> p \<Rightarrow>^a  p'\<close>
   using steps.refl[of p' tau]
  by (meson steps_concat weak_step_seq.simps(1) weak_step_seq.simps(2))

abbreviation weak_enabled :: \<open>'s \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>weak_enabled p a \<equiv>
    \<exists> pq1 pq2. p \<longmapsto>* tau pq1 \<and> pq1 \<longmapsto>a pq2\<close>

lemma weak_enabled_step:
  shows \<open>weak_enabled p a = (\<exists> p'. p \<Rightarrow>a p')\<close>
  using step_weak_step steps_concat by blast

abbreviation tau_max :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>tau_max p \<equiv>  (\<forall>p'. p \<longmapsto>* tau p' \<longrightarrow> p = p')\<close>

lemma tau_max_deadlock:
  fixes q
  assumes
    \<open>\<And> r1 r2. r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> \<comment>\<open>contracted cycles (anti-symmetry)\<close>
    \<open>finite {q'. q \<longmapsto>* tau q'}\<close>
  shows
    \<open>\<exists> q' . q \<longmapsto>* tau q' \<and> tau_max q'\<close>
  using step_max_deadlock assms by blast

abbreviation stable_state :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>stable_state p \<equiv> \<nexists> p' . step_pred p tau p'\<close>
   
lemma stable_tauclosure_only_loop:
  assumes
    \<open>stable_state p\<close>
  shows
    \<open>tau_max p\<close>
  using assms  steps_left by blast

coinductive divergent_state :: \<open>'s \<Rightarrow> bool\<close> where
  omega: \<open>divergent_state p' \<Longrightarrow> tau t \<Longrightarrow>  p \<longmapsto>t p'\<Longrightarrow> divergent_state p\<close>
    
lemma ex_divergent:
  assumes \<open>p \<longmapsto>a p\<close> \<open>tau a\<close>
  shows \<open>divergent_state p\<close>
  using assms 
proof (coinduct)
  case (divergent_state p)
  then show ?case using assms by auto
qed
  
lemma ex_not_divergent:
  assumes \<open>\<forall>a q. p \<longmapsto>a q \<longrightarrow> \<not> tau a\<close> \<open>divergent_state p\<close>
  shows \<open>False\<close> using assms(2)
proof (cases rule:divergent_state.cases)
  case (omega p' t)
  thus ?thesis using assms(1) by auto
qed

lemma perpetual_instability_divergence:
  assumes
    \<open>\<forall> p' . p \<longmapsto>* tau p' \<longrightarrow> \<not> stable_state p'\<close>
  shows
    \<open>divergent_state p\<close>
  using assms
proof (coinduct rule: divergent_state.coinduct)
  case (divergent_state p)
  then obtain t p' where \<open>tau t\<close> \<open>p \<longmapsto>t  p'\<close> using steps.refl by blast
  then moreover have \<open>\<forall>p''. p' \<longmapsto>* tau  p'' \<longrightarrow> \<not> stable_state p''\<close>
     using divergent_state step_weak_step_tau steps_concat by blast
  ultimately show ?case by blast 
qed

corollary non_divergence_implies_eventual_stability:
  assumes
    \<open>\<not> divergent_state p\<close>
  shows
    \<open>\<exists> p' . p \<longmapsto>* tau p' \<and> stable_state p'\<close>
  using assms perpetual_instability_divergence by blast

end \<comment>\<open>context @{locale lts_tau}\<close>

subsection \<open>Finite Transition Systems with Silent Steps\<close>

locale lts_tau_finite = lts_tau trans \<tau> for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> +
assumes 
  finite_state_set: \<open>finite (top::'s set)\<close>
begin

lemma finite_state_rel: \<open>finite (top::('s rel))\<close>
  using finite_state_set
  by (simp add: finite_prod)

end

end