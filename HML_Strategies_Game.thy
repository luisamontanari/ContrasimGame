theory HML_Strategies_Game
  imports
    Contrasim_Set_Game
    HM_Logic_Infinitary
begin

locale c_game_with_attacker_strategy  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> +
fixes
  strat :: \<open>('s, 'a) c_set_game_node posstrategy\<close> and
  attacker_winning_region :: \<open>('s, 'a) c_set_game_node set\<close> and
  attacker_order
defines
  \<open>attacker_order \<equiv> {(g', g). c_set_game_moves g g' \<and>
      g \<in> attacker_winning_region \<and> g' \<in> attacker_winning_region \<and>
      (player1_position g \<longrightarrow> g' = strat g)}\<^sup>+\<close>
assumes
  finite_win:
    \<open>wf attacker_order\<close> and
  strat_stays_winning:
    \<open>g \<in> attacker_winning_region \<Longrightarrow> player1_position g \<Longrightarrow>
      strat g \<in> attacker_winning_region \<and> c_set_game_moves g (strat g)\<close> and
  defender_keeps_losing:
    \<open>g \<in> attacker_winning_region \<Longrightarrow> c_set_game_defender_node g \<Longrightarrow> c_set_game_moves g g' \<Longrightarrow>
      g' \<in> attacker_winning_region\<close>
begin

text \<open>This construction of attacker formulas from a game only works if \<open>strat\<close> is a (non-cyclic)
  attacker strategy. (If it's winning and sound, the constructed formula should be distinguishing.)\<close>

function attack_formula :: \<open>('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula\<close> where
  \<open>attack_formula (AttackerNode p Q) =
    (if (AttackerNode p Q) \<in> attacker_winning_region then attack_formula (strat (AttackerNode p Q)) else HML_true)\<close>
| \<open>attack_formula (DefenderSimNode a p Q) =
    (if (DefenderSimNode a p Q) \<in> attacker_winning_region then \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p (dsuccs a Q))) else HML_true)\<close>
| \<open>attack_formula (DefenderSwapNode p Q) =
    (if Q = {} \<or> DefenderSwapNode p Q \<notin> attacker_winning_region then HML_true else
    (HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then (attack_formula (AttackerNode q {p})) else HML_true )))\<close>
  using c_set_game_defender_node.cases
  by (auto, blast)

termination attack_formula
  using finite_win
proof (standard, safe)
  fix p Q
  assume \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
  thus \<open>(strat (AttackerNode p Q), AttackerNode p Q) \<in> attacker_order\<close>
    unfolding attacker_order_def
    using strat_stays_winning
    by auto
next
  fix a p Q
  assume attacker_wins: \<open>DefenderSimNode a p Q \<in> attacker_winning_region\<close>
  hence \<open>AttackerNode p (dsuccs a Q) \<in> attacker_winning_region\<close>
    using defender_keeps_losing simulation_answer by force
  with attacker_wins show \<open>(AttackerNode p (dsuccs a Q), DefenderSimNode a p Q) \<in> attacker_order\<close>
    unfolding attacker_order_def
    by (simp add: r_into_trancl')
next
  fix p Q q' q
  assume case_assms:
    \<open>q' \<in> weak_tau_succs Q\<close>
    \<open>(AttackerNode q' {p}, DefenderSwapNode p Q) \<notin> attacker_order\<close>
    \<open>DefenderSwapNode p Q \<in> attacker_winning_region\<close>
    \<open>q \<in> Q\<close>
  hence \<open>AttackerNode q' {p} \<notin> attacker_winning_region\<close>
    unfolding attacker_order_def by auto
  moreover from case_assms have \<open>AttackerNode q' {p} \<in> attacker_winning_region\<close>
    using swap_answer defender_keeps_losing by force
  ultimately show \<open>q \<in> {}\<close> by blast
qed

lemma attacker_defender_switch:
  assumes
    \<open>(AttackerNode p Q) \<in> attacker_winning_region\<close>
  shows
    \<open>(\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or>(\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p' )\<close>
  using strat_stays_winning[OF assms] by (cases \<open>strat (AttackerNode p Q)\<close>, auto)

lemma attack_options: 
  assumes
    \<open>(AttackerNode p Q) \<in> attacker_winning_region\<close>
  shows
    \<open>(\<exists>a p'. p =\<rhd>a p' \<and> \<not>tau a \<and> strat (AttackerNode p Q) = (DefenderSimNode a p' Q) \<and>
      attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p' (dsuccs a Q))))
    \<or> (\<exists>p'. p \<longmapsto>* tau p' \<and> strat (AttackerNode p Q) = (DefenderSwapNode p' Q) \<and>
      attack_formula (AttackerNode p Q) =
      (HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then (attack_formula (AttackerNode q {p'})) else HML_true )))
    \<or> (Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true)\<close>
proof -
  from assms have \<open>attack_formula (AttackerNode p Q) = attack_formula (strat (AttackerNode p Q))\<close> by simp
  moreover from attacker_defender_switch assms have
    \<open>(\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or>(\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p')\<close> by blast
  ultimately have 
    \<open>(\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and>
      (attack_formula (AttackerNode p Q)) = attack_formula (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or>(\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and>
      (attack_formula (AttackerNode p Q)) = attack_formula (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p')\<close>
    by metis
  moreover from assms have \<open>strat (AttackerNode p Q) \<in> attacker_winning_region\<close>
    by (simp add: strat_stays_winning)
  ultimately show ?thesis using assms empty_iff 
    by fastforce
qed

lemma distinction_soundness:
  fixes p Q p0 Q0
  defines
    \<open>pQ == AttackerNode p Q\<close>
  defines
    \<open>\<phi> == attack_formula pQ\<close>
  assumes
    \<open>pQ \<in> attacker_winning_region\<close>
  shows
    \<open>p \<Turnstile> \<phi> \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> \<phi>)\<close>
  using finite_win assms
proof (induct arbitrary: p Q \<phi>)
  case (less p Q)
  from attack_options[OF this(2)] show ?case
  proof
    assume \<open>\<exists>a p'. p =\<rhd> a  p' \<and> \<not> tau a \<and> strat (AttackerNode p Q) = DefenderSimNode a p' Q \<and>
      attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
    then obtain a p' where case_assms:
      \<open>p =\<rhd> a  p' \<and> \<not> tau a\<close>
      \<open>strat (AttackerNode p Q) = DefenderSimNode a p' Q\<close>
      \<open>attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close> by blast
    hence moves:
      \<open>c_set_game_moves (AttackerNode p Q) (DefenderSimNode a p' Q)\<close>
      \<open>c_set_game_moves (DefenderSimNode a p' Q) (AttackerNode p' (dsuccs a Q))\<close> by auto
    with case_assms less(2) defender_keeps_losing strat_stays_winning have all_winning:
      \<open>(AttackerNode p' (dsuccs a Q)) \<in> attacker_winning_region\<close>
      \<open>(DefenderSimNode a p' Q) \<in> attacker_winning_region\<close>
        by (metis c_set_game_defender_node.simps(2), force)
    with case_assms moves less(2) have
      \<open>(AttackerNode p' (dsuccs a Q), DefenderSimNode a p' Q) \<in> attacker_order\<close>
      \<open>(DefenderSimNode a p' Q, AttackerNode p Q) \<in> attacker_order\<close>
      unfolding attacker_order_def by (simp add: r_into_trancl')+
    hence \<open>(AttackerNode p' (dsuccs a Q), AttackerNode p Q) \<in> attacker_order\<close>
      unfolding attacker_order_def by auto
    with less.hyps all_winning(1) have
      \<open>p' \<Turnstile> attack_formula (AttackerNode p' (dsuccs a Q)) \<and> (\<forall>q\<in>(dsuccs a Q). \<not> q \<Turnstile> attack_formula (AttackerNode p' (dsuccs a Q)))\<close>
      by blast
    with case_assms have
      \<open>p \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
      \<open>\<forall>q\<in>Q. \<not>q \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
      unfolding dsuccs_def by (auto, blast+)
    thus ?case unfolding case_assms by blast
  next
    assume \<open>(\<exists>p'. p \<longmapsto>* tau  p' \<and> strat (AttackerNode p Q) = DefenderSwapNode p' Q \<and>
        attack_formula (AttackerNode p Q) = HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then attack_formula (AttackerNode q {p'}) else HML_true)) \<or>
      Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true\<close>
    thus ?case
    proof
      assume \<open>\<exists>p'. p \<longmapsto>* tau  p' \<and> strat (AttackerNode p Q) = DefenderSwapNode p' Q \<and>
        attack_formula (AttackerNode p Q) = HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then attack_formula (AttackerNode q {p'}) else HML_true)\<close>
      then obtain p' where case_assms:
        \<open>p \<longmapsto>* tau  p'\<close>
        \<open>strat (AttackerNode p Q) = DefenderSwapNode p' Q\<close>
        \<open>attack_formula (AttackerNode p Q) = HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then attack_formula (AttackerNode q {p'}) else HML_true)\<close>
        by blast
      from case_assms have moves:
        \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p' Q)\<close>
        \<open>\<forall>q'\<in>(weak_tau_succs Q). c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q' {p'})\<close> by auto
      with case_assms less(2) defender_keeps_losing strat_stays_winning have all_winning:
        \<open>(DefenderSwapNode p' Q) \<in> attacker_winning_region\<close>
        \<open>\<forall>q'\<in>(weak_tau_succs Q). (AttackerNode q' {p'}) \<in> attacker_winning_region\<close>
        by (metis, metis c_set_game_defender_node.simps(1,3))
      with case_assms moves less(2) have
        \<open>\<forall>q'\<in> weak_tau_succs Q. (AttackerNode q' {p'}, DefenderSwapNode p' Q) \<in> attacker_order\<close>
        \<open>(DefenderSwapNode p' Q, AttackerNode p Q) \<in> attacker_order\<close>
        unfolding attacker_order_def by (simp add: r_into_trancl')+
      hence \<open>\<forall>q'\<in> weak_tau_succs Q. (AttackerNode q' {p'}, AttackerNode p Q) \<in> attacker_order\<close>
        unfolding attacker_order_def by auto
      with less.hyps all_winning have
        \<open>\<forall>q'\<in> weak_tau_succs Q. q' \<Turnstile> attack_formula (AttackerNode q' {p'}) \<and> \<not> p' \<Turnstile> attack_formula (AttackerNode q' {p'})\<close>
        by blast
      with case_assms have
        \<open>p' \<Turnstile> HML_conj (weak_tau_succs Q) (\<lambda>q'. HML_neg (attack_formula (AttackerNode q' {p'})))\<close>
        \<open>\<forall>q'\<in> weak_tau_succs Q. \<not> q' \<Turnstile> HML_conj (weak_tau_succs Q) (\<lambda>qq'. HML_neg (attack_formula (AttackerNode qq' {p'})))\<close>
        by (simp, fastforce)
      with case_assms have
        \<open>p \<Turnstile>  HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then attack_formula (AttackerNode q {p'}) else HML_true)\<close>
        \<open>\<forall>q\<in>Q. \<not>q \<Turnstile>  HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> (weak_tau_succs Q) then attack_formula (AttackerNode q {p'}) else HML_true)\<close>
        unfolding weak_tau_succs_def HML_weaknor_def
        using conj_only_depends_on_indexset by (auto, force, fastforce)
      thus ?case unfolding case_assms by blast
    next
      assume \<open>Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true\<close>
      thus ?case by auto
    qed
  qed
qed

lemma distinction_in_language:
  fixes p Q
  defines
    \<open>pQ == AttackerNode p Q\<close>
  defines
    \<open>\<phi> == attack_formula pQ\<close>
  assumes
    \<open>pQ \<in> attacker_winning_region\<close>
  shows
    \<open>\<phi> \<in> HML_weak_formulas\<close>
  using assms(2,3) unfolding assms(1)
proof (induct arbitrary: \<phi> rule: attack_formula.induct)
  case (1 p Q)
  then show ?case using strat_stays_winning by auto
next
  case (2 a p Q)
  then show ?case
    by (simp add: HML_weak_formulas.Base HML_weak_formulas.Obs)
next
  case (3 p Q)
  hence \<open>\<forall>q' \<in> weak_tau_succs Q. attack_formula (AttackerNode q' {p}) \<in> HML_weak_formulas\<close>
    using weak_tau_succs_def HML_weak_formulas.Base by fastforce
  then show ?case
    using HML_weak_formulas.Base \<open>DefenderSwapNode p Q \<in> attacker_winning_region\<close>
    by (auto simp add: HML_weak_formulas.Conj)
qed

end
end
