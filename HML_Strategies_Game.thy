theory HML_Strategies_Game
  imports
    Contrasim_Set_Game
    Contrasim_HML
begin

locale c_game_with_attacker_strategy  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> +
fixes
  strat :: \<open>('s, 'a) c_set_game_node posstrategy\<close> and
  attacker_winning_region :: \<open>('s, 'a) c_set_game_node set\<close>
assumes
  finite_win:
    \<open>wf {(g, g'). c_set_game_moves g g' \<and>
      g \<in> attacker_winning_region \<and> g' \<in> attacker_winning_region \<and>
      (player1_position g \<longrightarrow> g' = strat g)}\<close> and
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
    \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p (dsuccs a Q)))\<close>
| \<open>attack_formula (DefenderSwapNode p Q) =
    (if Q = {} then HML_true else
    (HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> Q then (attack_formula (AttackerNode q {p})) else HML_true )))\<close>
  using c_set_game_defender_node.cases
  by (auto, blast)

termination attack_formula
  using finite_win strat_stays_winning defender_keeps_losing
  sorry

thm attack_formula.induct

lemma False using attack_formula.induct oops (*sledgehammer*)

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
    \<open>(\<exists>a p'. attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p' (dsuccs a Q))))
    \<or> (\<exists>p'. attack_formula (AttackerNode p Q) = (HML_weaknor (weak_tau_succs Q) (\<lambda>q. if q \<in> Q then (attack_formula (AttackerNode q {p'})) else HML_true )))
    \<or> (Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true)\<close>
proof -
  from assms have \<open>attack_formula (AttackerNode p Q) = attack_formula (strat (AttackerNode p Q))\<close> by simp
  moreover from attacker_defender_switch assms have
    \<open>(\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or>(\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p' )\<close> by blast
  ultimately have 
    \<open>(\<exists>a p'. (attack_formula (AttackerNode p Q)) = attack_formula (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or>(\<exists>p'. (attack_formula (AttackerNode p Q)) = attack_formula (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p')\<close>
    by metis
  thus ?thesis unfolding dsuccs_def
    by (metis attack_formula.simps(2) attack_formula.simps(3) dsuccs_def)
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
  using finite_win assms(3) unfolding assms(1,2)
proof (induct)
  case (less pQ)
  show ?case proof (cases \<open>attack_formula pQ\<close>)
qed
proof (induct rule: attack_formula.induct[of _ \<open>(AttackerNode p Q)\<close>])
  case (1 p Q)
  then show ?case
next
  case (2 a p Q)
  then show ?case sorry
next
  case (3 p Q)
  then show ?case sorry
qed



lemma distinction_soundness:
  fixes p Q p0 Q0
  defines
    \<open>pQ == AttackerNode p Q\<close>
  defines
    \<open>\<phi> == attack_formula pQ\<close>
  assumes
    \<open>\<exists>rest. pQ # rest \<in> plays_for_1strategy (strategy_from_positional strat) (AttackerNode p0 Q0)\<close>
    \<open>player1_winning_strategy (strategy_from_positional strat) pQ\<close>
    \<open>sound_1strategy (strategy_from_positional strat) pQ\<close>
  shows
    \<open>p \<Turnstile> \<phi> \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> \<phi>)\<close>
  using assms(3,4,5) unfolding assms(1,2)
  by (induct arbitrary: p Q rule: attack_formula.induct[of _ \<open>(AttackerNode p Q)\<close>], auto)

lemma distinction_soundness:
  fixes p Q rest p0 Q0
  defines
    \<open>pQ == AttackerNode p Q\<close>
  defines
    \<open>\<phi> == attack_formula pQ\<close>
  assumes
    \<open>\<exists>rest. pQ # rest \<in> plays_for_1strategy (strategy_from_positional strat) (AttackerNode p0 Q0)\<close>
    \<open>player1_winning_strategy (strategy_from_positional strat) pQ\<close>
    \<open>sound_1strategy (strategy_from_positional strat) pQ\<close>
  shows
    \<open>p \<Turnstile> \<phi> \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> \<phi>)\<close>
  using assms(1,3,4,5) unfolding \<open>\<phi> == attack_formula pQ\<close>


  case (1 p' Q')
  then show ?case sorry
next
  case (2 a p Q)
  then show ?case sorry
next
  case (3 p Q)
  then show ?case sorry
qed
  case (1 p' Q')
  then show ?case sorry
next
  case (2 a p' Q')
  then show ?case by auto
next
  case (3 p' Q')
  then show ?case by auto
qed
  case (1)
  then show ?case sorry
next
  case 2
  then show ?case sorry
next
  case 3
  then show ?case sorry
qed
  case (1 p' Q')
  then show ?case sorry
next
  case (2 a p' Q')
  then show ?case sorry
next
  case (3 p' Q')
  then show ?case sorry
qed



  case HML_true
  hence \<open>False\<close> using attack_options HML_weaknor_def HML_formula.distinct(5)
    by metis
  then show ?case ..
next
  case (HML_conj Q F)
  hence \<open>False\<close> using attack_options HML_weaknor_def HML_formula.distinct(9)
    by metis
  then show ?case ..
next
  case (HML_neg \<phi>)
  hence \<open>False\<close> using attack_options HML_weaknor_def HML_formula.distinct(11)
    by metis
  then show ?case ..
next
  case (HML_poss t \<phi>)
  hence \<open>(\<exists>a p'. attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p' (dsuccs a Q))))
    \<or> (\<exists>p'. attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>(AND (weak_tau_succs Q) (\<lambda>q. HML_neg (attack_formula (AttackerNode q {p'})))))\<close>
    using attack_options[of p Q] unfolding HML_weaknor_def by blast
  hence
    \<open>t = \<tau>\<close>
    \<open>(\<exists>a p'. \<phi> = \<langle>a\<rangle>(attack_formula (AttackerNode p' (dsuccs a Q))))
    \<or> (\<exists>p'. \<phi> = (AND (weak_tau_succs Q) (\<lambda>q. HML_neg (attack_formula (AttackerNode q {p'})))))\<close>
    using \<open>(\<langle>t\<rangle>\<phi>) = attack_formula (AttackerNode p Q)\<close> by auto
  from this(2) show ?case unfolding \<open>t = \<tau>\<close>
  proof (rule disjE)
    assume \<open>\<exists>a p'. \<phi> = \<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
    then obtain a p' where phi_def: \<open>\<phi> = \<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close> by blast
    have \<open>player1_winning_strategy (strategy_from_positional strat) (AttackerNode p' (dsuccs a Q))\<close>
        \<open>sound_1strategy (strategy_from_positional strat) (AttackerNode p' (dsuccs a Q))\<close> sorry
    with HML_poss(1) phi_def have \<open>p' \<Turnstile> \<phi> \<and> (\<forall>q\<in>(dsuccs a Q). \<not> q \<Turnstile> \<phi>)\<close>
    show \<open>(p \<Turnstile> (\<langle>\<tau>\<rangle>\<phi>)) \<and> (\<forall>q\<in>Q. \<not> (q \<Turnstile> (\<langle>\<tau>\<rangle>\<phi>)))\<close> sorry
  qed
qed

end
end
