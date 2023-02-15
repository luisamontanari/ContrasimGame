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
  winning_dist :: \<open>('s, 'a) c_set_game_node \<Rightarrow> nat\<close>
assumes
  \<comment>\<open>This assumption seems to create an inconsistency.... :/ Will have to restrict it to non-immediately attacker-won positions (?)\<close>
  winning_dist_attacker_decreasing:
    \<open>\<And>pos. player1_position pos \<Longrightarrow> winning_dist (strat pos) < winning_dist pos\<close> and
  winning_dist_defender_constant:
    \<open>\<And>pos. player0_position pos \<Longrightarrow> game_move pos pos' \<Longrightarrow>  winning_dist pos' \<le> winning_dist pos\<close>
begin

lemma INCONSISTENCY:
  False using winning_dist_attacker_decreasing winning_dist_defender_constant wf_measure[of winning_dist] wf_def
  oops

text \<open>This construction of attacker formulas from a game only works if \<open>strat\<close> is a (non-cyclic)
  attacker strategy. (If it's winning and sound, the constructed formula should be distinguishing.)\<close>

function attack_formula :: \<open>('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula\<close> where
  \<open>attack_formula (AttackerNode p Q) =
    attack_formula (strat (AttackerNode p Q))\<close>
| \<open>attack_formula (DefenderSimNode a p Q) =
    \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p (dsuccs a Q)))\<close>
| \<open>attack_formula (DefenderSwapNode p Q) =
    (if Q = {} then HML_true else
    (HML_weaknor (weak_tau_succs Q) (\<lambda>q. (attack_formula (AttackerNode q {p})))))\<close>
  using c_set_game_defender_node.cases
  by (auto, blast)

termination attack_formula
proof -
  define m where \<open>m \<equiv> \<lambda>pos. if player1_position pos then 2 * winning_dist pos else Suc (2 * winning_dist pos)\<close>
  thus ?thesis
    using local.termination[OF wf_measure[of m]]
      winning_dist_defender_constant winning_dist_attacker_decreasing linorder_not_le
    unfolding m_def measure_def
    by (auto simp add: less_Suc_eq_le Suc_double_not_eq_double Suc_lessI)
qed
\<comment> \<open>zipperposition thinks that one can still prove an inconsistency here ...? :|\<close>

thm attack_formula.induct

lemma False using attack_formula.induct sledgehammer

lemma \<open>(\<forall> p Q. P  (strat (AttackerNode p Q)) \<longrightarrow> P (AttackerNode p Q)) \<longrightarrow>
  (\<forall>a p Q. P (AttackerNode p (dsuccs a Q)) \<longrightarrow> P (DefenderSimNode a p Q)) \<longrightarrow> (\<forall>p Q. (\<forall> x. P (AttackerNode x {p})) \<longrightarrow> P (DefenderSwapNode p Q)) \<Longrightarrow> P b\<close>
  nitpick
  oops

declare [[simp_trace]]

lemma Apparently_something_is_inconsistent:
  shows \<open>(\<forall>P b. (\<forall> p Q. P  (strat (AttackerNode p Q)) \<longrightarrow> P (AttackerNode p Q)) \<longrightarrow>
  (\<forall>a p Q. P (AttackerNode p (dsuccs a Q)) \<longrightarrow> P (DefenderSimNode a p Q)) \<longrightarrow> (\<forall>p Q. (\<forall> x. P (AttackerNode x {p})) \<longrightarrow> P (DefenderSwapNode p Q)) \<longrightarrow> P b) \<longrightarrow> False\<close> apply auto


lemma attack_options: 
  assumes
    \<open>player1_winning_strategy (strategy_from_positional strat) (AttackerNode p Q)\<close>
    \<open>sound_1strategy (strategy_from_positional strat) (AttackerNode p Q)\<close>
  shows
    \<open>(\<exists>a p'. attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p' (dsuccs a Q))))
    \<or> (\<exists>p'. attack_formula (AttackerNode p Q) = (HML_weaknor (weak_tau_succs Q) (\<lambda>q. (attack_formula (AttackerNode q {p'})))))\<close>
proof -
  have \<open>[AttackerNode p Q] \<in> plays_for_1strategy (strategy_from_positional strat) (AttackerNode p Q)\<close>
    using plays_for_1strategy.init by auto
  with assms(1) have unstuck:
    \<open>\<exists>p'. c_set_game_moves (AttackerNode p Q) p'\<close>
    unfolding player1_winning_strategy_def player0_wins_immediately_def by fastforce
  with assms(2) have \<open>c_set_game_moves (AttackerNode p Q) (strat (AttackerNode p Q))\<close>
    unfolding sound_1strategy_def strategy_from_positional_def
    using plays_for_1strategy.init by fastforce
  hence \<open>(\<exists>a p'. p =\<rhd>a p' \<and> \<not> tau a \<and> strat (AttackerNode p Q) = (DefenderSimNode a p' Q))
    \<or> (\<exists>p'. p \<Rightarrow>^\<tau> p' \<and> strat (AttackerNode p Q) = (DefenderSwapNode p' Q))\<close>
    using c_set_game_defender_node.elims(1) c_set_game_moves_no_step(5) simulation_challenge swap_challenge
    by (smt (verit))
  hence  \<open>(\<exists>a p'. attack_formula (AttackerNode p Q) = (attack_formula (DefenderSimNode a p' Q)))
    \<or> (\<exists>p'. attack_formula (AttackerNode p Q) = (attack_formula (DefenderSwapNode p' Q)))\<close>
    by auto
  thus ?thesis by simp
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
