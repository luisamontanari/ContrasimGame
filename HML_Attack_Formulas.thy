theory HML_Attack_Formulas
  imports
    Contrasim_Set_Game
    HM_Logic_Infinitary
begin

locale c_game_with_attacker_formula  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> 
begin

inductive_set attacker_winning_region :: \<open>('s, 'a) c_set_game_node set\<close> where
  Base: \<open>DefenderSwapNode _ {} \<in> attacker_winning_region\<close> |
  Atk: \<open>(c_set_game_moves (AttackerNode p Q) g' \<and> g' \<in> attacker_winning_region) \<Longrightarrow> (AttackerNode p Q) \<in> attacker_winning_region\<close> |
  Def: \<open>c_set_game_defender_node g \<Longrightarrow> (\<And>g'. c_set_game_moves g g' \<Longrightarrow> g' \<in> attacker_winning_region) \<Longrightarrow> g \<in> attacker_winning_region\<close>

lemma attacker_wins_in_winning_region: 
  assumes 
    \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
  shows \<open>\<exists>f. player1_winning_strategy f (AttackerNode p Q) \<and> positional_strategy f \<close>
proof (induct  rule: attacker_winning_region.induct[OF assms(1)])
  case (1 p)
  obtain f where f_def: \<open>positional_strategy f\<close> 
    using positional_strategy_def by fastforce
  have \<open>weak_tau_succs {} = {}\<close> unfolding weak_tau_succs_def by auto
  hence \<open>\<nexists>g'. c_set_game_moves (DefenderSwapNode p {}) g'\<close> 
    using move_DefSwap_to_AtkNode by fastforce
  thus ?case using stuck_0_all_strats_win f_def by auto
next
  case Atk: (2 p Q g')
  let ?g = \<open>AttackerNode p Q\<close>
  obtain f where f_win: \<open>player1_winning_strategy f g'\<close> 
    and f_pos: \<open>positional_strategy f\<close> using Atk by auto
  then obtain n where n_def: \<open>\<forall>play\<in>plays_for_1strategy f g'.
      \<not> player0_wins_immediately play \<and> length play \<le> n\<close>
    using player1_winning_strategy_def by auto
  show ?case 
  proof (cases \<open>\<exists>play \<in> plays_for_1strategy f g'. ?g \<in> set(play)\<close>)
    case True
    then obtain play where 
      \<open>play \<in> plays_for_1strategy f g'\<close>
      \<open>?g \<in> set(play)\<close> by auto
    hence \<open>player1_winning_strategy f ?g\<close> sorry
    then show ?thesis sorry
  next
    case False
    define f' where \<open>f' \<equiv> (\<lambda>play. (if hd play = ?g then g' else (f play)))\<close>
    have \<open>positional_strategy f'\<close> unfolding f'_def 
      using f_pos positional_strategy_def by auto
    thm plays_for_1strategy.induct
    hence not_g: \<open>\<forall>play g. play \<in> plays_for_1strategy f g' \<and> g \<in> set play \<longrightarrow> g  \<noteq> ?g\<close> 
      using False by auto
    thm plays_for_1strategy.induct[of _ _ g']
    have \<open>\<And>play. play \<in> plays_for_1strategy f' g' \<Longrightarrow> play \<in> plays_for_1strategy f g'\<close>
    proof -
      fix play 
      assume subassms: \<open>play \<in> plays_for_1strategy f' g'\<close>
      show \<open>play \<in> plays_for_1strategy f g'\<close>
      proof (induct rule: plays_for_1strategy.induct[OF subassms])
        case 1
        then show ?case by (simp add: plays_for_1strategy.init)
      next
        case (2 n0 play n1)
        then show ?case by (simp add: plays_for_1strategy.p0move)
      next
        case (3 n1 play)
        then show ?case
        proof(cases \<open>n1 = ?g\<close>)
          case True
          hence \<open>False\<close>  using "3.hyps"(2) False by fastforce
          then show ?thesis by auto
        next
          case False
          then show ?thesis
            using f'_def "3.hyps" plays_for_1strategy.p1move 
            by fastforce
        qed
      qed
    qed
    hence f'_win_on_g': \<open>\<forall>play\<in>plays_for_1strategy f' g'.
          \<not> player0_wins_immediately play \<and> length play \<le> n\<close>  using f_win n_def by blast
    hence winning_tail: \<open>\<forall>play\<in>plays_for_1strategy f' ?g. 
\<exists>xs. play = xs@[?g] \<and> (xs = [] \<or> xs \<in> plays_for_1strategy f' g')\<close> 
    proof(clarify)
      fix play 
      assume subassm: \<open>play\<in>plays_for_1strategy f' ?g\<close>
      show \<open>\<exists>xs. play = xs@[?g] \<and> (xs = [] \<or> xs \<in> plays_for_1strategy f' g')\<close> 
      proof(induct rule: plays_for_1strategy.induct[OF subassm])
        case 1 show ?case by simp
      next
        case (2 n0 play n1)
        then obtain xs where 
          xs_def: \<open>n0 # play = xs @ [AttackerNode p Q]\<close> 
                  \<open>(xs = [] \<or> xs \<in> plays_for_1strategy f' g')\<close> by auto
        then have \<open>xs \<noteq> [] \<and> hd xs = n0\<close> using "2.hyps"(3)
          by (metis c_set_game_defender_node.simps(1) hd_append2 list.sel(1) self_append_conv2)
        hence \<open>n1#xs \<in> plays_for_1strategy f' g'\<close> 
          using "2.hyps" plays_for_1strategy.p0move
          by (smt (verit) append_eq_Cons_conv xs_def)
        then show ?case using xs_def(1) by auto
      next
        case hd_attacker: (3 n1 play)
        then obtain xs where 
          xs_def: \<open>n1 # play = xs @ [AttackerNode p Q]\<close>                     
                  \<open>(xs = [] \<or> xs \<in> plays_for_1strategy f' g')\<close> by auto
        then show ?case 
        proof (cases \<open>xs = []\<close>)
          case True
          hence \<open>n1 = ?g\<close>
            using xs_def(1) by auto
          hence \<open>f' (n1#play) = g'\<close> using f'_def by auto
          then show ?thesis
            using True plays_for_1strategy.init xs_def(1) by auto
        next
          case False
          hence head: \<open>hd xs = n1\<close> using xs_def 
            by (metis hd_append2 list.sel(1))
          have in_plays: \<open>f' (n1 # play) # n1 # play = f' (n1 # play) # xs @ [?g]\<close>
            by (simp add: xs_def(1)) 
          have \<open>f' (n1 # play) # xs \<in> plays_for_1strategy f' g'\<close> 
            using plays_for_1strategy.p1move[OF hd_attacker(1) hd_attacker.hyps(3, 4)] head
            by (smt (verit) False \<open>positional_strategy f'\<close> append1_eq_conv 
                  hd_attacker.hyps(2, 4) list.sel(1) plays_for_1strategy.simps 
                  positional_strategy_def xs_def(1))
          then show ?thesis using in_plays by auto
        qed
      qed
    qed
    hence \<open>\<forall>play\<in>plays_for_1strategy f' ?g. \<exists>xs. play = xs@[?g] \<and> (xs = [] \<or> length xs \<le> n)\<close>
      using f'_win_on_g' by auto
    hence bounded: \<open>\<forall>play\<in>plays_for_1strategy f' ?g. length play \<le> (Suc n)\<close> using nat_le_linear by auto
(*
       from winning_tail have \<open>\<forall>play\<in>plays_for_1strategy f' ?g. \<not>player0_wins_immediately play\<close> *)
    hence \<open>\<forall>play\<in>plays_for_1strategy f' ?g. \<exists>xs. play = xs@[?g] \<and> 
          (xs = [] \<or> \<not>player0_wins_immediately xs)\<close> 
      using winning_tail f'_win_on_g' by auto
    hence \<open>\<forall>play\<in>plays_for_1strategy f' ?g. \<not>player0_wins_immediately play\<close>
      unfolding player0_wins_immediately_def
      by (metis hd_append list.sel(1) local.Atk)

    then show ?thesis unfolding player1_winning_strategy_def 
      using bounded \<open>positional_strategy f'\<close> by blast
  qed
next
  case Def: (3 g)
  then show ?case
(*
if no game move exists, the defender is stuck and every strategy wins. 

otherwise: for every g_i with g \<longrightarrow> g_i we have a winning strategy f_i starting from g'.
The winning strategy on g combines them all, i.e.
for all g_i with g\<longrightarrow>g_i, f'(g_i) = f_i(g_i). 

*)


  proof(cases \<open>c_set_game_moves g g'\<close>)
    case True
    hence \<open>g' \<in> attacker_winning_region\<close> using Def.hyps by auto
    hence \<open>\<exists>f. player1_winning_strategy f g' \<and>
        positional_strategy f\<close> using Def.hyps True by auto
    then show ?thesis  sorry
  next
    case False
    hence \<open>\<forall>play. player1_wins_immediately (g#play)\<close>sorry
    then show ?thesis sorry
  qed
qed


lemma Atk_node_wins_if_Q_is_empty: 
  assumes \<open>Q = {}\<close>
  shows \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
proof - 
  have atk_move: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p Q)\<close> 
    by (simp add: steps.refl)
  have \<open>DefenderSwapNode p Q \<in> attacker_winning_region\<close> using assms attacker_winning_region.Base by simp
  thus ?thesis using atk_move attacker_winning_region.Atk by blast
qed


lemma Atk_node_wins_in_2_moves: 
  assumes 
        \<open>AttackerNode p' (dsuccs a Q) \<in> attacker_winning_region\<close>
        \<open>p =\<rhd>a p'\<close>
        \<open>\<not>tau a\<close>
  shows \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
proof - 
  have AtkToSim: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSimNode a p' Q)\<close>
    using assms(2, 3) by simp
  have \<open>\<forall>g. c_set_game_moves 
(DefenderSimNode a p' Q) g \<longrightarrow> (g = AttackerNode p' (dsuccs a Q))\<close>
    by (simp add: move_DefSim_to_AtkNode)
  hence \<open>(DefenderSimNode a p' Q) \<in> attacker_winning_region\<close> 
    using assms(1) attacker_winning_region.Def
    by (metis c_set_game_defender_node.simps(2))
  thus ?thesis using AtkToSim attacker_winning_region.Atk by blast
qed


lemma dist_formula_implies_wr_inclusion: 
  assumes 
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>distinguishes_from_set \<phi> p Q\<close>
  shows \<open>(AttackerNode p Q) \<in> attacker_winning_region\<close>
proof(cases \<open>Q = {}\<close>)
  case True
  then show ?thesis using Atk_node_wins_if_Q_is_empty by auto
next
  case False
  then show ?thesis using assms
  proof (induct arbitrary: p Q rule: HML_weak_formulas.induct[OF assms(1)])
    case Base: 1
    have \<open>\<forall>q. q \<Turnstile> HML_true\<close> by simp
    hence \<open>False\<close> 
      using Base.prems(1, 3) by simp
    then show ?case by auto
  next
    case Obs: (2 \<phi> a)
    then obtain p' where p'_def: \<open>p =\<rhd>a p' \<and> p' \<Turnstile> \<phi> \<close> 
      using tau_a_obs_implies_delay_step[of p a \<phi>] by auto
    have \<open>\<forall>q. q \<in> Q \<longrightarrow> \<not> q \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close> using Obs by auto
    hence \<open>\<forall>q. q \<in> Q \<longrightarrow> (\<forall>q'.  \<not>q  =\<rhd>a  q' \<or> \<not>q' \<Turnstile> \<phi>)\<close>
      using delay_step_implies_tau_a_obs by blast
    hence \<open>\<forall>q'. q' \<in> dsuccs a Q \<longrightarrow> \<not> q' \<Turnstile> \<phi>\<close> 
      unfolding dsuccs_def by blast
    hence phi_distinguishing: \<open>distinguishes_from_set \<phi> p' (dsuccs a Q)\<close> 
      using p'_def by simp
    thus ?case
    proof (cases \<open>dsuccs a Q = {}\<close>)
      case dsuccs_empty: True
      then show ?thesis
      proof (cases \<open>tau a\<close>)
        case True
        hence \<open>{q1. \<exists>q\<in> Q. q \<longmapsto>* tau q1} = {}\<close> using dsuccs_def dsuccs_empty by auto
        hence \<open>Q = {}\<close> using steps.refl by blast
        then show ?thesis using Atk_node_wins_if_Q_is_empty by auto
      next
        case False
        hence \<open>AttackerNode p' (dsuccs a Q) \<in> attacker_winning_region\<close> 
          using Atk_node_wins_if_Q_is_empty dsuccs_empty by auto
        thus ?thesis using Atk_node_wins_in_2_moves False p'_def by blast
      qed
    next
      case False
      hence wr_pred_atk_node: \<open>AttackerNode p' (dsuccs a Q) \<in> attacker_winning_region\<close> 
        using Obs.hyps phi_distinguishing by auto
      thus ?thesis 
      proof(cases \<open>tau a\<close>)
        case True
        hence \<open>\<forall>p. (p \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) = (p  \<Turnstile> \<phi>)\<close>
          using delay_step_implies_tau_a_obs p'_def satisfies.simps(4) tau_tau 
            Obs.hyps(1) weak_backwards_truth
          by (meson lts.refl)
        hence \<open>distinguishes_from_set \<phi> p Q\<close> using Obs.prems by auto
        thus ?thesis using Obs.hyps Obs.prems by blast
      next
        case False
        then show ?thesis 
          using wr_pred_atk_node Atk_node_wins_in_2_moves p'_def by blast
      qed
    qed
  next
    case Conj: (3 I F)
    then obtain p' where \<open>p \<Rightarrow>^\<tau> p'\<close> and p_sat:  \<open>p' \<Turnstile> HML_conj I (\<lambda>f. HML_neg (F f))\<close>
      unfolding HML_weaknor_def by auto
    have \<open>\<And>q . q \<in> Q  \<Longrightarrow> \<not>q  \<Turnstile>  HML_poss \<tau> (HML_conj I (\<lambda>f. HML_neg (F f)))\<close>
      by (metis Conj.prems(3) HML_weaknor_def distinguishes_from_set.elims(2))
    hence \<open>\<And>q q'. q \<in> Q \<Longrightarrow> \<not>q \<Rightarrow>^\<tau> q' \<or> \<not>q'  \<Turnstile> HML_conj I (\<lambda>f. HML_neg (F f))\<close>
      using satisfies.simps(4) tau_tau by blast
    hence \<open>\<And>q'. \<not>q' \<in> (weak_tau_succs Q) \<or> \<not>q'  \<Turnstile> HML_conj I (\<lambda>f. HML_neg (F f))\<close>
      using weak_tau_succs_def by auto
    hence Ex: \<open>\<And>q'.  q' \<in> (weak_tau_succs Q) \<Longrightarrow> (\<exists>i. i \<in> I \<and> q'  \<Turnstile>  (F i))\<close>
      by auto
    have atk_move: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p' Q)\<close>
      using \<open>p \<Rightarrow>^\<tau> p'\<close> by auto
    have Ex_i: \<open>\<forall>q1 P1. c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1) \<longrightarrow> 
          (\<exists>i. i \<in> I \<and> q1  \<Turnstile>  (F i)) \<and> P1 = {p'}\<close>
      using Ex by auto
    hence \<open>\<forall>q1 P1. 
          c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1) \<longrightarrow> 
          (\<exists>i. i \<in> I \<and> q1  \<Turnstile>  (F i) \<and> (\<forall>p'. p' \<in> P1 \<longrightarrow> \<not> p' \<Turnstile> (F i)))\<close>
      using p_sat by auto
    hence  \<open>\<forall>q1 P1. 
          c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1) \<longrightarrow> 
          (\<exists>i. i \<in> I \<and> distinguishes_from_set (F i) q1 P1)\<close> 
      unfolding distinguishes_from_set.simps using p_sat by blast
    hence all_atk_succs_in_wr: 
          \<open>\<forall>q1 P1. c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1) \<longrightarrow> 
          (AttackerNode q1 P1 \<in> attacker_winning_region)\<close> 
      using Conj.hyps Ex_i by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g \<longrightarrow> 
          (\<exists> q1 P1. g = (AttackerNode q1 P1))\<close> 
      using move_DefSwap_to_AtkNode by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g \<longrightarrow> g \<in> attacker_winning_region\<close> 
      using all_atk_succs_in_wr by auto
    hence \<open>DefenderSwapNode p' Q \<in> attacker_winning_region\<close> 
      using attacker_winning_region.Def
      by (meson c_set_game_defender_node.simps(3)) 
    then show ?case using atk_move attacker_winning_region.Atk by blast
  qed
qed

end
end
