theory HML_Attack_Formulas
  imports
    Contrasim_Set_Game
    Contrasim_HML
begin

locale c_game_with_attacker_formula  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> 
begin

fun is_dist ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close>
  where
   \<open>is_dist \<phi> p q = (p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>)\<close>

fun is_dist_set ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool\<close>
  where
   \<open>is_dist_set \<phi> p Q = (p \<Turnstile> \<phi> \<and> (\<forall>q. q \<in> Q \<longrightarrow> \<not> q \<Turnstile> \<phi>))\<close>

inductive_set atk_WR :: \<open>('s, 'a) c_set_game_node set\<close> where
  Base: \<open>DefenderSwapNode _ {} \<in> atk_WR\<close> |
  Atk: \<open>(c_set_game_moves (AttackerNode p Q) g' \<and> g' \<in> atk_WR) \<Longrightarrow> (AttackerNode p Q) \<in> atk_WR\<close> |
  Def: \<open>(c_set_game_moves g g' \<and> c_set_game_defender_node g \<Longrightarrow> g' \<in> atk_WR) \<Longrightarrow> g \<in> atk_WR\<close> 

definition Phi :: "(nat => nat) set" where
  "Phi = {f. \<forall>x. 0 < f x \<and> f x < 11}"

fun atk_state :: \<open>('s, 'a) c_set_game_node \<Rightarrow> 's\<close>
  where
    \<open>atk_state (AttackerNode p Q) = p\<close> 
  | \<open>atk_state (DefenderSimNode a p Q) = p\<close>
  | \<open>atk_state (DefenderSwapNode p Q) = p\<close>


fun maintains_WR :: \<open>(('s, 'a) c_set_game_node list \<Rightarrow> ('s, 'a) c_set_game_node) 
      \<Rightarrow> ('s, 'a) c_set_game_node \<Rightarrow> bool\<close> 
  where
 \<open>maintains_WR f g = (\<forall>play. c_set_game_moves g (f (g#play)) \<and> f (g#play) \<in> atk_WR)\<close>

definition atk_strat_set :: \<open>(('s, 'a) c_set_game_node list \<Rightarrow> ('s, 'a) c_set_game_node) set\<close>
  where 
    \<open>atk_strat_set = {f. (\<forall>p Q. (AttackerNode p Q \<in> atk_WR) \<longrightarrow> 
                          maintains_WR f (AttackerNode p Q))}\<close>

lemma atk_strat_set_nonempty : \<open>atk_strat_set \<noteq> {}\<close> 
  unfolding atk_strat_set_def
proof (rule ccontr)
  assume \<open>\<not>{f. (\<forall>p Q. (AttackerNode p Q \<in> atk_WR) \<longrightarrow> 
                          maintains_WR f (AttackerNode p Q))} \<noteq> {}\<close>
  hence \<open>\<And>f. \<not>(\<forall>p Q. (AttackerNode p Q \<in> atk_WR) \<longrightarrow> 
                          maintains_WR f (AttackerNode p Q))\<close> by auto
  hence ex: \<open>\<And>f. \<exists>p Q. (AttackerNode p Q \<in> atk_WR \<and> \<not>maintains_WR f (AttackerNode p Q))\<close> by auto
  hence no_main: \<open>\<exists> p Q. (AttackerNode p Q \<in> atk_WR) \<longrightarrow>  (\<forall>f. \<not>maintains_WR f (AttackerNode p Q))\<close>
    by (metis (mono_tags, opaque_lifting) atk_WR.Def list.sel(1) 
        maintains_WR.elims(1) simple_game.player0_wins_immediately_def)
  then obtain p Q where \<open>(AttackerNode p Q) \<in> atk_WR\<close>
    by (metis atk_WR.Def c_set_game_defender_node.simps(1))
  let g = AttackerNode p Q
  hence \<open>\<forall>f. \<exists>play. \<not>c_set_game_moves g (f (g#play)) \<or> \<not>f (g#play) \<in> atk_WR\<close>
    using maintains_WR.simps no_main
    sledgehammer

  thus \<open>False\<close> sledgehammer  sorry
qed


(*
fun atk_strat :: \<open>('s, 'a) c_set_game_node list \<Rightarrow> ('s, 'a) c_set_game_node\<close>
  where 
\<open>atk_strat ((AttackerNode p Q)#play) =  
(SOME g'. c_set_game_moves (AttackerNode p Q) g' \<and> g' \<in> atk_WR)\<close>
| \<open>atk_strat _ = undefined\<close>*)

thm atk_WR.induct

thm someI_ex

lemma attacker_wins_in_winning_region: 
  assumes 
    \<open>AttackerNode p Q \<in> atk_WR\<close>
  shows \<open>\<exists>f. f \<in> atk_strat_set \<and> player1_winning_strategy f (AttackerNode p Q)\<close>
proof (induct rule: atk_WR.induct[OF assms(1)])
  case (1 p)
  have \<open>weak_tau_succs {} = {}\<close> unfolding weak_tau_succs_def by auto
  hence \<open>\<nexists>g'. c_set_game_moves (DefenderSwapNode p {}) g'\<close> 
    using move_DefSwap_to_AtkNode by fastforce
  thus ?case sledgehammer by (simp add: stuck_0_all_strats_win)
next
  case Atk: (2 p Q g')
  then obtain n where n_def: \<open>\<forall>play\<in>plays_for_1strategy f g'.
      \<not> player0_wins_immediately play \<and> length play \<le> n\<close>
    using player1_winning_strategy_def by auto
  hence \<open>\<forall>play. atk_strat ((AttackerNode p Q)#play) =  g'\<close> 
    using Atk.hyps sledgehammer


  hence \<open>\<forall>play\<in>plays_for_1strategy atk_strat (AttackerNode p Q).
      \<not> player0_wins_immediately play \<and> length play \<le> (Suc n)\<close> sledgehammer

  thm player1_winning_strategy_def
  then show ?case sorry
next
  case Def: (3 g g')
  then show ?case sorry
qed

lemma Atk_node_wins_if_Q_is_empty: 
  assumes \<open>Q = {}\<close>
  shows \<open>AttackerNode p Q \<in> atk_WR\<close>
proof - 
  have atk_move: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p Q)\<close> 
    by (simp add: steps.refl)
  have \<open>DefenderSwapNode p Q \<in> atk_WR\<close> using assms atk_WR.Base by simp
  thus ?thesis using atk_move atk_WR.Atk by blast
qed


lemma Atk_node_wins_in_2_moves: 
  assumes 
        \<open>AttackerNode p' (dsuccs a Q) \<in> atk_WR\<close>
        \<open>p =\<rhd>a p'\<close>
        \<open>\<not>tau a\<close>
  shows \<open>AttackerNode p Q \<in> atk_WR\<close>
proof - 
  have AtkToSim: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSimNode a p' Q)\<close>
    using assms(2, 3) by simp
  have \<open>\<forall>g. c_set_game_moves 
(DefenderSimNode a p' Q) g \<longrightarrow> (g = AttackerNode p' (dsuccs a Q))\<close>
    by (simp add: move_DefSim_to_AtkNode)
  hence \<open>(DefenderSimNode a p' Q) \<in> atk_WR\<close> using assms(1) atk_WR.Def by blast
  thus ?thesis using AtkToSim atk_WR.Def by blast
qed


lemma dist_formula_implies_wr_inclusion: 
  assumes 
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>is_dist_set \<phi> p Q\<close>
  shows \<open>(AttackerNode p Q) \<in> atk_WR\<close>
proof(cases \<open>Q = {}\<close>)
  case True
  then show ?thesis using Atk_node_wins_if_Q_is_empty by auto
next
  case False
  then show ?thesis using assms
  proof (induct arbitrary: p Q rule: HML_weak_formulas.induct[OF assms(1)])
    case Base: 1
    have \<open>\<forall>q. q \<Turnstile> (HML_weaknor {} (\<lambda>i. HML_true))\<close>
      by (simp add: all_states_sat_empty_conj)
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
    hence phi_distinguishing: \<open>is_dist_set \<phi> p' (dsuccs a Q)\<close> 
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
        hence \<open>AttackerNode p' (dsuccs a Q) \<in> atk_WR\<close> 
          using Atk_node_wins_if_Q_is_empty dsuccs_empty by auto
        thus ?thesis using Atk_node_wins_in_2_moves False p'_def by blast
      qed
    next
      case False
      hence wr_pred_atk_node: \<open>AttackerNode p' (dsuccs a Q) \<in> atk_WR\<close> using Obs.hyps phi_distinguishing by auto
      thus ?thesis 
      proof(cases \<open>tau a\<close>)
        case True
        hence \<open>\<forall>p. (p \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) = (p  \<Turnstile> \<phi>)\<close>
          using delay_step_implies_tau_a_obs p'_def satisfies.simps(4) tau_tau 
            Obs.hyps(1) backwards_truth
          by (meson lts.refl)
        hence \<open>is_dist_set \<phi> p Q\<close> using Obs.prems by auto
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
      by (metis Conj.prems(3) HML_weaknor_def is_dist_set.elims(2))
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
          (\<exists>i. i \<in> I \<and> is_dist_set (F i) q1 P1)\<close> 
      unfolding is_dist_set.simps using p_sat by blast
    hence all_atk_succs_in_wr: 
          \<open>\<forall>q1 P1. c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1) \<longrightarrow> 
          (AttackerNode q1 P1 \<in> atk_WR)\<close> 
      using Conj.hyps Ex_i by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g \<longrightarrow> 
          (\<exists> q1 P1. g = (AttackerNode q1 P1))\<close> 
      using move_DefSwap_to_AtkNode by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g \<longrightarrow> g \<in> atk_WR\<close> 
      using all_atk_succs_in_wr by auto
    hence \<open>DefenderSwapNode p' Q \<in> atk_WR\<close> using atk_WR.Def by blast
    then show ?case using atk_move atk_WR.Atk by blast
  qed
qed

end
end
