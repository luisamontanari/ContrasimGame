theory HML_Attack_Formulas
  imports
    Contrasim_Set_Game
    Contrasim_HML
begin

locale c_game_with_attacker_formula  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> + 
fixes 
  wr ::  \<open>('s, 'a) c_set_game_node \<Rightarrow> bool\<close> 
assumes 
    \<open>wr (DefenderSwapNode p Q) = (if Q = {} then True
     else (\<forall>g. c_set_game_moves (DefenderSwapNode p Q) g \<longrightarrow> wr g))\<close>
    \<open>wr (AttackerNode p Q) = (\<exists>g. c_set_game_moves (AttackerNode p Q) g \<and> wr g)\<close>
    \<open>wr (DefenderSimNode a p Q) = (\<forall>g. c_set_game_moves (DefenderSimNode a p Q) g \<longrightarrow> wr g)\<close>
begin

fun is_dist ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close>
  where
   \<open>is_dist \<phi> p q = (p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>)\<close>

fun is_dist_set ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool\<close>
  where
   \<open>is_dist_set \<phi> p Q = (p \<Turnstile> \<phi> \<and> (\<forall>q. q \<in> Q \<longrightarrow> \<not> q \<Turnstile> \<phi>))\<close>


lemma all_states_sat_empty_conj:
  shows \<open>\<forall>q. q \<Turnstile> (HML_weaknor {} (\<lambda>i. HML_true))\<close>
proof - 
  have \<open>\<forall>q F. q \<Turnstile> (HML_conj {} (\<lambda>f. HML_neg (F f)))\<close> by auto
  thus ?thesis                     
    by (metis HML_formula.distinct(9, 11)
        HML_formula.inject(3) HML_weaknor_def satisfies.elims(3) step_tau_refl tau_def)
qed

lemma tau_a_obs_implies_delay_step: 
  assumes \<open>p  \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close>
  shows \<open>\<exists>p'. p =\<rhd>a p' \<and> p' \<Turnstile> \<phi>\<close>
proof - 
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p'' \<and> p'' \<Turnstile> \<langle>a\<rangle>\<phi>\<close> using assms by auto
  thus ?thesis using satisfies.simps(4) steps_concat tau_tau by blast
qed

lemma delay_step_implies_tau_a_obs: 
  assumes 
    \<open>p =\<rhd>a p'\<close>
    \<open>p' \<Turnstile> \<phi>\<close>
  shows \<open>p  \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close>
proof - 
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p''\<close> and \<open>p'' \<Rightarrow>^a p'\<close> using assms steps.refl tau_tau by blast
  thus ?thesis by (metis assms(1,2) lts_tau.satisfies.simps(4) lts_tau.tau_tau)
qed


function wr2 ::  \<open>('s, 'a) c_set_game_node \<Rightarrow> bool\<close> 
  where 
    \<open>wr2 (DefenderSwapNode p Q) = (if Q = {} then True
     else (\<forall>g. c_set_game_moves (DefenderSwapNode p Q) g \<longrightarrow> wr2 g))\<close>
  | \<open>wr2 (AttackerNode p Q) = (\<exists>g. c_set_game_moves (AttackerNode p Q) g \<and> wr2 g)\<close>
  | \<open>wr2 (DefenderSimNode a p Q) = (\<forall>g. c_set_game_moves (DefenderSimNode a p Q) g \<longrightarrow> wr2 g)\<close>
  using c_set_game_node.exhaust
       apply blast
       apply simp+
  done

fun atk_strat :: \<open>('s, 'a) c_set_game_node list \<Rightarrow> ('s, 'a) c_set_game_node\<close>
  where 
\<open>atk_strat ((AttackerNode p Q)#play) = 
(SOME g'. c_set_game_moves (AttackerNode p Q) g' \<and> wr g')\<close>
| \<open>atk_strat _ = undefined\<close>

(*
lemma attacker_wins_in_winning_region: 
  assumes \<open>wr (AttackerNode p Q)\<close>
  shows \<open>player1_winning_strategy atk_strat (AttackerNode p Q)\<close>
  (*unfolding player1_winning_strategy_def*)
proof -
  obtain g where \<open>c_set_game_moves (AttackerNode p Q) g \<and> wr g\<close> using assms sledgehammer
  show ?thesis sorry
qed
*)

lemma tau_obs_implies_delay: 
  assumes 
    \<open>q \<Rightarrow>^\<tau> q'\<close> 
    \<open>q' \<longmapsto>a q''\<close>
  shows \<open>q =\<rhd>a q''\<close>
proof -
  have \<open>q  \<longmapsto>* tau q' \<and> q'  \<longmapsto>a q''\<close> using assms by auto
  then show ?thesis
    using steps.step by blast
qed

lemma Atk_node_wins_if_Q_is_empty: 
  assumes \<open>Q = {}\<close>
  shows \<open>wr (AttackerNode p Q)\<close>
proof - 
  have atk_move: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p Q)\<close> 
    by (simp add: steps.refl)
  have \<open>wr (DefenderSwapNode p Q)\<close> using assms
    by (metis c_game_with_attacker_formula_axioms c_game_with_attacker_formula_def)
  thus ?thesis using atk_move 
    by (metis c_game_with_attacker_formula_axioms c_game_with_attacker_formula_def)
qed


lemma Atk_node_wins_in_2_moves: 
  assumes 
        \<open>wr (AttackerNode p' (dsuccs a Q))\<close>
        \<open>p =\<rhd>a p'\<close>
        \<open>\<not>tau a\<close>
  shows \<open>wr (AttackerNode p Q)\<close>
proof - 
  have AtkToSim: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSimNode a p' Q)\<close>
    using assms(2, 3) by simp
  have \<open>\<forall>g. c_set_game_moves 
(DefenderSimNode a p' Q) g \<longrightarrow> (g = AttackerNode p' (dsuccs a Q))\<close>
    by (simp add: move_DefSim_to_AtkNode)
  hence \<open>wr (DefenderSimNode a p' Q)\<close> using assms(1)
    by (metis c_game_with_attacker_formula_axioms c_game_with_attacker_formula_def)
  thus ?thesis using AtkToSim     
    by (metis c_game_with_attacker_formula_axioms c_game_with_attacker_formula_def)
qed


lemma dist_formula_implies_wr_inclusion: 
  assumes 
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>is_dist_set \<phi> p Q\<close>
  shows \<open>wr (AttackerNode p Q)\<close>
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
        hence \<open>wr (AttackerNode p' (dsuccs a Q))\<close> 
          using Atk_node_wins_if_Q_is_empty dsuccs_empty by auto
        thus \<open>wr (AttackerNode p Q)\<close>
          using Atk_node_wins_in_2_moves False p'_def by blast
      qed
    next
      case False
      hence wr_pred_atk_node: \<open>wr (AttackerNode p' (dsuccs a Q))\<close> using Obs.hyps phi_distinguishing by auto
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
          wr ((AttackerNode q1 P1))\<close> 
      using Conj.hyps Ex_i by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g \<longrightarrow> 
          (\<exists> q1 P1. g = (AttackerNode q1 P1))\<close> 
      using move_DefSwap_to_AtkNode by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g \<longrightarrow> wr g\<close> 
      using all_atk_succs_in_wr by auto
    hence \<open>wr (DefenderSwapNode p' Q)\<close> 
      by (metis c_game_with_attacker_formula_axioms c_game_with_attacker_formula_def)
    then show ?case using atk_move
      by (metis c_game_with_attacker_formula_axioms c_game_with_attacker_formula_def)
  qed
qed

end
end
