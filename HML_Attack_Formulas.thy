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
(* +
fixes
  wr :: \<open>('s, 'a) c_set_game_node \<Rightarrow> bool\<close>
assumes 
  \<open>\<forall>p. wr (DefenderSwapNode p {})\<close>
  \<open>\<forall>atk_node. \<exists>g. (c_set_game_moves atk_node g) \<and> wr g \<longrightarrow> wr atk_node\<close>
  \<open>\<forall>def_node g. (c_set_game_moves def_node g) \<and> wr g \<longrightarrow> wr def_node\<close>
*)
begin

function wr ::  \<open>('s, 'a) c_set_game_node \<Rightarrow> bool\<close> 
  where 
    \<open>wr (DefenderSwapNode p Q) = (if Q = {} then True
     else (\<forall>g. c_set_game_moves (DefenderSwapNode p Q) g \<and> wr g))\<close>
  | \<open>wr (AttackerNode p Q) = (\<exists>g. c_set_game_moves (AttackerNode p Q) g \<and> wr g)\<close>
  | \<open>wr (DefenderSimNode a p Q) = (\<forall>g. c_set_game_moves (DefenderSimNode a p Q) g \<and> wr g)\<close>
  using c_set_game_node.exhaust apply blast
       apply simp
       apply simp
       apply simp
       apply simp
       apply simp
  apply simp
  done
fun is_dist ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close>
  where
   \<open>is_dist \<phi> p q = (p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>)\<close>


lemma all_states_sat_empty_conjunction:
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
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p'' \<and> p'' \<Turnstile> \<langle>a\<rangle>\<phi>\<close>
    using assms 
    by auto
  thus ?thesis
    using satisfies.simps(4) steps_concat tau_tau by blast
qed


lemma dist_formula_implies_wr_inclusion: 
  assumes \<open>\<phi> \<in> HML_weak_formulas\<close>
  shows \<open>\<forall>q. q \<in> Q \<and> (is_dist \<phi> p q) \<Longrightarrow> wr (AttackerNode p Q)\<close>
proof (induct arbitrary: p Q rule: HML_weak_formulas.induct[OF assms])
  case Base: 1
  have \<open>\<forall>q. q \<Turnstile> (HML_weaknor {} (\<lambda>i. HML_true))\<close>
    by (simp add: all_states_sat_empty_conjunction)
  then show ?case
    using Base is_dist.elims(2) by blast
next
  case Obs: (2 \<phi> a)
  thus ?case 
    by (meson is_dist.elims(2))
next
  case Conj: (3 I F)
  then show ?case by auto
qed

(*
fun attack_strat :: \<open>('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula \<Rightarrow> ('s, 'a) c_set_game_node\<close>
  where
  
  \<open>attack_strat (AttackerNode p Q) (\<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) = DefenderSimNode a (SOME p' . p =\<rhd>a p' \<and> p' \<Turnstile> \<phi> \<and>
                                           (\<forall>q'. q' \<in> dsuccs a Q \<longrightarrow> is_dist \<phi> p' q')) Q\<close> |

  \<open>attack_strat (AttackerNode p Q) (HML_weaknor I F) = DefenderSwapNode (SOME p' . p \<Rightarrow>^\<tau> p' \<and> 
                                           (\<forall>q'. q' \<in> weak_tau_succs Q  \<longrightarrow>
                                           (\<exists>i. i \<in> I \<and> is_dist (F i) q' p'))) Q\<close> |

  \<open>attack_strat _ _ = undefined\<close>
  apply auto
  apply (simp add: lts_tau.HML_weaknor_def)
  sledgehammer
*)

end
end
