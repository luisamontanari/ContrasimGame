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
  winning_dist_decreasing: \<open>winning_dist (strat pos) < winning_dist pos\<close>
begin

text \<open>This construction of attacker formulas from a game only works if \<open>strat\<close> is a (non-cyclic)
  attacker strategy. (If it's winning and sound, the constructed formula should be distinguishing.)\<close>

function attack_formula :: \<open>('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula\<close> where
  \<open>attack_formula (AttackerNode p Q) =
    attack_formula (strat ((AttackerNode p Q)))\<close>
| \<open>attack_formula (DefenderSimNode a p Q) =
    (HML_poss a (attack_formula (AttackerNode p Q)))\<close>
| \<open>attack_formula (DefenderSwapNode p Q) =
    (HML_weaknor Q (\<lambda>q. (attack_formula (AttackerNode q {p}))))\<close>
  using c_set_game_defender_node.cases
  by (auto, blast)

termination attack_formula
  using winning_dist_decreasing
    wf_measure[of winning_dist]
  unfolding wf_def
  by auto

end
end
