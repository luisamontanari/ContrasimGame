theory HML_Strategies_Game
  imports
    Contrasim_Set_Game
    HM_Logic_Infinitary
begin

context c_set_game
begin

text \<open>This construction of attacker formulas from a game only works if \<open>strat\<close> is a (non-cyclic)
  attacker strategy. (If it's winning and sound, the constructed formula should be distinguishing.)\<close>

function attack_formula :: \<open>('s, 'a) c_set_game_node posstrategy \<Rightarrow> ('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula\<close> where
  \<open>attack_formula strat (AttackerNode p Q) =
    attack_formula strat (strat ((AttackerNode p Q)))\<close>
| \<open>attack_formula strat (DefenderSimNode a p Q) =
    (HML_poss a (attack_formula strat (AttackerNode p Q)))\<close>
| \<open>attack_formula strat (DefenderSwapNode p Q) =
    (HML_weaknor Q (\<lambda>q. (attack_formula strat (AttackerNode q {p}))))\<close>

end
end
