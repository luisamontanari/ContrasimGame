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

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name HML_formula} |> Option.map #ctrs\<close>

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name nat} |> Option.map #ctrs\<close>



fun attack_strat :: \<open>('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula \<Rightarrow> ('s, 'a) c_set_game_node\<close>
  where
  
  \<open>attack_strat (AttackerNode p Q) (\<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) = DefenderSimNode a (SOME p' . p =\<rhd>a p' \<and> p' \<Turnstile> \<phi> \<and>
                                           (\<forall>q'. q' \<in> dsuccs a Q \<longrightarrow> is_dist \<phi> p' q')) Q\<close> |

  \<open>attack_strat (AttackerNode p Q) (HML_weaknor I F) = DefenderSwapNode (SOME p' . p \<Rightarrow>^\<tau> p' \<and> 
                                           (\<forall>q'. q' \<in> weak_tau_succs Q  \<longrightarrow>
                                           (\<exists>i. i \<in> I \<and> is_dist (F i) q' p'))) Q\<close> |

  \<open>attack_strat _ _ = undefined\<close>

end
end
