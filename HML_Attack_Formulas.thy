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
  wr :: \<open>('s, 'a) c_set_game_node \<Rightarrow> bool\<close>
assumes 
  \<open>\<forall>p. wr (DefenderSwapNode p {})\<close>
  \<open>\<forall>atk_node. \<exists>g. (c_set_game_moves atk_node g) \<and> wr g \<longrightarrow> wr atk_node\<close>
  \<open>\<forall>def_node g. (c_set_game_moves def_node g) \<and> wr g \<longrightarrow> wr def_node\<close>

begin

fun is_dist ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close>
  where
   \<open>is_dist \<phi> p q = (p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>)\<close>

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name HML_formula} |> Option.map #ctrs\<close>

(*
(induct arbitrary: n p Q rule: plays_for_0strategy.induct[OF assms(3)])
*)

thm  HML_weak_formulas.induct

lemma all_states_sat_empty_conjunction:
  shows \<open>\<And>q. q \<Turnstile> (HML_weaknor {} (\<lambda>i. HML_true))\<close>
proof - 
  show ?thesis sorry
qed


lemma beweisziel: 
  assumes \<open>\<phi> \<in> HML_weak_formulas\<close>
  shows \<open>\<And>q. q \<in> Q \<and>(is_dist \<phi> p q) \<Longrightarrow> wr (AttackerNode p Q)\<close>
proof (induct rule: HML_weak_formulas.induct[OF assms])
  case 1
  have \<open>\<forall>q. q \<Turnstile> (HML_weaknor {} (\<lambda>i. HML_true))\<close> sledgehammer
  then show ?case sorry
next
  case (2 \<phi> a)
  then show ?case sorry
next
  case (3 I F)
  then show ?case sorry
qed


(*
proof (induct \<phi> rule: HML_weak_formulas.induct[OF assms])
qed

*)

(*

assumptions in local: 
(oder lemmas mit sorry)
es gibt winning region: ist abgeschlossen
-wenn attacker von p in winning region mit einem zug kommt, ist p in wr
-wenn defender mit allen zügen von g in wr kommen MUSS, dann ist g in wr


kann man vllt auch induktiv hinschreiben? 
(mit base: Swap(p, {})_d  ist in wr )

beweisziel: phi dist's p from Q \<longrightarrow> (p, Q) in wr


*)

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


end
