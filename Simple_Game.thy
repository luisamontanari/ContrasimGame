section \<open>Simple Games\<close>

theory Simple_Game
imports
  Main
begin

text \<open>Simple games are games where player0 wins all infinite plays.\<close>
locale simple_game =
fixes
  game_move :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<longmapsto>\<heartsuit> _" [70, 70] 80) and
  player0_position :: \<open>'s \<Rightarrow> bool\<close>
begin

abbreviation player1_position :: \<open>'s \<Rightarrow> bool\<close>
  where \<open>player1_position s \<equiv> \<not> player0_position s\<close>

\<comment>\<open>plays (to be precise: play prefixes) are lists. we model them 
  with the most recent move at the beginning. (for our purpose it's enough to consider finite plays)\<close>
type_synonym ('s2) play = \<open>'s2 list\<close>
type_synonym ('s2) strategy = \<open>'s2 play \<Rightarrow> 's2\<close>
type_synonym ('s2) posstrategy = \<open>'s2 \<Rightarrow> 's2\<close>

definition strategy_from_positional :: \<open>'s posstrategy \<Rightarrow> 's strategy\<close> where
  \<open>strategy_from_positional pf = (\<lambda> play. pf (hd play))\<close>

inductive_set plays :: \<open>'s \<Rightarrow> 's play set\<close> 
  for initial :: 's where
  \<open>[initial] \<in> plays initial\<close> |
  \<open>p#play \<in> plays initial \<Longrightarrow> p \<longmapsto>\<heartsuit> p' \<Longrightarrow> p'#p#play \<in> plays initial\<close>

definition play_continuation :: \<open>'s play \<Rightarrow> 's play \<Rightarrow> bool\<close>
  where \<open>play_continuation p1 p2 \<equiv> (drop (length p2 - length p1) p2) = p1\<close>

\<comment>\<open>plays for a given player 0 strategy\<close>
inductive_set plays_for_0strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> 's play set\<close>
  for f initial where
  init: \<open>[initial] \<in> plays_for_0strategy f initial\<close> |
  p0move: \<open>n0#play \<in> plays_for_0strategy f initial \<Longrightarrow> player0_position n0 \<Longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)
    \<Longrightarrow> (f (n0#play))#n0#play \<in> plays_for_0strategy f initial\<close> |
  p1move: \<open>n1#play \<in> plays_for_0strategy f initial \<Longrightarrow> player1_position n1 \<Longrightarrow> n1 \<longmapsto>\<heartsuit> n1'
    \<Longrightarrow> n1'#n1#play \<in> plays_for_0strategy f initial\<close>

lemma strategy0_step:
  assumes
    \<open>n0 # n1 # rest \<in> plays_for_0strategy f initial\<close>
    \<open>player0_position n1\<close>
  shows
    \<open>f (n1 # rest) = n0\<close>
  using assms
  by (induct rule: plays_for_0strategy.cases, auto)

\<comment>\<open>plays for a given player 1 strategy\<close>
inductive_set plays_for_1strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> 's play set\<close>
  for f initial where
  init: \<open>[initial] \<in> plays_for_1strategy f initial\<close> |
  p0move: \<open>n0#play \<in> plays_for_1strategy f initial \<Longrightarrow> player0_position n0 \<Longrightarrow> n0 \<longmapsto>\<heartsuit> n0'
    \<Longrightarrow> n0'#n0#play \<in> plays_for_1strategy f initial\<close> |
  p1move: \<open>n1#play \<in> plays_for_1strategy f initial \<Longrightarrow> player1_position n1 \<Longrightarrow> n1 \<longmapsto>\<heartsuit> f (n1#play)
    \<Longrightarrow> (f (n1#play))#n1#play \<in> plays_for_1strategy f initial\<close>


definition positional_strategy :: \<open>'s strategy \<Rightarrow> bool\<close> where
  \<open>positional_strategy f \<equiv> \<forall>r1 r2 n. f (n # r1) = f (n # r2)\<close>

text \<open>a strategy is sound if it only decides on enabled transitions.\<close>
definition sound_0strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>sound_0strategy f initial \<equiv>
    \<forall> n0 play . n0#play \<in> plays_for_0strategy f initial \<and> player0_position n0 \<longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)\<close>

definition sound_1strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>sound_1strategy f initial \<equiv>
    \<forall> n1 play . n1#play \<in> plays_for_1strategy f initial \<and> player1_position n1 \<longrightarrow> n1 \<longmapsto>\<heartsuit> f (n1#play)\<close>

lemma strategy0_plays_subset:
  assumes \<open>play \<in> plays_for_0strategy f initial\<close>
  shows \<open>play \<in> plays initial\<close>
  using assms by (induct rule: plays_for_0strategy.induct, auto simp add: plays.intros)
lemma strategy1_plays_subset:
  assumes \<open>play \<in> plays_for_1strategy f initial\<close>
  shows \<open>play \<in> plays initial\<close>
  using assms by (induct rule: plays_for_1strategy.induct, auto simp add: plays.intros)

lemma no_empty_plays:
  assumes \<open>[] \<in> plays initial\<close>
  shows \<open>False\<close> 
  using assms plays.cases by blast

text \<open>player1 wins a play if the play has reached a deadlock where it's player0's turn\<close>

definition player1_wins_immediately :: \<open>'s play \<Rightarrow> bool\<close> where
  \<open>player1_wins_immediately play \<equiv> player0_position (hd play) \<and> (\<nexists> p' . (hd play) \<longmapsto>\<heartsuit> p')\<close>

definition player0_winning_strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>player0_winning_strategy f initial \<equiv> (\<forall> play \<in> plays_for_0strategy f initial . \<not> player1_wins_immediately play)\<close>

definition player0_wins :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>player0_wins s \<equiv> (\<exists> f . player0_winning_strategy f s \<and> sound_0strategy f s)\<close>

lemma stuck_player0_win:
  assumes \<open>player1_position initial\<close> \<open>(\<nexists> p' . initial \<longmapsto>\<heartsuit> p')\<close>
  shows \<open>player0_wins initial\<close>
proof -
  have \<open>\<And>pl. pl \<in> plays initial \<Longrightarrow> pl = [initial]\<close>
  proof -
    fix pl
    assume \<open>pl \<in> plays initial\<close>
    thus \<open>pl = [initial]\<close> using assms(2) by (induct, auto)
  qed
  thus ?thesis using assms(1)
    by (metis list.sel(1) player0_winning_strategy_def player0_wins_def player1_wins_immediately_def
        sound_0strategy_def strategy0_plays_subset)
qed


definition player0_wins_immediately :: \<open>'s play \<Rightarrow> bool\<close> where
  \<open>player0_wins_immediately play \<equiv> player1_position (hd play) \<and> (\<nexists> p' . (hd play) \<longmapsto>\<heartsuit> p')\<close>


\<comment> \<open>in comparison to the defender, the attacker also has to bound the depth of plays.\<close>
definition player1_winning_strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>player1_winning_strategy f initial \<equiv>
    \<exists>maxn. (\<forall> play \<in> plays_for_1strategy f initial . \<not> player0_wins_immediately play \<and> length play \<le> maxn)\<close>

definition player1_wins :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>player1_wins s \<equiv> (\<exists> f . player1_winning_strategy f s \<and> sound_1strategy f s)\<close>



lemma stuck_0_all_strats_win:
  assumes \<open>player0_position initial\<close> \<open>(\<nexists> p' . initial \<longmapsto>\<heartsuit> p')\<close>
  shows  \<open>\<forall>f. player1_winning_strategy f initial\<close>
proof -
  have \<open>\<And>pl. pl \<in> plays initial \<Longrightarrow> pl = [initial]\<close>
  proof -
    fix pl
    assume \<open>pl \<in> plays initial\<close>
    thus \<open>pl = [initial]\<close> using assms(2) by (induct, auto)
  qed
  hence \<open>\<forall>f. (\<forall> play \<in> plays_for_1strategy f initial . \<not> player0_wins_immediately play \<and> length play \<le> 1)\<close>
    by (metis assms(1) butlast.simps(1) butlast_conv_take diff_is_0_eq' 
       le_numeral_extra(4) length_tl list.sel(1, 2) list.size(3) 
       one_eq_numeral_iff player0_wins_immediately_def 
       strategy1_plays_subset take_Cons_numeral take_all_iff)
  thus ?thesis using player1_winning_strategy_def by auto
qed

lemma stuck_player1_win:
 assumes \<open>player0_position initial\<close> \<open>(\<nexists> p' . initial \<longmapsto>\<heartsuit> p')\<close>
  shows \<open>player1_wins initial\<close>
proof -
  have all_plays_stuck: \<open>\<And>pl. pl \<in> plays initial \<Longrightarrow> pl = [initial]\<close>
  proof -
    fix pl
    assume \<open>pl \<in> plays initial\<close>
    thus \<open>pl = [initial]\<close> using assms(2) by (induct, auto)
  qed
  have \<open>sound_1strategy (\<lambda>x. hd x) initial\<close> 
    unfolding sound_1strategy_def 
    using all_plays_stuck assms(1) strategy1_plays_subset by auto
  thus ?thesis unfolding player1_wins_def using assms stuck_0_all_strats_win by auto
qed

end

end
