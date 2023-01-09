section \<open>Simple Games\<close>

theory Simple_Game
imports
  Main
begin

text \<open>Simple games are games where player0 wins all infinite plays.\<close>
locale simple_game =
fixes
  game_move :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<longmapsto>\<heartsuit> _" [70, 70] 80) and
  player0_position :: \<open>'s \<Rightarrow> bool\<close> and
  initial :: 's
begin

definition player1_position :: \<open>'s \<Rightarrow> bool\<close>
  where \<open>player1_position s \<equiv> \<not> player0_position s\<close>

\<comment>\<open>plays (to be precise: play prefixes) are lists. we model them 
  with the most recent move at the beginning. (for our purpose it's enough to consider finite plays)\<close>
type_synonym ('s2) play = \<open>'s2 list\<close>
type_synonym ('s2) strategy = \<open>'s2 play \<Rightarrow> 's2\<close>

inductive_set plays :: \<open>'s play set\<close> where
  \<open>[initial] \<in> plays\<close> |
  \<open>p#play \<in> plays \<Longrightarrow> p \<longmapsto>\<heartsuit> p' \<Longrightarrow> p'#p#play \<in> plays\<close>

\<comment>\<open>plays for a given player 0 strategy\<close>
inductive_set plays_for_strategy :: \<open>'s strategy \<Rightarrow> 's play set\<close> for f where
  init: \<open>[initial] \<in> plays_for_strategy f\<close> |
  p0move: \<open>n0#play \<in> plays_for_strategy f \<Longrightarrow> player0_position n0 \<Longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)
    \<Longrightarrow> (f (n0#play))#n0#play \<in> plays_for_strategy f\<close> |
  p1move: \<open>n1#play \<in> plays_for_strategy f \<Longrightarrow> player1_position n1 \<Longrightarrow> n1 \<longmapsto>\<heartsuit> n1'
    \<Longrightarrow> n1'#n1#play \<in> plays_for_strategy f\<close>

lemma strategy_step:
  assumes
    \<open>n0 # n1 # rest \<in> plays_for_strategy f\<close>
    \<open>player0_position n1\<close>
  shows
    \<open>f (n1 # rest) = n0\<close>
  using assms
  by (induct rule: plays_for_strategy.cases, auto simp add: simple_game.player1_position_def)

definition positional_strategy :: \<open>'s strategy \<Rightarrow> bool\<close> where
  \<open>positional_strategy f \<equiv> \<forall>r1 r2 n. f (n # r1) = f (n # r2)\<close>

text \<open>a strategy is sound if it only decides on enabled transitions.\<close>
definition sound_strategy :: \<open>'s strategy \<Rightarrow> bool\<close> where
  \<open>sound_strategy f \<equiv>
    \<forall> n0 play . n0#play \<in> plays_for_strategy f \<and> player0_position n0 \<longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)\<close>

lemma strategy_plays_subset:
  assumes \<open>play \<in> plays_for_strategy f\<close>
  shows \<open>play \<in> plays\<close>
  using assms by (induct rule: plays_for_strategy.induct, auto simp add: plays.intros)

lemma no_empty_plays:
  assumes \<open>[] \<in> plays\<close>
  shows \<open>False\<close> 
  using assms plays.cases by blast

text \<open>player1 wins a play if the play has reached a deadlock where it's player0's turn\<close>

definition player1_wins :: \<open>'s play \<Rightarrow> bool\<close> where
  \<open>player1_wins play \<equiv> player0_position (hd play) \<and> (\<nexists> p' . (hd play) \<longmapsto>\<heartsuit> p')\<close>

definition player0_winning_strategy :: \<open>'s strategy \<Rightarrow> bool\<close> where
  \<open>player0_winning_strategy f \<equiv> (\<forall> play \<in> plays_for_strategy f . \<not> player1_wins play)\<close>

end

end
