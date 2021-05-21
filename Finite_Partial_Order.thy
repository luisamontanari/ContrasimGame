section \<open>Preliminaries\<close>

subsection \<open>Some Utilities for Finite Partial Orders\<close>

text \<open>For some reason there seems to be no Isaeblle support for maximal elements in finite regions
  of incomplete partial orders (such as the transitive step relation in cycle-compressed transition
  systems ;).)\<close>

theory Finite_Partial_Order
  imports Main
begin

context preorder
begin

lemma foldl_max_inflation:
  \<open>foldl max x0 xs \<le> foldl max x0 (xs @ [x])\<close>
  unfolding foldl_append foldl.simps 
  by (simp add: ord.max_def)

lemma foldl_max_soundness:
  shows
    \<open>foldl max x0 (x0 # xs) \<in> set (x0 # xs)\<close>
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: max_def)
next
  case (snoc x xs)
  then show ?case  unfolding foldl_append max_def by auto
qed

lemma foldl_max_maximal:
  shows
    \<open>\<forall> y \<in> set (x0 # xs). foldl max x0 (x0 # xs) \<le> y \<longrightarrow> y \<le> foldl max x0 (x0 # xs)\<close>
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: max_def)
next
  case (snoc x xs)
  then show ?case unfolding foldl.simps foldl_append
    by (metis Un_insert_right append_Nil2 foldl_Cons insert_iff list.simps(15) local.order_refl
        local.order_trans ord.max_def set_append snoc.hyps)
qed
end

context order \<comment>\<open>that is: partial order\<close>
begin

lemma finite_max:
  fixes q
  defines \<open>above_q \<equiv> {q'. q \<le> q'}\<close>
  assumes
    \<open>finite above_q\<close>
  shows
    \<open>\<exists> q_max. q_max \<in> above_q \<and> (\<forall> q''\<in> above_q. q_max \<le> q'' \<longrightarrow> q'' = q_max)\<close>
proof -
  have \<open>q \<in> above_q\<close> unfolding above_q_def by blast
  then obtain above_list where above_list_spec: \<open>set (q#above_list) = above_q\<close>
    using \<open>finite above_q\<close> finite_list by auto
  define q_max where \<open>q_max \<equiv> foldl max q (q#above_list)\<close>
  have \<open>q_max \<in> above_q\<close>
    unfolding q_max_def above_list_spec[symmetric] using foldl_max_soundness .
  moreover have \<open>\<forall> q'' \<in> above_q. q_max \<le> q'' \<longrightarrow> q'' = q_max\<close>
    unfolding q_max_def above_list_spec[symmetric] using foldl_max_maximal antisym by blast
  ultimately show ?thesis by blast
qed

end

end