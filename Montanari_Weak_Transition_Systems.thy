subsection \<open>Montanari Weak Transition Systems\<close>

theory Montanari_Weak_Transition_Systems
imports
  Weak_Transition_Systems
  Strong_Relations
  Weak_Relations_modified
begin

context lts_tau
begin

lemma step_tau_concat: 
  assumes 
    \<open>q \<Rightarrow>^a q'\<close>
    \<open>q' \<Rightarrow>^\<tau> q1\<close>
  shows \<open>q \<Rightarrow>^a q1\<close>
proof - 
  show ?thesis using assms steps_concat tau_tau by blast 
qed

lemma tau_step_concat: 
  assumes 
    \<open>q \<Rightarrow>^\<tau> q'\<close>
    \<open>q' \<Rightarrow>^a q1\<close>
  shows \<open>q \<Rightarrow>^a q1\<close>
proof - 
  show ?thesis using assms steps_concat tau_tau by blast 
qed


lemma tau_word_concat: 
  assumes
    \<open>q \<Rightarrow>^\<tau> q'\<close> 
    \<open>q' \<Rightarrow>$A q1\<close> 
  shows \<open>q \<Rightarrow>$A q1\<close> using assms
proof (cases A)
  case Nil
  hence \<open>q' \<Rightarrow>^\<tau> q1\<close> using assms by auto
  thus ?thesis using Nil assms steps_concat tau_tau weak_step_seq.simps by blast
next
  case (Cons a A)
  then obtain q'' where  \<open>q' \<Rightarrow>^a q''\<close> and A_step:  \<open>q'' \<Rightarrow>$A q1 \<close> using assms by auto
  hence \<open>q \<Rightarrow>^a q''\<close> using tau_step_concat[OF assms(1)] by auto
  then show ?thesis using Cons A_step  \<open>q \<Rightarrow>^a q''\<close> by auto 
qed


lemma rev_seq_split : 
  assumes \<open>q \<Rightarrow>$ (xs @ [x])  q1\<close>
  shows \<open>\<exists>q'. q \<Rightarrow>$xs q' \<and> q' \<Rightarrow>^x q1\<close> using assms
proof (induct xs arbitrary: q)
  case Nil
  hence \<open>q \<Rightarrow>$ [x]  q1\<close> by auto
  hence x_succ: \<open>q \<Rightarrow>^x q1\<close> by blast 
  have \<open>q \<Rightarrow>$[] q\<close> by (simp add: steps.refl) 
  then show ?case using x_succ by auto
next
  case (Cons a xs)
  then obtain q' where q'_def: \<open>q \<Rightarrow>^a q' \<and> q' \<Rightarrow>$(xs@[x]) q1\<close> by auto
  then obtain q'' where \<open>q' \<Rightarrow>$ xs  q'' \<and> q'' \<Rightarrow>^x  q1\<close> using Cons.hyps[of \<open>q'\<close>] by auto
  then show ?case using q'_def by auto
qed

lemma rev_seq_concat: 
  assumes 
    \<open>q \<Rightarrow>$as q'\<close> 
    \<open>q'\<Rightarrow>$A q1\<close>
  shows \<open>q \<Rightarrow>$(as@A) q1\<close> using assms
proof (induct as arbitrary: A q' rule: rev_induct)
  case Nil
  hence \<open>q \<Rightarrow>^\<tau> q'\<close> by auto
  hence \<open>q \<Rightarrow>^\<tau> q' \<and> q' \<Rightarrow>$A q1\<close> using Nil.prems(2) by blast 
  hence \<open>q \<Rightarrow>$A q1\<close> using tau_word_concat by auto 
  then show ?case by simp
next
  case (snoc x xs)
  hence \<open>\<exists>q''. q \<Rightarrow>$xs q'' \<and> q'' \<Rightarrow>^x q'\<close> using rev_seq_split by simp
  then obtain q'' where q_def: \<open>q \<Rightarrow>$xs q''\<close> \<open>q'' \<Rightarrow>^x q'\<close> by auto
  from snoc.prems(2) have \<open>q' \<Rightarrow>$A q1\<close> by blast
  hence \<open>q'' \<Rightarrow>$(x#A) q1\<close> using q_def by auto
  hence \<open>q'' \<Rightarrow>$([x]@A) q1\<close> by auto
  then show ?case using snoc.hyps[of \<open>q''\<close> \<open>[x]@A\<close>] q_def by auto
qed

lemma rev_seq_step_concat : 
  assumes 
    \<open>q \<Rightarrow>$as q'\<close> 
    \<open>q'\<Rightarrow>^a q1\<close>
  shows \<open>q \<Rightarrow>$(as@[a]) q1\<close>
proof - 
  from assms(2) have \<open>q'\<Rightarrow>$[a] q1\<close> by blast
  thus ?thesis using rev_seq_concat assms(1) by auto
qed

lemma word_tau_concat: 
  assumes 
    \<open>q \<Rightarrow>$A q'\<close>
    \<open>q' \<Rightarrow>^\<tau> q1\<close> 
  shows \<open>q \<Rightarrow>$A q1\<close> 
proof - 
  from assms(2) have \<open>q' \<Rightarrow>$[] q1\<close>
    using tau_tau weak_step_seq.simps(1) by blast 
  thus ?thesis using assms(1) rev_seq_concat
    by (metis append.right_neutral) 
qed

lemma list_rev_split : 
  assumes \<open>A \<noteq> []\<close>
  shows \<open>\<exists>as a. A = as@[a]\<close>
proof - 
  show ?thesis using assms rev_exhaust by blast 
qed


primrec taufree :: \<open>'a list \<Rightarrow> 'a list\<close>
  where
    \<open>taufree [] = []\<close>
  | \<open>taufree (a#A) = (if tau a then taufree A else a#(taufree A))\<close>


lemma weak_step_over_tau : 
  assumes 
    \<open>p \<Rightarrow>$A p'\<close>
  shows \<open>p \<Rightarrow>$(taufree A) p'\<close> using assms
proof (induct A arbitrary: p)
  case Nil
  thus ?case by auto
next
  case (Cons a as)
  then obtain p0 where \<open>p \<Rightarrow>^a p0\<close> \<open>p0\<Rightarrow>$as p'\<close> by auto
  then show ?case
  proof (cases \<open>tau a\<close>)
    case True
    hence \<open>p \<Rightarrow>$as p'\<close> using tau_word_concat \<open>p \<Rightarrow>^a p0\<close> \<open>p0 \<Rightarrow>$ as p'\<close> tau_tau by blast
    hence \<open>p \<Rightarrow>$ (taufree as)  p'\<close> using Cons by auto
    thus \<open>p \<Rightarrow>$ (taufree (a#as))  p'\<close> using True by auto
  next
    case False
    hence rec: \<open>taufree (a#as) = a#(taufree as)\<close> by auto
    hence \<open>p0 \<Rightarrow>$ (taufree as)  p'\<close> using \<open>p0\<Rightarrow>$as p'\<close> Cons by auto
    hence \<open>p \<Rightarrow>$(a#(taufree as)) p'\<close> using  \<open>p \<Rightarrow>^a p0\<close> by auto
    then show ?thesis using rec by auto
  qed
qed

lemma app_tau_taufree_list : 
  assumes 
    \<open>\<forall>a \<in> set A. \<not>tau a\<close>
    \<open>b = \<tau>\<close>
  shows \<open>A = taufree (A@[b])\<close> using assms(1)
proof (induct A)
  case Nil
  then show ?case using assms by simp
next
  case (Cons x xs)
  have \<open>\<forall>a\<in>set xs. \<not> tau a\<close> \<open>\<not>tau x\<close> using assms(1) butlast_snoc Cons by auto 
  hence last: \<open>xs = taufree (xs @ [b])\<close> using Cons by auto
  have \<open>taufree (x#xs@[b]) = x#taufree (xs @ [b])\<close> using \<open>\<not>tau x\<close> by auto
  hence \<open>x # xs = x# taufree (xs@ [b])\<close> using last by auto
  then show ?case using Cons.prems last by auto 
qed

definition succs :: "'a \<Rightarrow> 's set \<Rightarrow> 's set" where
\<open>succs a Q  = {q1. \<exists>q\<in> Q. q \<Rightarrow>^a q1}\<close> 

primrec succs_seq_rec :: "'a list \<Rightarrow> 's set \<Rightarrow> 's set" where
\<open>succs_seq_rec [] Q  = Q\<close> | 
\<open>succs_seq_rec (a#as) Q  = succs a (succs_seq_rec as Q)\<close>

lemma in_s_implies_word_reachable : 
  assumes 
    \<open>q' \<in> succs_seq_rec (rev A) {q}\<close>
  shows \<open>q \<Rightarrow>$A q'\<close> using assms
proof (induct arbitrary: q' rule: rev_induct) 
  case Nil
  hence \<open>q' = q\<close> by auto
  hence \<open>q \<Rightarrow>^\<tau> q'\<close> by (simp add: steps.refl) 
  thus \<open>q \<Rightarrow>$[] q'\<close> by simp
next
  case (snoc a as)
  hence \<open>q' \<in> succs_seq_rec (a#(rev as)) {q}\<close> by simp
  hence \<open>q' \<in> succs a (succs_seq_rec (rev as) {q})\<close> by simp
  then obtain q0 where \<open>q0 \<in> succs_seq_rec (rev as) {q}\<close> 
    and \<open>q0 \<Rightarrow>^a q'\<close> using succs_def  by auto
  hence \<open>q \<Rightarrow>$as q0\<close> using snoc.hyps by auto
  thus \<open>q \<Rightarrow>$(as @ [a]) q'\<close> using \<open>q0 \<Rightarrow>^a q'\<close> rev_seq_step_concat by auto 
qed

lemma word_reachable_implies_in_s : 
  assumes 
    \<open>q \<Rightarrow>$A q'\<close>
    \<open>A \<noteq> []\<close>
  shows \<open>q' \<in> succs_seq_rec (rev A) {q}\<close> using assms(1)
proof (induct arbitrary: q' rule: rev_nonempty_induct[OF assms(2)])
  case single: (1 a)
  hence \<open>q \<Rightarrow>^a q'\<close> by blast
  hence \<open>q' \<in> succs a {q}\<close> using succs_def by blast
  thus ?case by simp 
next
  case snoc: (2 a as)
  then obtain q0 where \<open>q \<Rightarrow>$as q0\<close> and \<open>q0 \<Rightarrow>^a q'\<close> using rev_seq_split by blast 
  hence in_succs: \<open>q0 \<in> succs_seq_rec (rev as) {q}\<close> using snoc.hyps by auto
  hence \<open>\<exists>q0 \<in> succs_seq_rec (rev as) {q}. q0 \<Rightarrow>^a q'\<close> using \<open>q0 \<Rightarrow>^a q'\<close> by auto
  hence \<open>q' \<in> succs a (succs_seq_rec (rev as) {q})\<close> using succs_def by auto
  hence \<open>q' \<in> succs_seq_rec (a#(rev as)) {q}\<close> by simp
  thus ?case by simp
qed

lemma simp_succs_seq_rev: 
  assumes 
    \<open>Q = succs_seq_rec (rev A) {q0}\<close>
  shows 
    \<open>succs a Q = succs_seq_rec (rev (A@[a])) {q0}\<close>
proof - 
  show ?thesis by (simp add: assms) 
qed

end 
end