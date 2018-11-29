theory ImplicitQuorums_2
  imports Main "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

section "personal quorums"

locale personal =
  fixes quorum :: "'node set \<Rightarrow> bool" 
    assumes quorum_union:"\<And> Q Q'  . \<lbrakk>quorum Q; quorum Q'\<rbrakk> \<Longrightarrow> quorum (Q \<union> Q')"
begin

abbreviation quorum_of where 
  "quorum_of p Q \<equiv> quorum Q \<and> p \<in> Q"

definition blocks where
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"


lemma l1:
  assumes "S \<noteq> {}" and "\<And> p . p \<in> S \<Longrightarrow> \<exists> Q . quorum_of p Q \<and> Q \<subseteq> S"
  shows "quorum S" 
proof -
  
  obtain f where "quorum_of p (f p)" and "f p \<subseteq> S" if "p \<in> S" for p using assms(2) 

abbreviation blocked where "blocked R \<equiv> {p . blocks R p}"

lemma blocked_blocked_eq_blocked:
  "blocks (blocked R) q = blocks R q" 
  unfolding blocks_def by fastforce

end

locale wb = personal quorum for quorum :: "'node set \<Rightarrow> bool"  +
  fixes W::"'node set"
begin

abbreviation B where "B \<equiv> -W"

definition is_intact where 
  "is_intact I \<equiv> I \<subseteq> W \<and> quorum I
      \<and> (\<forall> Q Q' . quorum Q \<and> quorum Q' \<and> Q \<inter> I \<noteq> {} \<and> Q' \<inter> I \<noteq> {} \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition L where "L \<equiv> W - (blocked B)"

lemma l1: "p \<in> L \<Longrightarrow> \<exists> Q  \<subseteq> W. quorum_of p Q" 
  unfolding L_def blocks_def using DiffD2 by auto

lemma l2:
  assumes "p \<in> L" shows "\<exists> Q \<subseteq> L . quorum_of p Q"
proof -
  have False if "\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> (-L) \<noteq> {}"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> W" 
      using l1 \<open>p \<in> L\<close> by auto 
    moreover have "Q \<inter> (-L) \<noteq> {}" 
      using that \<open>quorum_of p Q\<close> by simp
    ultimately show False unfolding L_def blocks_def by auto
  qed
  thus ?thesis
    by fastforce 
qed


lemma "L \<noteq> {} \<Longrightarrow> quorum L" using quorum_union 

lemma intact_union:
  assumes "is_intact I\<^sub>1" and "is_intact I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_intact (I\<^sub>1\<union> I\<^sub>2)"
proof -
  have "I\<^sub>1 \<union> I\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_intact_def by auto 
  moreover
  have "quorum (I\<^sub>1\<union>I\<^sub>2)" 
    using \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> unfolding is_intact_def using quorum_union by auto
  moreover 
  have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" 
    if "quorum Q\<^sub>1" and "quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" and "Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "Q\<^sub>1 \<inter> I \<noteq> {}" and "Q\<^sub>2 \<inter> I \<noteq> {}" and "I = I\<^sub>1 \<or> I = I\<^sub>2" for I
      using \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> \<open>quorum Q\<^sub>1\<close> \<open>quorum Q\<^sub>2\<close>
      by (metis \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> personal.is_intact_def personal_axioms that) 
    moreover
    have \<open>W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "is_intact I\<^sub>1" and "is_intact I\<^sub>2" 
      and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}"
    for I\<^sub>1 I\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      note \<open>I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}\<close>
      moreover have "quorum I\<^sub>2" using \<open>is_intact I\<^sub>2\<close> unfolding is_intact_def by auto
      ultimately have "I\<^sub>2 \<inter> Q\<^sub>1 \<noteq> {}" using \<open>is_intact I\<^sub>1\<close>  \<open>quorum Q\<^sub>1\<close> \<open>Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}\<close> 
        unfolding is_intact_def using inf_sup_aci(1) by blast 
      thus "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" using \<open>is_intact I\<^sub>2\<close> \<open>quorum Q\<^sub>2\<close> \<open>quorum Q\<^sub>1\<close> \<open>Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}\<close>
        unfolding is_intact_def by blast
    qed
    ultimately show ?thesis using assms that by auto
  qed
  ultimately show ?thesis using assms
    unfolding is_intact_def by simp
qed

end

section slices

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>The well-behaved nodes\<close>
begin

definition B where "B \<equiv> -W"

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q - B . \<exists> Sl \<in> slices p . Sl \<subseteq> Q"

definition blocked where
  "blocked R p \<equiv> \<forall> Q . quorum Q \<and> p \<in> Q \<longrightarrow> Q \<inter> R \<noteq> {}"

lemma "blocked {p . blocked R p} p = blocked R p"

end