theory ImplicitQuorums_2
  imports Main "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

section "quorums quorums"

locale quorums =
  fixes quorum :: "'node set \<Rightarrow> bool" 
    assumes quorum_union:"\<And> Q Q'  . \<lbrakk>quorum Q; quorum Q'\<rbrakk> \<Longrightarrow> quorum (Q \<union> Q')"
begin

abbreviation quorum_of where 
  "quorum_of p Q \<equiv> quorum Q \<and> p \<in> Q"

definition blocks where
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"

lemma l1:
  assumes "finite S" and "S \<noteq> {}" and "\<And> p . p \<in> S \<Longrightarrow> \<exists> Q . quorum_of p Q \<and> Q \<subseteq> S"
  shows "quorum S" 
    \<comment> \<open>This is trivial by the quorum union property but seems clumsy to prove in Isabelle/HOL\<close>
proof -
  obtain f where "quorum_of p (f p)" and "f p \<subseteq> S" if "p \<in> S" for p using assms(3) by (auto; metis)
  have "\<Union> {f p | p . p \<in> S} = S"
  proof -
    have "\<forall> p \<in> S . p \<in> f p \<and> f p \<subseteq> S"
      by (simp add: \<open>\<And>p. p \<in> S \<Longrightarrow> f p \<subseteq> S\<close> \<open>\<And>p. p \<in> S \<Longrightarrow> quorum_of p (f p)\<close>)  
    thus "\<Union> {f p | p . p \<in> S} = S" by auto
  qed
  moreover
  have "quorum (\<Union> {f p | p . p \<in> S})"
  proof -
    have "wf {(X, Y). X \<subset> Y \<and> finite Y}" by (metis finite_psubset_def wf_finite_psubset)
      \<comment> \<open>We are going to use well-founded induction\<close>
    moreover
    have "\<forall> p \<in> S . p \<in> f p \<and> quorum (f p)"
      by (simp add: \<open>\<And>p. p \<in> S \<Longrightarrow> f p \<subseteq> S\<close> \<open>\<And>p. p \<in> S \<Longrightarrow> quorum_of p (f p)\<close>) 
    moreover note \<open>S \<noteq> {}\<close> and \<open>finite S\<close>
    ultimately 
    show "quorum (\<Union> {f p | p . p \<in> S})" 
    proof (induct S rule:wf_induct_rule) 
      \<comment> \<open>Is this also called Noetherian induction?\<close>
      case (less S) 
      obtain S' x where "S = insert x S'" and "S' \<noteq> S" using \<open>S \<noteq> {}\<close> \<open>finite S\<close>
        by (metis finite.cases insertI1 mk_disjoint_insert)
      have "S' \<subset> S" using \<open>S = insert x S'\<close> \<open>S' \<noteq> S\<close> by auto
      moreover have "\<forall> p \<in> S' . p \<in> f p \<and> quorum (f p)"
        by (simp add: \<open>\<forall> p \<in> S . p \<in> f p \<and> quorum (f p)\<close> \<open>S = insert x S'\<close>) 
      moreover have "finite S'"
        using \<open>finite S\<close> \<open>S = insert x S'\<close> by auto 
      moreover note \<open>finite S\<close> less.hyps
      ultimately have "quorum (\<Union>{f p | p . p \<in> S'})" if "S' \<noteq> {}" using that by auto
      moreover have "{f p | p . p \<in> S} = insert (f x) {f p | p . p \<in> S'}" 
        using \<open>S = insert x S'\<close> by auto
      moreover have "quorum (f x)"
        by (simp add: \<open>\<forall> p \<in> S . p \<in> f p \<and> quorum (f p)\<close> \<open>S = insert x S'\<close>)
      ultimately show ?case using quorum_union 
        by (cases "S' = {}", auto)
    qed
  qed
  ultimately show ?thesis by simp 
qed

abbreviation blocked where "blocked R \<equiv> {p . blocks R p}"

lemma blocked_blocked_eq_blocked:
  "blocks (blocked R) q = blocks R q" 
  unfolding blocks_def by fastforce

end

subsection "Intact sets"

locale wb = quorums quorum for quorum :: "'node set \<Rightarrow> bool"  +
  fixes W::"'node set"
begin

abbreviation B where "B \<equiv> -W"

definition is_intact where 
  "is_intact I \<equiv> I \<subseteq> W \<and> quorum I
      \<and> (\<forall> Q Q' . quorum Q \<and> quorum Q' \<and> Q \<inter> I \<noteq> {} \<and> Q' \<inter> I \<noteq> {} \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

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
      by (metis \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> is_intact_def that)
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

subsection "The live set"

definition L where "L \<equiv> W - (blocked B)"

lemma l2: "p \<in> L \<Longrightarrow> \<exists> Q  \<subseteq> W. quorum_of p Q" 
  unfolding L_def blocks_def using DiffD2 by auto

lemma l3:
  assumes "p \<in> L" shows "\<exists> Q \<subseteq> L . quorum_of p Q"
proof -
  have False if "\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> (-L) \<noteq> {}"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> W" 
      using l2 \<open>p \<in> L\<close> by auto 
    moreover have "Q \<inter> (-L) \<noteq> {}" 
      using that \<open>quorum_of p Q\<close> by simp
    ultimately show False unfolding L_def blocks_def by auto
  qed
  thus ?thesis
    by fastforce 
qed

lemma l4:
  assumes "L \<noteq> {}" and "finite L" 
  shows "quorum L" using l1 l3 assms by metis

lemma l5:  "quorum L' \<Longrightarrow> L' \<subseteq> W \<Longrightarrow> L' \<subseteq> L"
   unfolding L_def blocks_def by auto

lemma l6: "is_intact I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> I \<subseteq> L"
  by (simp add: is_intact_def l5)

end

section "Stellar quorums"

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>The well-behaved nodes\<close>
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . \<exists> Sl \<in> slices p . Sl \<subseteq> Q"

lemma quorum_union:"quorum Q \<Longrightarrow> quorum Q' \<Longrightarrow> quorum (Q \<union> Q')" 
  unfolding quorum_def
  by (metis IntE Int_iff UnE inf_sup_aci(1) sup.coboundedI1 sup.coboundedI2)  

interpretation wb quorum W using quorum_union unfolding wb_def quorums_def by auto

end