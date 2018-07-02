theory PersonalQuorums
imports Main
begin

locale system_1 = 
  fixes V :: "'node::finite set" and W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  assumes "W \<noteq> {}" and "W \<subseteq> V" and "\<And> n q . quorum n q \<Longrightarrow> q \<noteq> {} \<and> q \<subseteq> V" 
    and "\<And> n . \<exists> q . quorum n q"
    and quorum_intersection:
    "\<And> q\<^sub>1 q\<^sub>2 . \<exists> n\<^sub>1 \<in> V . quorum n\<^sub>1 q\<^sub>1 \<Longrightarrow> \<exists> n\<^sub>2 \<in> V . quorum n\<^sub>2 q\<^sub>2 \<Longrightarrow> (\<exists> n . n \<in> q\<^sub>1 \<inter> q\<^sub>2)"
    and quorum_mono: "\<And> q\<^sub>1 q\<^sub>2 n . quorum n q\<^sub>1 \<and> q\<^sub>1 \<subseteq> q\<^sub>2 \<Longrightarrow> quorum n q\<^sub>2"
begin

inductive befouled where 
  "n \<in> V - W \<Longrightarrow> befouled n"
| "\<lbrakk>n \<in> V; \<forall> q . quorum n q \<longrightarrow> (\<exists> n . befouled n \<and> n \<in> q)\<rbrakk> \<Longrightarrow> befouled n"

abbreviation B where "B \<equiv> {n . befouled n}"

lemma l1:"B \<subseteq> V"
  using befouled.cases by fastforce 

lemma l2:
  assumes "\<not>befouled n" and "n \<in> V"
  shows "\<exists> q . quorum n q \<and> q \<inter> B = {}"
  using assms befouled.intros(2) by fastforce 

definition self_reliant where 
  "self_reliant S \<equiv> S \<subseteq> V - B \<and> S \<noteq> {} \<and> (\<forall> n \<in> S . quorum n S)
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 . (\<exists> n\<^sub>1 \<in> S . quorum n\<^sub>1 q\<^sub>1) \<and> (\<exists> n\<^sub>2 \<in> S . quorum n\<^sub>2 q\<^sub>2) \<longrightarrow> (\<exists> n \<in> S . n \<in> q\<^sub>1 \<and> n \<in> q\<^sub>2))"

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)" nitpick[verbose, eval="B", iter system_1.befouled=20]
  oops

definition dset where 
  "dset D \<equiv> self_reliant (V - D)"

lemma "dset D \<Longrightarrow> B \<subseteq> D"
  using Diff_subset Int_Diff dset_def l1 self_reliant_def by auto

lemma "dset D\<^sub>1 \<Longrightarrow> dset D\<^sub>2 \<Longrightarrow> dset (D\<^sub>1 \<inter> D\<^sub>2)" nitpick[verbose, eval="B", iter system_1.befouled=30]
  oops

definition closed where "closed S \<equiv> S \<noteq> {} \<and> (\<forall> n \<in> S . quorum n S)"

definition intersection_despite where 
  "intersection_despite D \<equiv> (\<forall> q\<^sub>1 q\<^sub>2 . (\<exists> n\<^sub>1 \<in> V-D . quorum n\<^sub>1 q\<^sub>1) \<and> (\<exists> n\<^sub>2 \<in> V-D . quorum n\<^sub>2 q\<^sub>2) \<longrightarrow> (q\<^sub>1 \<inter> q\<^sub>2 \<inter> (V-D) \<noteq> {}))"

definition dset_2 where 
  "dset_2 D \<equiv> D \<subseteq> V \<and> closed (V-D) \<and> intersection_despite D"

lemma "dset_2 D\<^sub>1 \<Longrightarrow> dset_2 D\<^sub>2 \<Longrightarrow> dset_2 (D\<^sub>1 \<inter> D\<^sub>2)" nitpick[verbose, iter system_1.befouled=10]
  oops

lemma l3:"closed (V - B\<^sub>1) \<Longrightarrow> closed (V - B\<^sub>2) \<Longrightarrow> closed (V - (B\<^sub>1 \<inter> B\<^sub>2))"
  (* nitpick[verbose,iter system_1.befouled=10, card 'node=5] *)
  using quorum_mono apply (simp add: closed_def)
  by (metis DiffE DiffI Diff_Int IntI inf_commute sup_ge1)

lemma l4:"closed (V - B\<^sub>1) \<Longrightarrow> closed (V - B\<^sub>2) \<Longrightarrow> V - (B\<^sub>1 \<union> B\<^sub>2) \<noteq> {}"
  nitpick[verbose,iter system_1.befouled=10, card 'node=5]
  using quorum_intersection unfolding closed_def by fastforce

definition quorum_delete where "quorum_delete D U \<equiv> \<exists> q n . n \<in> V - D \<and> quorum n q \<and> U = q - D"

lemma "closed (V - B\<^sub>1) \<Longrightarrow> closed (V - B\<^sub>2) \<Longrightarrow> quorum_delete B\<^sub>1 (V - (B\<^sub>1 \<union> B\<^sub>2))"
\<comment> \<open>V - (b1 union b2) is a quorum in delete V b1\<close>
  nitpick[card 'node=6, timeout=800]
  oops

lemma "U\<^sub>a-B\<^sub>1 \<noteq> {} \<Longrightarrow> quorum_delete B\<^sub>1 (V - (B\<^sub>1 \<union> B\<^sub>2)) \<Longrightarrow> intersection_despite B\<^sub>1
\<Longrightarrow> quorum_delete (V - (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>a  \<Longrightarrow> U\<^sub>a\<inter>(V - (B\<^sub>1 \<union> B\<^sub>2))\<noteq> {}" nitpick[card 'node=6] 
  oops

lemma "U\<^sub>a-B\<^sub>1 \<noteq> {} \<Longrightarrow> quorum_delete B\<^sub>1 (V - (B\<^sub>1 \<union> B\<^sub>2)) \<Longrightarrow> intersection_despite B\<^sub>1
\<Longrightarrow> quorum_delete (V - (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>a  \<Longrightarrow> U\<^sub>a-B\<^sub>2\<noteq> {}" nitpick[card 'node=8] oops

abbreviation set_minus (infixl "\<setminus>" 65) where "set_minus A D \<equiv> A - D"

lemma l5:
  assumes "safe fbas S" and "quorum_delete (B\<^sub>1 \<inter> B\<^sub>2) U" and "S \<inter> U \<noteq> {}"
    and "dset B\<^sub>1" and "dset B\<^sub>2"
  shows "quorum_delete B\<^sub>1 (U \<setminus> B\<^sub>1)" and "(U \<setminus> B\<^sub>1) \<inter> S \<noteq> {}"
  nitpick  oops
    \<comment> \<open>This is the crucial lemma\<close>
proof -
  let ?V = "fst fbas" 
  have "S \<subseteq> ?V \<setminus> B\<^sub>1" and "S \<subseteq> ?V \<setminus> B\<^sub>2" using \<open>dset fbas S B\<^sub>1\<close> and  \<open>dset fbas S B\<^sub>2\<close>
    by (simp_all add:dset_def availability_despite_def)

  have "(U \<setminus> B\<^sub>1) \<inter> S \<noteq> {}" and "(U \<setminus> B\<^sub>2) \<inter> S \<noteq> {}"
  proof -
    have "S \<subseteq> ?V - B\<^sub>1" and "S \<subseteq> ?V - B\<^sub>2"
      by (meson availability_despite_def dset_def \<open>dset fbas S B\<^sub>1\<close> \<open>dset fbas S B\<^sub>2\<close>)+
    then show "(U \<setminus> B\<^sub>1) \<inter> S \<noteq> {}" and "(U \<setminus> B\<^sub>2) \<inter> S \<noteq> {}"
      using \<open>S \<inter> U \<noteq> {}\<close> by blast+
  qed
  thus "(U \<setminus> B\<^sub>1) \<inter> S \<noteq> {}" by auto

  have "S \<noteq> {}" using \<open>S \<inter> U \<noteq> {}\<close> by blast 
  consider (a) "(U \<setminus> B\<^sub>1) \<inter> W \<noteq> {}" | (b) "(U \<setminus> B\<^sub>2) \<inter> W \<noteq> {}"
  proof -
    have "(U \<setminus> (B\<^sub>1 \<inter> B\<^sub>2)) \<inter> W = {}" if "(U \<setminus> B\<^sub>1) \<inter> W = {}" and "(U \<setminus> B\<^sub>2)  \<inter> W = {}"
      using that by fastforce
    thus ?thesis using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> apply (simp add:quorum_def)
      by (smt Diff_Int Diff_disjoint Diff_empty Diff_eq_empty_iff a b fstI sup_inf_absorb system.delete_def)
  qed
  thus "quorum (delete fbas B\<^sub>1) (U \<setminus> B\<^sub>1)"
  proof (cases)
    case b
    have "(U \<setminus> B\<^sub>2) \<inter> (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> W \<noteq> {}" 
    proof -
      from b have "quorum (delete fbas B\<^sub>2) (U \<setminus> B\<^sub>2)" 
        using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> delete_more
        by (metis Int_commute inf_le2) 
      moreover
      have "quorum (delete fbas B\<^sub>2) (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2))" 
        using l4 \<open>dset fbas S B\<^sub>1\<close> \<open>dset fbas S B\<^sub>2\<close> \<open>S \<subseteq> ?V \<setminus> B\<^sub>1\<close> \<open>S \<subseteq> ?V \<setminus> B\<^sub>2\<close> \<open>S \<noteq> {}\<close> \<open>safe fbas S\<close>
        unfolding dset_def availability_despite_def
        by (metis sup_commute)
      moreover have "(?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> S \<noteq> {}"
        by (smt Diff_Un Int_left_commute \<open>S \<noteq> {}\<close> \<open>S \<subseteq> ?V - B\<^sub>1\<close> \<open>S \<subseteq> ?V - B\<^sub>2\<close> inf.commute inf.orderE) 
      moreover note \<open>(U \<setminus> B\<^sub>2) \<inter> S \<noteq> {}\<close>
      moreover have "safe (delete fbas B\<^sub>2) S"
        by (simp add: \<open>S \<noteq> {}\<close> l2 assms(1) assms(5)) 
      ultimately 
      show "(U \<setminus> B\<^sub>2) \<inter> (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> W \<noteq> {}"
        by (simp add: safe_def)
    qed
    hence "(U \<setminus> B\<^sub>1) \<inter> W \<noteq> {}" by (auto)
    thus ?thesis by (meson inf_le1 system.delete_more \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close>) 
  next
    case a thus ?thesis 
      using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> delete_more by (metis Int_lower1)
  qed
qed


lemma "U\<^sub>a - B\<^sub>1 \<noteq> {} \<Longrightarrow> \<exists> n \<in> V-(B\<^sub>1\<inter>B\<^sub>2) . quorum n U\<^sub>a \<Longrightarrow> U\<^sub>b - B\<^sub>1 \<noteq> {} \<Longrightarrow> \<exists> n \<in> V-(B\<^sub>1\<inter>B\<^sub>2) . quorum n U\<^sub>b
\<Longrightarrow> U\<^sub>a \<inter> U\<^sub>b \<inter> (V-(B\<^sub>1\<inter>B\<^sub>2))\<noteq> {}" nitpick

end

locale system_2 = 
  fixes V :: "'node set" and W :: "'node set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node set \<Rightarrow> bool"
  assumes a1:"W \<noteq> {}" and a2:"W \<subseteq> V" and a3:"\<And> q . quorum q \<Longrightarrow> q \<noteq> {} \<and> q \<subseteq> V" 
    and a4:"\<And> n . n \<in> V \<longrightarrow> (\<exists> q . n \<in> q \<and> quorum q)"
    and quorum_intersection:
    "\<And> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<Longrightarrow> quorum q\<^sub>2 \<Longrightarrow> (\<exists> n . n \<in> q\<^sub>1 \<inter> q\<^sub>2)"
    and quorum_union:"\<And> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<Longrightarrow> quorum q\<^sub>2 \<Longrightarrow> quorum (q\<^sub>1 \<union> q\<^sub>2)"
begin

lemma False nitpick oops

inductive befouled where 
  "n \<in> V - W \<Longrightarrow> befouled n"
| "\<lbrakk>n \<in> V; \<forall> q . n \<in> q \<and> quorum q \<longrightarrow> (\<exists> n . befouled n \<and> n \<in> q)\<rbrakk> \<Longrightarrow> befouled n"

abbreviation B where "B \<equiv> {n . befouled n}"

lemma l1:"B \<subseteq> V"
  using befouled.cases by fastforce 

lemma l2:
  assumes "\<not>befouled n" and "n \<in> V"
  shows "\<exists> q . n \<in> q \<and> quorum q \<and> q \<inter> B = {}"
  using assms befouled.intros(2) by fastforce 

definition self_reliant where 
  "self_reliant S \<equiv> S \<subseteq> V \<and> S \<noteq> {} \<and> quorum S
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 (*\<and> q\<^sub>1 \<inter> S \<noteq> {}*) \<and> quorum q\<^sub>2 (*\<and> q\<^sub>2 \<inter> S \<noteq> {}*) \<longrightarrow> (\<exists> n \<in> W . n \<in> q\<^sub>1 \<and> n \<in> q\<^sub>2))"

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)"
    \<comment> \<open>Should be pretty obvious\<close>
  apply (simp add:self_reliant_def)
  by (metis quorum_union)

lemma "self_reliant S\<^sub>1 \<Longrightarrow> S\<^sub>1 - W = {} \<Longrightarrow> B \<subseteq> V - S\<^sub>1" nitpick[eval=B, verbose, iter system_2.befouled = 9, card 'node=7, timeout=300]
  apply (auto simp add:self_reliant_def)
  apply (meson Diff_iff befouled.cases) 
  oops

lemma "self_reliant S\<^sub>1 \<Longrightarrow> S\<^sub>1 - W = {} \<Longrightarrow> (\<And> S\<^sub>2 . \<not> (S\<^sub>1 \<subset> S\<^sub>2 \<and> self_reliant S\<^sub>2)) \<Longrightarrow> B = V - S\<^sub>1"
  nitpick[eval=B, verbose, iter system_2.befouled = 8, card 'node=6, timeout=800]
  oops

end

locale system_3 = 
  fixes W :: "'node set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node set \<Rightarrow> bool"
  assumes a1:"W \<noteq> {}" 
    and quorum_intersection:
    "\<And> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<Longrightarrow> quorum q\<^sub>2 \<Longrightarrow> (\<exists> n . n \<in> q\<^sub>1 \<inter> q\<^sub>2)"
    and quorum_union:"\<And> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<Longrightarrow> quorum q\<^sub>2 \<Longrightarrow> quorum (q\<^sub>1 \<union> q\<^sub>2)"
begin

lemma False nitpick oops

inductive befouled where 
  "n \<notin> W \<Longrightarrow> befouled n"
| "\<lbrakk>n \<in> V; \<forall> q . n \<in> q \<and> quorum q \<longrightarrow> (\<exists> n . befouled n \<and> n \<in> q)\<rbrakk> \<Longrightarrow> befouled n"

abbreviation B where "B \<equiv> {n . befouled n}"

lemma l2:
  assumes "\<not>befouled n"
  shows "\<exists> q . n \<in> q \<and> quorum q \<and> q \<inter> B = {}"
  using assms befouled.intros(2) by fastforce

definition self_reliant where 
  "self_reliant S \<equiv> S \<noteq> {} \<and> quorum S
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 (*\<and> q\<^sub>1 \<inter> S \<noteq> {}*) \<and> quorum q\<^sub>2 (*\<and> q\<^sub>2 \<inter> S \<noteq> {}*) \<longrightarrow> (\<exists> n \<in> S . n \<in> q\<^sub>1 \<and> n \<in> q\<^sub>2))"

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)"
    \<comment> \<open>Should be pretty obvious\<close>
  apply (simp add:self_reliant_def)
  by (metis UnI2 quorum_union)

lemma "self_reliant S\<^sub>1 \<Longrightarrow> S\<^sub>1 \<subseteq> W \<Longrightarrow> B \<inter> S\<^sub>1 = {}" nitpick[eval=B, verbose, iter system_3.befouled = 9, card 'node=5, timeout=300]
  apply (auto simp add:self_reliant_def)
  oops

lemma "self_reliant S\<^sub>1 \<Longrightarrow> S\<^sub>1 \<subseteq> W \<Longrightarrow> (\<And> S\<^sub>2 . \<not> (S\<^sub>1 \<subset> S\<^sub>2 \<and> self_reliant S\<^sub>2)) \<Longrightarrow> B = -S\<^sub>1"
  nitpick[eval=B, verbose, iter system_3.befouled = 8, card 'node=5, timeout=800]
  apply (auto simp add:self_reliant_def)
  oops

definition dset where
  \<comment> \<open>Note that since -D is a quorum, all quorums intersect it\<close>
  "dset D \<equiv> quorum (-D) \<and> (\<forall> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<and> quorum q\<^sub>2 (* \<and> (-D) \<inter> q\<^sub>1 \<noteq> {} \<and> (-D) \<inter> q\<^sub>2 \<noteq> {}*) \<longrightarrow> (\<exists> n \<in> (-D) . n \<in> q\<^sub>1 \<and> n \<in> q\<^sub>2))"

lemma "dset D\<^sub>1 \<Longrightarrow> dset D\<^sub>2 \<Longrightarrow> dset (D\<^sub>1 \<inter> D\<^sub>2)" nitpick[verbose, eval="B", iter system_3.befouled=10, card 'node=5]
  apply (simp add:dset_def)
  by (metis Compl_iff Int_iff compl_inf empty_iff quorum_intersection quorum_union)

lemma "\<Inter>{D . dset D \<and> -W \<subseteq> D} = B"
  nitpick[verbose, eval="(B,{D . dset D \<and> -W \<subseteq> D})", iter system_3.befouled=4, card 'node=3]
  oops

lemma "dset D = self_reliant (-D)" nitpick[verbose, eval="B", iter system_3.befouled=10, card 'node=6]

end

end