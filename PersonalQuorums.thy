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
    and "\<And> q\<^sub>1 q\<^sub>2 n . quorum n q\<^sub>1 \<and> q\<^sub>1 \<subseteq> q\<^sub>2 \<Longrightarrow> quorum n q\<^sub>2"
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

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)" nitpick[verbose, eval="B", iter system_1.befouled=5]
  oops

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
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 (*\<and> q\<^sub>1 \<inter> S \<noteq> {}*) \<and> quorum q\<^sub>2 (*\<and> q\<^sub>2 \<inter> S \<noteq> {}*) \<longrightarrow> (\<exists> n \<in> S . n \<in> q\<^sub>1 \<and> n \<in> q\<^sub>2))"

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)"
    \<comment> \<open>Should be pretty obvious\<close>
  apply (simp add:self_reliant_def)
  by (metis Int_iff inf_sup_absorb quorum_union)

lemma "self_reliant S\<^sub>1 \<Longrightarrow> S\<^sub>1 - W = {} \<Longrightarrow> B \<subseteq> V - S\<^sub>1" nitpick[eval=B, verbose, iter system_2.befouled = 9, card 'node=8, timeout=300]
  apply (auto simp add:self_reliant_def)
  apply (meson Diff_iff befouled.cases) 
  oops

lemma "self_reliant S\<^sub>1 \<Longrightarrow> S\<^sub>1 - W = {} \<Longrightarrow> (\<And> S\<^sub>2 . \<not> (S\<^sub>1 \<subset> S\<^sub>2 \<and> self_reliant S\<^sub>2)) \<Longrightarrow> B = V - S\<^sub>1"
  nitpick[eval=B, verbose, iter system_2.befouled = 8, card 'node=8, timeout=600]
  oops

end

end