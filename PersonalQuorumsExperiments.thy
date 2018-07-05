theory PersonalQuorumsExperiments
imports Main
begin

text \<open>
The Stellar Consensus Protocol is based on Federated Voting. 
Federated Voting is a mechanism through which nodes which do not 
have a uniform view of the system can nevertheless, under some conditions, reach agreement.
The core idea is that each nodes knows of a subset of the other nodes and has some level of trust for each of them.

The Stellar White-Paper describes federated voting bottom-up, starting from how the trust relationship is encoded, i.e. as quorum slices.
Here we take a higher-level approach. We assume that each nodes has a set of quorums, where a quorum is a set of knows that the node
considers trustworthy. We do node make assumptions on how these quorums are built in practice.
We then derive conditions on these quorums that are sufficient for allowing a subset of the nodes, called the intact nodes, to achieve atomic broadcast.
The conditions we obtain are weaker than those given in the Stellar Whitepaper; for example, quorum intersection in the whole system is not necessary\<close>


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


lemma "U\<^sub>a - B\<^sub>1 \<noteq> {} \<Longrightarrow> \<exists> n \<in> V-(B\<^sub>1\<inter>B\<^sub>2) . quorum n U\<^sub>a \<Longrightarrow> U\<^sub>b - B\<^sub>1 \<noteq> {} \<Longrightarrow> \<exists> n \<in> V-(B\<^sub>1\<inter>B\<^sub>2) . quorum n U\<^sub>b
\<Longrightarrow> U\<^sub>a \<inter> U\<^sub>b \<inter> (V-(B\<^sub>1\<inter>B\<^sub>2))\<noteq> {}" nitpick oops

lemma "quorum_delete D U \<Longrightarrow> D \<subseteq> E \<Longrightarrow> quorum_delete E (U \<setminus> E)" nitpick[card 'node=2]
  oops

lemma assumes "dset_2 B\<^sub>1" and  "dset_2 B\<^sub>2" and "V-B\<^sub>1\<noteq>{}" and "V-B\<^sub>2\<noteq>{}" shows "dset_2 (B\<^sub>1 \<inter> B\<^sub>2)"
proof -
  text \<open>availability:\<close>
  have "closed (V - (B\<^sub>1 \<inter> B\<^sub>2))" using l3
    using assms(1) assms(2) dset_2_def by blast

  have "V - (B\<^sub>1 \<union> B\<^sub>2) \<noteq> {}" using l4
    using assms(1) assms(2) dset_2_def by blast 

  have "quorum_delete B\<^sub>1 (V - (B\<^sub>1 \<union> B\<^sub>2))" nitpick[card 'node=6] sorry

  have "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}" if "quorum_delete (B\<^sub>1 \<inter> B\<^sub>2) U\<^sub>a" and "quorum_delete (B\<^sub>1 \<inter> B\<^sub>2) U\<^sub>b" for U\<^sub>a U\<^sub>b
  proof -
    consider (a)"U\<^sub>a \<setminus> B\<^sub>1 \<noteq> {}" | (b)"U\<^sub>a \<setminus> B\<^sub>2 \<noteq> {}" nitpick[card 'node=6] sorry
    thus ?thesis
    proof (cases)
      case a
      have "quorum_delete B\<^sub>1 (U\<^sub>a\<setminus>B\<^sub>1)"  nitpick[card 'node=3] oops

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
| "\<lbrakk>\<forall> q . n \<in> q \<and> quorum q \<longrightarrow> (\<exists> n . befouled n \<and> n \<in> q)\<rbrakk> \<Longrightarrow> befouled n"

abbreviation Be where "Be \<equiv> {n . befouled n}"

lemma l2:
  assumes "\<not>befouled n"
  shows "\<exists> q . n \<in> q \<and> quorum q \<and> q \<inter> Be = {}"
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

lemma "dset D\<^sub>1 \<Longrightarrow> dset D\<^sub>2 \<Longrightarrow> dset (D\<^sub>1 \<inter> D\<^sub>2)" nitpick[verbose, iter system_3.befouled=10, card 'node=5]
  apply (simp add:dset_def)
  by (metis Compl_iff Int_iff compl_inf empty_iff quorum_intersection quorum_union)

lemma "\<Inter>{D . dset D \<and> -W \<subseteq> D} = B"
  nitpick[verbose, eval="(B,{D . dset D \<and> -W \<subseteq> D})", iter system_3.befouled=4, card 'node=3]
  oops

lemma "dset D = self_reliant (-D)" nitpick[verbose, iter system_3.befouled=10, card 'node=6] oops

end

locale system_4 = 
  fixes W :: "'node set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node set \<Rightarrow> bool"
  assumes quorum_intersection:
    "\<And> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<Longrightarrow> quorum q\<^sub>2 \<Longrightarrow> (\<exists> n . n \<in> q\<^sub>1 \<inter> q\<^sub>2)"
    and quorum_union:
    "\<And> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 \<Longrightarrow> quorum q\<^sub>2 \<Longrightarrow> quorum (q\<^sub>1 \<union> q\<^sub>2)"
begin

lemma False nitpick oops

definition self_reliant where 
  "self_reliant S \<equiv> S \<noteq> {} \<and> quorum S
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 . quorum q\<^sub>1 (*\<and> q\<^sub>1 \<inter> S \<noteq> {}*) \<and> quorum q\<^sub>2 (*\<and> q\<^sub>2 \<inter> S \<noteq> {}*) \<longrightarrow> (\<exists> n \<in> W . n \<in> q\<^sub>1 \<and> n \<in> q\<^sub>2))"

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)"
    \<comment> \<open>Should be pretty obvious\<close>
  by (simp add:self_reliant_def; metis quorum_union)

inductive befouled where
  "n \<notin> W \<Longrightarrow> befouled n"
| "\<lbrakk>\<forall> q . n \<in> q \<and> quorum q \<longrightarrow> (\<exists> n . befouled n \<and> n \<in> q)\<rbrakk> \<Longrightarrow> befouled n"

abbreviation Be where "Be \<equiv> {n . befouled n}"

lemma l2:
  assumes "\<not>befouled n"
  shows "\<exists> q . n \<in> q \<and> quorum q \<and> q \<inter> Be = {}"
  using assms befouled.intros(2) by fastforce

lemma l3:
  "\<Union>{S . self_reliant S \<and> S \<subseteq> W} \<inter> Be = {}" nitpick[card 'node=6, verbose, iter system_4.befouled = 6] oops

end

locale system_5 = 
  fixes W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  assumes 
    quorum_intersection: "\<And> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . quorum n\<^sub>1 q\<^sub>1 \<Longrightarrow> quorum n\<^sub>2 q\<^sub>2 \<Longrightarrow> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}"
    and
    quorum_closed: "\<And> q n\<^sub>1 n\<^sub>2 . \<lbrakk>quorum n\<^sub>1 q; n\<^sub>2 \<in> q\<rbrakk> \<Longrightarrow> quorum n\<^sub>2 q"
begin

lemma assumes "quorum n\<^sub>1 q\<^sub>1" and "quorum n\<^sub>2 q\<^sub>2"
  shows "\<exists> n . quorum n (q\<^sub>1 \<union> q\<^sub>2)" nitpick oops \<comment> \<open>does not hold\<close>

definition self_reliant where 
  "self_reliant S \<equiv> S \<noteq> {} \<and> (\<forall> n \<in> S . \<exists> S' . S' \<subseteq> S \<and> quorum n S')
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . n\<^sub>1 \<in> S \<and> quorum n\<^sub>1 q\<^sub>1 (*\<and> q\<^sub>1 \<inter> S \<noteq> {}*) \<and> n\<^sub>2 \<in> S \<and> quorum n\<^sub>2 q\<^sub>2 (*\<and> q\<^sub>2 \<inter> S \<noteq> {}*) \<longrightarrow> (W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}))"

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)" nitpick[card 'node=2, verbose]
  apply (auto simp add:self_reliant_def)
  apply (meson le_supI1)
  apply (meson le_supI2)
  apply blast
  apply (metis (no_types, lifting) Int_emptyI set_rev_mp quorum_intersection quorum_closed)
  apply (smt Int_emptyI rev_subsetD  quorum_intersection quorum_closed)
  by blast

end

locale system_6 = 
  fixes W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  fixes self_reliant 
  defines "self_reliant S \<equiv> S \<noteq> {} (*\<and> S \<subseteq> W*) \<and> (\<forall> n \<in> S . \<exists> S' . S' \<subseteq> S \<and> quorum n S')
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . n\<^sub>1 \<in> S \<and> quorum n\<^sub>1 q\<^sub>1  \<and> n\<^sub>2 \<in> S \<and> quorum n\<^sub>2 q\<^sub>2  \<longrightarrow> (W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}))"
  assumes 
    quorum_intersection: "\<And> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 S\<^sub>1 S\<^sub>2. \<lbrakk>quorum n\<^sub>1 q\<^sub>1; quorum n\<^sub>2 q\<^sub>2; self_reliant S\<^sub>1; self_reliant S\<^sub>2\<rbrakk> \<Longrightarrow> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}"
    and
    quorum_closed: "\<And> q n\<^sub>1 n\<^sub>2 . \<lbrakk>quorum n\<^sub>1 q; n\<^sub>2 \<in> q\<rbrakk> \<Longrightarrow> quorum n\<^sub>2 q"
begin

lemma assumes "quorum n\<^sub>1 q\<^sub>1" and "quorum n\<^sub>2 q\<^sub>2"
  shows "\<exists> n . quorum n (q\<^sub>1 \<union> q\<^sub>2)" nitpick oops \<comment> \<open>does not hold\<close>

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)" nitpick[card 'node=5, verbose, timeout=800]
  oops
  apply (auto simp add:self_reliant_def)
  apply (meson le_supI1)
  apply (meson le_supI2)
  apply blast
  apply (metis (no_types, lifting) Int_emptyI set_rev_mp quorum_intersection quorum_closed)
  apply (smt Int_emptyI rev_subsetD  quorum_intersection quorum_closed)
  by blast

end

locale system_7 = 
  fixes W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
    and quorum :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  fixes self_reliant 
  defines "self_reliant S \<equiv> S \<noteq> {} \<and> S \<subseteq> W \<and> (\<forall> n \<in> S . quorum n S)
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . n\<^sub>1 \<in> S \<and> quorum n\<^sub>1 q\<^sub>1  \<and> n\<^sub>2 \<in> S \<and> quorum n\<^sub>2 q\<^sub>2  \<longrightarrow> (S \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}))"
  assumes 
    quorum_union: "\<And> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . \<lbrakk>quorum n\<^sub>1 q\<^sub>1; quorum n\<^sub>2 q\<^sub>2\<rbrakk> \<Longrightarrow> quorum n\<^sub>1 (q\<^sub>1 \<union> q\<^sub>2)"
    and
    quorum_closed: "\<And> q n\<^sub>1 n\<^sub>2 . \<lbrakk>quorum n\<^sub>1 q; n\<^sub>2 \<in> q\<rbrakk> \<Longrightarrow> quorum n\<^sub>2 q"
    and "\<And> n q . quorum n q \<Longrightarrow> n \<in> q"
begin

lemma "self_reliant S\<^sub>1 \<and> self_reliant S\<^sub>2 \<Longrightarrow> self_reliant (S\<^sub>1 \<union> S\<^sub>2)" nitpick[card 'node=3, verbose, timeout=600]

end


end