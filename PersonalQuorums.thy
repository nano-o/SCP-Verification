section Introduction

theory PersonalQuorums
imports Main
begin

text \<open>
The Stellar Consensus Protocol (SCP) implements some form of Consensus in an environment in which
nodes do not have a uniform view of the whole system. Instead, a node knows about a subset of the
other nodes and can assign them some degree of trust.

A basic building block used by SCP is Atomic Broadcast, implemented by Federated Voting. In
Federated Voting, information on trust relationships, embodied by quorum slices, is exchanged and
collected by nodes, which use it to determine quorums. Quorums are sets of nodes considered
trustworthy as a whole by their members. Roughly speaking, nodes act on information voted for by any
quorum they belong to. When quorums intersect, this can guarantee that nodes do not use
contradictory information.

One difference between quorums that arise from trust relationships and the quorums studied in the
traditional Byzantine agreement model is that, in Federated Voting, not all nodes use the same
quorums. We call this kind of quorums personal quorums.

In this document, we abstract over the concrete mechanism used to build quorums and investigate the
intrinsic properties of personal quorums that allow to implement Atomic Broadcast using personal
quorums. We hope that this abstract view of Federate Voting might help clarify its exposition.

We present conditions that are necessary for allowing a subset of the nodes to achieve quorum-based
atomic broadcast. Moreover we note that the classical Bracha Broadcast algorithm @{cite
bracha_asynchronous_1987}, also used in SCP, works under those condition, making the conditions and
the algorithm, in some sense, optimal. Finally, we show that, under some quorum intersection
property, there is a unique maximal set of nodes, whose members are called intact, that can achieve
atomic broadcast.

The ideas presented here have been developed with Eli Gafni.
\<close>

section \<open>Personal Quorums\<close>

text \<open>
We start by modeling a system in which each node has a set of quorums, called its personal quorums.
We also fix a set @{text W} of well-behaved nodes.
\<close>

locale personal_quorums = 
  fixes W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
  fixes quorum :: "'node \<Rightarrow> 'node set \<Rightarrow> bool" \<comment> \<open>the quorums of each node\<close>
begin

text \<open>
Atomic broadcast among set S requires that (safety) no two members of S confirm contradictory
statements, and (atomicity) that if a member of S confirms a statement, then, given sufficient
communication, all members of S confirm the statement.

Given a subset @{text S} of the nodes, we can ensure safety based on quorums for @{text S} only if
(a) every node in @{text S} has a quorum in @{text S}, and (b) given two nodes @{text "n\<^sub>1\<in>S"} and
@{text "n\<^sub>2\<in>S"}, if @{text q\<^sub>1} is a quorum of @{text n\<^sub>1} and @{text q\<^sub>2} is a quorum of @{text
n\<^sub>2}, then @{text q\<^sub>1} and @{text q\<^sub>2} intersect at a well-behaved node. We call such a non-empty
subset S of nodes a self-reliant subset.
\<close>

definition self_reliant where "self_reliant S \<equiv> S \<noteq> {} \<and> (\<forall> n \<in> S . \<exists> q . q \<subseteq> S \<and> quorum n q)
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . n\<^sub>1 \<in> S \<and> quorum n\<^sub>1 q\<^sub>1 \<and> n\<^sub>2 \<in> S \<and> quorum n\<^sub>2 q\<^sub>2  \<longrightarrow> (W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}))"

text \<open>Note that all properties proved below would also hold if we required intersection in the set
@{text S}, and not only at a well-behaved node.\<close>

text \<open>@{text B} is a blocking set for node @{text n} when @{text B} intersects all quorums of @{text
n}. This is meant to replace the definition of blocking set in the classical Atomic Broadcast
algorithm.\<close>

definition blocking where "blocking n B \<equiv> \<forall> q . quorum n q \<longrightarrow> B \<inter> q \<noteq> {}"

text \<open>Bracha Broadcast works as follows. We assume that nodes have an initial value to
broadcast. First a node votes for its value. Then it tries to accept a value using the following
rule. A node n accepts a value v when either

  \<^enum> there is a quorum q of n such that every member of q reports voting or accepting v (this can be
  restricted to only voting), or 
  \<^enum> there is a set B blocking n such that every member of B report
  accepting v.

Once a node has accepted a value v, it broadcasts this fact and tries to confirm v. A node n
confirms value v when there is a quorum q of n such that every member of q reports accepting v.
\<close>

text \<open>Note that if a set @{text B} blocks a node belonging to a self-reliant set @{text S}, then
@{text B} intersects @{text S}:\<close>

lemma blocking_intersects_self_reliant:
  assumes "n \<in> S" and "blocking n B" and "self_reliant S" 
  shows "B \<inter> S \<noteq> {}"
  using assms self_reliant_def blocking_def by fastforce 

text \<open>This implies that Bracha Broadcast is safe for a self-reliant set, assuming we
modify the Atomic Broadcast algorithm rule for accept by taking only votes into account in the first
condition for accepting. Otherwise, one must must require quorums of a self-reliant set to intersect
in the self-reliant set itself, not just at a well-behaved node. \<close>

text \<open>Also note that any quorum of a self-reliant set @{text S} is blocking for any member of @{text
S}.\<close>

lemma quorum_is_blocking:
  assumes "self_reliant S" and "n \<in> S" and "quorum n q"
  shows "blocking n q"
  by (metis Int_assoc assms blocking_def inf_bot_right self_reliant_def) 

text \<open> In Bracha Broadcast, this implies that if a node in @{text S} confirms a
statement then all nodes in @{text S} will eventually confirm it too.Thus the Atomic Broadcast
algorithm is in some sense optimal, since the self-reliant property is necessary for atomic
broadcast based on quorums.\<close>

text \<open>Now just an observation: The union of two quorum is not necessarily a quorum; this is one
example of a property of quorums obtained through slices that is not needed in our setting.\<close>
lemma assumes "quorum n\<^sub>1 q\<^sub>1" and "quorum n\<^sub>2 q\<^sub>2"
  shows "\<exists> n . quorum n (q\<^sub>1 \<union> q\<^sub>2)" nitpick oops

end

subsection \<open>Existence of a unique maximal self-reliant set\<close>

text \<open> Here we show that if we assume that (a) quorums of self-reliant sets intersect, and (b) that
quorums are closed (meaning that if @{text q} is a quorum of @{text n} and @{text "n' \<in> q"}, then
@{text q} is also a quorum of @{text n'}), then there exists a unique maximal self-reliant set. To
make a parallel with SCP, we can call this maximal self-reliant set the set of intact nodes.

Note that the quorums used in SCP, derived from slices, do satisfy assumption (b) by construction.\<close>

locale max_self_reliant = personal_quorums +
  assumes quorum_intersection:  "\<And> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 S\<^sub>1 S\<^sub>2. 
    \<lbrakk>n\<^sub>1 \<in> S\<^sub>1; n\<^sub>2 \<in> S\<^sub>2; quorum n\<^sub>1 q\<^sub>1; quorum n\<^sub>2 q\<^sub>2; self_reliant S\<^sub>1; self_reliant S\<^sub>2\<rbrakk> \<Longrightarrow> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" 
    and  quorum_closed: "\<And> q n\<^sub>1 n\<^sub>2 . \<lbrakk>quorum n\<^sub>1 q; n\<^sub>2 \<in> q\<rbrakk> \<Longrightarrow> quorum n\<^sub>2 q"
begin

text \<open>We will use the following auxiliary lemma (a mere technicality)\<close>
lemma quorum_not_empty:
  assumes "self_reliant S" and "n \<in> S" and "quorum n q"
  shows "q \<noteq> {}"
  using assms quorum_intersection by fastforce 

text \<open>We can now show that the union of two self-reliant sets is self-reliant. This implies that
there is a unique maximal self-reliant set, which we call the set of intact nodes.\<close>

text \<open>To prove that the union of two self-reliant sets is self-reliant, we consider two self-reliant
sets @{text S\<^sub>1} and @{text S\<^sub>2} and show that @{text "S\<^sub>1 \<union> S\<^sub>2"} satisfies the three properties of
self-reliant sets.

The first properties follow trivially from the assumption that @{text S\<^sub>1} and @{text S\<^sub>2} are
self-reliant: @{text "S\<^sub>1 \<union> S\<^sub>2 \<noteq> {}"} and every member of @{text "S\<^sub>1 \<union> S\<^sub>2"} has a quorum in
@{text "S\<^sub>1 \<union> S\<^sub>2"}.

We now show the third property, i.e. that given two nodes @{text n\<^sub>1} and @{text n\<^sub>2} in @{text "S\<^sub>1
\<union> S\<^sub>2"} and two sets @{text q\<^sub>1} and @{text q\<^sub>2} such that @{text q\<^sub>1} is a quorum of @{text n\<^sub>1}
and @{text q\<^sub>2} is a quorum of @{text n\<^sub>2}, @{text q\<^sub>1} and @{text q\<^sub>2} intersect at a well-behaved
node.

First, if @{term "n\<^sub>1"} and @{term "n\<^sub>2"} are both in @{term "S\<^sub>1"} or both in @{term "S\<^sub>2"}, then,
by the definition of self-reliant, we trivially have that @{term q\<^sub>1} and @{term q\<^sub>1} intersect at a
well-behaved node. Without loss of generality, we therefore assume that @{term "n\<^sub>1\<in>S\<^sub>1"} and @{term
"n\<^sub>2\<in>S\<^sub>2"}.

Note that, since @{text S\<^sub>2} is self-reliant, there is a node @{text "n \<in> S\<^sub>2"} and a set @{text "q
\<subseteq> S\<^sub>2"} where @{text q} is a quorum of n. Then, apply the @{text quorum_intersection} assumption to
the self-reliant sets @{term "S\<^sub>1"} and @{term "S\<^sub>2"} and their quorums @{text q\<^sub>1} and @{text q},
we get that @{text "q \<inter> q1 \<noteq> {}"}. Since @{text "q \<subseteq> S\<^sub>2"}, we thus have a node @{text n'} where
@{text "n'\<in> S\<^sub>2 \<inter> q1"}. Because @{text q\<^sub>1} is a quorum of @{text n\<^sub>1}, using the @{text
quorum_closed} assumption we get that @{text q\<^sub>1} is a quorum of @{text "n'\<in> S\<^sub>2"}. Finally, because
@{text S\<^sub>2} is a self-reliant set, any two quorums of nodes in @{text S\<^sub>2} intersect at a
well-behaved node. Therefore @{text q\<^sub>1} and @{text q\<^sub>2} intersect at a well-behaved node.

Below is the Isabelle version of the proof. \<close>

lemma union_closed:
  assumes "self_reliant S\<^sub>1" and "self_reliant S\<^sub>2" 
  shows "self_reliant (S\<^sub>1 \<union> S\<^sub>2)" (* using quorum_not_empty quorum_closed quorum_intersection assms
  unfolding self_reliant_def sledgehammer[provers=z3 spass, timeout=800] (add:Int_iff IntE all_not_in_conv inf_commute inf_commute inf_sup_distrib2 sup.absorb_iff1 sup_bot.left_neutral sup_eq_bot_iff UnE le_supI1 le_supI2 all_not_in_conv) *)
proof -
  have "S\<^sub>1 \<union> S\<^sub>2 \<noteq> {}"
    using assms(2) self_reliant_def
    by (metis sup_eq_bot_iff)
  moreover
  have "\<exists> q . q \<subseteq> (S\<^sub>1 \<union> S\<^sub>2) \<and> quorum n q" if "n \<in> S\<^sub>1 \<union> S\<^sub>2" for n
    using assms unfolding self_reliant_def
    by (metis UnE le_supI1 le_supI2 that)
  moreover  
  have "W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" 
    if "n\<^sub>1 \<in> S\<^sub>1 \<union> S\<^sub>2" and "quorum n\<^sub>1 q\<^sub>1" and "n\<^sub>2 \<in> S\<^sub>1 \<union> S\<^sub>2" and "quorum n\<^sub>2 q\<^sub>2" for q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2
  proof -
    have \<open>W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> 
      if "n\<^sub>1 \<in> S" and "n\<^sub>2 \<in> S" and "S = S\<^sub>1 \<or> S = S\<^sub>2" for S
      by (metis \<open>quorum n\<^sub>1 q\<^sub>1\<close> \<open>quorum n\<^sub>2 q\<^sub>2\<close> assms self_reliant_def that) 
    moreover
    have \<open>W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> 
      if "n\<^sub>1 \<in> S\<^sub>1" and "n\<^sub>2 \<in> S\<^sub>2" and \<open>self_reliant S\<^sub>1\<close> and \<open>self_reliant S\<^sub>2\<close> and \<open>quorum n\<^sub>1 q\<^sub>1\<close> and \<open>quorum n\<^sub>2 q\<^sub>2\<close>
      for q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 S\<^sub>1 S\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      obtain n where "n \<in> S\<^sub>2" and "quorum n q\<^sub>1"
      proof -
        obtain n' q where "q \<subseteq> S\<^sub>2" and "q \<noteq> {}" and "n' \<in> S\<^sub>2" and "quorum n' q" 
          using \<open>self_reliant S\<^sub>2\<close> quorum_not_empty self_reliant_def 
          by (metis all_not_in_conv) 
        hence "q\<^sub>1 \<inter> q \<noteq> {}" 
          by (metis \<open>self_reliant S\<^sub>2\<close> \<open>self_reliant S\<^sub>1\<close> \<open>n\<^sub>1 \<in> S\<^sub>1\<close> \<open>quorum n\<^sub>1 q\<^sub>1\<close> quorum_intersection)
        hence "q\<^sub>1 \<inter> S\<^sub>2 \<noteq> {}" using \<open>q \<subseteq> S\<^sub>2\<close>
          by (metis inf_commute inf_sup_distrib2 sup.absorb_iff1 sup_bot.left_neutral) 
        with this obtain n'' where "n'' \<in> S\<^sub>2 \<inter> q\<^sub>1"
          by (metis all_not_in_conv inf_commute)
        moreover have "quorum n'' q\<^sub>1"
          by (metis Int_iff \<open>quorum n\<^sub>1 q\<^sub>1\<close> calculation quorum_closed) 
        ultimately show ?thesis using that[of n'']
          by (metis IntE)  
      qed
      thus \<open>W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> by (metis \<open>quorum n\<^sub>2 q\<^sub>2\<close> \<open>self_reliant S\<^sub>2\<close> self_reliant_def \<open>n\<^sub>2 \<in> S\<^sub>2\<close>) 
    qed
    ultimately show "W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" using assms that by force 
  qed
  ultimately show "self_reliant (S\<^sub>1 \<union> S\<^sub>2)" using self_reliant_def by force 
qed

end

section \<open>SCP Quorums\<close>

text \<open>In SCP, quorums are derived from the slices of nodes\<close>

locale SCP_quorums = 
  fixes Q :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>the well-behaved nodes\<close>
begin

definition quorum where 
  "quorum q \<equiv> \<forall> n \<in> q . \<exists> S \<in> Q n . S \<subseteq> q"

definition quorum_of where
  "quorum_of n q \<equiv> n \<in> q \<and> quorum q"

lemma quorums_closed: \<comment> \<open>This is trivial\<close>
  assumes "quorum_of n q" and "n' \<in> q"
  shows "quorum_of n' q"
  using assms unfolding quorum_of_def by auto

end

end