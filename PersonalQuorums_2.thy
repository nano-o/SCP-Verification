section Introduction

theory PersonalQuorums
imports Main
begin

text \<open>
The Stellar Consensus Protocol (SCP) uses Federated Voting to implement some form of Consensus in an environment in which nodes do not 
have a uniform view of the whole system but do know about a subset of the nodes and can assign them some degree of trust.
Trust relationships are used to build quorums, i.e. sets of nodes considered trustworthy as a whole by their members.
Node act on information agreed upon by one of the quorums they belong to.

In SCP, quorums are built by a mechanism based on quorum slices, which embody node's trust relationships.
In this document we investigate what are the abstract properties that quorums must satisfy, independently of how they are built, in order for
Federating Voting to implement Atomic Broadcast, which is the condition relied upon by SCP.

We present conditions that seem necessary for allowing a subset of the nodes to achieve quorum-based atomic broadcast.
Moreover we note that federated voting achieves atomic broadcast under those condition, making the conditions and SCP, in some sense, optimal.
Finally, we show that, under some quorum intersection property, there is a unique maximal set of nodes, called the intact nodes, that can achieve atomic broadcast.

The ideas presented here were developed with Eli Gafni.
\<close>

section \<open>Personal Quorums\<close>

text \<open>
We start by modeling a system in which each node has a set of quorums, called its personal quorums.
We also fix a set @{text W} of well-behaved nodes.

The only assumption is that quorums are closed, which means that if @{text q} is 
a quorum of @{text n} and @{text "n' \<in> q"}, then @{text q} is also a quorum of @{text n'}.
Note that the Stellar quorums, derived from slices, do satisfy this assumption.\<close>

locale personal_quorums = 
  fixes W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
  fixes quorum :: "'node \<Rightarrow> 'node set \<Rightarrow> bool" \<comment> \<open>the quorums of each node\<close>
  assumes
    quorum_closed: "\<And> q n\<^sub>1 n\<^sub>2 . \<lbrakk>quorum n\<^sub>1 q; n\<^sub>2 \<in> q\<rbrakk> \<Longrightarrow> quorum n\<^sub>2 q"
begin

text \<open>
Given a subset @{text S} of the nodes, we can implement atomic broadcast based on quorums for @{text S} only if (a) every node in @{text S} has a quorum in @{text S}, 
and (b) given two nodes @{text "n\<^sub>1\<in>S"} and @{text "n\<^sub>2\<in>S"}, if @{text q\<^sub>1} is a quorum of @{text n\<^sub>1} and @{text q\<^sub>2} is a quorum of @{text n\<^sub>2}, 
then @{text q\<^sub>1} and @{text q\<^sub>2} intersect at a well-behaved node.

In this file not only require intersection at a well-behaved node, but also intersection at @{text S}.
This is what SCP requires.
It seems to be a tradeoff between performance and resilience.

We call such a non-empty subset S of nodes a self-reliant subset.
\<close>

definition self_reliant where "self_reliant S \<equiv> S \<noteq> {} \<and> (\<forall> n \<in> S . \<exists> S' . S' \<subseteq> S \<and> quorum n S')
    \<and> (\<forall> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 . n\<^sub>1 \<in> S \<and> quorum n\<^sub>1 q\<^sub>1 \<and> n\<^sub>2 \<in> S \<and> quorum n\<^sub>2 q\<^sub>2  \<longrightarrow> (S \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}))"

text \<open>@{text B} is a blocking set for node @{text n} when @{text B} intersects all quorums of @{text n}.
This is meant to replace the definition of blocking set in Federated Voting.\<close>

definition blocking where "blocking n B \<equiv> \<forall> q . quorum n q \<longrightarrow> B \<inter> q \<noteq> {}"

text \<open>If a set @{text B} blocks a node belonging to a self-reliant set @{text S}, then @{text B} intersects @{text S}.
This implies that Federated Voting is safe for a self-reliant set.\<close>

lemma blocking_intersects_self_reliant:
  assumes "n \<in> S" and "blocking n B" and "self_reliant S" 
  shows "B \<inter> S \<noteq> {}"
  using assms self_reliant_def blocking_def by fastforce 

text \<open>Moreover, any quorum of a self-reliant set @{text S} is blocking for any member of @{text S}.
This implies that Federated Voting implements atomic broadcast for a self-reliant set.
Thus Federated Voting is in some sense optimal, since the self-reliant property is necessary for atomic broadcast based on quorums.\<close>

lemma quorum_is_blocking:
  assumes "self_reliant S" and "n \<in> S" and "quorum n q"
  shows "blocking n q"
  by (metis Int_assoc assms blocking_def inf_bot_right self_reliant_def) 

end

section \<open>Existence of a unique maximal self-reliant set\<close>

text \<open>Here we show that if  we assume that quorums of self-reliant sets intersect, then there
exists a unique maximal self-reliant set. 
To make a parallel with the Stellar White-Paper, we can call this maximal set the set of intact nodes.\<close>

locale max_self_reliant = personal_quorums +
  assumes quorum_intersection:  "\<And> q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 S\<^sub>1 S\<^sub>2. 
    \<lbrakk>n\<^sub>1 \<in> S\<^sub>1; n\<^sub>2 \<in> S\<^sub>2; quorum n\<^sub>1 q\<^sub>1; quorum n\<^sub>2 q\<^sub>2; self_reliant S\<^sub>1; self_reliant S\<^sub>2\<rbrakk> 
    \<Longrightarrow> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}"
begin

text \<open>We can now show that the union of two self-reliant sets is self-reliant.
This implies that there is a unique maximal self-reliant set, which we call the set of intact nodes.\<close>

lemma quorum_not_empty:
  assumes "self_reliant S" and "n \<in> S" and "quorum n q"
  shows "q \<noteq> {}"
  using assms quorum_intersection by fastforce 

text \<open>To prove that the union of two self-reliant sets is self-reliant, we consider two self-reliant sets @{text S\<^sub>1} and @{text S\<^sub>2}
and show that @{text "S\<^sub>1 \<union> S\<^sub>2"} satisfies the three properties of self-reliant sets.

The first properties follow trivially from the assumption that @{text S\<^sub>1} and @{text S\<^sub>2} are self-reliant: @{text "S\<^sub>1 \<union> S\<^sub>2 \<noteq> {}"} and every member of @{text "S\<^sub>1 \<union> S\<^sub>2"} has a quorum in @{text "S\<^sub>1 \<union> S\<^sub>2"}.

We now show the third property, i.e. that given two nodes @{text n\<^sub>1} and @{text n\<^sub>2} in @{text "S\<^sub>1 \<union> S\<^sub>2"} and two sets @{text q\<^sub>1} and @{text q\<^sub>2} such that 
@{text q\<^sub>1} is a quorum of @{text n\<^sub>1} and @{text q\<^sub>2} is a quorum of @{text n\<^sub>2}, @{text q\<^sub>1} and @{text q\<^sub>2} intersect at a well-behaved node.

First, if @{term "n\<^sub>1"} and @{term "n\<^sub>2"} are both in @{term "S\<^sub>1"} or both in @{term "S\<^sub>2"},
then, by the definition of self-reliant, we trivially have that @{term q\<^sub>1} and @{term q\<^sub>1} intersect at a well-behaved node.
Without loss of generality, we therefore assume that @{term "n\<^sub>1\<in>S\<^sub>1"} and @{term "n\<^sub>2\<in>S\<^sub>2"}

Note that, since @{text S\<^sub>2} is self-reliant, there is a node @{text "n \<in> S\<^sub>2"} and a set @{text "q \<subseteq> S\<^sub>2"} where @{text q} is a quorum of n.
Then, because of the  @{text quorum_intersection} assumption, applied to the self-reliant sets @{term "S\<^sub>1"} and @{term "S\<^sub>2"},
we get that @{text "q \<inter> q1 \<noteq> {}"}. Since @{text "q\<subseteq>S\<^sub>2"}, we have thus obtained a node @{text n'} where 
@{text "n'\<in> S\<^sub>2 \<inter> q1"}. Because @{text q\<^sub>1} is a quorum of @{text n\<^sub>1}, using the @{text quorum_closed} 
assumption we get that @{text q\<^sub>1} is a quorum of @{text "n'\<in> S\<^sub>2"}.
Finally, because @{text S\<^sub>2} is a self-reliant set, any two quorums of nodes in @{text S\<^sub>2} intersect at a well-behaved node.
Therefore @{text q\<^sub>1} and @{text q\<^sub>2} intersect at a well-behaved node.

Below is the Isabelle version of the proof.
\<close>

lemma union_closed:
  assumes "self_reliant S\<^sub>1" and "self_reliant S\<^sub>2" 
  shows "self_reliant (S\<^sub>1 \<union> S\<^sub>2)"
proof -
  have "S\<^sub>1 \<union> S\<^sub>2 \<noteq> {}"
    using assms(2) self_reliant_def by auto 
  moreover
  have "\<exists> S' . S' \<subseteq> (S\<^sub>1 \<union> S\<^sub>2) \<and> quorum n S'" if "n \<in> S\<^sub>1 \<union> S\<^sub>2" for n
    using assms unfolding self_reliant_def
    by (metis UnE le_supI1 le_supI2 that)
  moreover  
  have "(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" 
    if "n\<^sub>1 \<in> S\<^sub>1 \<union> S\<^sub>2" and "quorum n\<^sub>1 q\<^sub>1" and "n\<^sub>2 \<in> S\<^sub>1 \<union> S\<^sub>2" and "quorum n\<^sub>2 q\<^sub>2" for q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2
  proof -
    have \<open>(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> 
      if "n\<^sub>1 \<in> S" and "n\<^sub>2 \<in> S" and "S = S\<^sub>1 \<or> S = S\<^sub>2" for S 
      using \<open>self_reliant S\<^sub>1\<close> \<open>self_reliant S\<^sub>2\<close> that \<open>quorum n\<^sub>1 q\<^sub>1\<close> \<open>quorum n\<^sub>2 q\<^sub>2\<close> unfolding self_reliant_def 
      by (metis Un_empty inf_sup_distrib2) 
    moreover
    have \<open>(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> if "n\<^sub>1 \<in> S\<^sub>1" and "n\<^sub>2 \<in> S\<^sub>2"
    proof -
      obtain n where "n \<in> S\<^sub>2" and "quorum n q\<^sub>1"
      proof -
        obtain n' q where "q \<subseteq> S\<^sub>2" and "q \<noteq> {}" and "n' \<in> S\<^sub>2" and "quorum n' q" 
          using \<open>self_reliant S\<^sub>2\<close> quorum_not_empty self_reliant_def
          by (metis all_not_in_conv) 
        hence "q\<^sub>1 \<inter> q \<noteq> {}" 
          using \<open>self_reliant S\<^sub>2\<close> \<open>self_reliant S\<^sub>1\<close> \<open>n\<^sub>1 \<in> S\<^sub>1\<close> \<open>quorum n\<^sub>1 q\<^sub>1\<close> quorum_intersection by blast 
        hence "q\<^sub>1 \<inter> S\<^sub>2 \<noteq> {}" using \<open>q \<subseteq> S\<^sub>2\<close> by blast 
        thus ?thesis  using \<open>quorum n\<^sub>1 q\<^sub>1\<close> quorum_closed that by auto
      qed
      thus \<open>(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> using \<open>quorum n\<^sub>2 q\<^sub>2\<close> \<open>self_reliant S\<^sub>2\<close> self_reliant_def \<open>n\<^sub>2 \<in> S\<^sub>2\<close>
        by (metis Un_empty inf_sup_distrib2) 
    qed
    moreover
    have \<open>(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> if "n\<^sub>2 \<in> S\<^sub>1" and "n\<^sub>1 \<in> S\<^sub>2"
    \<comment> \<open>This is the symmetric of what we just did:\<close>
    proof -
      obtain n where "n \<in> S\<^sub>2" and "quorum n q\<^sub>2"
      proof -
        obtain n' q where "q \<subseteq> S\<^sub>2" and "q \<noteq> {}" and "n' \<in> S\<^sub>2" and "quorum n' q" using \<open>self_reliant S\<^sub>2\<close> quorum_not_empty self_reliant_def
          by (metis all_not_in_conv) 
        hence "q\<^sub>2 \<inter> q \<noteq> {}" using \<open>self_reliant S\<^sub>2\<close> \<open>self_reliant S\<^sub>1\<close> \<open>n\<^sub>2 \<in> S\<^sub>1\<close> \<open>quorum n\<^sub>2 q\<^sub>2\<close> quorum_intersection by blast 
        hence "q\<^sub>2 \<inter> S\<^sub>2 \<noteq> {}" using \<open>q \<subseteq> S\<^sub>2\<close> by blast 
        thus ?thesis using \<open>quorum n\<^sub>2 q\<^sub>2\<close> quorum_closed that by auto
      qed
      thus "(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" using  \<open>quorum n\<^sub>1 q\<^sub>1\<close> \<open>self_reliant S\<^sub>2\<close> self_reliant_def \<open>n\<^sub>1 \<in> S\<^sub>2\<close> 
        by (metis Un_empty inf_sup_distrib2) 
    qed 
    ultimately show "(S\<^sub>1 \<union> S\<^sub>2) \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" using \<open>n\<^sub>1 \<in> S\<^sub>1 \<union> S\<^sub>2\<close> \<open>n\<^sub>2 \<in> S\<^sub>1 \<union> S\<^sub>2\<close> by blast 
  qed
  ultimately show "self_reliant (S\<^sub>1 \<union> S\<^sub>2)" using self_reliant_def by force 
qed

text \<open>Now just an observation: The union of two quorum is not necessarily a quorum; this is one example of a property of quorums obtained through slices that is not needed in our setting.\<close>
lemma assumes "quorum n\<^sub>1 q\<^sub>1" and "quorum n\<^sub>2 q\<^sub>2"
  shows "\<exists> n . quorum n (q\<^sub>1 \<union> q\<^sub>2)" nitpick oops

end


end