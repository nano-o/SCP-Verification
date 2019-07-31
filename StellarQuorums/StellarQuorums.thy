text 
\<open>This theory formalizes some of the results appearing in the paper "Stellar Consensus By Reduction"\cite{disc_paper}.
We prove static properties of personal Byzantine quorum systems and Stellar quorum systems.\<close>

theory StellarQuorums
  imports Main 
begin

section "Personal Byzantine quorum systems"

locale personal_quorums =
  fixes quorum_of :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  assumes quorum_assm:"\<And> p p' . \<lbrakk>p \<in> W; quorum_of p Q; p' \<in> Q\<inter>W\<rbrakk> \<Longrightarrow> quorum_of p' Q"
    \<comment> \<open>In other words, a quorum (of some participant) is a quorum of all its members.\<close>
begin

\<^cancel>\<open>
definition quorum where "quorum Q \<equiv> \<exists> p. quorum_of p Q"
\<close>

definition blocks where
  \<comment> \<open>Set @{term R} blocks participant @{term p}.\<close>
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"

abbreviation blocked_by where "blocked_by R \<equiv> {p . blocks R p}"

lemma blocked_blocked_subset_blocked:
  "blocked_by (blocked_by R) \<subseteq> blocked_by R"
proof -
  have False if "p \<in> blocked_by (blocked_by R)" and "p \<notin> blocked_by R" for p
  proof -
    have "Q \<inter> blocked_by R \<noteq> {}" if "quorum_of p Q" for Q
      using \<open>p \<in> blocked_by (blocked_by R)\<close> that unfolding blocks_def by auto
    have "Q \<inter> R \<noteq> {}" if " quorum_of p Q" for Q
    proof -
      obtain p' where "p' \<in> blocked_by R" and "p' \<in> Q"
        by (meson Int_emptyI \<open>\<And>Q. quorum_of p Q \<Longrightarrow> Q \<inter> blocked_by R \<noteq> {}\<close> \<open>quorum_of p Q\<close>)
      hence "quorum_of p' Q"
        using quorum_assm that by blast
      with \<open>p' \<in> blocked_by R\<close> show "Q \<inter> R \<noteq> {}"
        using blocks_def by auto
    qed
    hence "p \<in> blocked_by R" by (simp add: blocks_def)
    thus False using that(2) by auto
  qed
  thus "blocked_by (blocked_by R) \<subseteq> blocked_by R"
    by blast
qed

end

text \<open>We now add the set of correct nodes to the model.\<close>

locale with_w = personal_quorums quorum_of for quorum_of  :: "'node \<Rightarrow> 'node set \<Rightarrow> bool" +
  fixes W::"'node set"
begin

abbreviation B where "B \<equiv> -W"
  \<comment> \<open>@{term B} is the set of malicious nodes.\<close>

definition quorum_of_set where "quorum_of_set S Q \<equiv> \<exists> p \<in> S . quorum_of p Q"

subsection "The set of participants not blocked by malicious participants"

definition L where "L \<equiv> W - (blocked_by B)"

lemma l2: "p \<in> L \<Longrightarrow> \<exists> Q  \<subseteq> W. quorum_of p Q" 
  unfolding L_def blocks_def using DiffD2 by auto
 
lemma l3:
\<comment>  \<open>If a participant is not blocked by the malicious participants, then it has a quorum consisting exclusively of correct 
participants which are not blocked by the malicious participants.\<close>
  assumes "p \<in> L" shows "\<exists> Q \<subseteq> L . quorum_of p Q"
proof -
  have False if "\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> (-L) \<noteq> {}"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> W" 
      using l2 \<open>p \<in> L\<close> by auto 
    have "Q \<inter> (-L) \<noteq> {}"  using that \<open>quorum_of p Q\<close> by simp
    obtain p' where "p' \<in> Q \<inter> (-L)" and "quorum_of p' Q"
      using \<open>Q \<inter> - L \<noteq> {}\<close> \<open>quorum_of p Q\<close> inf.left_idem quorum_assm by fastforce 
    hence "Q \<inter> B \<noteq> {}" unfolding L_def
      using CollectD Compl_Diff_eq Int_iff inf_le1 personal_quorums.blocks_def personal_quorums_axioms subset_empty by fastforce
    thus False using \<open>Q \<subseteq> W\<close> by auto  
  qed 
  thus ?thesis by (metis disjoint_eq_subset_Compl double_complement)
qed

subsection "Consensus clusters and intact sets"

definition is_intertwined where
  \<comment> \<open>This definition is not used in this theory,
    but we include it to formalize the notion of intertwined set appearing in the DISC paper.\<close>
  "is_intertwined S \<equiv> S \<subseteq> W 
    \<and> (\<forall> Q Q' . quorum_of_set S Q \<and> quorum_of_set S Q' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition is_cons_cluster where
  \<comment> \<open>Consensus clusters\<close>
  "is_cons_cluster I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<subseteq> I . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set I Q \<and> quorum_of_set I Q' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition stellar_intact where
  \<comment> \<open>This is equivalent to the notion of intact set presented in the Stellar Whitepaper~\cite{MazieresStellarConsensusProtocol2015}\<close>
  "stellar_intact I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<subseteq> I . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set I Q \<and> quorum_of_set I Q' \<longrightarrow> I \<inter> Q \<inter> Q' \<noteq> {})"

lemma stellar_intact_imp_cons_cluster:
\<comment> \<open>Every intact set is a consensus cluster\<close>
  shows "stellar_intact I \<Longrightarrow> is_cons_cluster I" 
  unfolding stellar_intact_def is_cons_cluster_def
  by blast 

lemma cons_cluster_not_intact:
  \<comment> \<open>Some consensus clusters are not intact and have no intact superset.\<close>
  shows "is_cons_cluster I \<and> (\<forall> J . I \<subseteq> J \<longrightarrow> \<not>stellar_intact J)" nitpick[falsify=false, card 'node=3, expect=genuine]
  oops

text \<open>Next we show that the union of two consensus clusters that intersect is a consensus cluster.\<close>

lemma cluster_union:
  assumes "is_cons_cluster I\<^sub>1" and "is_cons_cluster I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_cons_cluster (I\<^sub>1\<union> I\<^sub>2)"
proof -
  have "I\<^sub>1 \<union> I\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_cons_cluster_def by auto 
  moreover
  have "\<forall> p \<in> (I\<^sub>1\<union>I\<^sub>2) . \<exists> Q \<subseteq> (I\<^sub>1\<union>I\<^sub>2) . quorum_of p Q" 
    using \<open>is_cons_cluster I\<^sub>1\<close> \<open>is_cons_cluster I\<^sub>2\<close> unfolding is_cons_cluster_def
    by (meson UnE le_supI1 le_supI2)
  moreover
  have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}"
    if "quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>1" and "quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>2" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "quorum_of_set I Q\<^sub>1" and "quorum_of_set I Q\<^sub>2" and "I = I\<^sub>1 \<or> I = I\<^sub>2" for I
      using \<open>is_cons_cluster I\<^sub>1\<close> \<open>is_cons_cluster I\<^sub>2\<close> \<open>quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>1\<close> \<open>quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>2\<close> that
      unfolding quorum_of_set_def is_cons_cluster_def by metis
    moreover
    have \<open>W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "is_cons_cluster I\<^sub>1" and "is_cons_cluster I\<^sub>2"
      and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "quorum_of_set I\<^sub>1 Q\<^sub>1" and "quorum_of_set I\<^sub>2 Q\<^sub>2"
    for I\<^sub>1 I\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      obtain p Q where "quorum_of p Q" and "p \<in> I\<^sub>1 \<inter> I\<^sub>2" and "Q \<subseteq> I\<^sub>2" 
        using \<open>I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}\<close> \<open>is_cons_cluster I\<^sub>2\<close> unfolding is_cons_cluster_def by blast
      have "Q \<inter> Q\<^sub>1 \<noteq> {}" using \<open>is_cons_cluster I\<^sub>1\<close> \<open>quorum_of_set I\<^sub>1 Q\<^sub>1\<close> \<open>quorum_of p Q\<close> \<open>p \<in> I\<^sub>1 \<inter> I\<^sub>2\<close>
        unfolding is_cons_cluster_def quorum_of_set_def
        by (metis Int_assoc Int_iff inf_bot_right)
      hence "quorum_of_set I\<^sub>2 Q\<^sub>1"  using \<open>Q \<subseteq> I\<^sub>2\<close> \<open>quorum_of_set I\<^sub>1 Q\<^sub>1\<close> quorum_assm unfolding quorum_of_set_def by blast 
      thus "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" using \<open>is_cons_cluster I\<^sub>2\<close> \<open>quorum_of_set I\<^sub>2 Q\<^sub>2\<close>
        unfolding is_cons_cluster_def by blast
    qed
    ultimately show ?thesis using assms that unfolding quorum_of_set_def by auto 
  qed
  ultimately show ?thesis using assms
    unfolding is_cons_cluster_def by simp
qed

end

section "Stellar quorum systems"

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>the well-behaved nodes\<close>
  assumes slices_ne:"\<And>p . p \<in> W \<Longrightarrow> slices p \<noteq> {}"
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . (\<exists> Sl \<in> slices p . Sl \<subseteq> Q)"

definition quorum_of where "quorum_of p Q \<equiv> quorum Q \<and> (p \<notin> W \<or> (\<exists> Sl \<in> slices p . Sl \<subseteq> Q))"
  \<comment> \<open>TODO: @{term "p\<notin>W"} needed?\<close>

lemma quorum_union:"quorum Q \<Longrightarrow> quorum Q' \<Longrightarrow> quorum (Q \<union> Q')"
  unfolding quorum_def
  by (metis IntE Int_iff UnE inf_sup_aci(1) sup.coboundedI1 sup.coboundedI2)

lemma l1:
  assumes "\<And> p . p \<in> S \<Longrightarrow> \<exists> Q \<subseteq> S . quorum_of p Q" and "p\<in> S"
  shows "quorum_of p S" using assms unfolding quorum_of_def quorum_def
  by (meson Int_iff subset_trans)

lemma is_pbqs:
  assumes "quorum_of p Q" and "p' \<in> Q"
  shows "quorum_of p' Q" 
  \<comment> \<open>This is the property required of a PBQS.\<close>
  using assms
  by (simp add: quorum_def quorum_of_def)

interpretation with_w quorum_of 
  \<comment> \<open>Stellar quorums form a personal quorum system.\<close>
  unfolding with_w_def personal_quorums_def 
  quorum_def quorum_of_def by simp

lemma quorum_is_quorum_of_some_slice:
  assumes "quorum_of p Q" and "p \<in> W"
  obtains S where "S \<in> slices p" and "S \<subseteq> Q"
    and "\<And> p' . p' \<in> S \<inter> W \<Longrightarrow> quorum_of p' Q"
  using assms unfolding quorum_def quorum_of_def by fastforce

lemma "is_cons_cluster C \<Longrightarrow> quorum C" 
  \<comment> \<open>Every consensus cluster is a quorum.\<close>
  unfolding is_cons_cluster_def
  by (metis inf.order_iff l1 quorum_of_def stellar.quorum_def stellar_axioms) 

subsection \<open>Properties of blocking sets\<close>

inductive blocking_min where
  \<comment> \<open>This is the set of correct participants that are eventually blocked by a set @{term R} when byzantine processors do not take steps.\<close>
  "\<lbrakk>p \<in> W; \<forall> Sl \<in> slices p . \<exists> q \<in> Sl\<inter>W . q \<in> R \<or> blocking_min R q\<rbrakk> \<Longrightarrow> blocking_min R p"
inductive_cases blocking_min_elim:"blocking_min R p"

inductive blocking_max where
  \<comment> \<open>This is the set of participants that are eventually blocked by a set @{term R} when byzantine processors help epidemic propagation.\<close>
  "\<lbrakk>p \<in> W; \<forall> Sl \<in> slices p . \<exists> q \<in> Sl . q \<in> R\<union>B \<or> blocking_max R q\<rbrakk> \<Longrightarrow> blocking_max R p"
inductive_cases "blocking_max R p"

text \<open>Next we show that if @{term \<open>R\<close>} blocks @{term \<open>p\<close>} and @{term p} belongs to a consensus cluster @{term S}, then @{term \<open>R \<inter> S \<noteq> {}\<close>}.\<close>

text \<open>We first prove two auxiliary lemmas:\<close>

lemma cons_cluster_wb:"p \<in> I \<Longrightarrow> is_cons_cluster I \<Longrightarrow> p\<in>W"
  using is_cons_cluster_def  by fastforce 

lemma cons_cluster_has_cons_cluster_slice:
  assumes "is_cons_cluster I" and "p\<in>I"
  obtains Sl where "Sl \<in> slices p" and "Sl \<subseteq> I"
proof -
  obtain Q where "quorum_of p Q" and "Q \<subseteq> I" 
    using \<open>is_cons_cluster I\<close> \<open>p\<in>I\<close> unfolding is_cons_cluster_def by blast
  obtain Sl where "Sl \<in> slices p" and "Sl \<subseteq> Q"
    using quorum_is_quorum_of_some_slice \<open>p\<in>I\<close> \<open>is_cons_cluster I\<close> cons_cluster_wb \<open>quorum_of p Q\<close> by metis
  show ?thesis using that \<open>Sl \<subseteq> Q\<close> \<open>Q \<subseteq> I\<close> \<open>Sl \<in> slices p\<close> by simp
qed

theorem blocking_max_intersects_intact:
  \<comment> \<open>if @{term \<open>R\<close>} blocks @{term \<open>p\<close>} when malicious participants help epidemic propagation, 
and @{term p} belongs to a consensus cluster @{term S}, then @{term \<open>R \<inter> S \<noteq> {}\<close>}\<close>
  assumes  "blocking_max R p" and "is_cons_cluster S" and "p \<in> S"
  shows "R \<inter> S \<noteq> {}" using assms
proof (induct)
  case (1 p R)
  obtain Sl where "Sl \<in> slices p" and "Sl \<subseteq> S" using cons_cluster_has_cons_cluster_slice
    using "1.prems" by blast
  moreover have "Sl \<subseteq> W" using assms(2) calculation(2) is_cons_cluster_def by auto 
  ultimately show ?case
    using "1.hyps" assms(2) by fastforce
qed

text \<open>Now we show that if @{term \<open>p \<in> S\<close>}, @{term S} is a consensus cluster, and quorum @{term Q} is such that @{term \<open>Q \<inter> S \<noteq> {}\<close>},
    then @{term \<open>Q \<inter> W\<close>} blocks @{term p}. 

We start by defining the set of participants reachable from a participant through correct participants.
Their union trivially forms a quorum. 
Moreover, if @{term p} is not blocked by a set @{term R}, 
then we show that the set of participants reachable from @{term p} minus @{term R} and all participants blocked by @{term R} forms a quorum.
It follows that if @{term p } is a member of a consensus cluster @{term S} and @{term Q} is a quorum of a member of @{term S}, then @{term "Q\<inter>W"}
 must block @{term p}, as otherwise quorum intersection would be violated. \<close>

inductive reachable_slice for p where
\<comment> \<open>Slices reachable from @{term p} through correct participants\<close>
  "Sl \<in> slices p \<Longrightarrow> reachable_slice p Sl"
| "\<lbrakk>reachable_slice p Sl'; q \<in> Sl'\<inter>W; Sl \<in> slices q\<rbrakk> \<Longrightarrow> reachable_slice p Sl"

definition reachable 
\<comment> \<open>The participants reachable from @{term p} through correct participants.\<close>
  where "reachable p = \<Union>{Sl . reachable_slice p Sl}"

\<^cancel>\<open>
lemma reachable_is_quorum:
  assumes "p \<in> W"
  shows "quorum (reachable p)"
proof -
  have "\<exists> Sl \<in> slices q . Sl \<subseteq> reachable p" if "reachable_slice p Sl" and "q\<in>Sl\<inter>W" for q Sl unfolding reachable_def
    using slices_ne reachable_slice.intros(2) that by fastforce 
  thus ?thesis unfolding quorum_def reachable_def
    by (metis Int_iff mem_Collect_eq mem_simps(9))
qed\<close>

lemma reachable_minus_blocked_min_is_quorum:
  fixes R p
  defines "bmin \<equiv>  {q . blocking_min R q}"
  assumes "p\<in>W" and "\<not>blocking_min R p" and "R\<subseteq>W" and "p\<notin>R"
  shows "quorum ({p} \<union> reachable p - (bmin \<union> R))"
proof -
  have "bmin \<union> R \<subseteq> W" using blocking_min_elim bmin_def assms(4) by auto
  text \<open>First, if @{term q} is correct and reachable from @{term p}, then all slices of @{term q} are reachable from @{term p}\<close>
  have "Sl \<subseteq> reachable p" if "Sl \<in> slices q" and "q \<in> reachable p \<inter> W" for Sl q
    using that unfolding reachable_def using reachable_slice.intros
    by (metis CollectD CollectI Int_Union2 UN_E Union_upper) 
  moreover
  text \<open>Second, if @{term q} is correct, reachable from @{term p}, and not blocked by @{term R}, 
  then q must have a slice that does not intersect the set of participants blocked by @{term R}. 
  Otherwise, @{term q} would by blocked by @{term R}.\<close>
  have "\<exists> Sl \<in> slices q . Sl \<inter> (bmin \<union> R) = {}" if "q \<in> (reachable p - (bmin \<union> R)) \<inter> W" for q 
  proof -
    have "q \<notin> bmin" and "q\<in> W" using that by auto
    have "\<exists> Sl . Sl \<in> slices q \<and> Sl \<inter> (bmin \<union> R) = {}"
    proof (rule ccontr)
      assume a:"\<not>(\<exists>Sl. Sl \<in> slices q \<and> Sl \<inter> (bmin \<union> R) = {})" 
      have "q \<in> bmin" if "\<forall> Sl \<in> slices q . Sl \<inter> (bmin \<union> R) \<noteq> {}" 
      proof -
        have "Sl \<inter> (bmin \<union> R) \<subseteq> W" for Sl using \<open>bmin \<union> R \<subseteq> W\<close> by blast 
        hence "\<forall> Sl \<in> slices q . \<exists> q' \<in> Sl \<inter> W . q' \<in> R \<or> blocking_min R q'" using that unfolding bmin_def by fast
        thus ?thesis
          by (metis CollectI \<open>q \<in> W\<close> blocking_min.intros bmin_def)
      qed
      with a have "q \<in> bmin" by auto
      with \<open>q \<notin> bmin\<close> show False by auto
    qed
    from this obtain Sl where "Sl \<in> slices q" and "Sl \<inter> (bmin \<union> R) = {}" by auto
    thus ?thesis using that by metis 
  qed
  ultimately
  have "\<exists> Sl \<in> slices q . Sl \<subseteq> reachable p - (bmin \<union> R)" if "q \<in> (reachable p - (bmin \<union> R)) \<inter> W" for q
    by (metis DiffD1 Diff_Int_distrib2 Diff_eq Int_subset_iff disjoint_eq_subset_Compl that)
  hence 1:"\<exists> Sl \<in> slices q . Sl \<subseteq> {p} \<union> reachable p - (bmin \<union> R)" if "q \<in> (reachable p - (bmin \<union> R)) \<inter> W" for q
    by (meson Diff_mono Un_upper2 subset_refl subset_trans that)

  text \<open>The same two properties hold for @{term p} itself.\<close>
  
  have "Sl \<subseteq> reachable p" if "Sl \<in> slices p" for Sl unfolding reachable_def
    by (simp add: Union_upper reachable_slice.intros(1) that)
  moreover
  have "\<exists> Sl \<in> slices p . Sl \<inter> (bmin \<union> R) = {}"  
  proof (rule ccontr; simp)
    assume "\<forall> Sl\<in>slices p. Sl\<inter> (bmin \<union> R) \<noteq> {}"
    hence "\<forall> Sl \<in> slices p . \<exists> q \<in> Sl \<inter> W . q \<in> R \<or> blocking_min R q" using  \<open>bmin \<union> R \<subseteq> W\<close>  unfolding bmin_def by fastforce
    hence "blocking_min R p" using \<open>p\<in>W\<close> blocking_min.intros unfolding bmin_def by simp
    thus False using \<open>\<not>blocking_min R p\<close> by blast
  qed
  ultimately have 2:"\<exists> Sl \<in> slices p . Sl \<subseteq> {p} \<union> reachable p - (bmin \<union> R)"
    by (metis Diff_mono Diff_triv insert_is_Un subset_insertI2 subset_refl)

  text \<open>Now, by the definition of quorum, we trivially have that @{term "reachable p - bmin"} is a quorum.\<close>
  show ?thesis using 1 2 unfolding quorum_def by blast
qed

theorem quorum_blocks_cons_cluster:
  assumes "quorum_of_set I Q" and "p\<in>I" and "is_cons_cluster I" and "p \<notin> Q"
  shows "blocking_min (Q \<inter> W) p"
proof (rule ccontr)
  have "p\<in>W" using assms(2-3) cons_cluster_wb by blast 
  assume "\<not> blocking_min (Q \<inter> W) p"
  define bmin where "bmin \<equiv>  {q . blocking_min (Q \<inter> W) q}"
  define Q' where "Q' \<equiv> {p} \<union> reachable p - (bmin \<union> (Q \<inter> W))"
  have "quorum Q'" unfolding Q'_def
    using \<open>\<not> blocking_min (Q \<inter> W) p\<close> \<open>p \<in> W\<close> bmin_def stellar.reachable_minus_blocked_min_is_quorum stellar_axioms \<open>p \<notin> Q\<close> by fastforce
  moreover have "p\<in>Q'" unfolding Q'_def using \<open>p\<notin>Q\<close> bmin_def \<open>\<not>blocking_min (Q\<inter>W) p\<close> by auto
  ultimately have "quorum_of_set I Q'"
    using assms(2) quorum_of_set_def stellar.quorum_def stellar.quorum_of_def stellar_axioms 
    unfolding quorum_def quorum_of_def by blast 
  have "Q' \<inter> (Q\<inter>W) = {}" unfolding Q'_def by blast
  show False
    by (metis \<open>Q' \<inter> (Q \<inter> W) = {}\<close> \<open>quorum_of_set I Q'\<close> assms(1) assms(3) inf_commute is_cons_cluster_def)
qed

section \<open>Reachability through a set\<close>

text \<open>Here we define the part of a quorum Q of p that is reachable through correct
nodes from p. We show that if p and p' are members of the same consensus cluter and Q is a quorum of p and Q' is a quorum of p',
then the intersection of Q, Q', and W is reachable from both p and p' through the consensus cluster.\<close>

inductive reachable_through for p S where
  "reachable_through p S p"
| "\<lbrakk>reachable_through p S p'; p' \<in> W; Sl \<in> slices p'; Sl \<subseteq> S; p'' \<in> Sl\<rbrakk> \<Longrightarrow> reachable_through p S p''"

definition truncation where "truncation p S \<equiv> {p' . reachable_through p S p'}"

lemma l13:
  assumes "quorum_of p Q" and "p \<in> W" and "reachable_through p Q p'"
  shows "quorum_of p' Q"
  using assms using quorum_assm reachable_through.cases
  by (metis is_pbqs subset_iff)

lemma l14:
  assumes "quorum_of p Q" and "p \<in> W"
  shows "quorum (truncation p Q)"
proof -
  have "\<exists> S \<in> slices p' . \<forall> q \<in> S . reachable_through p Q q" if "reachable_through p Q p'" and "p' \<in> W" for p'
    by (meson assms l13 quorum_is_quorum_of_some_slice stellar.reachable_through.intros(2) stellar_axioms that)
  thus ?thesis
    by (metis IntE mem_Collect_eq stellar.quorum_def stellar_axioms subsetI truncation_def)  
qed

lemma l15:
  assumes "is_cons_cluster I" and "quorum_of p Q" and "quorum_of p' Q'" and "p \<in> I" and "p' \<in> I" and "Q \<inter> Q' \<inter> W \<noteq> {}"
  shows "W \<inter> (truncation p Q) \<inter> (truncation p' Q') \<noteq> {}" 
proof -
  have "quorum (truncation p Q)" and "quorum (truncation p' Q')" using l14 assms is_cons_cluster_def by auto
  moreover have "quorum_of_set I (truncation p Q)" and "quorum_of_set I (truncation p' Q')"
    by (metis IntI assms(4,5) calculation mem_Collect_eq quorum_def quorum_of_def quorum_of_set_def reachable_through.intros(1) truncation_def)+
  moreover note \<open>is_cons_cluster I\<close>
  ultimately show ?thesis unfolding is_cons_cluster_def by auto
qed

end

section "Elementary quorums"

text \<open>In this section we define the notion of elementary quorum, which is a quorum that has no strict subset that is a quorum.
  It follows directly from the definition that every quorum contains an elementary quorum. Moreover, we show 
that if @{term Q} is an elementary quorum and @{term n\<^sub>1} and @{term n\<^sub>2} are members of @{term Q}, then @{term n\<^sub>2} is reachable from @{term n\<^sub>1} 
in the directed graph over participants defined as the set of edges @{term "(n,m)"} such that @{term m} is a member of a slice of @{term n}.
This lemma is used in the companion paper to show that probabilistic leader-election is feasible.\<close>

locale elementary = stellar
begin 

definition elementary where
  "elementary s \<equiv> quorum s \<and> (\<forall> s' . s' \<subset> s \<longrightarrow> \<not>quorum s')"

lemma finite_subset_wf:
  shows "wf {(X, Y). X \<subset> Y \<and> finite Y}"
  by (metis finite_psubset_def wf_finite_psubset)

lemma quorum_contains_elementary:
  assumes "finite s" and  "\<not> elementary s" and "quorum s" 
  shows "\<exists> s' . s' \<subset> s \<and> elementary s'" using assms
proof (induct s rule:wf_induct[where ?r="{(X, Y). X \<subset> Y \<and> finite Y}"])
  case 1
  then show ?case using finite_subset_wf by simp
next
  case (2 x)
  then show ?case
    by (metis (full_types) elementary_def finite_psubset_def finite_subset in_finite_psubset less_le psubset_trans)
qed

inductive path where
  "path []"
| "\<And> x . path [x]"
| "\<And> l n . \<lbrakk>path l; S \<in> Q (hd l); n \<in> S\<rbrakk> \<Longrightarrow> path (n#l)"

lemma elementary_connected:
  assumes "elementary s" and "n\<^sub>1 \<in> s" and "n\<^sub>2 \<in> s" and "n\<^sub>1 \<in> W" and "n\<^sub>2 \<in> W"
  shows "\<exists> l . hd (rev l) = n\<^sub>1 \<and> hd l = n\<^sub>2 \<and> path l" (is ?P)
proof -
  { assume "\<not>?P"
    define x where "x \<equiv> {n \<in> s . \<exists> l . l \<noteq> [] \<and> hd (rev l) = n\<^sub>1 \<and> hd l = n \<and> path l}"
    have "n\<^sub>2 \<notin> x" using \<open>\<not>?P\<close> x_def by auto 
    have "n\<^sub>1 \<in> x" unfolding x_def using assms(2) path.intros(2) by force
    have "quorum x"
    proof -
      { fix n
        assume "n \<in> x"
        have "\<exists> S . S \<in> slices n \<and> S \<subseteq> x"
        proof -
          obtain S where "S \<in> slices n" and "S \<subseteq> s" using \<open>elementary s\<close> \<open>n \<in> x\<close> unfolding x_def
            by (force simp add:elementary_def quorum_def)
          have "S \<subseteq> x"
          proof -
            { assume "\<not> S \<subseteq> x"
              obtain m where "m \<in> S" and "m \<notin> x" using \<open>\<not> S \<subseteq> x\<close> by auto
              obtain l' where "hd (rev l') = n\<^sub>1" and "hd l' = n" and "path l'" and "l' \<noteq> []"
                using \<open>n \<in> x\<close> x_def by blast 
              have "path (m # l')" using \<open>path l'\<close> \<open>m\<in> S\<close> \<open>S \<in> slices n\<close> \<open>hd l' = n\<close>
                using path.intros(3) by fastforce
              moreover have "hd (rev (m # l')) = n\<^sub>1" using \<open>hd (rev l') = n\<^sub>1\<close> \<open>l' \<noteq> []\<close> by auto
              ultimately have "m \<in> x" using \<open>m \<in> S\<close> \<open>S \<subseteq> s\<close> x_def by auto 
              hence False using \<open>m \<notin> x\<close> by blast }
            thus ?thesis by blast
          qed
          thus ?thesis
            using \<open>S \<in> slices n\<close> by blast
        qed }
      thus ?thesis by (meson Int_iff quorum_def)
    qed 
    moreover have "x \<subset> s"
      using \<open>n\<^sub>2 \<notin> x\<close> assms(3) x_def by blast
    ultimately have False using \<open>elementary s\<close>
      using elementary_def by auto
  }
  thus ?P by blast  
qed

end

end
