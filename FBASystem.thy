section \<open>Formalization of the definitions and theorems of the Stellar white-paper.\<close>

text \<open>TODO: why not take the set of nodes to be the universe of their type?\<close>

text 
\<open>
A few notes.

The white-paper explains that accepting is needed to overcome votes against ratified statements.
I thought that it might be easier to see it as a virtual leader implementation that
ensures that no two nodes accept different values in the same round (much like Byzantine Paxos
uses pre-prepare).

Note, however, that accepting only guarantees anything to intact nodes.
Since the set of befouled nodes is a dset, that is sufficient to guarantee 
safety to all well-behaved nodes.
\<close>

theory FBASystem
imports Main Intersection
begin

(*<*)
declare Let_def[simp]
(*>*)

subsection \<open>Section 3\<close>

type_synonym 'node fbas = "('node set \<times> ('node \<Rightarrow> 'node set set))"
  \<comment> \<open>A federated byzantine agreement system is a pair @{term "(fbas::'node fbas) = (V,Q)"} consisting
of a node set @{term "V::'node set"} and a quorum function @{term "Q::'node \<Rightarrow> 'node set set"}. 
Note that in this case @{term "fst fbas"} is @{term V} and @{term "snd fbas"} is @{term Q}.\<close>

locale system = fixes well_behaved :: "'node::finite \<Rightarrow> bool"
begin

definition well_formed_fbas where
  "well_formed_fbas fbas \<equiv> let V = fst fbas; Q = snd fbas in 
    V \<noteq> {}  
    \<and> (\<forall> n \<in> V . Q n \<noteq> {} 
    \<and> (\<forall> S \<in> Q n . n \<in> S \<and> S \<subseteq> V))"

text \<open>
A quorum is something that will be used by a well-behaved node.
Thus we require a quorum to contain at least one well-behaved node.
Also note that not requiring that leads to ruling out any FBAS that has at least one byzantine node, 
since this node can use a single slice consisting of only itself.

Moreover, in order to node depend on the slices of byzantine nodes, we only require that good 
nodes have their slices included.
This means that we can add arbitrarily byzantine nodes to a quorum and still obtain a quorum.\<close>

definition quorum where 
  \<comment> \<open>Note that adding arbitrarily many byzantine nodes to a quorum yields another quorum\<close>
  "quorum fbas U \<equiv> let V = fst fbas; Q = snd fbas in
    (\<exists> n . well_behaved n \<and> n \<in> U) \<and> U \<subseteq> V  \<and> (\<forall> n \<in> U . well_behaved n \<longrightarrow> (\<exists> S \<in> Q n . S \<subseteq> U))"

subsection \<open>Section 4\<close>

definition quorum_intersection where
  \<comment> \<open>Note that here there is no requirement on the nodes in the intersection (could be correct or ill-behaved).
This seems strange to me.\<close>
  "quorum_intersection fbas \<equiv> 
    \<forall> U1 U2. quorum fbas U1 \<and> quorum fbas U2 \<longrightarrow> U1 \<inter> U2 \<noteq> {}"

abbreviation set_minus (infixl "\<setminus>" 65) where "set_minus A B \<equiv> A - B"

text \<open>
There is a problem with quorum intersection: with quorums as formalized above, it precludes having any byzantine node.
So we might define quorums as containing at least one correct node.
But then if U is a quorum then @{term "U \<setminus> B"} is not necessarily a quorum anymore
\<close>

definition delete where
  "delete fbas B \<equiv> let V = fst fbas; Q = snd fbas in 
    (V \<setminus> B, \<lambda> n . {U \<setminus> B | U . U \<in> Q n})" 
  \<comment> \<open>@{term "{U \<setminus> B | U . U \<in> Q n}"} is a set-comprehension.
It means the set of sets of the form @{term "U \<setminus> V"} where @{term U} belongs to @{term "Q n"}}}}\<close>

(*<*)
(*
lemma delete_validity:
  -- \<open>TODO: used anywhere?\<close>
  assumes "well_formed_fbas fbas" and "\<not>fst fbas \<subseteq> B"
  shows "well_formed_fbas (delete fbas B)" using assms 
  unfolding well_formed_fbas_def delete_def by auto
*)
(*>*)

lemma delete_delete_subseteq:
  assumes "B \<subseteq> B'" shows "delete (delete fbas B) B' = delete fbas B'"
proof - 
  have "ns \<setminus> B' = ns \<setminus> B \<setminus> B'" for ns using assms(1) by blast
  thus ?thesis unfolding delete_def 
    by (simp add:fun_eq_iff; clarsimp; intro set_eqI; blast)
qed

definition intersection_despite where
  "intersection_despite fbas B \<equiv> quorum_intersection (delete fbas B)"

definition availability_despite where
  "availability_despite fbas B \<equiv> let V = fst fbas in
    quorum fbas (V \<setminus> B) \<or> B = V"

definition dset where
  "dset fbas B \<equiv> let V = fst fbas in
    B \<subseteq> V \<and> intersection_despite fbas B \<and> availability_despite fbas B"

definition intact where
  "intact fbas n \<equiv> let V = fst fbas in n \<in> V \<and>
    (\<exists> B . dset fbas B \<and> n \<notin> B \<and> (\<forall> n \<in> V . \<not> well_behaved n \<longrightarrow> n \<in> B))"

abbreviation befouled where "befouled fbas n \<equiv> \<not> intact fbas n"

theorem quorum_delete: 
  assumes "quorum fbas U" and "U' = U \<setminus> B" and "\<exists> n . well_behaved n \<and> n \<in> U'"
  shows "quorum (delete fbas B) U'"
  using assms unfolding quorum_def delete_def
  by (clarsimp; metis Diff_iff Diff_mono order_refl)

lemma quorum_union:
  assumes "quorum fbas U1" and "quorum fbas U2"
  shows "quorum fbas (U1 \<union> U2)"
  using assms unfolding quorum_def
  by (metis Un_iff Un_subset_iff le_supI1 sup.coboundedI2)  

lemma delete_more:
  assumes "quorum (delete fbas Y) U" and "\<exists> n . well_behaved n \<and>  n \<in> U \<setminus> Z" and "Y \<subseteq> Z"
  shows "quorum (delete fbas Z) (U \<setminus> Z)"
proof -
  have "quorum (delete (delete fbas Y) Z) (U \<setminus> Z)" using assms(1,2) quorum_delete by metis
  moreover have "delete (delete fbas Y) Z = delete fbas Z" using assms(3)
    by (simp add: system.delete_delete_subseteq)
  ultimately show ?thesis by simp
qed

theorem dset_closed:
  \<comment> \<open>This is theorem 2 of the white paper\<close>
  fixes B\<^sub>1 B\<^sub>2 fbas
  assumes "quorum_intersection fbas" and "dset fbas B\<^sub>1" and "dset fbas B\<^sub>2"
  shows "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)"
proof -
  let ?V = "fst fbas"
  let ?U1 = "?V \<setminus> B\<^sub>1"
  let ?U2 = "?V \<setminus> B\<^sub>2"
  let ?B = "B\<^sub>1 \<inter> B\<^sub>2"
  have ?thesis if "?U1 = {} \<or> ?U2 = {}"
  proof -
    have "?B = B\<^sub>2 \<or> ?B = B\<^sub>1" using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> unfolding dset_def by force
    thus ?thesis using \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> by metis
  qed
  moreover have ?thesis if "?U1 \<noteq> {} \<and> ?U2 \<noteq> {}"
  proof -
    text \<open>First qwe show the @{term ?U1} and @{term ?U2} are quorums in @{term fbas}, which will come handy later on. 
This comes from quorum availability.\<close>

    have 1:"quorum fbas ?U1" and 2:"quorum fbas ?U2" 
      using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> availability_despite_def
      by (metis Diff_cancel dset_def)+

    text \<open>We need to prove quorum availability despite @{term "?B"} and quorum intersection despite @{term "?B"}\<close>

    text \<open>We start with availability. This is simple.\<close>
    have "availability_despite fbas (?B)"
    proof -
      have "quorum fbas (?U1 \<union> ?U2)" 
        using quorum_union 1 2 by blast
      thus "availability_despite fbas (?B)" 
        by (simp add: Diff_Int system.availability_despite_def) 
    qed

    moreover
    text \<open>Now we prove quorum intersection.\<close>
    have "intersection_despite fbas (?B)"
    proof -

      have "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}" if "quorum (delete fbas ?B) U\<^sub>a" and "quorum (delete fbas ?B) U\<^sub>b" for U\<^sub>a U\<^sub>b
      -- \<open>We show that if we take two quorums @{term U\<^sub>a} and @{term U\<^sub>b} in @{term "delete fbas ?B"}, 
        then @{term "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}"}. This suffices to show quorum intersection despite @{term ?B}\<close>
      proof -
        let ?U = "?U1 \<inter> ?U2"
        text \<open>First we show that @{term ?U} is a quorum in @{term "delete fbas B\<^sub>1"}. 
          For this we use theorem 1:@{thm quorum_delete}\<close>
        have 3:"quorum (delete fbas B\<^sub>1) ?U"
        proof - 
          text \<open>@{term ?U} is not empty:\<close>
          have "\<exists> n . well_behaved n \<and> n \<in> ?U" sorry
          show "quorum (delete fbas B\<^sub>1) ?U"
            using quorum_delete[of fbas ?U2 ?U B\<^sub>1] \<open>\<exists> n . well_behaved n \<and> n \<in> ?U\<close>
            using "2" by blast 
        qed

        text \<open>Then we prove the following lemma, which we will apply to both @{term U\<^sub>a} and @{term U\<^sub>b}\<close>
        { fix U
          assume "quorum (delete fbas ?B) U"
          have "quorum (delete fbas B\<^sub>2) (U \<setminus> B\<^sub>2)"
          proof -
            consider (a) "U \<setminus> B\<^sub>1 \<noteq> {}" | (b) "U \<setminus> B\<^sub>2 \<noteq> {}" 
              \<comment> \<open>We have two cases\<close>
            proof -
              have "U \<setminus> ?B = {}" if "U \<setminus> B\<^sub>1 = {}" and "U \<setminus> B\<^sub>2 = {}" 
                using that by blast
              moreover have "U \<setminus> ?B \<noteq> {}" 
                using \<open>quorum (delete fbas ?B) U\<close> 
                unfolding quorum_def delete_def by fastforce
              ultimately show ?thesis 
                using that by blast
            qed
            thus ?thesis proof (cases)
              case a
              hence "quorum (delete fbas B\<^sub>1) (U \<setminus> B\<^sub>1)" 
                using \<open>quorum (delete fbas ?B) U\<close> delete_more 
                by (metis inf.cobounded1)
              hence "(U \<setminus> B\<^sub>1) \<inter> ?U \<noteq> {}" 
                using \<open>quorum (delete fbas B\<^sub>1) ?U\<close>  \<open>dset fbas B\<^sub>1\<close> 
                unfolding dset_def intersection_despite_def quorum_intersection_def 
                by force
              hence "(U \<setminus> B\<^sub>2) \<noteq> {}" by blast
              thus "quorum (delete fbas B\<^sub>2) (U \<setminus> B\<^sub>2)" 
                using \<open>quorum (delete fbas ?B) U\<close> delete_more 
                by (metis inf_le2)
            next
              case b thus ?thesis 
                using \<open>quorum (delete fbas ?B) U\<close> delete_more 
                by fastforce
            qed
          qed
        }
        note l = this \<comment> \<open>we give name l to this lemma\<close>

        text \<open>Now we apply lemma l to both @{term U\<^sub>a} and @{term U\<^sub>b}\<close>
        have "quorum (delete fbas B\<^sub>2) (U\<^sub>a \<setminus> B\<^sub>2)" 
          using l \<open>quorum (delete fbas ?B) U\<^sub>a\<close> unfolding dset_def by simp
        moreover
        have "quorum (delete fbas B\<^sub>2) (U\<^sub>b \<setminus> B\<^sub>2)" 
          using l \<open>quorum (delete fbas ?B) U\<^sub>b\<close> unfolding dset_def by simp
        ultimately have "(U\<^sub>a \<setminus> B\<^sub>2) \<inter> (U\<^sub>b \<setminus> B\<^sub>2) \<noteq> {}" 
          using \<open>dset fbas B\<^sub>2\<close>
          unfolding quorum_intersection_def dset_def intersection_despite_def 
          by simp
        thus "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}" by blast 
            \<comment> \<open>And we are done\<close>
      qed
      thus "intersection_despite fbas (?B)" 
        by (simp add: intersection_despite_def quorum_intersection_def) 
    qed
    ultimately show "dset fbas (?B)"
      by (meson \<open>dset fbas B\<^sub>2\<close> inf.coboundedI2 system.dset_def)
  qed
  ultimately show "dset fbas (?B)" by blast
qed

theorem befouled_is_dset: 
  \<comment> \<open>This is theorem 3: in an FBAS with quorum intersection, the set of befouled nodes a dispensable set\<close>
  fixes S and fbas
  defines "S \<equiv> {n \<in> fst fbas . befouled fbas n}"
  assumes "quorum_intersection fbas" and "well_formed_fbas fbas"
  shows "dset fbas S"
proof (cases "S = {}")
  case True
  thus "dset fbas S" using \<open>quorum_intersection fbas\<close> \<open>well_formed_fbas fbas\<close> 
    unfolding dset_def availability_despite_def well_formed_fbas_def intersection_despite_def delete_def quorum_def
    by (auto simp add:True)
next 
  case False
  show "dset fbas S"
  proof (cases "S = fst fbas")
    case True
    thus "dset fbas S"
      by (simp add: system.availability_despite_def system.delete_def system.dset_def system.intersection_despite_def system.quorum_def system.quorum_intersection_def) 
  next
    case False
    define  is_complete_dset 
      where "is_complete_dset B \<equiv> 
        dset fbas B \<and> (\<forall> n \<in> fst fbas . \<not>well_behaved n \<longrightarrow> n \<in> B)" for B
    let ?c_dsets = "{B | B . is_complete_dset B}"
    let ?D = "\<Inter>?c_dsets"
    text \<open>First we show that the set of befouled nodes is equal to the intersection of all dsets 
that contain all ill-behaved nodes (called complete dsets)\<close>
    have "S = ?D"
    proof - 
      have "x \<in> ?D" if "x \<in> S" for x using that
        unfolding S_def intact_def is_complete_dset_def by force
      moreover have "x \<in> S" if "x \<in> ?D" for x
        using that unfolding S_def intact_def is_complete_dset_def 
        by (auto; simp add: availability_despite_def delete_def quorum_def quorum_intersection_def dset_def intersection_despite_def)
      ultimately show "S = ?D" by blast
    qed

    text \<open>The we apply theorem 2. For that we need to establish a few preconditions about @{term ?c_dsets}.\<close>
    have 1:"X \<noteq> {}" if "X \<in> ?c_dsets" for X
    proof -
      have "B \<noteq> {}" if "dset fbas B \<and> (\<forall> n \<in> fst fbas . \<not>well_behaved n \<longrightarrow> n \<in> B)" for B
        using that \<open>S \<noteq> {}\<close> unfolding S_def intact_def by auto
      thus ?thesis using that is_complete_dset_def by blast
    qed
    have 2:"?c_dsets \<noteq> {}" using \<open>S = ?D\<close> \<open>S \<noteq> fst fbas\<close> S_def by auto
    have 3:"\<And>A B. A \<in> ?c_dsets \<Longrightarrow> B \<in> ?c_dsets \<Longrightarrow> A \<inter> B \<in> ?c_dsets" 
      using dset_closed[OF \<open>quorum_intersection fbas\<close>] is_complete_dset_def by fastforce

    text \<open>Now we can apply theorem 2.\<close>
    have "S \<in> ?c_dsets" using ne_family_intersection[of ?c_dsets] 1 2 3 by (simp add:\<open>S = ?D\<close>)
    thus "dset fbas S" unfolding is_complete_dset_def by blast 
  qed
qed

end

subsection \<open>Section 5\<close>

locale voting = system well_behaved for well_behaved::"'node::finite \<Rightarrow> bool" + 
  fixes vote :: "'node \<Rightarrow> 'statement \<Rightarrow> bool" and contradictory :: "'statement \<Rightarrow> 'statement \<Rightarrow> bool"
  assumes "\<And> n v v' . well_behaved n \<Longrightarrow> vote n v \<Longrightarrow> vote n v' \<Longrightarrow> contradictory v v' \<Longrightarrow> False"
    \<comment> \<open>here we assume model a system state in which nodes have cast votes and no well-behaved node
voted for contradictory statements\<close>
begin

definition ratified_by_set where
  \<comment> \<open>note here that we talk only about well-behaved nodes\<close>
  "ratified_by_set ns v \<equiv> \<forall> n \<in> ns . well_behaved n \<longrightarrow> vote n v"

definition ratified where
  "ratified fbas U v \<equiv> quorum fbas U \<and> ratified_by_set U v"

definition ratifies where
  "ratifies fbas n v \<equiv> \<exists> U . n \<in> U \<and> ratified fbas U v"

theorem theorem_4:
  assumes "ratified fbas U\<^sub>1 v" and "ratified fbas U\<^sub>2 v'"
    and "contradictory v v'" and "quorum_intersection fbas"
    and "\<And> n . n \<in> fst fbas \<Longrightarrow> well_behaved n"
  shows False
proof -
  from \<open>ratified fbas U\<^sub>1 v\<close> and \<open>ratified fbas U\<^sub>2 v'\<close> have 
    "quorum fbas U\<^sub>1" and "quorum fbas U\<^sub>2" unfolding ratified_by_set_def using ratified_def by auto
  obtain n where "well_behaved n" and "n\<in>U\<^sub>1" and "n\<in>U\<^sub>2"
    using \<open>quorum fbas U\<^sub>1\<close> \<open>quorum fbas U\<^sub>2\<close> \<open>quorum_intersection fbas\<close> \<open>\<And> n. n \<in> fst fbas \<Longrightarrow> well_behaved n\<close>
    by (metis disjoint_iff_not_equal subsetCE system.quorum_def system.quorum_intersection_def)
  hence "vote n v" and "vote n v'" 
    using \<open>ratified fbas U\<^sub>1 v\<close> \<open>ratified fbas U\<^sub>2 v'\<close> unfolding ratified_def ratified_by_set_def by auto
  thus False using \<open>contradictory v v'\<close> \<open>well_behaved n\<close>
    by (meson voting_axioms voting_def)
qed

theorem theorem_5:
  assumes "intersection_despite fbas B" and "\<And> n . n \<in> fst fbas \<Longrightarrow> \<not>well_behaved n \<Longrightarrow> n \<in> B"
    and "contradictory v v'" and "n \<notin> B" and "n' \<notin> B"
    and "ratifies fbas n v" and "ratifies fbas n' v'"
  shows False
proof -
  text \<open>There are two quorum that ratified @{term v} and @{term v'} respectively\<close>
  obtain U\<^sub>1 and U\<^sub>2 where "quorum fbas U\<^sub>1" and "ratified_by_set U\<^sub>1 v"
    and "ratified_by_set U\<^sub>2 v'" and "quorum fbas U\<^sub>2" and "U\<^sub>2 - B \<noteq> {}" and "U\<^sub>1 - B \<noteq> {}"
    using \<open>ratifies fbas n v\<close> \<open>ratifies fbas n' v'\<close> ratifies_def \<open>n \<notin> B\<close> \<open>n' \<notin> B\<close> ratified_def by auto

  text \<open>Now we use theorem 4\<close>
  have "quorum (delete fbas B) (U\<^sub>1 - B)" and "quorum (delete fbas B) (U\<^sub>2 - B)"
    using \<open>U\<^sub>2 - B \<noteq> {}\<close> and \<open>U\<^sub>1 - B \<noteq> {}\<close> and \<open>quorum fbas U\<^sub>1\<close> and \<open>quorum fbas U\<^sub>2\<close> and quorum_delete
    by blast+
  moreover have "\<And> n . n \<in> fst (delete fbas B) \<Longrightarrow> well_behaved n" 
    using \<open>\<And> n . n \<in> fst fbas \<Longrightarrow> \<not>well_behaved n \<Longrightarrow> n \<in> B\<close> unfolding delete_def by auto
  moreover have "ratified_by_set (U\<^sub>1 - B) v" and "ratified_by_set (U\<^sub>2 - B) v'"
    using \<open>ratified_by_set U\<^sub>1 v\<close> \<open>ratified_by_set U\<^sub>2 v'\<close> ratified_by_set_def by auto
  ultimately show False 
    using \<open>intersection_despite fbas B\<close> theorem_4 \<open>contradictory v v'\<close>
    unfolding intersection_despite_def ratifies_def ratified_def by blast
qed

theorem theorem_6:
  assumes "intact fbas n" and "intact fbas n'" and "ratifies fbas n v" and "ratifies fbas n' v'"
    and "contradictory v v'" and "quorum_intersection fbas" and "well_formed_fbas fbas"
  shows False
proof -
  let ?B = "{n \<in> fst fbas . befouled fbas n}"
  have "dset fbas ?B" using befouled_is_dset
    by (simp add: \<open>quorum_intersection fbas\<close> \<open>well_formed_fbas fbas\<close>)
  hence "intersection_despite fbas ?B" using dset_def by fastforce 
  moreover have "n \<in> ?B" if "\<not>well_behaved n" and "n \<in> fst fbas" for n 
    using that unfolding intact_def by auto
  moreover have "n \<notin> ?B" and "n' \<notin> ?B"
    using \<open>intact fbas n\<close> \<open>intact fbas n'\<close> intact_def by blast+
  ultimately show False 
    using theorem_5 \<open>contradictory v v'\<close> \<open>ratifies fbas n v\<close> \<open>ratifies fbas n' v'\<close> by blast
qed

end

context system begin

definition v_blocking where 
  "v_blocking fbas B n \<equiv> let Q = snd fbas in \<forall> U \<in> Q n . U \<inter> B \<noteq> {}"

theorem theorem_7:
  fixes fbas B
  defines "V \<equiv> fst fbas"
  assumes "B \<subseteq> V" and "well_formed_fbas fbas"
  shows "availability_despite fbas B = (\<forall> n \<in> V \<setminus> B . well_behaved n \<longrightarrow> \<not> v_blocking fbas B n)"
proof -
  let ?Q = "snd fbas"
  have "(\<forall> n \<in> V \<setminus> B . well_behaved n \<longrightarrow> \<not> v_blocking fbas B n) \<longleftrightarrow>
    (\<forall> n \<in> V \<setminus> B . well_behaved n \<longrightarrow> (\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B))"
  proof -
    have "(\<not> v_blocking fbas B n) = (\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B)" if "n \<in> V \<setminus> B" and "well_behaved n" for n
    proof -
      have "(\<not> v_blocking fbas B n) \<Longrightarrow> (\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B)"
      proof -
        assume "\<not> v_blocking fbas B n"
        with this
        obtain U where "U \<in> ?Q n" and "U \<inter> B = {}" 
          unfolding v_blocking_def by auto
        moreover have "U \<subseteq> V" using \<open>well_formed_fbas fbas\<close> \<open>n \<in> V \<setminus> B\<close> \<open>U \<in> ?Q n\<close>
          unfolding  V_def well_formed_fbas_def by force
        ultimately show "\<exists>U\<in>snd fbas n. U \<subseteq> V - B" by blast
      qed
      moreover have "(\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B) \<Longrightarrow> (\<not> v_blocking fbas B n)"
        unfolding v_blocking_def V_def by fastforce
      ultimately show ?thesis by blast
    qed
    thus ?thesis by fastforce
  qed
  also have "... = availability_despite fbas B"
    unfolding availability_despite_def V_def quorum_def
    using V_def \<open>B \<subseteq> V\<close> by auto
  finally show ?thesis by simp
qed

end

end