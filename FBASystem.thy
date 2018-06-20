section \<open>Formalization of the definitions and theorems of the Stellar white-paper.\<close>

text \<open>TODO: why not take the set of nodes to be the universe of their type?\<close>

text 
\<open>
A few notes.

The white-paper explains that accepting is needed to overcome votes against ratified statements.
I thought that it might be easier to see it as a virtual leader implementation that
ensures that no two nodes accept different values in the same round (much like Byzantine Paxos
uses pre-prepare). However this does not explain accepting because of a v-blocking set.

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

definition C where "C fbas \<equiv> {n \<in> fst fbas . well_behaved n}"
\<comment> \<open>TODO: let's just use a fixed set of well_behaved nodes. Using both predicate and set causes problems.\<close>

definition well_formed_fbas where
  "well_formed_fbas fbas \<equiv> let V = fst fbas; Q = snd fbas in 
    V \<noteq> {}  
    \<and> (\<forall> n \<in> V . Q n \<noteq> {} \<comment> \<open>every node has at least one quorum slice\<close>
    \<and> (\<forall> S \<in> Q n . n \<in> S \<and> S \<subseteq> V)) \<comment> \<open>a node belong to its own quorum slices, which are also included in V\<close>"

text \<open>
A quorum is something that will be used by a well-behaved node.
Thus we require a quorum to contain at least one well-behaved node.
Also note that not requiring that leads to ruling out any FBAS that has at least one byzantine node, 
since this node can use a single slice consisting of only itself.
UPDATE: this reasoning is incorrect since for a given configuration of the correct nodes we can come up
with byzantine slices that do not break quorum intersection.

Moreover, in order to node depend on the slices of byzantine nodes, we only require that good 
nodes have their slices included.
This means that we can add arbitrarily byzantine nodes to a quorum and still obtain a quorum.\<close>

definition quorum where 
  \<comment> \<open>Note that adding arbitrarily many byzantine nodes to a quorum yields another quorum\<close>
  "quorum fbas U \<equiv> let V = fst fbas; Q = snd fbas in
    U \<inter> C fbas \<noteq> {} \<and> U \<subseteq> V  \<and> (\<forall> n \<in> U . well_behaved n \<longrightarrow> (\<exists> S \<in> Q n . S \<subseteq> U))"

subsection \<open>Section 4\<close>

definition quorum_intersection where
  \<comment> \<open>Note that here there is no requirement on the nodes in the intersection (could be correct or ill-behaved).
This seems strange to me.\<close>
  "quorum_intersection fbas \<equiv> 
    \<forall> U1 U2. quorum fbas U1 \<and> quorum fbas U2 \<longrightarrow> U1 \<inter> U2 \<inter> C fbas \<noteq> {}"

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

lemma delete_empty: "delete fbas {} = fbas" unfolding delete_def by auto

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
  "intact fbas n \<equiv> let V = fst fbas in n \<in> V \<and> well_behaved n \<and>
    (\<exists> B . dset fbas B \<and> n \<notin> B \<and> -(C fbas) \<subseteq> B)"

abbreviation befouled where "befouled fbas n \<equiv> \<not> intact fbas n"

theorem quorum_delete: 
  assumes "quorum fbas U" and "U' = U \<setminus> B" and "U' \<inter> C fbas \<noteq> {}"
  shows "quorum (delete fbas B) U'"
  using assms unfolding quorum_def delete_def C_def
  by (auto, metis Diff_mono order_refl)

lemma quorum_union:
  assumes "quorum fbas U1" and "quorum fbas U2"
  shows "quorum fbas (U1 \<union> U2)"
  using assms unfolding quorum_def
  by (metis (no_types, hide_lams) Diff_cancel Diff_disjoint Un_iff Un_subset_iff inf_aci(2) inf_sup_absorb le_supI1 sup.coboundedI2)

lemma delete_more:
  assumes "quorum (delete fbas Y) U" and "(U \<setminus> Z) \<inter> C (delete fbas Y) \<noteq> {}" and "Y \<subseteq> Z"
  shows "quorum (delete fbas Z) (U \<setminus> Z)"
proof -
  have "quorum (delete (delete fbas Y) Z) (U \<setminus> Z)" using assms(1,2) quorum_delete by blast 
  moreover have "delete (delete fbas Y) Z = delete fbas Z" using assms(3)
    by (simp add: system.delete_delete_subseteq)
  ultimately show ?thesis by simp
qed

lemma C_delete:"C (delete fbas B) = (C fbas - B)" unfolding delete_def C_def by auto

text \<open>Some lemmas about sets\<close>

lemma l1:"A \<inter> (B \<setminus> C) \<noteq> {}" if "A \<inter> (B \<setminus> C\<^sub>1) \<noteq> {} | A \<inter> (B \<setminus> C\<^sub>2) \<noteq> {}" and "C = C\<^sub>1 \<inter> C\<^sub>2" 
  for A B C C\<^sub>1 C\<^sub>2
  by (metis Diff_eq_empty_iff Int_Diff inf.bounded_iff that)

lemma l2:"(A \<setminus> (B\<^sub>1 \<inter> B\<^sub>2)) \<inter> C \<setminus> (B\<^sub>1 \<inter> B\<^sub>2) = {}" 
  if "(A \<setminus> B\<^sub>1) \<inter> (C \<setminus> B\<^sub>1) = {}" and "(A \<setminus> B\<^sub>2)  \<inter> (C \<setminus> B\<^sub>2) = {}"
  for A B\<^sub>1 B\<^sub>2 C
  by (metis Diff_Int Diff_idemp Int_Diff inf_bot_right inf_commute that) 

theorem dset_closed:
  \<comment> \<open>This is theorem 2 of the white paper\<close>
  fixes B\<^sub>1 B\<^sub>2 fbas
  assumes "quorum_intersection fbas" and "dset fbas B\<^sub>1" and "dset fbas B\<^sub>2"
  shows "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)"
proof -
  let ?V = "fst fbas"
  let ?U1 = "?V \<setminus> B\<^sub>1"
  let ?U2 = "?V \<setminus> B\<^sub>2"

  have ?thesis if "?U1 = {} \<or> ?U2 = {}"
  proof -
    have "B\<^sub>1 \<inter> B\<^sub>2 = B\<^sub>2 \<or> B\<^sub>1 \<inter> B\<^sub>2 = B\<^sub>1" using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> unfolding dset_def by force
    thus ?thesis using \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> by metis
  qed

  moreover have ?thesis if "?U1 \<noteq> {} \<and> ?U2 \<noteq> {}"
  proof -

    text \<open>First a basic property\<close>
    have 1:"quorum fbas (?V \<setminus> B)" if "dset fbas B" and "?V \<setminus> B \<noteq> {}" for B 
      using that availability_despite_def by (metis Diff_cancel dset_def)+

    text \<open>We need to prove quorum availability despite @{term "B\<^sub>1 \<inter> B\<^sub>2"} and quorum intersection despite @{term "B\<^sub>1 \<inter> B\<^sub>2"}\<close>

    text \<open>We start with availability. This is simple.\<close>
    have "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      have "quorum fbas (?U1 \<union> ?U2)" 
        using quorum_union 1 that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> by simp
      thus "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
        by (simp add: Diff_Int system.availability_despite_def) 
    qed

    moreover
    text \<open>Now we prove quorum intersection.\<close>
    have "intersection_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -

      have "U\<^sub>a \<inter> U\<^sub>b \<inter> C (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) \<noteq> {}" if "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>a" and "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>b" for U\<^sub>a U\<^sub>b
      \<comment> \<open>We show that if we take two quorums @{term U\<^sub>a} and @{term U\<^sub>b} in @{term "delete fbas ?B"}, 
        then @{term "U\<^sub>a \<inter> U\<^sub>b \<inter> C (delete fbas ?B) \<noteq> {}"}. This suffices to show quorum intersection despite @{term ?B}\<close>
      proof -

        text \<open>
First we show that @{term "?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2)"} is a quorum in both @{term "delete fbas B\<^sub>1"} and @{term "delete fbas B\<^sub>2"}. 
This is where the quorum intersection property is used\<close>
        have 2:"quorum (delete fbas B\<^sub>1) (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2))"  if "quorum fbas (?V \<setminus> B\<^sub>1)" and "quorum fbas (?V \<setminus> B\<^sub>2)" for B\<^sub>1 B\<^sub>2
        proof -
          have "(?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> C fbas \<noteq> {}" using that \<open>quorum_intersection fbas\<close>
            by (metis Diff_Un quorum_intersection_def) 
              \<comment> \<open>@{term ?U} contains a well-behaved node\<close>
          thus "quorum (delete fbas B\<^sub>1) (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2))" using quorum_delete that
            by (smt Diff_Un Diff_eq inf.commute inf.left_commute inf.left_idem)
        qed

        text \<open>Then we prove the following lemma, which we will apply to both @{term U\<^sub>a} and @{term U\<^sub>b}\<close>
        have 3:"quorum (delete fbas B\<^sub>1) (U \<setminus> B\<^sub>1)" 
          if "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U" and "dset fbas B\<^sub>1" and "dset fbas B\<^sub>2" and "B\<^sub>1 \<noteq> ?V" and "B\<^sub>2 \<noteq> ?V" for U B\<^sub>1 B\<^sub>2
        proof -
          consider (a) "(U \<setminus> B\<^sub>1) \<inter> C (delete fbas B\<^sub>1) \<noteq> {}" | (b) "(U \<setminus> B\<^sub>2)  \<inter> C (delete fbas B\<^sub>2) \<noteq> {}" 
          proof -
            have "(U \<setminus> (B\<^sub>1 \<inter> B\<^sub>2)) \<inter> C (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) = {}" if "(U \<setminus> B\<^sub>1) \<inter> C (delete fbas B\<^sub>1) = {}"
              and "(U \<setminus> B\<^sub>2)  \<inter> C (delete fbas B\<^sub>2) = {}"
              by (metis (no_types, hide_lams) C_delete Int_Diff system.l2 that)
            thus ?thesis using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close>
              by (metis C_delete Diff_Int2 Diff_Int_distrib2 Diff_idemp Int_Diff a b quorum_def)
          qed
          thus ?thesis 
          proof (cases)
            case b
            have "(U \<setminus> B\<^sub>2) \<inter> (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> C (delete fbas B\<^sub>2) \<noteq> {}" 
            proof -
              from b have "quorum (delete fbas B\<^sub>2) (U \<setminus> B\<^sub>2)" 
                using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> delete_more
                by (metis C_delete Int_commute inf_le2 system.l1) 
              moreover
              have "quorum (delete fbas B\<^sub>2) (?V \<setminus> (B\<^sub>1 \<union> B\<^sub>2))"
                by (metis "1" "2" Diff_eq_empty_iff Un_commute subset_antisym system.dset_def \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> \<open>B\<^sub>1 \<noteq> ?V\<close> \<open>B\<^sub>2 \<noteq> ?V\<close>)
              ultimately 
              show ?thesis  using 2 \<open>dset fbas B\<^sub>2\<close> \<open>B\<^sub>2 \<noteq> ?V\<close> unfolding dset_def intersection_despite_def quorum_intersection_def by simp
            qed
            hence "(U \<setminus> B\<^sub>1) \<inter> C (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) \<noteq> {}" by (auto simp add:C_delete)
            thus ?thesis by (meson inf_le1 system.delete_more \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close>) 
          next
            case a thus ?thesis 
              using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> delete_more by (metis C_delete Int_lower1 system.l1)
          qed
        qed

        text \<open>Now we apply @{thm 3} to both @{term U\<^sub>a} and @{term U\<^sub>b}\<close>
        have 4:"U\<^sub>a \<inter> U\<^sub>b \<inter> C (delete fbas B\<^sub>1) \<noteq> {}"  
          if "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>a" and "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>b" 
            and "dset fbas B\<^sub>1" and "dset fbas B\<^sub>2" and "B\<^sub>1 \<noteq> ?V" and "B\<^sub>2 \<noteq> ?V" for U\<^sub>a U\<^sub>b B\<^sub>1 B\<^sub>2
        proof -
          have "quorum (delete fbas B\<^sub>1) (U\<^sub>a \<setminus> B\<^sub>1)" and "quorum (delete fbas B\<^sub>1) (U\<^sub>b \<setminus> B\<^sub>1)" 
            using "3" that by auto 
          hence  "(U\<^sub>a \<setminus> B\<^sub>1) \<inter> (U\<^sub>b \<setminus> B\<^sub>1) \<inter> C (delete fbas B\<^sub>1) \<noteq> {}"  
            using \<open>dset fbas B\<^sub>1\<close> unfolding quorum_intersection_def dset_def intersection_despite_def by auto 
          thus ?thesis
            by (simp add: C_delete Diff_Int_distrib2 inf.assoc)
        qed

        text "Finally we use @{thm 4} to complete the proof"
        have "U\<^sub>a \<inter> U\<^sub>b \<inter> C (delete fbas B\<^sub>1) \<noteq> {}" \<comment> \<open>The symmetric holds but we do not need it...\<close>
          using "4" \<open>fst fbas - B\<^sub>1 \<noteq> {} \<and> fst fbas - B\<^sub>2 \<noteq> {}\<close> assms(2) assms(3) that(1) that(2) by auto
        thus "U\<^sub>a \<inter> U\<^sub>b \<inter> C (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) \<noteq> {}"
          by (metis C_delete system.l1) \<comment> \<open>And we are done\<close> 
      qed
      thus "intersection_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)" 
        by (simp add: intersection_despite_def quorum_intersection_def) 
    qed
    ultimately show "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)"
      by (meson \<open>dset fbas B\<^sub>2\<close> inf.coboundedI2 system.dset_def)
  qed
  ultimately show "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)" by blast
qed

theorem befouled_is_dset: 
  \<comment> \<open>This is theorem 3: in an FBAS with quorum intersection, the set of befouled nodes a dispensable set\<close>
  fixes S and fbas
  defines "S \<equiv> {n \<in> fst fbas . befouled fbas n}"
  assumes "quorum_intersection fbas" and "well_formed_fbas fbas"
  shows "dset fbas S"
proof (cases "S = {}")
  case True 
  have "intersection_despite fbas S" 
    using True \<open>quorum_intersection fbas\<close> unfolding dset_def intersection_despite_def by (simp add: delete_empty)
  have "quorum fbas (fst fbas)"
  proof -
    have "\<exists> U . U \<subseteq> fst fbas \<and> quorum fbas U \<and> n \<in> U" if "n \<in> fst fbas" for n
    proof -
      have "intact fbas n" using S_def True that by blast
      obtain B where "quorum fbas (fst fbas - B)" and "B \<subseteq> fst fbas" and "n \<notin> B"
        by (metis \<open>intact fbas n\<close> intact_def system.availability_despite_def system.dset_def)
      with this obtain U where "quorum fbas U" and "n \<in> U" and "U \<subseteq> fst fbas"
        using \<open>n \<in> fst fbas\<close> by blast
      thus ?thesis
        by blast
    qed
    hence "\<exists> q \<in> (snd fbas) n . q \<subseteq> fst fbas" if "n \<in> fst fbas" for n
      by (meson \<open>well_formed_fbas fbas\<close> ex_in_conv system.well_formed_fbas_def that)
    thus ?thesis using \<open>well_formed_fbas fbas\<close> True apply (simp add: quorum_def well_formed_fbas_def S_def)
      by (metis disjoint_eq_subset_Compl disjoint_iff_not_equal inf.idem intact_def subsetCE)
  qed
  hence "availability_despite fbas S"
    by (simp add: True availability_despite_def)
  thus "dset fbas S"
    using True \<open>intersection_despite fbas S\<close> dset_def by auto
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
        dset fbas B \<and> - (C fbas) \<subseteq> B" for B
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