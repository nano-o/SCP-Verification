section \<open>Formalization of the definitions and theorems of the Stellar white-paper.\<close>

text \<open>
I do not like the assumptions that quorum intersect: quorum intersection at byz nodes cannot help, thus why assume that?
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

locale system = 
  fixes W :: "'node::finite set" \<comment> \<open>@{term W} is the set of well-behaved nodes\<close>
begin

definition well_formed_fbas where
  "well_formed_fbas fbas \<equiv> let V = fst fbas; Q = snd fbas in 
    V \<inter> W \<noteq> {} \<comment> \<open>contains at least one well-behaved node\<close>
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
    U \<inter> W \<noteq> {} \<and> U \<subseteq> V  \<and> (\<forall> n \<in> U \<inter> W . \<exists> S \<in> Q n . S \<subseteq> U)"

subsection \<open>Section 4\<close>

(* definition quorum_intersection where
  \<comment> \<open>quorum intersection at well-behaved nodes\<close>
  "quorum_intersection fbas S \<equiv>
    \<forall> U1 U2 . U1 \<inter> S \<noteq> {} \<and> U2 \<inter> S \<noteq> {} \<and> quorum fbas U1 \<and> quorum fbas U2 \<longrightarrow> U1 \<inter> U2 \<inter> W \<noteq> {}" *)
definition quorum_intersection where
  \<comment> \<open>quorum intersection at well-behaved nodes\<close>
  "quorum_intersection fbas \<equiv>
    \<forall> U1 U2 . quorum fbas U1 \<and> quorum fbas U2 \<longrightarrow> U1 \<inter> U2 \<inter> W \<noteq> {}"

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
  "intersection_despite fbas S B \<equiv> quorum_intersection (delete fbas B)"

definition availability_despite where
  "availability_despite fbas S B \<equiv> let V = fst fbas in
    S \<subseteq> V \<setminus> B \<and> (quorum fbas (V \<setminus> B) \<or> B = V)"

definition dset where
  \<comment> \<open>B is dispensable to agree with set S\<close>
  "dset fbas S B \<equiv> let V = fst fbas in
    B \<subseteq> V \<and> intersection_despite fbas S B \<and> availability_despite fbas S B"

definition intact where
  \<comment> \<open>A node is intact with respect to set S\<close>
  "intact fbas S n \<equiv> let V = fst fbas in n \<in> V \<inter> W \<and>
    (\<exists> B . dset fbas S B \<and> n \<notin> B \<and> -W \<inter> V \<subseteq> B)"

abbreviation befouled where "befouled fbas S n \<equiv> \<not> intact fbas S n"

theorem quorum_delete: 
  assumes "quorum fbas U" and "U' = U \<setminus> B" and "U' \<inter> W \<noteq> {}"
  shows "quorum (delete fbas B) U'"
  using assms unfolding quorum_def delete_def 
  by (auto, metis Diff_Int2 Diff_Int_distrib2 IntI Int_lower1 inf.absorb_iff2)

lemma quorum_union:
  assumes "quorum fbas U1" and "quorum fbas U2"
  shows "quorum fbas (U1 \<union> U2)"
  using assms unfolding quorum_def
  by (simp; metis Int_iff Un_iff disjoint_iff_not_equal le_supI1 sup.coboundedI2)

lemma delete_more:
  assumes "quorum (delete fbas Y) U" and "(U \<setminus> Z) \<inter> W \<noteq> {}" and "Y \<subseteq> Z"
  shows "quorum (delete fbas Z) (U \<setminus> Z)"
proof -
  have "quorum (delete (delete fbas Y) Z) (U \<setminus> Z)" using assms(1,2) quorum_delete by blast 
  moreover have "delete (delete fbas Y) Z = delete fbas Z" using assms(3)
    by (simp add: system.delete_delete_subseteq)
  ultimately show ?thesis by simp
qed

text \<open>Some lemmas about sets\<close>

\<^cancel>\<open>lemma l1:"A \<inter> (B \<setminus> C) \<noteq> {}" if "A \<inter> (B \<setminus> C\<^sub>1) \<noteq> {} | A \<inter> (B \<setminus> C\<^sub>2) \<noteq> {}" and "C = C\<^sub>1 \<inter> C\<^sub>2" 
  for A B C C\<^sub>1 C\<^sub>2
  by (metis Diff_eq_empty_iff Int_Diff inf.bounded_iff that)\<close>

\<^cancel>\<open>lemma l2:"(A \<setminus> (B\<^sub>1 \<inter> B\<^sub>2)) \<inter> C \<setminus> (B\<^sub>1 \<inter> B\<^sub>2) = {}"
  if "(A \<setminus> B\<^sub>1) \<inter> (C \<setminus> B\<^sub>1) = {}" and "(A \<setminus> B\<^sub>2)  \<inter> (C \<setminus> B\<^sub>2) = {}"
  for A B\<^sub>1 B\<^sub>2 C
  by (metis Diff_Int Diff_idemp Int_Diff inf_bot_right inf_commute that)\<close>

subsubsection \<open>Theorem 2\<close>

lemma l3:"quorum fbas (fst fbas \<setminus> B)" and "S \<subseteq> (fst fbas \<setminus> B)" if "dset fbas S B" and "fst fbas \<setminus> B \<noteq> {}" for B
  using that availability_despite_def dset_def apply auto[1]
  by (meson availability_despite_def system.dset_def that(1)) 

definition safe where 
  \<comment> \<open>We would like to determine what we can do at best for a safe set\<close>
  "safe fbas S \<equiv> \<forall> U1 U2 . U1 \<inter> S \<noteq> {} \<and> U2 \<inter> S \<noteq> {} \<and> quorum fbas U1 \<and> quorum fbas U1 \<longrightarrow> U1 \<inter> U2 \<inter> W \<noteq> {}"

lemma l4: "quorum (delete fbas B\<^sub>1) (fst fbas \<setminus> (B\<^sub>1 \<union> B\<^sub>2))"
  if "S \<noteq> {}" and "safe fbas S" and "S \<subseteq> (fst fbas \<setminus> B\<^sub>1)" and "S \<subseteq> (fst fbas \<setminus> B\<^sub>2)" 
    and "quorum fbas (fst fbas \<setminus> B\<^sub>1)" and "quorum fbas (fst fbas \<setminus> B\<^sub>2)" for B\<^sub>1 B\<^sub>2
  nitpick
proof -
  have "(fst fbas \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> W \<noteq> {}" using that \<open>safe fbas S\<close>
    by (simp add: Diff_Un inf.absorb_iff2 safe_def) 
      \<comment> \<open>@{term "fst fbas \<setminus> (B\<^sub>1 \<union> B\<^sub>2)"} contains a well-behaved node\<close>
  thus "quorum (delete fbas B\<^sub>1) (fst fbas \<setminus> (B\<^sub>1 \<union> B\<^sub>2))" using quorum_delete that
    by (smt Diff_Un Diff_eq inf.commute inf.left_commute inf.left_idem)
qed

lemma l5:"quorum (delete fbas B\<^sub>1) (U \<setminus> B\<^sub>1)" and "(U \<setminus> B\<^sub>1) \<inter> S \<noteq> {}"
  if "safe fbas S" and "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U" and "S \<inter> U \<noteq> {}"
    and "dset fbas S B\<^sub>1" and "dset fbas S B\<^sub>2" and "B\<^sub>1 \<noteq> fst fbas" and "B\<^sub>2 \<noteq> fst fbas" for U B\<^sub>1 B\<^sub>2
    \<comment> \<open>This is the crucial lemma\<close>
  nitpick
proof -
  show "(U \<setminus> B\<^sub>1) \<inter> S \<noteq> {}"
  proof -
    have "S \<subseteq> fst fbas - B\<^sub>1"
      by (meson availability_despite_def dset_def that(4))
    then show ?thesis
      using that(3) by blast
  qed
next
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
    have "(U \<setminus> B\<^sub>2) \<inter> (fst fbas \<setminus> (B\<^sub>1 \<union> B\<^sub>2)) \<inter> W \<noteq> {}" 
    proof -
      from b have "quorum (delete fbas B\<^sub>2) (U \<setminus> B\<^sub>2)" 
        using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> delete_more
        by (metis Int_commute inf_le2) 
      moreover
      have "quorum (delete fbas B\<^sub>2) (fst fbas \<setminus> (B\<^sub>1 \<union> B\<^sub>2))" 
        using l4 \<open>dset fbas S B\<^sub>1\<close> \<open>dset fbas S B\<^sub>2\<close> \<open>B\<^sub>1 \<noteq> fst fbas\<close> \<open>B\<^sub>2 \<noteq> fst fbas\<close> \<open>S \<noteq> {}\<close> \<open>safe fbas S\<close>
        unfolding dset_def availability_despite_def
        by (metis sup_commute)
      ultimately 
      show ?thesis using \<open>dset fbas S B\<^sub>2\<close> \<open>B\<^sub>2 \<noteq> fst fbas\<close> that(2) 
        by (auto simp add: dset_def intersection_despite_def quorum_intersection_def system.availability_despite_def)
    qed
    hence "(U \<setminus> B\<^sub>1) \<inter> W \<noteq> {}" by (auto)
    thus ?thesis by (meson inf_le1 system.delete_more \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close>) 
  next
    case a thus ?thesis 
      using \<open>quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<close> delete_more by (metis Int_lower1)
  qed
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

  have ?thesis if "?U1 = {} \<or> ?U2 = {}"
  proof -
    have "B\<^sub>1 \<inter> B\<^sub>2 = B\<^sub>2 \<or> B\<^sub>1 \<inter> B\<^sub>2 = B\<^sub>1" using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> unfolding dset_def by force
    thus ?thesis using \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> by metis
  qed

  moreover have ?thesis if "?U1 \<noteq> {} \<and> ?U2 \<noteq> {}"
  proof -
    text \<open>We need to prove quorum availability despite @{term "B\<^sub>1 \<inter> B\<^sub>2"} and quorum intersection despite @{term "B\<^sub>1 \<inter> B\<^sub>2"}\<close>

    text \<open>We start with availability. This is simple.\<close>
    have "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      have "quorum fbas (?U1 \<union> ?U2)" 
        using quorum_union l3 that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> by simp
      thus "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
        by (simp add: Diff_Int system.availability_despite_def) 
    qed

    moreover
    text \<open>Now we prove quorum intersection.\<close>
    have "intersection_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      have "U\<^sub>a \<inter> U\<^sub>b \<inter> W \<noteq> {}" if "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>a" and "quorum (delete fbas (B\<^sub>1 \<inter> B\<^sub>2)) U\<^sub>b" for U\<^sub>a U\<^sub>b
        \<comment> \<open>As direct application of l5, we show that if we take two quorums @{term U\<^sub>a} and @{term U\<^sub>b} in @{term "delete fbas (B\<^sub>1 \<inter> B\<^sub>2)"}, 
        then @{term "U\<^sub>a \<inter> U\<^sub>b \<inter> W \<noteq> {}"}. This suffices to show quorum intersection despite @{term "B\<^sub>1 \<inter> B\<^sub>2"}\<close>
      proof -
        have "quorum (delete fbas B\<^sub>1) (U\<^sub>a \<setminus> B\<^sub>1)" and "quorum (delete fbas B\<^sub>1) (U\<^sub>b \<setminus> B\<^sub>1)"
          using l5 \<open>quorum_intersection fbas\<close> \<open>fst fbas - B\<^sub>1 \<noteq> {} \<and> fst fbas - B\<^sub>2 \<noteq> {}\<close> assms(2-3) that(1-2) by fastforce+
        hence  "(U\<^sub>a \<setminus> B\<^sub>1) \<inter> (U\<^sub>b \<setminus> B\<^sub>1) \<inter> W \<noteq> {}"  
          using \<open>dset fbas B\<^sub>1\<close> unfolding quorum_intersection_def dset_def intersection_despite_def by auto 
        thus ?thesis by blast
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
proof (cases "S = fst fbas")
  case True \<comment> \<open>The case in which all nodes are befouled\<close>
  thus "dset fbas S"
    by (simp add: system.availability_despite_def system.delete_def system.dset_def system.intersection_despite_def system.quorum_def system.quorum_intersection_def) 
next
  case False
  text \<open>First we show that the set of befouled nodes is equal to the intersection of all dsets  that contain all ill-behaved nodes\<close>
  let ?D = "\<Inter>{B | B . dset fbas B \<and> -W \<subseteq> B}"
  have "S = ?D"
  proof - 
    have "x \<in> ?D" if "x \<in> S" for x using that
      unfolding S_def intact_def by force
    moreover have "x \<in> S" if "x \<in> ?D" for x
      using that False by (auto simp add: S_def intact_def dset_def)
    ultimately show "S = ?D" by blast
  qed
  text \<open>The we apply theorem 2. For that we need to establish a few preconditions about @{term "{B | B . dset fbas B \<and> -W \<subseteq> B}"}.\<close>
  have "{B | B . dset fbas B \<and> -W \<subseteq> B} \<noteq> {}" using \<open>S = ?D\<close> \<open>S \<noteq> fst fbas\<close> S_def by auto
  moreover
  have "\<And>A B. A \<in> {B | B . dset fbas B \<and> -W \<subseteq> B} \<Longrightarrow> B \<in> {B | B . dset fbas B \<and> -W \<subseteq> B} \<Longrightarrow> A \<inter> B \<in> {B | B . dset fbas B \<and> -W \<subseteq> B}" 
    using dset_closed[OF \<open>quorum_intersection fbas\<close>] by fastforce \<comment> \<open>Here we applied theorem 2\<close>

  text \<open>Now we can apply ne_family_intersection\<close>
  ultimately have "S \<in> {B | B . dset fbas B \<and> -W \<subseteq> B}" using ne_family_intersection[of "{B | B . dset fbas B \<and> -W \<subseteq> B}"] 
    by (simp add:\<open>S = ?D\<close>)
  thus "dset fbas S" by blast 
qed

end

subsection \<open>Section 5\<close>

locale voting = system W for W::"'node::finite set" + 
  fixes vote :: "'node \<Rightarrow> 'statement \<Rightarrow> bool" and contradictory :: "'statement \<Rightarrow> 'statement \<Rightarrow> bool"
  assumes "\<And> n v v' . n \<in> W \<Longrightarrow> vote n v \<Longrightarrow> vote n v' \<Longrightarrow> contradictory v v' \<Longrightarrow> False"
    \<comment> \<open>here we assume model a system state in which nodes have cast votes and no well-behaved node
voted for contradictory statements\<close>
begin

definition ratified_by_set where
  \<comment> \<open>note here that we talk only about well-behaved nodes\<close>
  "ratified_by_set ns v \<equiv> \<forall> n \<in> ns \<inter> W . vote n v"

definition ratified where
  "ratified fbas U v \<equiv> quorum fbas U \<and> ratified_by_set U v"

definition ratifies where
  "ratifies fbas n v \<equiv> \<exists> U . n \<in> U \<and> ratified fbas U v"

theorem theorem_4:
  assumes "ratified fbas U\<^sub>1 v" and "ratified fbas U\<^sub>2 v'"
    and "contradictory v v'" and "quorum_intersection fbas"
  shows False
proof -
  from \<open>ratified fbas U\<^sub>1 v\<close> and \<open>ratified fbas U\<^sub>2 v'\<close> have 
    "quorum fbas U\<^sub>1" and "quorum fbas U\<^sub>2" unfolding ratified_by_set_def using ratified_def by auto
  hence "U\<^sub>1 \<inter> U\<^sub>2 \<inter> W \<noteq> {}" using \<open>quorum_intersection fbas\<close>  by (auto simp add:system.quorum_intersection_def)
  with this obtain n where "n \<in> W" and "n\<in>U\<^sub>1" and "n\<in>U\<^sub>2" by blast
  hence "vote n v" and "vote n v'"
    using \<open>ratified fbas U\<^sub>1 v\<close> \<open>ratified fbas U\<^sub>2 v'\<close> unfolding ratified_def ratified_by_set_def by auto
  thus False using \<open>contradictory v v'\<close> \<open>n \<in> W\<close> using voting_axioms by (simp add:voting_def)
qed

theorem theorem_5:
  assumes "intersection_despite fbas B" and "-W \<subseteq> B"
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
    using \<open>U\<^sub>2 - B \<noteq> {}\<close> and \<open>U\<^sub>1 - B \<noteq> {}\<close> and \<open>quorum fbas U\<^sub>1\<close> and \<open>quorum fbas U\<^sub>2\<close> and quorum_delete \<open>-W \<subseteq> B\<close>
    by blast+
  moreover have "fst (delete fbas B) \<subseteq> W" using \<open>-W \<subseteq> B\<close>
    by (smt ComplI DiffD2 fst_conv subset_eq system.delete_def)
  moreover have "ratified_by_set (U\<^sub>1 - B) v" and "ratified_by_set (U\<^sub>2 - B) v'"
    using \<open>ratified_by_set U\<^sub>1 v\<close> \<open>ratified_by_set U\<^sub>2 v'\<close> ratified_by_set_def by auto
  ultimately show False 
    using \<open>intersection_despite fbas B\<close> theorem_4 \<open>contradictory v v'\<close>
    unfolding intersection_despite_def ratifies_def ratified_def by blast
qed

theorem theorem_6:
  assumes "ratifies fbas n v" and "ratifies fbas n' v'"
    and "contradictory v v'" and "quorum_intersection fbas" and "well_formed_fbas fbas"
  shows False
  using assms ratifies_def theorem_4 by blast

end

context system begin

definition v_blocking where 
  "v_blocking fbas B n \<equiv> let Q = snd fbas in \<forall> U \<in> Q n . U \<inter> B \<noteq> {}"

theorem theorem_7:
  fixes fbas B
  defines "V \<equiv> fst fbas"
  assumes "B \<subseteq> V" and "well_formed_fbas fbas" and "W \<noteq> {}" and "B \<noteq> V"
  shows "availability_despite fbas B \<longrightarrow> ((V \<setminus> B) \<inter> W \<noteq> {} \<and> (\<forall> n \<in> (V \<setminus> B) \<inter> W . \<not> v_blocking fbas B n))"
proof -
  let ?Q = "snd fbas"
  have "(\<forall> n \<in> (V \<setminus> B) \<inter> W . \<not> v_blocking fbas B n) =
    (\<forall> n \<in> (V \<setminus> B) \<inter> W . (\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B))"
  proof -
    have "(\<not> v_blocking fbas B n) = (\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B)" if "n \<in> (V \<setminus> B)\<inter>W" for n
    proof -
      have "(\<not> v_blocking fbas B n) \<Longrightarrow> (\<exists> U \<in> ?Q n . U \<subseteq> V \<setminus> B)"
      proof -
        assume "\<not> v_blocking fbas B n"
        with this
        obtain U where "U \<in> ?Q n" and "U \<inter> B = {}" 
          unfolding v_blocking_def by auto
        moreover have "U \<subseteq> V" using \<open>well_formed_fbas fbas\<close> \<open>n \<in> (V \<setminus> B) \<inter> W\<close> \<open>U \<in> ?Q n\<close>
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
    using V_def \<open>B \<subseteq> V\<close> nitpick
  finally show ?thesis by simp
qed

end

end