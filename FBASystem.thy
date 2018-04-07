theory FBASystem
imports Main "HOL-Eisbach.Eisbach"
begin

text \<open>This is a formalization of the definitions and theorems of the Stellar white-paper.\<close>

section \<open>Section 3\<close>

type_synonym 'node fbas = "('node set \<times> 'node \<Rightarrow> 'node set set)"
 -- \<open>A federated byzantine agreement system is a pair @{term "fbas::'node fbas"} consisting 
of a node set @{term "fst fbas"} and a quorum function @{term "snd fbas"}.\<close>

locale system = fixes well_behaved :: "'node \<Rightarrow> bool"
begin

definition fbas_validity where
  -- \<open>TODO: used anywhere?\<close>
  "fbas_validity fbas \<equiv> 
    fst fbas \<noteq> {} 
    \<and> (\<forall> n \<in> fst fbas . snd fbas n \<noteq> {} \<and> (\<forall> S \<in> snd fbas n . n \<in> S \<and> S \<subseteq> fst fbas))"

definition quorum where 
  "quorum fbas ns \<equiv> ns \<noteq> {} \<and> ns \<subseteq> fst fbas \<and> (\<forall> n \<in> ns . \<exists> S \<in> snd fbas n . S \<subseteq> ns)"

section \<open>Section 4\<close>

definition quorum_intersection where
  "quorum_intersection fbas \<equiv> \<forall> ns1 ns2. quorum fbas ns1 \<and> quorum fbas ns2 \<longrightarrow> ns1 \<inter> ns2 \<noteq> {}"

definition delete where
  "delete fbas B \<equiv> (fst fbas - B, \<lambda> n . {ns - B | ns . ns \<in> snd fbas n})"

lemma delete_validity:
  -- \<open>TODO: used anywhere?\<close>
  assumes "fbas_validity fbas" and "\<not>fst fbas \<subseteq> B"
  shows "fbas_validity (delete fbas B)" using assms 
  unfolding fbas_validity_def delete_def by auto

lemma delete_delete_subseteq:
  assumes "B \<subseteq> B'" shows "delete (delete fbas B) B' = delete fbas B'" 
proof - 
  have "ns - B' = ns - B - B'" for ns using assms(1) by blast
  thus ?thesis unfolding delete_def 
    by (simp add:fun_eq_iff; clarsimp; intro set_eqI; blast)
qed

definition intersection_despite where
  "intersection_despite fbas B \<equiv> quorum_intersection (delete fbas B)"

definition availability_despite where
  "availability_despite fbas B \<equiv> quorum fbas (fst fbas - B) \<or> B = fst fbas"

definition dset where 
  "dset fbas B \<equiv> 
    B \<subseteq> fst fbas \<and> intersection_despite fbas B \<and> availability_despite fbas B"

definition intact where
  "intact fbas n \<equiv> n \<in> fst fbas \<and> 
    (\<exists> B . dset fbas B \<and> n \<notin> B \<and> (\<forall> n \<in> fst fbas . \<not> well_behaved n \<longrightarrow> n \<in> B))"

abbreviation befouled where "befouled fbas n \<equiv> \<not> intact fbas n"

theorem quorum_delete: 
  assumes "quorum fbas U" and "U' = U - B" and "U' \<noteq> {}"
  shows "quorum (delete fbas B) U'"
  using assms unfolding quorum_def delete_def
  by (clarsimp; metis Diff_iff Diff_mono order_refl)

lemma quorum_union:
  assumes "quorum fbas Q1" and "quorum fbas Q2"
  shows "quorum fbas (Q1 \<union> Q2)"
  using assms unfolding quorum_def
  by (metis (full_types) UnE Un_empty Un_subset_iff le_supI1 sup.coboundedI2) 

lemma delete_more:
  assumes "quorum (delete fbas Y) Q" and "Q - Z \<noteq> {}" and "Y \<subseteq> Z"
  shows "quorum (delete fbas Z) (Q - Z)"
proof -
  have "quorum (delete (delete fbas Y) Z) (Q - Z)" using assms(1,2) quorum_delete by blast
  moreover have "delete (delete fbas Y) Z = delete fbas Z" using assms(3)
    by (simp add: system.delete_delete_subseteq)
  ultimately show ?thesis by simp
qed

lemma L1:
  -- "Not used"
  fixes B\<^sub>1 B\<^sub>2 U2 U fbas
  defines "U\<^sub>2 \<equiv> fst fbas - B\<^sub>2"
  defines "U \<equiv> fst fbas - B\<^sub>1 - B\<^sub>2"
  assumes "availability_despite fbas B\<^sub>2" and "U \<noteq> {}"
  shows "quorum (delete fbas B\<^sub>1) U"
proof -
  have "quorum fbas U\<^sub>2" 
    using \<open>availability_despite fbas B\<^sub>2\<close> U\<^sub>2_def U_def \<open>U \<noteq> {}\<close> 
    unfolding availability_despite_def by auto
  thus "quorum (delete fbas B\<^sub>1) U"
    using quorum_delete[of fbas U\<^sub>2 U B\<^sub>1] U_def U\<^sub>2_def \<open>U \<noteq> {}\<close> by blast
qed

lemma Lemma2:
  -- \<open>This is a lemma used to prove that dsets are closed under intersection.\<close>
  fixes B\<^sub>1 B\<^sub>2 U fbas Q
  defines "U \<equiv> fst fbas - B\<^sub>1 - B\<^sub>2"
  defines "B \<equiv> B\<^sub>1 \<inter> B\<^sub>2"
  assumes 2:"quorum (delete fbas B) Q" 
    and 3:"intersection_despite fbas B\<^sub>1"
    and 6:"quorum (delete fbas B\<^sub>1) U"
  shows "quorum (delete fbas B\<^sub>2) (Q - B\<^sub>2)"
proof -
  text \<open>First we show @{term U} is a quorum in @{term "delete fbas B\<^sub>1"}. TODO: this should be outside this lemma, in T2\<close>
  consider (a) "Q - B\<^sub>1 \<noteq> {}" | (b) "Q - B\<^sub>2 \<noteq> {}" -- \<open>We have two cases\<close>
  proof -
    have "Q - B = {}" if "Q - B\<^sub>1 = {}" and "Q - B\<^sub>2 = {}" using that B_def by blast
    moreover have "Q - B \<noteq> {}" using 2 unfolding quorum_def delete_def by fastforce
    ultimately show ?thesis using that by blast
  qed
  thus ?thesis
  proof (cases)
    case a
    hence "quorum (delete fbas B\<^sub>1) (Q - B\<^sub>1)" using 2 delete_more B_def by (metis inf.cobounded1)
    hence "(Q - B\<^sub>1) \<inter> U \<noteq> {}" using 6 3
      by (meson dset_def intersection_despite_def quorum_intersection_def)
    hence "(Q - B\<^sub>2) \<noteq> {}" using U_def by blast
    thus "quorum (delete fbas B\<^sub>2) (Q - B\<^sub>2)" using 2 delete_more B_def by (metis inf_le2)
  next
    case b thus ?thesis using 2 B_def delete_more by fastforce
  qed
qed

theorem Theorem2:
  fixes B\<^sub>1 B\<^sub>2 V U fbas
  assumes "quorum_intersection fbas" and "dset fbas B\<^sub>1" and "dset fbas B\<^sub>2"
  shows "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)"
proof -
  let ?V = "fst fbas"
  let ?U1 = "?V - B\<^sub>1"
  let ?U2 = "?V - B\<^sub>2"
  let ?B = "B\<^sub>1 \<inter> B\<^sub>2"
  have ?thesis if "?U1 = {} \<or> ?U2 = {}"
  proof -
    have "?B = B\<^sub>2 \<or> ?B = B\<^sub>1" using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> unfolding dset_def by blast
    thus ?thesis using \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> by metis
  qed
  moreover have ?thesis if "?U1 \<noteq> {} \<and> ?U2 \<noteq> {}"
  proof -
    have 1:"quorum fbas ?U1" and 2:"quorum fbas ?U2" using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> availability_despite_def
      by (metis Diff_cancel dset_def)+
        -- \<open>Note how 1 and 2 come from quorum availability\<close>
    text \<open>We need to prove quorum availability despite @{term "B\<^sub>1 \<inter> B\<^sub>2"} and quorum intersection despite @{term "B\<^sub>1 \<inter> B\<^sub>2"}\<close>
    have "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      have "quorum fbas (?U1 \<union> ?U2)" using quorum_union 1 2 by blast
      thus ?thesis by (simp add: Diff_Int system.availability_despite_def) 
    qed
    moreover
    have "intersection_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      let ?U = "?U1 \<inter> ?U2"
      have 3:"?U \<noteq> {}" using \<open>quorum_intersection fbas\<close> 1 2 unfolding quorum_intersection_def by simp
      have 4:"quorum (delete fbas B\<^sub>1) ?U"
      proof -
        have "quorum fbas ?U2" 
          using \<open>dset fbas B\<^sub>2\<close> \<open>?U \<noteq> {}\<close> 
          unfolding dset_def availability_despite_def by auto
        thus "quorum (delete fbas B\<^sub>1) ?U"
          using quorum_delete[of fbas ?U2 ?U B\<^sub>1] \<open>?U \<noteq> {}\<close> by blast
      qed
      have "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}" if 5:"quorum (delete fbas ?B) U\<^sub>a" and 6:"quorum (delete fbas ?B) U\<^sub>b" for U\<^sub>a U\<^sub>b
      proof -
        have "quorum (delete fbas B\<^sub>2) (U\<^sub>a - B\<^sub>2)" using Lemma2[of fbas B\<^sub>1 B\<^sub>2 U\<^sub>a] 4 5 \<open>dset fbas B\<^sub>1\<close> unfolding dset_def
          by (metis (no_types, hide_lams) Diff_Compl Diff_Diff_Int Diff_Int2 Diff_cancel Diff_empty inf.commute)
        moreover
        have "quorum (delete fbas B\<^sub>2) (U\<^sub>b - B\<^sub>2)" using Lemma2[of fbas B\<^sub>1 B\<^sub>2 U\<^sub>b] 4 6 \<open>dset fbas B\<^sub>1\<close> unfolding dset_def
          by (metis (no_types, hide_lams) Diff_Compl Diff_Diff_Int Diff_Int2 Diff_cancel Diff_empty inf.commute)
        ultimately have "(U\<^sub>a - B\<^sub>2) \<inter> (U\<^sub>b - B\<^sub>2) \<noteq> {}"
          by (meson \<open>dset fbas B\<^sub>2\<close> quorum_intersection_def dset_def intersection_despite_def)
        thus ?thesis by blast
      qed
      thus ?thesis by (simp add: intersection_despite_def quorum_intersection_def) 
    qed
    ultimately show ?thesis
      by (meson \<open>dset fbas B\<^sub>2\<close> inf.coboundedI2 system.dset_def)
  qed
  ultimately show ?thesis by blast
qed

theorem T3:
  fixes S fbas
  defines "S \<equiv> {n \<in> fst fbas . befouled fbas n}"
  assumes "quorum_intersection fbas"
  shows "dset fbas S"
  using assms  unfolding quorum_intersection_def quorum_def dset_def Let_def delete_def

end

section \<open>Section 5\<close>

locale voting = system well_behaved for well_behaved::"'node \<Rightarrow> bool" 
  + fixes vote :: "'node \<Rightarrow> 'value"
begin

definition ratified_by_set where
  "ratified_by_set ns v \<equiv> \<forall> n \<in> ns . vote n = v"

definition ratifies where
  "ratifies fbas n v \<equiv> \<exists> Q . Q \<in> snd fbas n \<and> ratified_by_set Q v"





end

end