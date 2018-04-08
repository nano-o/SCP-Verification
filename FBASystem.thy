theory FBASystem
imports Main "HOL-Eisbach.Eisbach"
begin

section \<open> An auxiliary fact about closure under intersection\<close>

locale ne_family_intersection = fixes x::"'node::finite set" and X::"'node set set"
  assumes ne:"X \<noteq> {}" and all_ne:"\<And> x . x \<in> X \<Longrightarrow> x \<noteq> {}"
  and closed:"\<And> A B . A \<in> X \<Longrightarrow> B \<in> X \<Longrightarrow> A \<inter> B \<in> X"
  -- \<open>@{term X} is closed under intersection\<close>
begin

context begin

private lemma l2:
  "wf {(X::'a::finite set,Y). X \<subset> Y}"
  by (metis (mono_tags, hide_lams) finite_code finite_psubset_induct mem_Collect_eq old.prod.case wf_def) 

interpretation fold_inter:folding_idem "op\<inter>" "UNIV"
  by (unfold_locales, auto)

private lemma l3:"\<And> (X::'a::finite set set) . \<Inter>X = fold_inter.F X"
  by (simp add: Inf_fold_inf fold_inter.eq_fold)

theorem Int_in:"\<Inter>X \<in> X"
proof (simp add:l3)
  note l2
  moreover note closed ne all_ne
  ultimately show "fold_inter.F X \<in> X"
  proof (induct rule:wf_induct_rule)
    case (less X)
    have ?case if "X={x}" for x using that by auto 
    moreover
    have ?case if "\<And> x . X \<noteq> {x}"
    proof -
      obtain a b Y where "X = insert a (insert b Y)" and "a \<noteq> b"
        by (metis Set.set_insert \<open>\<And>x. X \<noteq> {x}\<close> ex_in_conv less.prems(2))
      obtain e S where "e \<noteq> {}" and "S \<noteq> {}" and "e \<notin> S"
        "X = insert e S" and "\<And> A B . A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A \<inter> B \<in> S" sorry
      have "\<And>x. x \<in> S \<Longrightarrow> x \<noteq> {}"
        by (simp add: \<open>X = insert e S\<close> less.prems(3)) 
      have "(S, X) \<in> {(x, y). x \<subset> y}" using \<open>X = insert e S\<close> \<open>e \<notin> S\<close> by auto
      have "\<Inter>S\<in>S" apply (simp add:l3)
        using \<open>(S, X) \<in> {(x, y). x \<subset> y}\<close> \<open>S \<noteq> {}\<close> \<open>\<And>B A. \<lbrakk>A \<in> S; B \<in> S\<rbrakk> \<Longrightarrow> A \<inter> B \<in> S\<close> \<open>\<And>x. x \<in> S \<Longrightarrow> x \<noteq> {}\<close> less.hyps by auto
      then show ?case
        by (metis Inf_insert \<open>X = insert e S\<close> insert_iff l3 less.prems(1))
    qed
    ultimately show ?case by blast
  qed
qed

end

end

text \<open>This is a formalization of the definitions and theorems of the Stellar white-paper.\<close>

section \<open>Section 3\<close>

type_synonym 'node fbas = "('node set \<times> ('node \<Rightarrow> 'node set set))"
 -- \<open>A federated byzantine agreement system is a pair @{term "(fbas::'node fbas) = (V,Q)"} consisting
of a node set @{term "V::'node set"} and a quorum function @{term "Q::'node \<Rightarrow> 'node set set"}.\<close>

locale system = fixes well_behaved :: "'node::finite \<Rightarrow> bool"
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

theorem dset_intersection: --\<open>This is theorem 2 of the whitepaper\<close>
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
    text \<open>First qwe show the @{term ?U1} and @{term ?U2} are quorums in @{term fbas}, which will come handy later on. This comes from quorum availability.\<close>
    have 1:"quorum fbas ?U1" and 2:"quorum fbas ?U2" 
      using that \<open>dset fbas B\<^sub>1\<close> \<open>dset fbas B\<^sub>2\<close> availability_despite_def
      by (metis Diff_cancel dset_def)+

    text \<open>We need to prove quorum availability despite @{term "B\<^sub>1 \<inter> B\<^sub>2"} and quorum intersection despite @{term "B\<^sub>1 \<inter> B\<^sub>2"}\<close>

    text \<open>We start with availability.\<close>
    have "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      have "quorum fbas (?U1 \<union> ?U2)" using quorum_union 1 2 by blast
      thus "availability_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)" by (simp add: Diff_Int system.availability_despite_def) 
    qed

    moreover
    text \<open>Now we prove quorum intersection.\<close>
    have "intersection_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)"
    proof -
      let ?U = "?U1 \<inter> ?U2"

      text \<open>We show that if we take two quorums @{term U\<^sub>a} and @{term U\<^sub>b} in @{term "delete fbas ?B"}, then @{term "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}"}.
      This sufficies to show quorum intersection despite @{term ?B}\<close>

      have "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}" if "quorum (delete fbas ?B) U\<^sub>a" and "quorum (delete fbas ?B) U\<^sub>b" for U\<^sub>a U\<^sub>b
      proof -
        text \<open>First we show that @{term ?U} is a quorum in @{term "delete fbas B\<^sub>1"}. For this we use the lemma @{thm quorum_delete}\<close>
        have 3:"quorum (delete fbas B\<^sub>1) ?U"
        proof -
          text \<open>@{term ?U} is not empty:\<close>
          have "?U \<noteq> {}" using \<open>quorum_intersection fbas\<close> 1 2 unfolding quorum_intersection_def by simp
          hence "quorum fbas ?U2"  using \<open>dset fbas B\<^sub>2\<close>
            unfolding dset_def availability_despite_def by auto
          thus "quorum (delete fbas B\<^sub>1) ?U"
            using quorum_delete[of fbas ?U2 ?U B\<^sub>1] \<open>?U \<noteq> {}\<close> by blast
        qed

        text \<open>The we prove the following lemma, which we will apply to both @{term U\<^sub>a} and @{term U\<^sub>b}\<close>
        { fix Q
          assume "quorum (delete fbas ?B) Q"
          have "quorum (delete fbas B\<^sub>2) (Q - B\<^sub>2)"
          proof -
            consider (a) "Q - B\<^sub>1 \<noteq> {}" | (b) "Q - B\<^sub>2 \<noteq> {}" -- \<open>We have two cases\<close>
            proof -
              have "Q - ?B = {}" if "Q - B\<^sub>1 = {}" and "Q - B\<^sub>2 = {}" using that by blast
              moreover have "Q - ?B \<noteq> {}" using \<open>quorum (delete fbas ?B) Q\<close> unfolding quorum_def delete_def by fastforce
              ultimately show ?thesis using that by blast
            qed
            thus ?thesis
            proof (cases)
              case a
              hence "quorum (delete fbas B\<^sub>1) (Q - B\<^sub>1)" using \<open>quorum (delete fbas ?B) Q\<close> delete_more by (metis inf.cobounded1)
              hence "(Q - B\<^sub>1) \<inter> ?U \<noteq> {}" using \<open>quorum (delete fbas B\<^sub>1) ?U\<close>  \<open>dset fbas B\<^sub>1\<close> 
                unfolding dset_def intersection_despite_def quorum_intersection_def by blast
              hence "(Q - B\<^sub>2) \<noteq> {}" by blast
              thus "quorum (delete fbas B\<^sub>2) (Q - B\<^sub>2)" using \<open>quorum (delete fbas ?B) Q\<close> delete_more by (metis inf_le2)
            next
              case b thus ?thesis using \<open>quorum (delete fbas ?B) Q\<close> delete_more by fastforce
            qed
          qed
        }
        note l = this -- \<open>we give name l to this lemma\<close>

        text \<open>Now we apply lemma l to both @{term U\<^sub>a} and @{term U\<^sub>b}\<close>
        have "quorum (delete fbas B\<^sub>2) (U\<^sub>a - B\<^sub>2)" using l \<open>quorum (delete fbas ?B) U\<^sub>a\<close> unfolding dset_def by simp
        moreover
        have "quorum (delete fbas B\<^sub>2) (U\<^sub>b - B\<^sub>2)" using l \<open>quorum (delete fbas ?B) U\<^sub>b\<close> unfolding dset_def by simp
        ultimately have "(U\<^sub>a - B\<^sub>2) \<inter> (U\<^sub>b - B\<^sub>2) \<noteq> {}" using \<open>dset fbas B\<^sub>2\<close>
          unfolding quorum_intersection_def dset_def intersection_despite_def by simp
        thus "U\<^sub>a \<inter> U\<^sub>b \<noteq> {}" by blast -- \<open>And we are done\<close>
      qed
      thus "intersection_despite fbas (B\<^sub>1 \<inter> B\<^sub>2)" by (simp add: intersection_despite_def quorum_intersection_def) 
    qed
    ultimately show "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)"
      by (meson \<open>dset fbas B\<^sub>2\<close> inf.coboundedI2 system.dset_def)
  qed
  ultimately show "dset fbas (B\<^sub>1 \<inter> B\<^sub>2)" by blast
qed

theorem befouled_is_dset: --\<open>This is theorem 3\<close>
  fixes S and fbas
  defines "S \<equiv> {n \<in> fst fbas . befouled fbas n}"
  assumes "quorum_intersection fbas" and "S \<noteq> {}"
  shows "dset fbas S"
proof -
  let ?D = "\<Inter>{B | B . dset fbas B \<and> (\<forall> n \<in> fst fbas . \<not>well_behaved n \<longrightarrow> n \<in> B)}"
  have "S = ?D"
  proof - 
    have "x \<in> ?D" if "x \<in> S" for x using that
      unfolding S_def intact_def by force
    moreover have "x \<in> S" if "x \<in> ?D" for x using that
      unfolding S_def intact_def 
      by (auto; simp add: availability_despite_def delete_def quorum_def quorum_intersection_def dset_def intersection_despite_def)
    ultimately show "S = ?D" by blast
  qed
  thus "dset fbas S" --\<open>TODO: prove by induction using fold on finite sets?\<close>
    oops

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