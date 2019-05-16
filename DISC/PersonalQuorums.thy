theory PersonalQuorums
  imports Main 
begin

section "Personal Quorums"

locale personal_quorums =
  fixes quorum :: "'node set \<Rightarrow> bool" and quorum_of :: "'node \<Rightarrow> 'node set \<Rightarrow> bool"
  assumes p1:"\<And> p . quorum_of p Q \<Longrightarrow> quorum Q"
    and p2:"\<And> p p' . \<lbrakk>quorum_of p Q; p' \<in> Q\<rbrakk> \<Longrightarrow> quorum_of p' Q"
begin

definition blocks where
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"

abbreviation blocked where "blocked R \<equiv> {p . blocks R p}"

lemma blocked_blocked_subset_blocked:
  "blocked (blocked R) \<subseteq> blocked R" 
proof -
  have False if "p \<in> blocked (blocked R)" and "p \<notin> blocked R" for p
  proof -
    have "\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> blocked R \<noteq> {}" 
      using \<open>p \<in> blocked (blocked R)\<close> blocks_def by auto
    have "Q \<inter> R \<noteq> {}" if " quorum_of p Q" for Q
    proof -
      obtain p' where "p' \<in> blocked R" and "p' \<in> Q"
        by (meson Int_emptyI \<open>\<And>Q. quorum_of p Q \<Longrightarrow> Q \<inter> blocked R \<noteq> {}\<close> \<open>quorum_of p Q\<close>)
      hence "quorum_of p' Q"
        using p2 that by blast
      with \<open>p' \<in> blocked R\<close> show "Q \<inter> R \<noteq> {}"
        using blocks_def by auto
    qed
    hence "p \<in> blocked R" by (simp add: blocks_def)
    thus False using that(2) by auto
  qed
  thus "blocked (blocked R) \<subseteq> blocked R"
    by blast
qed

end

subsection "Intact sets"

locale with_w = personal_quorums quorum quorum_of for quorum :: "'node set \<Rightarrow> bool" and quorum_of +
  fixes W::"'node set"
begin

abbreviation B where "B \<equiv> -W"

definition quorum_of_set where "quorum_of_set S Q \<equiv> quorum Q \<and> (\<exists> p \<in> S . quorum_of p Q)"

definition is_weakly_intact where
  "is_weakly_intact I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<subseteq> I . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set I Q \<and> quorum_of_set I Q' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition is_strongly_intact where
  "is_strongly_intact I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<subseteq> I . quorum_of p Q)
      \<and> (\<forall> Q Q' . quorum_of_set I Q \<and> quorum_of_set I Q' \<longrightarrow> I \<inter> Q \<inter> Q' \<noteq> {})"

lemma intact_union:
  assumes "is_weakly_intact I\<^sub>1" and "is_weakly_intact I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_weakly_intact (I\<^sub>1\<union> I\<^sub>2)"
proof -
  have "I\<^sub>1 \<union> I\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_weakly_intact_def by auto 
  moreover
  have "\<forall> p \<in> (I\<^sub>1\<union>I\<^sub>2) . \<exists> Q \<subseteq> (I\<^sub>1\<union>I\<^sub>2) . quorum_of p Q" 
    using \<open>is_weakly_intact I\<^sub>1\<close> \<open>is_weakly_intact I\<^sub>2\<close> unfolding is_weakly_intact_def
    by (meson UnE le_supI1 le_supI2)
  moreover
  have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}"
    if "quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>1" and "quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>2" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "quorum_of_set I Q\<^sub>1" and "quorum_of_set I Q\<^sub>2" and "I = I\<^sub>1 \<or> I = I\<^sub>2" for I
      using \<open>is_weakly_intact I\<^sub>1\<close> \<open>is_weakly_intact I\<^sub>2\<close> \<open>quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>1\<close> \<open>quorum_of_set (I\<^sub>1\<union>I\<^sub>2) Q\<^sub>2\<close> that
      unfolding quorum_of_set_def is_weakly_intact_def by metis
    moreover
    have \<open>W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "is_weakly_intact I\<^sub>1" and "is_weakly_intact I\<^sub>2"
      and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "quorum_of_set I\<^sub>1 Q\<^sub>1" and "quorum_of_set I\<^sub>2 Q\<^sub>2"
    for I\<^sub>1 I\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      obtain p Q where "quorum_of p Q" and "p \<in> I\<^sub>1 \<inter> I\<^sub>2" and "Q \<subseteq> I\<^sub>2" 
        using \<open>I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}\<close> \<open>is_weakly_intact I\<^sub>2\<close> unfolding is_weakly_intact_def by blast
      have "Q \<inter> Q\<^sub>1 \<noteq> {}" using \<open>is_weakly_intact I\<^sub>1\<close> \<open>quorum_of_set I\<^sub>1 Q\<^sub>1\<close> \<open>quorum_of p Q\<close> \<open>p \<in> I\<^sub>1 \<inter> I\<^sub>2\<close>
        unfolding is_weakly_intact_def quorum_of_set_def by (metis Int_ac(1) Int_iff inf_bot_right p1)
      hence "quorum_of_set I\<^sub>2 Q\<^sub>1"  using \<open>Q \<subseteq> I\<^sub>2\<close> \<open>quorum_of_set I\<^sub>1 Q\<^sub>1\<close> p2 unfolding quorum_of_set_def by fastforce 
      thus "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" using \<open>is_weakly_intact I\<^sub>2\<close> \<open>quorum_of_set I\<^sub>2 Q\<^sub>2\<close>
        unfolding is_weakly_intact_def by blast
    qed
    ultimately show ?thesis using assms that unfolding quorum_of_set_def by auto 
  qed
  ultimately show ?thesis using assms
    unfolding is_weakly_intact_def by simp
qed

subsection "The live set"

definition L where "L \<equiv> W - (blocked B)"

lemma l2: "p \<in> L \<Longrightarrow> \<exists> Q  \<subseteq> W. quorum_of p Q" 
  unfolding L_def blocks_def using DiffD2 by auto

lemma l3:
  assumes "p \<in> L" shows "\<exists> Q \<subseteq> L . quorum_of p Q" 
proof -
  have False if "\<And> Q . quorum_of p Q \<Longrightarrow> Q \<inter> (-L) \<noteq> {}"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> W" 
      using l2 \<open>p \<in> L\<close> by auto 
    have "Q \<inter> (-L) \<noteq> {}"  using that \<open>quorum_of p Q\<close> by simp
    obtain p' where "p' \<in> Q \<inter> (-L)" and "quorum_of p' Q"
      using \<open>Q \<inter> - L \<noteq> {}\<close> \<open>quorum_of p Q\<close> inf.left_idem p2 by fastforce 
    hence "Q \<inter> B \<noteq> {}" unfolding L_def
      using CollectD Compl_Diff_eq Int_iff inf_le1 personal_quorums.blocks_def personal_quorums_axioms subset_empty by fastforce
    thus False using \<open>Q \<subseteq> W\<close> by auto  
  qed 
  thus ?thesis by (metis disjoint_eq_subset_Compl double_complement)
qed

end

section "Stellar quorum systems"

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>the well-behaved nodes\<close>
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . \<exists> Sl \<in> slices p . Sl \<subseteq> Q"

definition quorum_of where "quorum_of p Q \<equiv> quorum Q \<and> (p \<notin> W \<or> (\<exists> Sl \<in> slices p . Sl \<subseteq> Q))"

lemma quorum_union:"quorum Q \<Longrightarrow> quorum Q' \<Longrightarrow> quorum (Q \<union> Q')"
  unfolding quorum_def
  by (metis IntE Int_iff UnE inf_sup_aci(1) sup.coboundedI1 sup.coboundedI2)

lemma l4:"quorum_of p Q \<Longrightarrow> p' \<in> Q \<Longrightarrow> quorum_of p' Q"
  \<comment> \<open>This is the main property of personal quorum systems\<close>
  by (simp add: quorum_def quorum_of_def)

interpretation with_w quorum quorum_of unfolding with_w_def personal_quorums_def 
  apply (intro conjI)
  subgoal unfolding quorum_of_def by simp
  subgoal unfolding quorum_def quorum_of_def by simp
  done

lemma quorum_is_quorum_of_some_slice:
  assumes "quorum_of p Q" and "p \<in> W"
  obtains S where "S \<in> slices p" and "S \<subseteq> Q"
    and "\<And> p' . p' \<in> S \<inter> W \<Longrightarrow> quorum_of p' Q"
  using assms unfolding quorum_def
  by (metis (full_types) IntD1 quorum_of_def p2 subset_eq) 

subsection "Inductive definition of blocked"

inductive blocking_min where
  \<comment> \<open>This is the set of participants eventually blocked by R when byzantine processors do not take steps\<close>
  "\<forall> Sl \<in> slices p . \<exists> q \<in> Sl\<inter>W . q \<in> R \<or> blocking_min R q \<Longrightarrow> blocking_min R p"

inductive blocking_max where
  \<comment> \<open>This is the set of participants eventually blocked by R when byzantine processors help epidemic propagation\<close>
  "\<forall> Sl \<in> slices p . \<exists> q \<in> Sl . q \<in> R \<or> blocking_max R q \<Longrightarrow> blocking_max R p"

subsubsection \<open>Properties of @{term blocking}\<close>

text \<open>Here we show two main lemmas:
  \<^item> if @{term \<open>R\<close>} blocks @{term \<open>p \<in> Intact\<close>}, then @{term \<open>R \<inter> Intact \<noteq> {}\<close>}
  \<^item> if @{term \<open>p \<in> Intact\<close>} and quorum @{term Q} is such that @{term \<open>Q \<inter> Intact \<noteq> {}\<close>}, 
    then @{term \<open>Q \<inter> W\<close>} is blocking @{term p}
\<close>

lemma intact_wb:"p \<in> I \<Longrightarrow> is_weakly_intact I \<Longrightarrow> p\<in>W"
  using is_weakly_intact_def  by fastforce 

lemma l8:
  assumes  "blocking_max R p" and "is_weakly_intact I" and "p \<in> I"
  shows "R \<inter> I \<noteq> {}"  using assms 
proof (induct)
  case (1 p R)
  obtain Sl where "Sl \<in> slices p" and "Sl \<subseteq> I"
  proof -
    obtain Q where "quorum_of p Q" and "Q \<subseteq> I" using \<open>is_weakly_intact I\<close> \<open>p\<in>I\<close> unfolding is_weakly_intact_def by blast
    obtain Sl where "Sl \<in> slices p" and "Sl \<subseteq> Q"using quorum_is_quorum_of_some_slice \<open>p\<in>I\<close> \<open>is_weakly_intact I\<close> intact_wb \<open>quorum_of p Q\<close> by metis
    show ?thesis using that \<open>Sl \<subseteq> Q\<close> \<open>Q \<subseteq> I\<close> \<open>Sl \<in> slices p\<close> by simp
  qed
  have "\<exists>q\<in>Sl. q \<in> R \<or> blocking_max R q \<and> (q \<in> I \<longrightarrow> R \<inter> I \<noteq> {})"
    using 1 \<open>Sl \<in> slices p\<close> by auto
  then show ?case using \<open>Sl \<subseteq> I\<close> by auto 
qed

inductive not_blocked for p R where
  "\<lbrakk>Sl \<in> slices p; \<forall> q \<in> Sl\<inter>W . q \<notin> R \<and> \<not>blocking_min R q; q \<in> Sl\<rbrakk> \<Longrightarrow> not_blocked p R q"
| "\<lbrakk>not_blocked p R p'; p' \<in> W; Sl \<in> slices p'; \<forall> q \<in> Sl\<inter>W . q \<notin> R \<and> \<not>blocking_min R q; q \<in> Sl\<rbrakk> \<Longrightarrow> not_blocked p R q"

lemma l9:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  shows "quorum Q" nitpick[card 'node=6, iter stellar.blocking_min=6, timeout=3000, iter stellar.not_blocked = 6, timeout=3000]  
proof -
  have "\<forall> n\<in>Q\<inter>W . \<exists> S\<in>slices n . S \<subseteq>Q"
  proof (simp add: Q_def; clarify)
    fix n
    assume "not_blocked p R n" and "n\<in>W"
    thus "\<exists>S\<in>slices n. S \<subseteq> Collect (not_blocked p R)"
    proof (cases)
      case (1 Sl)
      then show ?thesis
        by (smt Ball_Collect Int_iff \<open>n \<in> W\<close> \<open>not_blocked p R n\<close> blocking_min.intros not_blocked.intros(2))
    next
      case (2 p' Sl)
      hence "n \<notin> R" and "\<not>blocking_min R n" using \<open>n \<in> W\<close> by auto
      with this obtain Sl where "Sl \<in> slices n" and "\<forall> q \<in> Sl\<inter>W . q \<notin> R \<and> \<not> blocking_min R q"
        by (meson blocking_min.intros blocking_min.intros(1))
      moreover note \<open>not_blocked p R n\<close>
      ultimately show ?thesis
        by (metis \<open>n \<in> W\<close> mem_Collect_eq not_blocked.intros(2) subsetI)
    qed
  qed
  thus ?thesis by (simp add: quorum_def)
qed

lemma l10:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  shows "Q \<inter> R \<inter> W= {}" (* nitpick[card 'node=6, iter stellar.blocking_min=6, timeout=3000, iter stellar.not_blocked = 6] oops *)
proof -
  have "q \<notin> R" if "not_blocked p R q" and "q\<in> W" for q using that
  proof (induct)
    case (1 Sl)
    then show ?case by auto
  next
    case (2 p' Sl p'')
    then show ?case using blocking_min.intros(1) by blast 
  qed
  thus ?thesis unfolding Q_def by auto
qed

lemma l11:
  assumes "quorum_of_set I Q" and "p\<in>I" and "is_weakly_intact I"
  shows "blocking_min (Q \<inter> W) p" nitpick[card 'node=6, iter stellar.blocking_min=6, timeout=3000, iter stellar.not_blocked = 6]
proof (rule ccontr)
  assume "\<not> blocking_min (Q \<inter> W) p"
  define Q' where "Q' \<equiv> {q . not_blocked p (Q\<inter>W) q}"
  have "quorum Q'" and "Q' \<inter> (Q\<inter>W) = {}"
    by (simp add: Q'_def l9) (metis Q'_def inf.right_idem inf_bot_right inf_left_commute l10)
  obtain Sl where "Sl \<in> slices p" and "\<forall> q \<in> Sl\<inter>W . q \<notin> (Q\<inter>W) \<and> \<not>blocking_min (Q\<inter>W) q"
    by (meson \<open>\<not> blocking_min (Q \<inter> W) p\<close> stellar.blocking_min.intros) 
  have "Sl \<subseteq> Q'" unfolding Q'_def
    using \<open>Sl \<in> slices p\<close> \<open>\<forall>q\<in>Sl\<inter>W. q \<notin> Q \<inter> W \<and> \<not> blocking_min (Q \<inter> W) q\<close> not_blocked.intros(1) by force 
  hence "quorum_of p Q'"
    by (meson \<open>Sl \<in> slices p\<close> \<open>quorum Q'\<close> stellar.quorum_of_def)
  thus False using \<open>Q' \<inter> (Q\<inter>W) = {}\<close> \<open>quorum_of_set I Q\<close> \<open>is_weakly_intact I\<close> \<open>p\<in>I\<close> unfolding is_weakly_intact_def quorum_of_set_def
    by (metis (full_types) Int_commute stellar.quorum_of_def) 
qed

section \<open>Reachable part of a quorum\<close>

text \<open>Here we define the part of a quorum Q of p that is reachable through well-behaved
nodes from p. We show that if p and p' are intact and Q is a quorum of p and Q' is a quorum of p',
then the intersection of Q, Q', and W is reachable from both p and p' through intact participants.\<close>

inductive reachable for p Q where
  "reachable p Q p"
| "\<lbrakk>reachable p Q p'; p' \<in> W; S \<in> slices p'; S \<subseteq> Q; p'' \<in> S\<rbrakk> \<Longrightarrow> reachable p Q p''"

definition truncation where "truncation p Q \<equiv> {p' . reachable p Q p'}"

lemma l13:
  assumes "quorum_of p Q" and "p \<in> W" and "reachable p Q p'"
  shows "quorum_of p' Q"
  using assms using p2 reachable.cases by blast

lemma l14:
  assumes "quorum_of p Q" and "p \<in> W"
  shows "quorum (truncation p Q)"
proof -
  have "\<exists> S \<in> slices p' . \<forall> q \<in> S . reachable p Q q" if "reachable p Q p'" and "p' \<in> W" for p'
    by (meson assms quorum_is_quorum_of_some_slice reachable.intros(2) stellar.l13 that) 
  thus ?thesis by (simp add: stellar.quorum_def subset_eq truncation_def)  
qed

lemma l15:
  assumes "is_weakly_intact I" and "quorum_of p Q" and "quorum_of p' Q'" and "p \<in> I" and "p' \<in> I" and "Q \<inter> Q' \<inter> W \<noteq> {}"
  shows "W \<inter> (truncation p Q) \<inter> (truncation p' Q') \<noteq> {}" 
proof -
  have "quorum (truncation p Q)" and "quorum (truncation p' Q')" using l14 assms is_weakly_intact_def by auto
  moreover have "quorum_of_set I (truncation p Q)" and "quorum_of_set I (truncation p' Q')"
    by (metis IntI assms(4,5) calculation mem_Collect_eq quorum_def quorum_of_def quorum_of_set_def reachable.intros(1) truncation_def)+
  moreover note \<open>is_weakly_intact I\<close>
  ultimately show ?thesis unfolding is_weakly_intact_def by auto
qed

end

section "elementary quorums"

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
