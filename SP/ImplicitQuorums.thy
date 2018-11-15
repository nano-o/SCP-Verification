theory ImplicitQuorums
  imports Main
begin

section "personal quorums"

locale personal =
  fixes quorums :: "'node \<Rightarrow> 'node set set" and W::"'node set"
  assumes p1:"\<And> p . Q \<in> quorums p \<Longrightarrow> p \<in> Q"
    and p2:"\<And> p p' Q . \<lbrakk>Q \<in> quorums p; p' \<in> Q\<rbrakk> \<Longrightarrow> Q \<in> quorums p'"
      \<comment> \<open>the existence of at least one quorum per participant and closure under union are unnecessary for what follows\<close>
begin

definition is_intact where 
  "is_intact I \<equiv> I \<subseteq> W \<and> (\<forall> p \<in> I . \<exists> Q \<in> quorums p . Q \<subseteq> I)
      \<and> (\<forall> p p' Q Q' . p \<in> I \<and> p'\<in> I \<and> Q \<in> quorums p \<and> Q' \<in> quorums p' \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

definition blocked where
  "blocked R p \<equiv> \<forall> Q \<in> quorums p . Q \<inter> R \<noteq> {}"

lemma "\<And> q . blocked {p . blocked R p} q \<Longrightarrow> blocked R q"
  using p2 p1 unfolding blocked_def by fastforce

lemma quorum_not_empty:
  assumes "q \<in> quorums n"
  shows "q \<noteq> {}"
  by (metis assms empty_iff personal_axioms personal_def)

lemma intact_union:
  assumes "is_intact I\<^sub>1" and "is_intact I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_intact (I\<^sub>1\<union> I\<^sub>2)"
proof -
  have "I\<^sub>1 \<union> I\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_intact_def by auto 
  moreover
  have "\<exists> Q \<in> quorums p . Q \<subseteq> I\<^sub>1 \<union> I\<^sub>2" if "p \<in> I\<^sub>1 \<union> I\<^sub>2" for p 
    using \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> that unfolding is_intact_def
    by (meson Un_iff le_supI1 sup.coboundedI2) 
  moreover 
  have "W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" 
    if "n\<^sub>1 \<in> I\<^sub>1 \<union> I\<^sub>2" and "q\<^sub>1 \<in> quorums n\<^sub>1 " and "n\<^sub>2 \<in> I\<^sub>1 \<union> I\<^sub>2" and "q\<^sub>2 \<in> quorums n\<^sub>2 " for q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2
  proof -
    have \<open>W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> 
      if "n\<^sub>1 \<in> I" and "n\<^sub>2 \<in> I" and "I = I\<^sub>1 \<or> I = I\<^sub>2" for I
      using \<open>q\<^sub>1 \<in> quorums n\<^sub>1 \<close> \<open>q\<^sub>2 \<in> quorums n\<^sub>2\<close> assms(1,2) that unfolding is_intact_def
      by (metis Int_commute inf_left_commute) 
    moreover
    have \<open>W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}\<close> 
      if "n\<^sub>1 \<in> I\<^sub>1" and "n\<^sub>2 \<in> I\<^sub>2" and "is_intact I\<^sub>1" and "is_intact I\<^sub>2" 
        and "q\<^sub>2 \<in> quorums n\<^sub>2 " and "q\<^sub>1 \<in> quorums n\<^sub>1" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
      for q\<^sub>1 q\<^sub>2 n\<^sub>1 n\<^sub>2 I\<^sub>1 I\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      obtain n\<^sub>3 where "n\<^sub>3 \<in> I\<^sub>1 \<inter> I\<^sub>2" using \<open>I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}\<close> by blast
      obtain q\<^sub>3 where "q\<^sub>3 \<in> quorums n\<^sub>3" and "q\<^sub>3 \<subseteq> I\<^sub>1"
        using \<open>is_intact I\<^sub>1\<close> \<open>n\<^sub>3 \<in> I\<^sub>1 \<inter> I\<^sub>2\<close> is_intact_def by fastforce 
      moreover
      have "q\<^sub>3 \<inter> q\<^sub>2 \<noteq> {}"
        by (metis IntD2 Int_assoc Int_empty_right \<open>n\<^sub>3 \<in> I\<^sub>1 \<inter> I\<^sub>2\<close> calculation(1) is_intact_def that(2) that(4) that(5)) 
      ultimately 
      obtain n\<^sub>4 where "n\<^sub>4 \<in> I\<^sub>1" and "q\<^sub>2 \<in> quorums n\<^sub>4"
        by (meson Int_emptyI \<open>q\<^sub>2 \<in> quorums n\<^sub>2\<close> personal_axioms personal_def subset_iff) 
      thus "W \<inter> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" using \<open>is_intact I\<^sub>1\<close> \<open>q\<^sub>1 \<in> quorums n\<^sub>1\<close> \<open>n\<^sub>1 \<in> I\<^sub>1\<close> 
        unfolding is_intact_def by blast 
    qed
    ultimately show ?thesis using that assms by fast
  qed
  ultimately show ?thesis unfolding is_intact_def by fastforce
qed

end

section slices

locale slices =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
  (* assumes "\<And> n . slices n \<noteq> {}" *)
    \<^cancel>\<open>"\<And> n . slices n \<noteq> {} \<and> (\<forall> S \<in> slices n . n \<notin> S)"\<close>
    \<^cancel>\<open>and "\<And> p S S' . \<not>(S \<in> slices p \<and> S' \<in> slices p \<and> S \<subset> S')" 
    \<comment> \<open>The last assumption makes sense if one thinks of slices in terms of trust.\<close>\<close>
begin

definition quorum where 
  "quorum q \<equiv> \<forall> n \<in> q . \<exists> S \<in> slices n . S \<subseteq> q"

definition quorum_of where
  "quorum_of n q \<equiv> n \<in> q \<and> quorum q"

lemma quorums_closed:
  assumes "quorum_of n q" and "n' \<in> q"
  shows "quorum_of n' q"
  using assms unfolding quorum_of_def by auto

lemma quorum_union:
  assumes "quorum q\<^sub>1" and "quorum q\<^sub>2"
  shows "quorum (q\<^sub>1 \<union> q\<^sub>2)" using assms unfolding quorum_def
  by (meson UnE le_supI1 sup.coboundedI2 sup_eq_bot_iff) 

(* lemma quorum_univ:"quorum UNIV" unfolding quorum_def
  by (metis all_not_in_conv  slices_def top_greatest) *)

definition quorum_blocking where
  "quorum_blocking B p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> B \<noteq> {}"

inductive blocking where
  "p \<in> R \<Longrightarrow> blocking R p"
| "\<forall> Sl \<in> slices p . \<exists> q \<in> Sl . blocking R q \<Longrightarrow> blocking R p"

lemma not_blocking:"\<not>blocking R p \<Longrightarrow> p \<notin> R \<and> (\<exists> Sl \<in> slices p . \<forall> q \<in> Sl . \<not> blocking R q)"
  by (meson blocking.simps)

inductive not_blocked for p R where
  "\<lbrakk>p \<notin> R; Sl \<in> slices p; \<forall> q \<in> Sl . \<not> blocking R q\<rbrakk> \<Longrightarrow> not_blocked p R p"
| "\<lbrakk>not_blocked p R p'; Sl \<in> slices p'; \<forall> q \<in> Sl . \<not> blocking R q; p'' \<in> Sl\<rbrakk> \<Longrightarrow> not_blocked p R p''"

lemma ne_not_blocked_is_quorum:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  assumes "Q \<noteq> {}"
  shows "quorum Q"
proof -
  have "\<forall> n\<in>Q . \<exists> S\<in>slices n . S\<subseteq>Q"
  proof (simp add: Q_def; clarify)
    fix n
    assume "not_blocked p R n"
    thus "\<exists>S\<in>slices n. S \<subseteq> Collect (not_blocked p R)"
    proof (cases)
      case (1 Sl)
      then show ?thesis
        by (metis (full_types) Ball_Collect not_blocked.intros)
    next
      case (2 p' Sl)
      hence "\<not>blocking R n" by simp
      with this obtain Sl where "n \<notin> R" and "Sl \<in> slices n" and "\<forall> q \<in> Sl . \<not> blocking R q"
        by (meson blocking.intros(2) blocking.intros(1))
      moreover note \<open>not_blocked p R n\<close>
      ultimately show ?thesis by (metis (full_types) Ball_Collect not_blocked.intros(2))
    qed
  qed
  thus ?thesis
    by (simp add: assms(2) quorum_def) 
qed

lemma not_blocked_disjoint_R:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
  shows "Q \<inter> R = {}"
proof -
  have "q \<notin> R" if "not_blocked p R q" for q
    using that
  proof (induct)
    case (1 Sl)
    then show ?case by auto
  next
    case (2 p' Sl p'')
    then show ?case using blocking.intros(1) by blast 
  qed
  thus ?thesis unfolding Q_def by auto
qed

lemma quorum_blocking_blocking:
  assumes "quorum_blocking R p" shows "blocking R p"
proof -
  have "\<not>quorum_blocking R p" if "\<not>blocking R p"
    \<comment> \<open>this is the contrapositive\<close>
  proof -
    define Q where "Q \<equiv> {q . not_blocked p R q}"
    have "p \<in> Q" using \<open>\<not>blocking R p\<close>
      by (metis Q_def mem_Collect_eq not_blocked.intros(1) not_blocking)
    moreover
    have "quorum Q"
      using Q_def \<open>p \<in> Q\<close> ne_not_blocked_is_quorum by auto
    moreover
    have "Q \<inter> R = {}"
      by (simp add: Q_def not_blocked_disjoint_R) 
    ultimately show ?thesis unfolding quorum_blocking_def quorum_of_def by blast
  qed
  thus ?thesis using assms by auto
qed

lemma quorum_is_quorum_of_some_slice:
  assumes "quorum_of p Q" 
  obtains S where "S \<in> slices p" and "S \<subseteq> Q"
    and "\<And> p' . p' \<in> S \<Longrightarrow> quorum_of p' Q"
  using assms unfolding quorum_of_def quorum_def
  by (meson rev_subsetD)

lemma blocking_imp_quorum_blocking:
  assumes "blocking R p" shows "quorum_blocking R p"
  using assms
proof (induct)
case (1 p R)
  then show ?case
    using quorum_blocking_def quorum_of_def by auto 
next
  case (2 p R)
  then show ?case unfolding quorum_blocking_def
    by (meson quorum_is_quorum_of_some_slice)
qed

subsection "old stuff"

definition slice_blocking where
  "slice_blocking B p \<equiv> p \<in> B \<or> (\<forall> S \<in> slices p . S \<inter> B \<noteq> {})"

lemma cascade: \<comment> \<open>What is this?\<close>
  assumes "p \<notin> B" and "quorum_blocking B p"
  shows "\<exists> p' \<in> -B . slice_blocking B p'" 
proof (rule ccontr; auto) 
  assume "\<forall> p' \<in> -B . \<not>slice_blocking B p'"
  hence "quorum (-B)" 
    unfolding quorum_blocking_def slice_blocking_def quorum_def quorum_of_def
    using \<open>p \<notin> B\<close> disjoint_eq_subset_Compl by fastforce
  with \<open>p \<notin> B\<close> and \<open>quorum_blocking B p\<close> show False
    using quorum_blocking_def quorum_of_def by auto 
qed

lemma l:"\<lbrakk>\<not>blocking R p; not_blocked p R p'\<rbrakk> \<Longrightarrow> \<not>blocking R p'" 
  using not_blocked.cases by blast

end

section "projection"

locale projection = slices + 
  fixes W :: "'a set"
begin

definition proj_slices where
  \<comment> \<open>slices projected on the well-behaved participants\<close>
  "proj_slices p \<equiv> {S \<inter> W | S . S \<in> slices p}"

text \<open>Now we instantiate the slices locale using the projected slices\<close>

interpretation proj: slices proj_slices .

lemma quorum_is_proj_quorum:
  assumes "quorum q" shows "proj.quorum q"
  unfolding proj.quorum_def
proof -
  have "\<exists>S\<in>proj_slices n. S \<subseteq> q" if "n \<in> q" for n
  proof -
    have "\<exists>S\<in>slices n. S \<subseteq> q" if "n \<in> q" for n using assms that unfolding quorum_def by auto
    moreover
    have "\<exists> S'\<in> proj_slices n . S' \<subseteq> S" if "S\<in>slices n" for S unfolding proj_slices_def
      using that by auto
    ultimately show ?thesis
      by (meson order.trans that) 
  qed
  thus "\<forall>n\<in>q. \<exists>S\<in>proj_slices n. S \<subseteq> q"
    by blast
qed

lemma proj_blocking_is_blocking:
  assumes "proj.quorum_blocking B p"
  shows "quorum_blocking B p"
  by (meson assms quorum_is_proj_quorum slices.quorum_blocking_def slices.quorum_of_def) 

lemma proj_blocking_is_blocking:
  assumes "quorum_blocking B p" and "B \<inter> W \<noteq> {}" and "p \<in> W"
  shows "proj.quorum_blocking B p" nitpick[card 'a=3] oops

lemma W_slice_blocking_is_proj_slice_blocking:
  "slice_blocking (U \<inter> W) n = proj.slice_blocking (U \<inter> W) n"
  unfolding proj.slice_blocking_def  proj_slices_def slice_blocking_def by auto

definition proj_of where
  "proj_of q \<equiv> {p \<in> q \<inter> W . \<exists> S \<in> slices p . S \<inter> W \<subseteq> q}"

lemma proj_is_intersection: 
  assumes "quorum q"  shows "proj_of q = q \<inter> W"
  using assms unfolding quorum_def proj_of_def apply auto
  using inf.absorb_iff2 by fastforce

lemma l3: \<comment> \<open>needed?\<close>
  assumes  "S \<subseteq> Q \<inter> W" and "quorum Q"
  shows "S \<subseteq> proj_of Q"
  using assms unfolding quorum_def proj_of_def
  using Ball_Collect subset_eq by fastforce 

lemma proj_of_is_proj_quorum:
  assumes "quorum q" shows "proj.quorum (proj_of q)"
  using assms unfolding proj.quorum_def quorum_def proj_slices_def 
  by (simp add: proj_is_intersection[OF assms(1)]; meson Int_commute Int_iff inf_le1 inf_le2 subset_trans) 

lemma quorum_in_W_is_proj_of:
  assumes "quorum q" and "q \<subseteq> W" shows "proj_of q = q"
  using assms unfolding quorum_def  proj_of_def 
  by (auto; metis inf_absorb1 order.trans)

section "pseudo-quorums"

definition pseudo_quorum where
  "pseudo_quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . \<exists> Sl \<in> slices p . Sl \<subseteq> Q"

inductive reachable_in_W for p Q where
  "p \<in> Q \<inter> W \<Longrightarrow> reachable_in_W p Q p"
| "\<lbrakk>reachable_in_W p Q p'; S \<in> slices p'; S \<subseteq> Q; p'' \<in> S \<inter> W\<rbrakk> \<Longrightarrow> reachable_in_W p Q p''"

lemma p_in_reachable_from_p:
  fixes p Q
  defines "Q' \<equiv> {p' . reachable_in_W p Q p'}"
  assumes "p \<in> Q \<inter> W"
  shows "p \<in> Q'"
  using Q'_def assms(2) reachable_in_W.intros(1) by auto

lemma reachable_from_p_subset_W:
  fixes p Q
  defines "Q' \<equiv> {p' . reachable_in_W p Q p'}"
  assumes "p \<in> W"
  shows "Q' \<subseteq> Q \<inter> W"  unfolding Q'_def
proof (clarify)
  fix p'
  assume "reachable_in_W p Q p'"
  thus "p' \<in> Q \<inter> W" by (induct; auto)
qed

lemma pseudo_quorum_contains_proj_quorum:
  fixes p Q
  defines "Q' \<equiv> {p' . reachable_in_W p Q p'}"
  assumes "pseudo_quorum Q" and "p \<in> Q \<inter> W" 
  shows "proj.quorum Q'" 
  unfolding proj.quorum_def 
proof -
  show "\<forall>n\<in>Q'. \<exists>S\<in>proj_slices n. S \<subseteq> Q'"
    unfolding Q'_def
  proof (simp;clarify)
    fix n
    assume "reachable_in_W p Q n"
    thus "\<exists>S\<in>proj_slices n. S \<subseteq> Collect (reachable_in_W p Q)"
    proof (cases)
      case 1
      with \<open>pseudo_quorum Q\<close> obtain S where "S \<in> slices n" and "S \<subseteq> Q"
        by (meson assms(3) pseudo_quorum_def) 
      hence "reachable_in_W p Q p'" if "p' \<in> S \<inter> W" for p'
        by (meson \<open>reachable_in_W p Q n\<close> that reachable_in_W.intros(2))
      thus ?thesis unfolding proj_slices_def using \<open>S \<in> slices n\<close> by auto
    next
      case (2 p' S)
      obtain S' where "S' \<in> slices n" and "S' \<subseteq> Q"
        by (meson "2"(3) "2"(4) Int_iff assms(2) pseudo_quorum_def subset_iff)
      hence "reachable_in_W p Q p'" if "p' \<in> S' \<inter> W" for p'
        using \<open>reachable_in_W p Q n\<close> reachable_in_W.simps that by blast
      thus ?thesis unfolding proj_slices_def using \<open>S' \<in> slices n\<close> by auto
    qed
  qed
qed

definition intertwined where 
  "intertwined S \<equiv> \<forall> n \<in> S . \<forall> n' \<in> S . \<forall> q q' . 
    proj.quorum_of n q \<and> proj.quorum_of n' q' \<longrightarrow> q \<inter> q' \<inter> W \<noteq> {}"

lemma pseudo_quorum_intersection:
  assumes "intertwined S" and "S \<subseteq> W" and "pseudo_quorum Q" and "pseudo_quorum Q'" and "p \<in> S\<inter>Q" and "p' \<in> S\<inter>Q'" 
  shows "Q \<inter> Q' \<inter> W \<noteq> {}"
proof -
  have "p \<in> Q \<inter> W" and "p' \<in> Q' \<inter> W"
    using IntD2 IntI assms(2,5,6) by auto
  with this obtain Q_proj and Q'_proj where "proj.quorum Q_proj" and "Q_proj \<subseteq> Q \<inter> W" and "p \<in> Q_proj"
    and "proj.quorum Q'_proj" and "Q'_proj \<subseteq> Q' \<inter> W" and "p' \<in> Q'_proj"
    using pseudo_quorum_contains_proj_quorum p_in_reachable_from_p reachable_from_p_subset_W \<open>pseudo_quorum Q\<close> \<open>pseudo_quorum Q'\<close>
    by (auto; metis)
  have "Q_proj \<inter> Q'_proj \<inter> W \<noteq> {}" using \<open>intertwined S\<close> unfolding intertwined_def
    using \<open>p \<in> Q_proj\<close> \<open>p' \<in> Q'_proj\<close> \<open>proj.quorum Q'_proj\<close> \<open>proj.quorum Q_proj\<close> assms(5) assms(6) proj.quorum_of_def by auto
  show ?thesis
    using Int_assoc \<open>Q'_proj \<subseteq> Q' \<inter> W\<close> \<open>Q_proj \<inter> Q'_proj \<inter> W \<noteq> {}\<close> \<open>Q_proj \<subseteq> Q \<inter> W\<close> by auto  
qed

definition pseudo_blocked where
  "pseudo_blocked R p \<equiv> \<forall> Q . pseudo_quorum Q \<and> p \<in> Q \<longrightarrow> Q \<inter> R \<noteq> {}"

lemma pseudo_proj_is_intersection: 
  assumes "pseudo_quorum q"  shows "proj_of q = q \<inter> W" nitpick[card 'a=4]
  using assms unfolding pseudo_quorum_def proj_of_def apply auto
  using inf.absorb_iff2 by fastforce

lemma proj_of_pseudo_is_proj_quorum:
  assumes "pseudo_quorum q" shows "proj.quorum (proj_of q)"
  using assms unfolding proj.quorum_def pseudo_quorum_def proj_slices_def 
  apply (simp add: pseudo_proj_is_intersection[OF assms(1)])
  by (meson Int_commute inf_le1 inf_le2 order_trans) 

lemma l3': \<comment> \<open>needed?\<close>
  assumes  "S \<subseteq> Q \<inter> W" and "pseudo_quorum Q"
  shows "S \<subseteq> proj_of Q"
  using assms unfolding pseudo_quorum_def proj_of_def
  using contra_subsetD by fastforce

end

section "The intact set"

locale well_behaved = projection
  \<comment> \<open>Now @{term W} is the set of well-behaved participants\<close>
begin

interpretation proj: slices proj_slices .

definition is_intact where
  "is_intact I \<equiv> I \<subseteq> W \<and> quorum I \<and> (\<forall> q\<^sub>1 q\<^sub>2 . 
    q\<^sub>1 \<inter> I \<noteq> {} \<and> q\<^sub>2 \<inter> I \<noteq> {} \<and> proj.quorum q\<^sub>1 \<and> proj.quorum q\<^sub>2 \<longrightarrow> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {})"

\<^cancel>\<open>
lemma
  assumes "quorum_blocking B p" and "p \<in> I" and "is_intact I"
  shows "proj.quorum_blocking B p" nitpick[card 'a=3] oops
\<close>

subsection "The properties needed for consensus"

text "Note @{thm pseudo_quorum_intersection}}"

lemma l1:
  assumes "pseudo_blocked B p" and "p \<in> I" and "is_intact I"
  shows "B \<inter> I \<noteq> {}" 
proof -
  obtain Q where "quorum_of p Q" and "Q \<subseteq> I"
    using assms(2,3) is_intact_def quorum_of_def by auto 
  moreover
  have "pseudo_quorum Q"
    using \<open>quorum_of p Q\<close> pseudo_quorum_def quorum_def quorum_of_def by auto 
  with \<open>pseudo_blocked B p\<close> show ?thesis unfolding pseudo_blocked_def
    using calculation(1) calculation(2) slices.quorum_of_def by fastforce
qed

lemma l2:
  assumes "p \<in> I" and "is_intact I" and "pseudo_quorum Q" and "p' \<in> Q \<inter> I"
  shows "quorum_blocking (proj_of Q) p"
proof -
  have "proj.quorum (proj_of Q)"
    by (simp add: assms(3) proj_of_pseudo_is_proj_quorum) 
  moreover 
  have "proj_of Q \<inter> I \<noteq> {}"
    using assms(2-4) inf_assoc is_intact_def pseudo_proj_is_intersection by auto  
  ultimately 
  show ?thesis using \<open>p\<in>I\<close>  \<open>is_intact I\<close> unfolding is_intact_def
    by (metis IntI emptyE proj.quorum_blocking_def proj.quorum_of_def proj_blocking_is_blocking) 
qed

subsection "union of intact is intact"

interpretation perso:personal "\<lambda> p . {q . p \<in> q \<and> proj.quorum q}" W
proof standard
  fix Q p
  assume "Q \<in> {q. p \<in> q \<and> proj.quorum q}"
  thus "p \<in> Q" by auto
next
  fix p p' Q
  assume "Q \<in> {q. p \<in> q \<and> proj.quorum q}" and "p'\<in> Q"
  thus "Q \<in> {q. p' \<in> q \<and> proj.quorum q}"
    using proj.quorums_closed by fastforce
qed

lemma perso_intact_quorum_is_intact:
  assumes "quorum I" and "perso.is_intact I" shows "is_intact I"
  using assms unfolding is_intact_def perso.is_intact_def
  by blast

lemma proj_quorum_in_W:
  assumes "proj.quorum Q" and "Q \<inter> I \<noteq> {}" and "I \<subseteq> W"
  obtains Q\<^sub>w where "Q\<^sub>w \<subseteq> W" and "Q\<^sub>w \<subseteq> Q" and "proj.quorum Q\<^sub>w" and "Q\<^sub>w \<inter> I \<noteq> {}"
proof -
  have "proj.quorum (Q \<inter> W)" using assms unfolding proj.quorum_def proj_slices_def 
    by(auto; (metis inf_le2))
  thus ?thesis
  proof -
    have "I = I \<inter> W"
      by (meson assms(3) inf.orderE)
    then show ?thesis
      by (metis (no_types) Int_lower1 Int_lower2 \<open>proj.quorum (Q \<inter> W)\<close> assms(2) inf.orderE inf_left_commute that)
  qed 
qed

lemma stellar_intact_imp_perso_proj_intact:
  assumes "is_intact I" shows "perso.is_intact I"
  unfolding perso.is_intact_def
proof (intro conjI)
  show "I \<subseteq> W" using \<open>is_intact I\<close> by (simp add: is_intact_def) 
next
  show "\<forall>p\<in>I. \<exists>Q\<in>{q. p \<in> q \<and> proj.quorum q}. Q \<subseteq> I"
    using \<open>is_intact I\<close> using quorum_is_proj_quorum unfolding is_intact_def by auto 
next
  show "\<forall>p p' Q Q'.
       p \<in> I \<and> p' \<in> I \<and> Q \<in> {q. p \<in> q \<and> proj.quorum q} \<and> Q' \<in> {q. p' \<in> q \<and> proj.quorum q} \<longrightarrow>
       W \<inter> Q \<inter> Q' \<noteq> {}"
  proof -  
    have "W \<inter> Q \<inter> Q' \<noteq> {}"
      if "p \<in> I" and "p' \<in> I" and "p \<in> Q" and "p' \<in> Q'" and "proj.quorum Q" and "proj.quorum Q'"
      for p p' Q Q'
    proof -
      have "I \<subseteq> W"
        using assms is_intact_def by blast 
      have "Q \<inter> I \<noteq> {}" and "Q' \<inter> I \<noteq> {}"
        using that(1-4) by blast+
      obtain Q\<^sub>w and Q\<^sub>w' where "Q\<^sub>w \<inter> I \<noteq> {}" and "proj.quorum Q\<^sub>w" and "Q\<^sub>w \<subseteq> Q" and "Q\<^sub>w \<subseteq> W"
        and "Q\<^sub>w' \<inter> I \<noteq> {}" and "proj.quorum Q\<^sub>w'" and "Q\<^sub>w' \<subseteq> Q'"  and "Q\<^sub>w' \<subseteq> W"
        using proj_quorum_in_W
        by (metis \<open>I \<subseteq> W\<close> \<open>Q \<inter> I \<noteq> {}\<close> \<open>Q' \<inter> I \<noteq> {}\<close> \<open>proj.quorum Q'\<close> \<open>proj.quorum Q\<close>)
      have "Q\<^sub>w \<inter> Q\<^sub>w' \<noteq> {}" using \<open>is_intact I\<close> \<open>Q\<^sub>w \<inter> I \<noteq> {}\<close> \<open>Q\<^sub>w' \<inter> I \<noteq> {}\<close> \<open>proj.quorum Q\<^sub>w'\<close> \<open>proj.quorum Q\<^sub>w\<close>  
        unfolding is_intact_def by blast
      thus ?thesis
        using \<open>Q\<^sub>w \<subseteq> Q\<close> \<open>Q\<^sub>w' \<subseteq> Q'\<close> \<open>Q\<^sub>w' \<subseteq> W\<close> by auto
    qed
    thus ?thesis by blast 
  qed
qed

lemma intact_union:
  \<comment> \<open>Here we appeal to the union property proved in the personal model\<close>
  assumes  "is_intact I\<^sub>1" and "is_intact I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_intact (I\<^sub>1 \<union> I\<^sub>2)" 
  using perso.intact_union assms is_intact_def perso_intact_quorum_is_intact quorum_union stellar_intact_imp_perso_proj_intact
  by meson

end

subsection "with quorum intersection"

locale quorum_intersection = well_behaved  +
   assumes quorum_intersection:
    "\<And> q\<^sub>1 q\<^sub>2 . \<lbrakk>quorum q\<^sub>1; quorum q\<^sub>2\<rbrakk> \<Longrightarrow> q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}" 
begin
text "TODO: Anything to prove here?"
end

section "elementary quorums"

locale elementary = slices
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
      thus ?thesis by (metis quorum_def)
    qed 
    moreover have "x \<subset> s"
      using \<open>n\<^sub>2 \<notin> x\<close> assms(3) x_def by blast
    ultimately have False using \<open>elementary s\<close>
      using elementary_def by auto
  }
  thus ?P by blast  
qed

end

\<^cancel>\<open>
section "Personal elementary"

text "this has no use so far"

locale personal_elementary = slices
begin

definition elementary where
  "elementary p Q \<equiv> quorum_of p Q \<and> (\<forall> Q' . \<not>(quorum_of p Q' \<and> Q' \<subset> Q))"

lemma "elementary p Q \<Longrightarrow> \<exists>! S \<in> slices p . S \<subseteq> Q" nitpick[verbose, card 'a=3]
  oops

lemma assumes "elementary p Q"
  obtains S f where "S \<in> slices p" and "Q = insert p (\<Union>q\<in>S . f q)"
  and "\<And> q . q \<in> S \<Longrightarrow> quorum_of q (f q)" 
  oops

end
\<close>

end