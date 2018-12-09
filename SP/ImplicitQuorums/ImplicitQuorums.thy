theory ImplicitQuorums
  imports Main 
begin

section "quorums"

locale quorums =
  fixes quorum :: "'node set \<Rightarrow> bool" 
    assumes quorum_union:"\<And> Q Q'  . \<lbrakk>quorum Q; quorum Q'\<rbrakk> \<Longrightarrow> quorum (Q \<union> Q')"
begin

abbreviation quorum_of where 
  "quorum_of p Q \<equiv> quorum Q \<and> p \<in> Q"

definition blocks where
  "blocks R p \<equiv> \<forall> Q . quorum_of p Q \<longrightarrow> Q \<inter> R \<noteq> {}"

abbreviation blocked where "blocked R \<equiv> {p . blocks R p}"

lemma blocked_blocked_eq_blocked:
  "blocks (blocked R) q = blocks R q" 
  unfolding blocks_def by fastforce

lemma l1:
  assumes "finite S" and "S \<noteq> {}" and "\<And> p . p \<in> S \<Longrightarrow> \<exists> Q . quorum_of p Q \<and> Q \<subseteq> S"
  shows "quorum S" 
    \<comment> \<open>This is trivial by the quorum union property but seems clumsy to prove in Isabelle/HOL\<close>
proof -
  obtain f where "quorum_of p (f p)" and "f p \<subseteq> S" if "p \<in> S" for p using assms(3) by (auto; metis)
  have "\<Union> {f p | p . p \<in> S} = S"
  proof -
    have "\<forall> p \<in> S . p \<in> f p \<and> f p \<subseteq> S"
      by (simp add: \<open>\<And>p. p \<in> S \<Longrightarrow> f p \<subseteq> S\<close> \<open>\<And>p. p \<in> S \<Longrightarrow> quorum_of p (f p)\<close>)  
    thus "\<Union> {f p | p . p \<in> S} = S" by auto
  qed
  moreover
  have "quorum (\<Union> {f p | p . p \<in> S})"
  proof -
    have "wf {(X, Y). X \<subset> Y \<and> finite Y}" by (metis finite_psubset_def wf_finite_psubset)
      \<comment> \<open>We are going to use well-founded induction\<close>
    moreover
    have "\<forall> p \<in> S . p \<in> f p \<and> quorum (f p)"
      by (simp add: \<open>\<And>p. p \<in> S \<Longrightarrow> f p \<subseteq> S\<close> \<open>\<And>p. p \<in> S \<Longrightarrow> quorum_of p (f p)\<close>) 
    moreover note \<open>S \<noteq> {}\<close> and \<open>finite S\<close>
    ultimately 
    show "quorum (\<Union> {f p | p . p \<in> S})" 
    proof (induct S rule:wf_induct_rule) 
      \<comment> \<open>Is this also called Noetherian induction?\<close>
      case (less S) 
      obtain S' x where "S = insert x S'" and "S' \<noteq> S" using \<open>S \<noteq> {}\<close> \<open>finite S\<close>
        by (metis finite.cases insertI1 mk_disjoint_insert)
      have "S' \<subset> S" using \<open>S = insert x S'\<close> \<open>S' \<noteq> S\<close> by auto
      moreover have "\<forall> p \<in> S' . p \<in> f p \<and> quorum (f p)"
        by (simp add: \<open>\<forall> p \<in> S . p \<in> f p \<and> quorum (f p)\<close> \<open>S = insert x S'\<close>) 
      moreover have "finite S'"
        using \<open>finite S\<close> \<open>S = insert x S'\<close> by auto 
      moreover note \<open>finite S\<close> less.hyps
      ultimately have "quorum (\<Union>{f p | p . p \<in> S'})" if "S' \<noteq> {}" using that by auto
      moreover have "{f p | p . p \<in> S} = insert (f x) {f p | p . p \<in> S'}" 
        using \<open>S = insert x S'\<close> by auto
      moreover have "quorum (f x)"
        by (simp add: \<open>\<forall> p \<in> S . p \<in> f p \<and> quorum (f p)\<close> \<open>S = insert x S'\<close>)
      ultimately show ?case using quorum_union 
        by (cases "S' = {}", auto)
    qed
  qed
  ultimately show ?thesis by simp 
qed

end

subsection "Intact sets"

locale wb = quorums quorum for quorum :: "'node set \<Rightarrow> bool"  +
  fixes W::"'node set"
begin

abbreviation B where "B \<equiv> -W"

definition is_intact where 
  "is_intact I \<equiv> I \<subseteq> W \<and> quorum I
      \<and> (\<forall> Q Q' . quorum Q \<and> quorum Q' \<and> Q \<inter> I \<noteq> {} \<and> Q' \<inter> I \<noteq> {} \<longrightarrow> W \<inter> Q \<inter> Q' \<noteq> {})"

lemma intact_union:
  assumes "is_intact I\<^sub>1" and "is_intact I\<^sub>2" and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}"
  shows "is_intact (I\<^sub>1\<union> I\<^sub>2)"
proof -
  have "I\<^sub>1 \<union> I\<^sub>2 \<subseteq> W"
    using assms(1) assms(2) is_intact_def by auto 
  moreover
  have "quorum (I\<^sub>1\<union>I\<^sub>2)" 
    using \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> unfolding is_intact_def using quorum_union by auto
  moreover 
  have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" 
    if "quorum Q\<^sub>1" and "quorum Q\<^sub>2" and "Q\<^sub>1 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" and "Q\<^sub>2 \<inter> (I\<^sub>1\<union>I\<^sub>2) \<noteq> {}" 
    for Q\<^sub>1 Q\<^sub>2
  proof -
    have "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" if "Q\<^sub>1 \<inter> I \<noteq> {}" and "Q\<^sub>2 \<inter> I \<noteq> {}" and "I = I\<^sub>1 \<or> I = I\<^sub>2" for I
      using \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> \<open>quorum Q\<^sub>1\<close> \<open>quorum Q\<^sub>2\<close>
      by (metis \<open>is_intact I\<^sub>1\<close> \<open>is_intact I\<^sub>2\<close> is_intact_def that)
    moreover
    have \<open>W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}\<close>  if "is_intact I\<^sub>1" and "is_intact I\<^sub>2"
      and "I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}" and "Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}" and "Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}"
    for I\<^sub>1 I\<^sub>2 \<comment> \<open>We generalize to avoid repeating the argument twice\<close>
    proof -
      note \<open>I\<^sub>1 \<inter> I\<^sub>2 \<noteq> {}\<close>
      moreover have "quorum I\<^sub>2" using \<open>is_intact I\<^sub>2\<close> unfolding is_intact_def by auto
      ultimately have "I\<^sub>2 \<inter> Q\<^sub>1 \<noteq> {}" using \<open>is_intact I\<^sub>1\<close>  \<open>quorum Q\<^sub>1\<close> \<open>Q\<^sub>1 \<inter> I\<^sub>1 \<noteq> {}\<close> 
        unfolding is_intact_def using inf_sup_aci(1) by blast 
      thus "W \<inter> Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> {}" using \<open>is_intact I\<^sub>2\<close> \<open>quorum Q\<^sub>2\<close> \<open>quorum Q\<^sub>1\<close> \<open>Q\<^sub>2 \<inter> I\<^sub>2 \<noteq> {}\<close>
        unfolding is_intact_def by blast
    qed
    ultimately show ?thesis using assms that by auto
  qed
  ultimately show ?thesis using assms
    unfolding is_intact_def by simp
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
    moreover have "Q \<inter> (-L) \<noteq> {}" 
      using that \<open>quorum_of p Q\<close> by simp
    ultimately show False unfolding L_def blocks_def by auto
  qed
  thus ?thesis
    by fastforce 
qed

lemma l4:
  assumes "L \<noteq> {}" and "finite L" 
  shows "quorum L" using l1 l3 assms by metis

lemma l5:  "quorum L' \<Longrightarrow> L' \<subseteq> W \<Longrightarrow> L' \<subseteq> L"
   unfolding L_def blocks_def by auto

lemma l6: "is_intact I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> I \<subseteq> L"
  by (simp add: is_intact_def l5)

end

section "Stellar quorums"

locale stellar =
  fixes slices :: "'node \<Rightarrow> 'node set set" \<comment> \<open>the quorum slices\<close>
    and W :: "'node set" \<comment> \<open>The well-behaved nodes\<close>
begin

definition quorum where
  "quorum Q \<equiv> \<forall> p \<in> Q \<inter> W . \<exists> Sl \<in> slices p . Sl \<subseteq> Q"

lemma quorum_union:"quorum Q \<Longrightarrow> quorum Q' \<Longrightarrow> quorum (Q \<union> Q')"
  unfolding quorum_def
  by (metis IntE Int_iff UnE inf_sup_aci(1) sup.coboundedI1 sup.coboundedI2)

interpretation wb quorum W using quorum_union unfolding wb_def quorums_def by auto

lemma quorum_is_quorum_of_some_slice:
  assumes "quorum_of p Q" and "p \<in> W"
  obtains S where "S \<in> slices p" and "S \<subseteq> Q"
    and "\<And> p' . p' \<in> S \<inter> W \<Longrightarrow> quorum_of p' Q"
  using assms unfolding quorum_def by (metis IntD1 Int_iff subsetCE)

subsection "Inductive definition of blocked"

inductive blocking where
  "p \<in> R  \<Longrightarrow> blocking R p"
| "\<forall> Sl \<in> slices p . \<exists> q \<in> Sl . blocking R q \<Longrightarrow> blocking R p"

\<^cancel>\<open>
inductive blocking2 where
  "p \<in> R\<union>B  \<Longrightarrow> blocking2 R p"
| "\<forall> Sl \<in> slices p . \<exists> q \<in> Sl . blocking2 R q \<Longrightarrow> blocking2 R p"

lemma "p \<in> W \<Longrightarrow> R \<noteq> {} \<Longrightarrow> p \<notin> R \<Longrightarrow> blocking2 R p \<Longrightarrow> blocks R p" nitpick[card 'node=5, verbose, iter stellar.blocking2=5]
\<close>

subsubsection \<open>Properties of @{term blocking}\<close>

text \<open>Here we show two main lemmas:
  \<^item> if @{term \<open>R \<union> B\<close>} blocks @{term \<open>p \<in> Intact\<close>}, then @{term \<open>R \<inter> Intact \<noteq> {}\<close>}
  \<^item> if @{term \<open>p \<in> Intact\<close>} and quorum @{term Q} is such that @{term \<open>Q \<inter> Intact \<noteq> {}\<close>}, 
    then @{term \<open>Q \<inter> W\<close>} is blocking @{term p}
\<close>

lemma l7:
  assumes  "blocking (R \<union> B) p" and "p \<in> W" 
  shows "blocks (R \<union> B) p"
  using assms thm blocking.induct
proof (induct "R \<union> B" p rule:blocking.induct)
  case (1 p)
  then show ?case
    using blocks_def by auto 
next
  case (2 p)
  then show ?case unfolding blocks_def quorum_def
    by (metis Compl_partition IntE Int_Un_distrib inf_sup_absorb subsetCE subset_refl sup_assoc sup_bot.left_neutral) 
qed

lemma l8:
  assumes "is_intact I" and "p \<in> I" and "blocking (R \<union> B) p" 
  shows "R \<inter> I \<noteq> {}" 
proof -
  have "quorum I" and "I \<subseteq> W" and "I \<noteq> {}"
    using assms(1) is_intact_def using assms(2) by auto
  have "blocks (R \<union> B) p" using l7[OF \<open>blocking (R \<union> B) p\<close>] using \<open>I \<subseteq> W\<close> \<open>p \<in> I\<close> by auto
  hence "(R \<union> B) \<inter> Q \<noteq> {}" if "quorum_of p Q" for Q
    using  blocks_def that by auto
  moreover
  have "B \<inter> I = {}"
    using ComplD Int_emptyI \<open>I \<subseteq> W\<close> by auto 
  moreover 
  have "quorum_of p I" by (simp add: \<open>quorum I\<close> \<open>p \<in> I\<close>)
  ultimately
  show ?thesis
    by (metis Un_absorb assms(2) inf_sup_distrib2)
qed

inductive not_blocked for p R where
  "\<lbrakk>p \<notin> R; Sl \<in> slices p; \<forall> q \<in> Sl . \<not> blocking R q\<rbrakk> \<Longrightarrow> not_blocked p R p"
| "\<lbrakk>not_blocked p R p'; Sl \<in> slices p'; \<forall> q \<in> Sl . \<not> blocking R q; p'' \<in> Sl\<rbrakk> \<Longrightarrow> not_blocked p R p''"

lemma not_blocked_self:"not_blocked p R q \<Longrightarrow> not_blocked p R p" 
proof (induct rule:not_blocked.induct)
  case (1 Sl)
  then show ?case
    using not_blocked.intros(1) by blast 
next
  case (2 p' Sl p'')
  then show ?case
    by simp 
qed

lemma l9:
  fixes Q p R
  defines "Q \<equiv> {q . not_blocked p R q}"
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
  thus ?thesis by (simp add: quorum_def) 
qed

lemma l10:
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


lemma l11:
  assumes "p \<in> W" and "blocks R p" 
  shows "blocking R p"
proof -
  define Q where "Q \<equiv> {q . not_blocked p R q}"
  have "Q \<noteq> {}" if "\<not>blocking R p" unfolding  Q_def
    by (metis blocking.intros(2) empty_Collect_eq not_blocked.intros(1) blocking.intros(1) that)
  hence "p \<in> Q" if "\<not>blocking R p" unfolding Q_def using not_blocked_self that by blast
  moreover
  have "quorum Q" using l9 quorum_def Q_def by auto
  moreover have "Q \<inter> R = {}" by (simp add: l10  Q_def)
  ultimately have "\<not>blocks R p" if "\<not>blocking R p" using that unfolding blocks_def 
    by auto
  thus ?thesis using \<open>blocks R p\<close>
    by blast 
qed

lemma l12:
  assumes "is_intact I" and "p \<in> I" and "Q \<inter> I \<noteq> {}" and "quorum Q" 
  shows "blocking (Q \<inter> W) p" 
proof -
  have "blocks (Q \<inter> W) p" using assms unfolding blocks_def is_intact_def
    using disjoint_iff_not_equal by blast 
  moreover have "p \<in> W"
    using assms(1,2) is_intact_def by auto 
  ultimately 
  show ?thesis using l11 by auto
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
  assumes "quorum Q" and "p \<in> Q \<inter> W" and "reachable p Q p'"
  shows "p' \<in> Q"
  using assms by (metis IntE contra_subsetD reachable.cases)

lemma l14:
  assumes "quorum Q" and "p \<in> Q \<inter> W"
  shows "quorum (truncation p Q)"
proof -
  have "\<exists> S \<in> slices p' . \<forall> q \<in> S . reachable p Q q" if "reachable p Q p'" and "p' \<in> W" for p'
    by (metis IntI assms l13 quorum_def stellar.reachable.simps that)
  thus ?thesis
    by (metis IntE mem_Collect_eq stellar.quorum_def subsetI truncation_def) 
qed

lemma l15:
  assumes "is_intact I" and "quorum Q" and "quorum Q'" and "p \<in> Q \<inter> I" and "p' \<in> Q' \<inter> I" and "Q \<inter> Q' \<inter> W \<noteq> {}"
  shows "W \<inter> (truncation p Q) \<inter> (truncation p' Q') \<noteq> {}" 
proof -
  have "quorum (truncation p Q)" and "quorum (truncation p' Q')" using l14 assms is_intact_def by auto
  moreover have "truncation p Q \<inter> I \<noteq> {}" and "truncation p' Q' \<inter> I \<noteq> {}"
    by (metis IntD2 Int_Collect assms(4,5) empty_iff inf_commute reachable.intros(1) stellar.truncation_def)+
  moreover note \<open>is_intact I\<close>
  ultimately show ?thesis unfolding is_intact_def by auto
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