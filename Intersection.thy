theory Intersection
imports Main
begin

section \<open> An auxiliary fact about closure under intersection\<close>

lemma ne_family_intersection:
  fixes X::"'node::finite set set"
  assumes ne:"X \<noteq> {}" and all_ne:"\<And> x . x \<in> X \<Longrightarrow> x \<noteq> {}"
    and closed:"\<And> A B . A \<in> X \<Longrightarrow> B \<in> X \<Longrightarrow> A \<inter> B \<in> X"
  shows "\<Inter>X\<in>X"  \<comment> \<open>We assume this fact and check that it is okay with Nitpick\<close>
  sorry

end

