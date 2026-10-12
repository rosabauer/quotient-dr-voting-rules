(*  File:       Relation_Quotients_Ext.thy
    Extends:    Verified_Voting_Rule_Construction.Relation_Quotients
                (VeriVote/verifiedVotingRuleConstruction, commit 1d4225f)
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Relation Quotients: Subsets and Equivariance\<close>

theory Relation_Quotients_Ext
  imports "Verified_Voting_Rule_Construction.Relation_Quotients"
begin

lemma quotient_subset:
  fixes
    Y X :: "'x set" and
    r :: "'x rel"
  assumes subset: "Y \<subseteq> X"
  shows "Y // r \<subseteq> X // r"
  using subset
  unfolding quotient_def
  by blast

subsection \<open>Equivariance\<close>

text \<open>
  Invariance in the sense of the symmetry datatype coincides with
  congruence in the sense of the quotient  (\<open>respects\<close>).
\<close>

lemma invar_is_congruence:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r :: "'x rel"
  shows "is_symmetry f (Invariance r) = (f respects r)"
  unfolding congruent_def
  by auto

text \<open>
  Passing to the quotient preserves equivariance:
  Assume a function f is invariant under an equivalence relation r on s,
  so that it induces a well-defined function \<open>\<pi>\<^sub>\<Q> f\<close> on the quotient s // r
  (cf. \<open>pass_to_quotient\<close>). If f is also equivariant under a family of
  transformations \<phi> g with associated result transformations \<psi> g, and every
  \<phi> g maps r-classes onto r-classes, then \<open>\<pi>\<^sub>\<Q> f\<close> is equivariant on the
  quotient under the elementwise action of \<phi>, with the same \<psi>.
  This is needed to lift properties like neutrality, reversal symmetry, etc
  to quotients of election sets.
\<close>

theorem pass_to_quotient_equivar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    equiv_rel: "equiv s r" and
    invar: "f respects r" and
    equivar: "is_symmetry f (action_induced_equivariance T s \<phi> \<psi>)" and
    act_cls: "\<forall> g \<in> T. \<forall> x \<in> s. \<phi> g ` (r `` {x}) = r `` {\<phi> g x}"
  shows "is_symmetry (\<pi>\<^sub>\<Q> f)
            (action_induced_equivariance T (s // r) (set_action \<phi>) \<psi>)"
proof -
  have "\<forall> g \<in> T. \<forall> X \<in> s // r. \<pi>\<^sub>\<Q> f (\<phi> g ` X) = \<psi> g (\<pi>\<^sub>\<Q> f X)"
  proof (intro ballI)
    fix
      g :: "'z" and
      X :: "'x set"
    assume
      g_in_T: "g \<in> T" and
      cls_X: "X \<in> s // r"
    then obtain x :: "'x" where
      X_eq_cls_x: "X = r `` {x}" and
      x_in_s: "x \<in> s"
      using quotientE
      by blast
    have x_in_X: "x \<in> X"
      unfolding X_eq_cls_x
      by (rule equiv_class_self[OF equiv_rel x_in_s])
    have img_X_eq_cls: "\<phi> g ` X = r `` {\<phi> g x}"
      unfolding X_eq_cls_x
      by (rule bspec[OF bspec[OF act_cls g_in_T] x_in_s])
    have img_x_in_own_cls: "\<phi> g x \<in> r `` {\<phi> g x}"
      using x_in_X img_X_eq_cls
      by blast
    hence img_x_in_s: "\<phi> g x \<in> s"
      using equiv_type[OF equiv_rel]
      by blast
    have img_cls: "r `` {\<phi> g x} \<in> s // r"
      by (rule quotientI[OF img_x_in_s])
    have eq_1: "\<pi>\<^sub>\<Q> f (\<phi> g ` X) = f (\<phi> g x)"
      unfolding img_X_eq_cls
      by (rule bspec[OF bspec[OF pass_to_quotient[OF invar equiv_rel]
            img_cls] img_x_in_own_cls])
    have "(\<phi> g, \<psi> g) \<in> {(\<phi> z, \<psi> z) | z. z \<in> T}"
      using g_in_T
      by blast
    hence eq_2: "f (\<phi> g x) = \<psi> g (f x)"
      using equivar x_in_s
      unfolding action_induced_equivariance_def is_symmetry.simps
      by fastforce
    have eq_3: "\<pi>\<^sub>\<Q> f X = f x"
      by (rule bspec[OF bspec[OF pass_to_quotient[OF invar equiv_rel]
            cls_X] x_in_X])
    show "\<pi>\<^sub>\<Q> f (\<phi> g ` X) = \<psi> g (\<pi>\<^sub>\<Q> f X)"
      using eq_1 eq_2 eq_3
      by simp
  qed
  thus ?thesis
    unfolding action_induced_equivariance_def is_symmetry.simps
              set_action.simps
    by blast
qed

text \<open>
  The class-mapping condition above follows from two conditions:
  every transformation maps r-related elements to r-related elements, and
  every transformation has a two-sided (pointwise) inverse within that relation.
  Both hold in particular for group actions whose transformations respect r,
  however no group action instance is needed.
\<close>

lemma rel_compat_imp_act_maps_classes:
  fixes
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  assumes
    equiv_rel: "equiv s r" and
    compat: "\<forall> g \<in> T. \<forall> x y. (x, y) \<in> r \<longrightarrow> (\<phi> g x, \<phi> g y) \<in> r" and
    invs: "\<forall> g \<in> T. \<exists> h \<in> T. \<forall> x \<in> s. \<phi> h (\<phi> g x) = x \<and> \<phi> g (\<phi> h x) = x"
  shows "\<forall> g \<in> T. \<forall> x \<in> s. \<phi> g ` (r `` {x}) = r `` {\<phi> g x}"
proof (intro ballI)
  fix
    g :: "'z" and
    x :: "'x"
  assume
    g_in_T: "g \<in> T" and
    x_in_s: "x \<in> s"
  show "\<phi> g ` (r `` {x}) = r `` {\<phi> g x}"
  proof (intro equalityI subsetI)
    fix w :: "'x"
    assume "w \<in> \<phi> g ` (r `` {x})"
    then obtain y :: "'x" where
      "(x, y) \<in> r" and
      w_eq: "w = \<phi> g y"
      by blast
    hence "(\<phi> g x, \<phi> g y) \<in> r"
      using compat g_in_T
      by blast
    thus "w \<in> r `` {\<phi> g x}"
      using w_eq
      by blast
  next
    fix z :: "'x"
    assume "z \<in> r `` {\<phi> g x}"
    hence rel_img_x_z: "(\<phi> g x, z) \<in> r"
      by blast
    obtain h :: "'z" where
      h_in_T: "h \<in> T" and
      inv_h: "\<forall> x' \<in> s. \<phi> h (\<phi> g x') = x' \<and> \<phi> g (\<phi> h x') = x'"
      using invs g_in_T
      by blast
    have z_in_s: "z \<in> s"
      using rel_img_x_z equiv_rel equiv_type
      by blast
    have "(\<phi> h (\<phi> g x), \<phi> h z) \<in> r"
      using compat h_in_T rel_img_x_z
      by blast
    hence "(x, \<phi> h z) \<in> r"
      using inv_h x_in_s
      by fastforce
    hence "\<phi> h z \<in> r `` {x}"
      by blast
    moreover have "\<phi> g (\<phi> h z) = z"
      using inv_h z_in_s
      by blast
    ultimately show "z \<in> \<phi> g ` (r `` {x})"
      by force
  qed
qed

text \<open>
  Wrapper version with pointwise assumptions and the invariance property
  stated in the symmetry-datatype style of the VMCF.
\<close>

corollary pass_to_quotient_equivar':
  fixes
    f :: "'x \<Rightarrow> 'y" and
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    equiv_rel: "equiv s r" and
    invar: "is_symmetry f (Invariance r)" and
    equivar: "is_symmetry f (action_induced_equivariance T s \<phi> \<psi>)" and
    compat: "\<forall> g \<in> T. \<forall> x y. (x, y) \<in> r \<longrightarrow> (\<phi> g x, \<phi> g y) \<in> r" and
    invs: "\<forall> g \<in> T. \<exists> h \<in> T. \<forall> x \<in> s. \<phi> h (\<phi> g x) = x \<and> \<phi> g (\<phi> h x) = x"
  shows "is_symmetry (\<pi>\<^sub>\<Q> f)
            (action_induced_equivariance T (s // r) (set_action \<phi>) \<psi>)"
    using pass_to_quotient_equivar[OF equiv_rel
          invar[unfolded invar_is_congruence] equivar
          rel_compat_imp_act_maps_classes[OF equiv_rel compat invs]] .

text \<open>
  Under the same two conditions, the elementwise action of a
  transformation sends equivalence classes to equivalence classes,
  ie the quotient is closed under the induced set action.
\<close>

lemma act_maps_classes_into_quotient:
  fixes
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun" and
    g :: "'z" and
    X :: "'x set"
  assumes
    equiv_rel: "equiv s r" and
    compat: "\<forall> g \<in> T. \<forall> x y. (x, y) \<in> r \<longrightarrow> (\<phi> g x, \<phi> g y) \<in> r" and
    invs: "\<forall> g \<in> T. \<exists> h \<in> T. \<forall> x \<in> s. \<phi> h (\<phi> g x) = x \<and> \<phi> g (\<phi> h x) = x" and
    g_in_T: "g \<in> T" and
    cls_X: "X \<in> s // r"
  shows "\<phi> g ` X \<in> s // r"
proof -
  obtain x :: "'x" where
    X_eq_cls_x: "X = r `` {x}" and
    x_in_s: "x \<in> s"
    using cls_X quotientE
    by blast
  have img_X_eq_cls: "\<phi> g ` X = r `` {\<phi> g x}"
    unfolding X_eq_cls_x
    by (rule bspec[OF bspec[OF rel_compat_imp_act_maps_classes[OF
          equiv_rel compat invs] g_in_T] x_in_s])
  have "x \<in> X"
    unfolding X_eq_cls_x
    by (rule equiv_class_self[OF equiv_rel x_in_s])
  hence "\<phi> g x \<in> r `` {\<phi> g x}"
    using img_X_eq_cls
    by blast
  hence "\<phi> g x \<in> s"
    using equiv_type[OF equiv_rel]
    by blast
  thus ?thesis
    unfolding img_X_eq_cls
    by (rule quotientI)
qed

end
