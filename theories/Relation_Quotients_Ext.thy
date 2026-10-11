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

subsection ‹Equivariance›

text ‹
  Invariance in the sense of the symmetry datatype coincides with
  congruence in the sense of the quotient  (\<open>respects\<close>).
›

lemma invar_is_congruence:
  fixes
    f :: "'x ⇒ 'y" and
    r :: "'x rel"
  shows "is_symmetry f (Invariance r) = (f respects r)"
  unfolding congruent_def
  by auto

text ‹
  Passing to the quotient preserves equivariance:
  Assume a function f is invariant under an equivalence relation r on s,
  so that it induces a well-defined function \<open>π⇩𝒬 f\<close> on the quotient s // r
  (cf. \<open>pass_to_quotient\<close>). If f is also equivariant under a family of
  transformations φ g with associated result transformations ψ g, and every
  φ g maps r-classes onto r-classes, then \<open>π⇩𝒬 f\<close> is equivariant on the
  quotient under the elementwise action of φ, with the same ψ.
  This is needed to lift properties like neutrality, reversal symmetry, etc
  to quotients of election sets.
›

theorem pass_to_quotient_equivar:
  fixes
    f :: "'x ⇒ 'y" and
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    φ :: "('z, 'x) binary_fun" and
    ψ :: "('z, 'y) binary_fun"
  assumes
    equiv_rel: "equiv s r" and
    invar: "f respects r" and
    equivar: "is_symmetry f (action_induced_equivariance T s φ ψ)" and
    act_cls: "∀ g ∈ T. ∀ x ∈ s. φ g ` (r `` {x}) = r `` {φ g x}"
  shows "is_symmetry (π⇩𝒬 f)
            (action_induced_equivariance T (s // r) (set_action φ) ψ)"
proof -
  have "∀ g ∈ T. ∀ X ∈ s // r. π⇩𝒬 f (φ g ` X) = ψ g (π⇩𝒬 f X)"
  proof (intro ballI)
    fix
      g :: "'z" and
      X :: "'x set"
    assume
      g_in_T: "g ∈ T" and
      cls_X: "X ∈ s // r"
    then obtain x :: "'x" where
      X_eq_cls_x: "X = r `` {x}" and
      x_in_s: "x ∈ s"
      using quotientE
      by blast
    have x_in_X: "x ∈ X"
      unfolding X_eq_cls_x
      by (rule equiv_class_self[OF equiv_rel x_in_s])
    have img_X_eq_cls: "φ g ` X = r `` {φ g x}"
      unfolding X_eq_cls_x
      by (rule bspec[OF bspec[OF act_cls g_in_T] x_in_s])
    have img_x_in_own_cls: "φ g x ∈ r `` {φ g x}"
      using x_in_X img_X_eq_cls
      by blast
    hence img_x_in_s: "φ g x ∈ s"
      using equiv_type[OF equiv_rel]
      by blast
    have img_cls: "r `` {φ g x} ∈ s // r"
      by (rule quotientI[OF img_x_in_s])
    have eq_1: "π⇩𝒬 f (φ g ` X) = f (φ g x)"
      unfolding img_X_eq_cls
      by (rule bspec[OF bspec[OF pass_to_quotient[OF invar equiv_rel]
            img_cls] img_x_in_own_cls])
    have "(φ g, ψ g) ∈ {(φ z, ψ z) | z. z ∈ T}"
      using g_in_T
      by blast
    hence eq_2: "f (φ g x) = ψ g (f x)"
      using equivar x_in_s
      unfolding action_induced_equivariance_def is_symmetry.simps
      by fastforce
    have eq_3: "π⇩𝒬 f X = f x"
      by (rule bspec[OF bspec[OF pass_to_quotient[OF invar equiv_rel]
            cls_X] x_in_X])
    show "π⇩𝒬 f (φ g ` X) = ψ g (π⇩𝒬 f X)"
      using eq_1 eq_2 eq_3
      by simp
  qed
  thus ?thesis
    unfolding action_induced_equivariance_def is_symmetry.simps
              set_action.simps
    by blast
qed

text ‹
  The class-mapping condition above follows from two conditions:
  every transformation maps r-related elements to r-related elements, and
  every transformation has a two-sided (pointwise) inverse within that relation.
  Both hold in particular for group actions whose transformations respect r,
  however no group action instance is needed.
›

lemma rel_compat_imp_act_maps_classes:
  fixes
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    φ :: "('z, 'x) binary_fun"
  assumes
    equiv_rel: "equiv s r" and
    compat: "∀ g ∈ T. ∀ x y. (x, y) ∈ r ⟶ (φ g x, φ g y) ∈ r" and
    invs: "∀ g ∈ T. ∃ h ∈ T. ∀ x ∈ s. φ h (φ g x) = x ∧ φ g (φ h x) = x"
  shows "∀ g ∈ T. ∀ x ∈ s. φ g ` (r `` {x}) = r `` {φ g x}"
proof (intro ballI)
  fix
    g :: "'z" and
    x :: "'x"
  assume
    g_in_T: "g ∈ T" and
    x_in_s: "x ∈ s"
  show "φ g ` (r `` {x}) = r `` {φ g x}"
  proof (intro equalityI subsetI)
    fix w :: "'x"
    assume "w ∈ φ g ` (r `` {x})"
    then obtain y :: "'x" where
      "(x, y) ∈ r" and
      w_eq: "w = φ g y"
      by blast
    hence "(φ g x, φ g y) ∈ r"
      using compat g_in_T
      by blast
    thus "w ∈ r `` {φ g x}"
      using w_eq
      by blast
  next
    fix z :: "'x"
    assume "z ∈ r `` {φ g x}"
    hence rel_img_x_z: "(φ g x, z) ∈ r"
      by blast
    obtain h :: "'z" where
      h_in_T: "h ∈ T" and
      inv_h: "∀ x' ∈ s. φ h (φ g x') = x' ∧ φ g (φ h x') = x'"
      using invs g_in_T
      by blast
    have z_in_s: "z ∈ s"
      using rel_img_x_z equiv_rel equiv_type
      by blast
    have "(φ h (φ g x), φ h z) ∈ r"
      using compat h_in_T rel_img_x_z
      by blast
    hence "(x, φ h z) ∈ r"
      using inv_h x_in_s
      by fastforce
    hence "φ h z ∈ r `` {x}"
      by blast
    moreover have "φ g (φ h z) = z"
      using inv_h z_in_s
      by blast
    ultimately show "z ∈ φ g ` (r `` {x})"
      by force
  qed
qed

text ‹
  Wrapper version with pointwise assumptions and the invariance property
  stated in the symmetry-datatype style of the VMCF.
›

corollary pass_to_quotient_equivar':
  fixes
    f :: "'x ⇒ 'y" and
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    φ :: "('z, 'x) binary_fun" and
    ψ :: "('z, 'y) binary_fun"
  assumes
    equiv_rel: "equiv s r" and
    invar: "is_symmetry f (Invariance r)" and
    equivar: "is_symmetry f (action_induced_equivariance T s φ ψ)" and
    compat: "∀ g ∈ T. ∀ x y. (x, y) ∈ r ⟶ (φ g x, φ g y) ∈ r" and
    invs: "∀ g ∈ T. ∃ h ∈ T. ∀ x ∈ s. φ h (φ g x) = x ∧ φ g (φ h x) = x"
  shows "is_symmetry (π⇩𝒬 f)
            (action_induced_equivariance T (s // r) (set_action φ) ψ)"
    using pass_to_quotient_equivar[OF equiv_rel
          invar[unfolded invar_is_congruence] equivar
          rel_compat_imp_act_maps_classes[OF equiv_rel compat invs]] .

text ‹
  Under the same two conditions, the elementwise action of a
  transformation sends equivalence classes to equivalence classes,
  ie the quotient is closed under the induced set action.
›

lemma act_maps_classes_into_quotient:
  fixes
    r :: "'x rel" and
    s :: "'x set" and
    T :: "'z set" and
    φ :: "('z, 'x) binary_fun" and
    g :: "'z" and
    X :: "'x set"
  assumes
    equiv_rel: "equiv s r" and
    compat: "∀ g ∈ T. ∀ x y. (x, y) ∈ r ⟶ (φ g x, φ g y) ∈ r" and
    invs: "∀ g ∈ T. ∃ h ∈ T. ∀ x ∈ s. φ h (φ g x) = x ∧ φ g (φ h x) = x" and
    g_in_T: "g ∈ T" and
    cls_X: "X ∈ s // r"
  shows "φ g ` X ∈ s // r"
proof -
  obtain x :: "'x" where
    X_eq_cls_x: "X = r `` {x}" and
    x_in_s: "x ∈ s"
    using cls_X quotientE
    by blast
  have img_X_eq_cls: "φ g ` X = r `` {φ g x}"
    unfolding X_eq_cls_x
    by (rule bspec[OF bspec[OF rel_compat_imp_act_maps_classes[OF
          equiv_rel compat invs] g_in_T] x_in_s])
  have "x ∈ X"
    unfolding X_eq_cls_x
    by (rule equiv_class_self[OF equiv_rel x_in_s])
  hence "φ g x ∈ r `` {φ g x}"
    using img_X_eq_cls
    by blast
  hence "φ g x ∈ s"
    using equiv_type[OF equiv_rel]
    by blast
  thus ?thesis
    unfolding img_X_eq_cls
    by (rule quotientI)
qed

end
