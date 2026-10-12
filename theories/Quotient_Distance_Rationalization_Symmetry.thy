(*  File:  theories/Compositional_Structures/Basic_Modules/Component_Types/
           Quotient_Distance_Rationalization_Symmetry.thy
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Symmetry Properties of Quotient Distance-Rationalized Rules\<close>

theory Quotient_Distance_Rationalization_Symmetry
  imports Quotient_Distance_Rationalization_Ext
          Relation_Quotients_Ext
begin

text \<open>
  This theory lifts symmetry properties of distance-rationalized rules to
  their quotient counterparts, generically in the property: any symmetry of
  the base rule that is expressed as an equivariance under a family of
  transformations (T, \<phi>, \<psi>) and that is compatible with the quotient
  relation descends to the natively-constructed quotient rule
  \<open>distance_\<R>\<^sub>\<Q>\<close>. Invariance properties are the special case
  \<psi> g = id. Concrete properties (neutrality under the alternative-set
  stabilizer, reversal symmetry, ...) are obtained downstream by assuming equivariance, 
  compatibility, and invertibility for the respective action.
\<close>

subsection \<open>Auxiliary Lemma\<close>

text \<open>
  Invariance of the winner set and of the result limit under a relation
  yields invariance of the full DR rule, since the
  latter is assembled componentwise from the two. This makes winner-level
  invariance facts usable where full-rule invariance is required.
\<close>

lemma (in result) distance_\<R>_invar_of_winners_invar:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel"
  assumes
    invar_winners: "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)" and
    invar_res: "is_symmetry (\<lambda> E :: ('a, 'v) Election.
        limit (alternatives_\<E> E) UNIV) (Invariance r)"
  shows "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance r)"
proof -
  have win: "\<forall> E E'. (E, E') \<in> r \<longrightarrow> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E'"
    using invar_winners
    unfolding is_symmetry.simps
    by blast 
  have res: "\<forall> E E'. (E, E') \<in> r \<longrightarrow>
      limit (alternatives_\<E> E) UNIV = limit (alternatives_\<E> E') UNIV"
    using invar_res
    unfolding is_symmetry.simps
    by blast 
  have "\<forall> E E'. (E, E') \<in> r \<longrightarrow>
      fun\<^sub>\<E> (distance_\<R> d C) E = fun\<^sub>\<E> (distance_\<R> d C) E'"
  proof (intro allI impI)
    fix E E' :: "('a, 'v) Election"
    assume rel: "(E, E') \<in> r"
    have "fun\<^sub>\<E> (distance_\<R> d C) E =
        (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E,
          limit (alternatives_\<E> E) UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E, {})"
      by simp
    also have "\<dots> =
        (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E',
          limit (alternatives_\<E> E') UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E', {})"
      using win res rel
      by metis
    also have "\<dots> = fun\<^sub>\<E> (distance_\<R> d C) E'"
      by simp
    finally show "fun\<^sub>\<E> (distance_\<R> d C) E = fun\<^sub>\<E> (distance_\<R> d C) E'" .
  qed
  thus ?thesis
    unfolding is_symmetry.simps
    by blast
qed

subsection \<open>Theorem: Equivariance Lifts to the Quotient Rule\<close>

text \<open>
  Under the premises of \<open>invar_dr_simple_on_dist_imp_quotient_dr\<close>, any
  equivariance of the full distance-rationalized rule on X whose
  transformations respect the relation r and are invertible in the
  family descends to the quotient rule \<open>distance_\<R>\<^sub>\<Q>\<close> on X // r,
  under the elementwise action of the same transformations.
  The proof puts together 3 facts per transformation g and class B:
  the quotient-DR bridge identifies \<open>distance_\<R>\<^sub>\<Q>\<close> with the induced
  quotient function \<open>\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C))\<close>, both at B and at
  the transformed class \<phi> g ` B (a class again by
  \<open>act_maps_classes_into_quotient\<close>), and the generic equivariance
  lifting \<open>pass_to_quotient_equivar'\<close> provides the equivariance of the
  induced quotient function in between.
\<close>

theorem (in result) equivar_dr_simple_dist_imp_equivar_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel" and
    X :: "('a, 'v) Election set" and
    T :: "'z set" and
    \<phi> :: "('z, ('a, 'v) Election) binary_fun" and
    \<psi> :: "('z, 'r Result) binary_fun"
  assumes
    simple: "simple_on (elections_\<K> C) r X d" and
    closed_domain: "closed_restricted_rel r X (elections_\<K> C)" and
    invar_res: "is_symmetry (\<lambda> E :: ('a, 'v) Election.
        limit (alternatives_\<E> E) UNIV) (Invariance r)" and
    invar_C: "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
        (Invariance (Restr r (elections_\<K> C)))" and
    invar_dr: "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)" and
    equiv_rel: "equiv X r" and
    cons_subset: "elections_\<K> C \<subseteq> X" and
    equivar_dr: "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C))
        (action_induced_equivariance T X \<phi> \<psi>)" and
    compat: "\<forall> g \<in> T. \<forall> E E'. (E, E') \<in> r \<longrightarrow> (\<phi> g E, \<phi> g E') \<in> r" and
    invs: "\<forall> g \<in> T. \<exists> h \<in> T. \<forall> E \<in> X. \<phi> h (\<phi> g E) = E \<and> \<phi> g (\<phi> h E) = E"
  shows "is_symmetry (distance_\<R>\<^sub>\<Q> r d C)
      (action_induced_equivariance T (X // r) (set_action \<phi>) \<psi>)"
proof -
  have invar_full: "is_symmetry (fun\<^sub>\<E> (distance_\<R> d C)) (Invariance r)"
    by (rule distance_\<R>_invar_of_winners_invar[OF invar_dr invar_res])
  have lifted: "is_symmetry (\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)))
      (action_induced_equivariance T (X // r) (set_action \<phi>) \<psi>)"
    by (rule pass_to_quotient_equivar'[OF equiv_rel invar_full
          equivar_dr compat invs])
  have bridge: "\<forall> B \<in> X // r.
      \<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) B = distance_\<R>\<^sub>\<Q> r d C B"
  proof (intro ballI)
    fix B :: "('a, 'v) Election set"
    assume "B \<in> X // r"
    thus "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) B = distance_\<R>\<^sub>\<Q> r d C B"
      by (rule invar_dr_simple_on_dist_imp_quotient_dr[OF simple closed_domain
            invar_res invar_C invar_dr _ equiv_rel cons_subset])
  qed
  have "\<forall> g \<in> T. \<forall> B \<in> X // r.
      distance_\<R>\<^sub>\<Q> r d C (\<phi> g ` B) = \<psi> g (distance_\<R>\<^sub>\<Q> r d C B)"
  proof (intro ballI)
    fix
      g :: "'z" and
      B :: "('a, 'v) Election set"
    assume
      g_in_T: "g \<in> T" and
      cls_B: "B \<in> X // r"
    have img_cls: "\<phi> g ` B \<in> X // r"
      by (rule act_maps_classes_into_quotient[OF equiv_rel compat invs
            g_in_T cls_B])
    have lifted_eq: "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) (\<phi> g ` B)
        = \<psi> g (\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) B)"
      using lifted g_in_T cls_B
      unfolding rewrite_equivariance set_action.simps
      by blast 
    have bridge_img: "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) (\<phi> g ` B)
        = distance_\<R>\<^sub>\<Q> r d C (\<phi> g ` B)"
      by (rule bspec[OF bridge img_cls])
    have bridge_B: "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) B = distance_\<R>\<^sub>\<Q> r d C B"
      by (rule bspec[OF bridge cls_B])
    show "distance_\<R>\<^sub>\<Q> r d C (\<phi> g ` B) = \<psi> g (distance_\<R>\<^sub>\<Q> r d C B)"
      unfolding bridge_img[symmetric] bridge_B[symmetric]
      by (rule lifted_eq)
  qed
  thus ?thesis
    unfolding action_induced_equivariance_def is_symmetry.simps
              set_action.simps
    by blast
qed

end
