(*  File:       Quotient_Distance_Rationalization_Ext.thy
    Extends:    Verified_Voting_Rule_Construction.Quotient_Distance_Rationalization
                (VeriVote/verifiedVotingRuleConstruction, commit 1d4225f)
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Transfer under Consensus-Simplicity\<close>

theory Quotient_Distance_Rationalization_Ext
  imports "Verified_Voting_Rule_Construction.Quotient_Distance_Rationalization"
          Relation_Quotients_Ext
begin

text \<open>
  \<open>simple_on Y r X d\<close> weakens \<open>simple r X d\<close> by requiring the condition only
  for the classes \<open>B\<close> of a subset \<open>Y\<close> of \<open>X\<close>. In the quotient distance
  rationalization, \<open>Y\<close> will be the set of consensus elections, which are the
  only classes whose distance to \<open>A\<close> enters the rule. The theorems
  \<open>invar_dr_simple_on_dist_imp_quotient_dr_winners\<close> and
  \<open>invar_dr_simple_on_dist_imp_quotient_dr\<close> below restate
  \<open>invar_dr_simple_dist_imp_quotient_dr_winners\<close> and
  \<open>invar_dr_simple_dist_imp_quotient_dr\<close> with this weaker premise;
  \<open>simple_imp_simple_on\<close> recovers it from the original notion.
\<close>

fun simple_on :: "'x set \<Rightarrow> 'x rel \<Rightarrow> 'x set \<Rightarrow> 'x Distance \<Rightarrow> bool" where
  "simple_on Y r X d =
    (\<forall> A \<in> X // r.
      \<exists> a \<in> A. \<forall> B \<in> Y // r.
        distance_infimum\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B})"

text \<open>
  Simplicity on \<open>Y\<close> follows whenever the infimum of the distances from a point
  of a class \<open>A\<close> to a class \<open>B\<close> does not depend on which point of \<open>A\<close> is
  chosen: then any point of \<open>A\<close> witnesses it, since the two-sided infimum over
  \<open>A\<close> and \<open>B\<close> flattens to that common value.
\<close>

lemma inner_inf_const_imp_simple_on:
  fixes
    Y X :: "'x set" and
    r :: "'x rel" and
    d :: "'x Distance"
  assumes
    equiv_rel: "equiv X r" and
    const: "\<forall> A \<in> X // r. \<forall> B \<in> Y // r. \<forall> x \<in> A. \<forall> x' \<in> A.
              Inf {d x b | b. b \<in> B} = Inf {d x' b | b. b \<in> B}"
  shows "simple_on Y r X d"
proof (unfold simple_on.simps, intro ballI)
  fix A :: "'x set"
  assume A_cls: "A \<in> X // r"
  have "A \<noteq> {}"
    using A_cls equiv_rel in_quotient_imp_non_empty
    by blast
  then obtain a where a_in: "a \<in> A"
    by blast
  show "\<exists> a \<in> A. \<forall> B \<in> Y // r. distance_infimum\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
  proof (rule bexI[OF _ a_in], intro ballI)
    fix B :: "'x set"
    assume B_cls: "B \<in> Y // r"
    have inner_const: "Inf {d x b | b. b \<in> B} = Inf {d a b | b. b \<in> B}" if "x \<in> A" for x
      using const A_cls B_cls that a_in
      by blast
    have "{Inf {d x b | b. b \<in> B} | x. x \<in> A} = {Inf {d a b | b. b \<in> B}}"
      using inner_const a_in
      by blast
    thus "distance_infimum\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
      unfolding distance_infimum\<^sub>\<Q>.simps inf_helper
      by simp
  qed
qed

text \<open>
  A distance that is simple on all of \<open>X\<close> is in particular simple on every
  subset \<open>Y\<close> of \<open>X\<close>.
\<close>

lemma simple_imp_simple_on:
  fixes
    Y X :: "'x set" and
    r :: "'x rel" and
    d :: "'x Distance"
  assumes
    subset: "Y \<subseteq> X" and
    simple: "simple r X d"
  shows "simple_on Y r X d"
proof -
  have "Y // r \<subseteq> X // r"
    using subset
    by (rule quotient_subset)
  thus ?thesis
    using simple
    unfolding simple.simps simple_on.simps
    by blast
qed

text \<open>
  The following two theorems generalize \<open>invar_dr_simple_dist_imp_quotient_dr_winners\<close>
  and \<open>invar_dr_simple_dist_imp_quotient_dr\<close> of the imported theory
  \<open>Quotient_Distance_Rationalization\<close>: the premise \<open>simple r X d\<close>
  is weakened to \<open>simple_on (elections_\<K> C) r X d\<close>, which only asks for a
  representative against the classes of consensus elections. The proofs are
  those of the original theorems (A. Appelhagen); the only changes are at the
  one point where the premise is used, namely where the representative \<open>a\<close> of
  the class \<open>A\<close> is obtained, and in the subset fact for the quotient classes,
  which now uses \<open>quotient_subset\<close>. By \<open>simple_imp_simple_on\<close>, the original
  theorems are special cases.
\<close>

theorem (in result) invar_dr_simple_on_dist_imp_quotient_dr_winners:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel" and
    X A :: "('a, 'v) Election set"
  assumes
    simple: "simple_on (elections_\<K> C) r X d" and
    closed_domain: "closed_restricted_rel r X (elections_\<K> C)" and
    invar_res:
      "is_symmetry (\<lambda> (E :: ('a, 'v) Election).
        limit (alternatives_\<E> E) UNIV) (Invariance r)" and
    invar_C: "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
                    (Invariance (Restr r (elections_\<K> C)))" and
    invar_dr: "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)" and
    quot_class: "A \<in> X // r" and
    equiv_rel: "equiv X r" and
    cons_subset: "elections_\<K> C \<subseteq> X"
  shows "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = \<R>\<^sub>\<Q> r d C A"
proof -
  have "\<forall> (y :: 'r set). \<forall> (E :: ('a, 'v) Election)
        \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y. E \<in> r `` {E}"
    unfolding preimg.simps
    using equiv_rel equiv_class_self cons_subset in_mono mem_Collect_eq
    by (metis (mono_tags, lifting))
  hence "\<forall> (y :: 'r set).
    preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y
      \<subseteq> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)"
    unfolding quotient_def
    by blast
  moreover have "\<forall> (y :: 'r set).
      \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)
      \<subseteq> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y"
  proof (intro allI subsetI)
    fix
      Y :: "'r set" and
      E :: "('a, 'v) Election"
    assume "E \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) Y // r)"
    then obtain B :: "('a, 'v) Election set" where
      E_in_B: "E \<in> B" and
      "B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) Y // r"
      by blast
    then obtain E' :: "('a, 'v) Election" where
      "B = r `` {E'}" and
      map_to_Y: "E' \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) Y"
      using quotientE
      by blast
    hence "(E', E) \<in> Restr r (elections_\<K> C)"
      using closed_domain E_in_B equiv_rel
      unfolding closed_restricted_rel.simps restricted_rel.simps preimg.simps
                equiv_def refl_on_def
      by blast
    thus "E \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) Y"
      using map_to_Y invar_C
      unfolding preimg.simps is_symmetry.simps
      by blast
  qed
  ultimately have preimg_partition: "\<forall> (y :: 'r set).
      \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r) =
      preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y"
    by blast
  have quot_classes_subset: "(elections_\<K> C) // r \<subseteq> X // r"
    using cons_subset
    by (rule quotient_subset)
  have preimg_img_imp_cls:
    "\<forall> (y :: 'r set). \<forall> (B :: ('a, 'v) Election set)
      \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C) y.
          B \<in> (elections_\<K> C) // r"
    by simp
  moreover obtain a :: "('a, 'v) Election" where
    a_in_A: "a \<in> A" and
    a_def_inf_dist:
      "\<forall> (B :: ('a, 'v) Election set) \<in> (elections_\<K> C) // r.
        distance_infimum\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    using simple quot_class
    unfolding simple_on.simps
    by blast
  ultimately have inf_dist_preimg_sets:
    "\<forall> (y :: 'r set). \<forall> (B :: ('a, 'v) Election set)
      \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C) y.
          distance_infimum\<^sub>\<Q> d A B = Inf {d a b | b. b \<in> B}"
    using quot_classes_subset
    by blast
  have wf_res_eq: "singleton_set_system (limit (alternatives_\<E> a) UNIV) =
      singleton_set_system (limit\<^sub>\<Q> A UNIV)"
    using invar_res a_in_A quot_class cons_subset equiv_rel limit_invar
    by metis
  have preimg_partition_dist: "\<forall> (y :: 'r set).
      Inf {d a b | (b :: ('a, 'v) Election).
        b \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)}
    = Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y)"
    using Setcompr_eq_image preimg_partition
    by metis
  have "\<forall> (y :: 'r set).
      {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r}
    = {Inf E | (E :: ereal set). E \<in> {{d a b | (b :: ('a, 'v) Election). b \<in> B} |
          (B :: ('a, 'v) Election set).
        B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r}}"
    by blast
  hence "\<forall> (y :: 'r set).
      Inf {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r}
    = Inf (\<Union> {{d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)})"
    using union_inf
    by presburger
  moreover have
    "\<forall> (y :: 'r set).
        {d a b | (b :: ('a, 'v) Election).
          b \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)}
      = \<Union> {{d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
          B \<in> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)}"
    by blast
  ultimately have rewrite_inf_dist:
    "\<forall> (y :: 'r set).
      Inf
        {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
          B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r}
    = Inf {d a b | (b :: ('a, 'v) Election).
        b \<in> \<Union> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r)}"
    by presburger
  have "\<forall> (y :: 'r set).
      distance_infimum\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C) y
    = {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C) y}"
    using inf_dist_preimg_sets
    unfolding Image_def
    by auto
  moreover have
    "\<forall> (R :: 'r set).
        preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K> C // r) R
      = preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) R // r"
    using closed_domain cons_subset equiv_rel invar_C preimg_invar
    by (metis (no_types))
  hence "\<forall> (y :: 'r set).
      {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C) y}
    = {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> (preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y) // r}"
    unfolding elections_\<K>\<^sub>\<Q>.simps
    by presburger
  ultimately have
    "\<forall> (y :: 'r set).
      Inf (distance_infimum\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C) y)
    = Inf {Inf {d a b | (b :: ('a, 'v) Election). b \<in> B} | (B :: ('a, 'v) Election set).
        B \<in> preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y // r}"
    by simp
  hence inf_le_iff: "\<forall> (x :: 'r).
      (\<forall> (y :: 'r set) \<in> singleton_set_system (limit (alternatives_\<E> a) UNIV).
          Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {x})
        \<le> Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y))
    = (\<forall> (y :: 'r set) \<in> singleton_set_system (limit\<^sub>\<Q> A UNIV).
          Inf (distance_infimum\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)))
            (elections_\<K>\<^sub>\<Q> r C) {x})
        \<le> Inf (distance_infimum\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)))
            (elections_\<K>\<^sub>\<Q> r C) y))"
    using wf_res_eq rewrite_inf_dist preimg_partition_dist
    by presburger
  have "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a"
    using a_in_A invar_dr equiv_rel quot_class pass_to_quotient invariance_is_congruence
    by blast
  moreover have "\<forall> (x :: 'r). x \<in> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a \<longleftrightarrow> x \<in> \<R>\<^sub>\<Q> r d C A"
  proof
    fix x :: "'r"
    have "x \<in> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a =
       (x \<in> \<Union> (minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
              (singleton_set_system (limit (alternatives_\<E> a) UNIV)) a))"
      using \<R>\<^sub>\<W>_is_minimizer
      by metis
    also have "\<dots> =
        ({x} \<in> minimizer (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) d
                (singleton_set_system (limit (alternatives_\<E> a) UNIV)) a)"
      using singleton_set_union
      unfolding minimizer.simps arg_min_set.simps is_arg_min_def
      by auto
    also have "\<dots> = ({x} \<in> singleton_set_system (limit (alternatives_\<E> a) UNIV)
        \<and> (\<forall> (y :: 'r set) \<in> singleton_set_system (limit (alternatives_\<E> a) UNIV).
            Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) {x})
          \<le> Inf (d a ` preimg (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)) (elections_\<K> C) y)))"
      using minimizer_helper
      by (metis (no_types, lifting))
    also have "\<dots> = ({x} \<in> singleton_set_system (limit\<^sub>\<Q> A UNIV)
      \<and> (\<forall> (y :: 'r set) \<in> singleton_set_system (limit\<^sub>\<Q> A UNIV).
        Inf (distance_infimum\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)))
              (elections_\<K>\<^sub>\<Q> r C) {x})
        \<le> Inf (distance_infimum\<^sub>\<Q> d A ` preimg (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C)))
              (elections_\<K>\<^sub>\<Q> r C) y)))"
      using wf_res_eq inf_le_iff
      by blast
    also have "\<dots> =
        ({x} \<in> minimizer
            (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C)
            (distance_infimum\<^sub>\<Q> d)
              (singleton_set_system (limit\<^sub>\<Q> A UNIV)) A)"
      using minimizer_helper
      by (metis (no_types, lifting))
    also have "\<dots> =
      (x \<in> \<Union> (minimizer
            (\<pi>\<^sub>\<Q> (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))) (elections_\<K>\<^sub>\<Q> r C)
            (distance_infimum\<^sub>\<Q> d)
              (singleton_set_system (limit\<^sub>\<Q> A UNIV)) A))"
      using singleton_set_union
      unfolding minimizer.simps arg_min_set.simps is_arg_min_def
      by auto
    finally show "x \<in> fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) a = (x \<in> \<R>\<^sub>\<Q> r d C A)"
      unfolding \<R>\<^sub>\<Q>.simps
      by safe
  qed
  ultimately show "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = \<R>\<^sub>\<Q> r d C A"
    by blast
qed

theorem (in result) invar_dr_simple_on_dist_imp_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel" and
    X A :: "('a, 'v) Election set"
  assumes
    simple: "simple_on (elections_\<K> C) r X d" and
    closed_domain: "closed_restricted_rel r X (elections_\<K> C)" and
    invar_res:
      "is_symmetry (\<lambda> (E :: ('a, 'v) Election).
        limit (alternatives_\<E> E) UNIV) (Invariance r)" and
    invar_C: "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> C))
                  (Invariance (Restr r (elections_\<K> C)))" and
    invar_dr: "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) (Invariance r)" and
    quot_class: "A \<in> X // r" and
    equiv_rel: "equiv X r" and
    cons_subset: "elections_\<K> C \<subseteq> X"
  shows "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (distance_\<R> d C)) A = distance_\<R>\<^sub>\<Q> r d C A"
proof -
  have "\<forall> (E :: ('a, 'v) Election). fun\<^sub>\<E> (distance_\<R> d C) E =
          (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E,
            limit (alternatives_\<E> E) UNIV - fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E,
            {})"
    by simp
  moreover have "\<forall> (E :: ('a, 'v) Election) \<in> A. fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E = \<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A"
    using invar_dr invariance_is_congruence pass_to_quotient quot_class equiv_rel
    by blast
  moreover have "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C)) A = \<R>\<^sub>\<Q> r d C A"
    using invar_dr_simple_on_dist_imp_quotient_dr_winners assms
    by blast
  moreover have
    "\<forall> (E :: ('a, 'v) Election) \<in> A. limit (alternatives_\<E> E) UNIV =
        \<pi>\<^sub>\<Q> (\<lambda> (E :: ('a, 'v) Election). limit (alternatives_\<E> E) UNIV) A"
    using invar_res invariance_is_congruence' pass_to_quotient quot_class equiv_rel
    by blast
  ultimately have all_eq:
    "\<forall> (E :: ('a, 'v) Election) \<in> A. fun\<^sub>\<E> (distance_\<R> d C) E =
      (\<R>\<^sub>\<Q> r d C A,
        \<pi>\<^sub>\<Q> (\<lambda> (E :: ('a, 'v) Election). limit (alternatives_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A,
        {})"
    by fastforce
  hence
    "fun\<^sub>\<E> (distance_\<R> d C) ` A \<subseteq>
      {(\<R>\<^sub>\<Q> r d C A,
        \<pi>\<^sub>\<Q> (\<lambda> (E :: ('a, 'v) Election). limit (alternatives_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A,
        {})}"
    by blast
  moreover have "A \<noteq> {}"
    using quot_class equiv_rel in_quotient_imp_non_empty
    by metis
  ultimately have single_img:
    "{(\<R>\<^sub>\<Q> r d C A,
        \<pi>\<^sub>\<Q> (\<lambda> (E :: ('a, 'v) Election). limit (alternatives_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A,
        {})} =
      fun\<^sub>\<E> (distance_\<R> d C) ` A"
    using empty_is_image subset_singletonD
    by (metis (no_types, lifting))
  hence "card (fun\<^sub>\<E> (distance_\<R> d C) ` A) = 1"
    using is_singleton_altdef is_singletonI
    by (metis (no_types, lifting))
  moreover from this
  have "the_inv (\<lambda> (x :: 'r Result). {x}) (fun\<^sub>\<E> (distance_\<R> d C) ` A) =
          (\<R>\<^sub>\<Q> r d C A,
            \<pi>\<^sub>\<Q> (\<lambda> (E :: ('a, 'v) Election). limit (alternatives_\<E> E) UNIV) A - \<R>\<^sub>\<Q> r d C A,
            {})"
    using single_img singleton_insert_inj_eq singleton_set.elims
          singleton_set_def_if_card_one
    by (metis (no_types))
  ultimately show ?thesis
    unfolding distance_\<R>\<^sub>\<Q>.simps \<pi>\<^sub>\<Q>.simps singleton_set.simps
    by presburger
qed

end
