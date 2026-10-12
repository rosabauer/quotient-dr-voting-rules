(*  File:       Quotient_Kemeny_Rule.thy
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Quotient Kemeny Rule\<close>

theory Quotient_Kemeny_Rule
  imports Quotient_Swapwise_Rules_Helpers
begin

text \<open>
  The quotient counterpart of the Kemeny rule on anonymity-homogeneity
  classes of elections over a fixed alternative set A: the distance-
  rationalized quotient rule for the normalized (averaged) swap distance
  and the strong-unanimity consensus restricted to A.
  Note the two deltas to kemeny_rule (= swap_\<R> strong_unanimity):
  l_one_avg instead of l_one, since the raw swap distance is not invariant
  under homogeneity (copying an electorate scales it), and
  strong_unanimity_in A instead of strong_unanimity, since the relation
  fixes the alternative set. The equivalence of the induced winners is the
  interchangeability proposition in strong_unanimity_in. It is argued on
  paper in the thesis and is not formalized here.
\<close>

subsection \<open>Definition\<close>

fun kemeny_rule\<^sub>\<Q> :: "'a set \<Rightarrow> ('a, 'v :: wellorder) Election set \<Rightarrow> 'a Result" where
  "kemeny_rule\<^sub>\<Q> A E\<^sub>\<Q> =
      \<S>\<C>\<F>_result.distance_\<R>\<^sub>\<Q>
        (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
        (votewise_distance swap l_one_avg)
        (strong_unanimity_in A) E\<^sub>\<Q>"

subsection \<open>Invariance of the Winners\<close>

lemma swap_dr_invar_anon_hom:
  fixes A :: "'a set"
  shows "is_symmetry
           (fun\<^sub>\<E> (\<S>\<C>\<F>_result.\<R>\<^sub>\<W> (votewise_distance swap l_one_avg)
                      (strong_unanimity_in A)))
           (Invariance (anonymity_homogeneity\<^sub>\<R>
              (elections_\<A> A :: ('a, 'v :: wellorder) Election set)))"
  by (rule \<S>\<C>\<F>_result.anon_hom_score_invar_imp_invar_dr)
     (rule swap_score_invar_anon_hom)

subsection \<open>Quotient Instantiation Theorems\<close>

theorem kemeny_rule\<^sub>\<Q>_winners:
  fixes
    A :: "'a set" and
    AC :: "('a, 'v :: wellorder) Election set"
  assumes "AC \<in> elections_\<A> A // anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<S>\<C>\<F>_result.\<R>\<^sub>\<W> (votewise_distance swap l_one_avg)
                        (strong_unanimity_in A))) AC
       = \<S>\<C>\<F>_result.\<R>\<^sub>\<Q> (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
            (votewise_distance swap l_one_avg) (strong_unanimity_in A) AC"
  by (rule \<S>\<C>\<F>_result.invar_dr_simple_on_dist_imp_quotient_dr_winners[OF
        swap_l_one_avg_simple
        strong_unanimity_in_closed_under_anon_hom
        \<S>\<C>\<F>_result.limit_invar_anon_hom
        strong_unanimity_in_invar_anon_hom
        swap_dr_invar_anon_hom
        assms
        anon_hom_equiv
        strong_unanimity_elections_subset])

theorem kemeny_rule\<^sub>\<Q>_is_quotient_dr:
  fixes
    A :: "'a set" and
    AC :: "('a, 'v :: wellorder) Election set"
  assumes "AC \<in> elections_\<A> A // anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "\<pi>\<^sub>\<Q> (fun\<^sub>\<E> (\<S>\<C>\<F>_result.distance_\<R> (votewise_distance swap l_one_avg)
                        (strong_unanimity_in A))) AC
       = kemeny_rule\<^sub>\<Q> A AC"
  unfolding kemeny_rule\<^sub>\<Q>.simps
  by (rule \<S>\<C>\<F>_result.invar_dr_simple_on_dist_imp_quotient_dr[OF
        swap_l_one_avg_simple
        strong_unanimity_in_closed_under_anon_hom
        \<S>\<C>\<F>_result.limit_invar_anon_hom
        strong_unanimity_in_invar_anon_hom
        swap_dr_invar_anon_hom
        assms
        anon_hom_equiv
        strong_unanimity_elections_subset])

end