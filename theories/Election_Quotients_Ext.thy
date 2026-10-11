(*  File:       Election_Quotients_Ext.thy
    Extends:    Verified_Voting_Rule_Construction.Election_Quotients
                (VeriVote/verifiedVotingRuleConstruction, commit 1d4225f)
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>The Anonymity-Homogeneity Relation as an Equivalence\<close>

theory Election_Quotients_Ext
  imports "Verified_Voting_Rule_Construction.Election_Quotients"
begin

text \<open>
  On the elections over a fixed alternative set, all voter sets are finite, so
  the anonymity-homogeneity relation is an equivalence relation there.
\<close>

lemma anon_hom_equiv:
  fixes A :: "'a set"
  shows "equiv (elections_\<A> A) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))"
proof -
  have "\<forall> E \<in> elections_\<A> A. finite (voters_\<E> E)"
    unfolding elections_\<A>.simps
    by blast
  thus ?thesis
    by (rule anonymity_homogeneity_is_equivalence)
qed

end
