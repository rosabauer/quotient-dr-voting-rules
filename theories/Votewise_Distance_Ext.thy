(*  File:       Votewise_Distance_Ext.thy
    Extends:    Verified_Voting_Rule_Construction.Votewise_Distance
                (VeriVote/verifiedVotingRuleConstruction, commit 1d4225f)
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Votewise Distance with the Averaged Norm\<close>

theory Votewise_Distance_Ext
  imports "Verified_Voting_Rule_Construction.Votewise_Distance"
          Norm_Ext
begin

text \<open>
  On a finite, nonempty voter set, the votewise distance with the averaged norm
  \<open>l_one_avg\<close> is the votewise distance with \<open>l_one\<close> divided by the
  number of voters.
\<close>

lemma dist_avg_norm_eq_normalized_dist:
  fixes
    d :: "'a Vote Distance" and
    A A' :: "'a set" and
    V :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile"
  assumes
    "finite V" and
    "V \<noteq> {}"
  shows "votewise_distance d l_one_avg (A, V, p) (A', V, p') =
          votewise_distance d l_one (A, V, p) (A', V, p') / ereal (real (card V))"
  by (simp add: card_gt_0_iff)

end
