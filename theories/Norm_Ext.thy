(*  File:       Norm_Ext.thy
    Extends:    Verified_Voting_Rule_Construction.Norm
                (VeriVote/verifiedVotingRuleConstruction, commit 1d4225f)
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Averaged Norm\<close>

theory Norm_Ext
  imports "Verified_Voting_Rule_Construction.Norm"
begin

text \<open>
  The averaged variant of \<open>l_one\<close> divides by the length of the vector.
  Used for votewise distances, it scales the distance by the number of voters,
  following the normalized votewise distances of Hadjibeyli and Wilson, which
  do not grow when an electorate is copied.
\<close>

fun l_one_avg :: "Norm" where
  "l_one_avg x = (if x = [] then 0 else l_one x / ereal (real (length x)))"

end
