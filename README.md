# Verified Quotient Reasoning for Distance-Rationalizable Voting Rules

Isabelle/HOL theories of my Bachelor's thesis (LMU Munich, October 2026;
supervisor Jasmin Blanchette, advisor Michael Kirsten).

The thesis builds on the Verified Modular Construction Framework (VMCF) of
Diekhoff, Kirsten and Krämer, <https://github.com/VeriVote/verifiedVotingRuleConstruction>.
The VMCF is not copied into this repository. It is a git submodule (`upstream/`,
commit [`1d4225f`](https://github.com/VeriVote/verifiedVotingRuleConstruction/commit/1d4225f96c982ba23a65e0ef986a45d8cc0bdbe1))
and is not modified. Everything in `theories/` was written for the thesis.

## Abstract

A distance-rationalized voting rule elects the winners of the consensus election that is closest to the given election. For rules that are anonymous and homogeneous, Hadjibeyli and Wilson (2019) work on election quotients, where two elections are identified if they have the same vote fractions. The resulting quotients correspond to points of the rational simplex. Appelhagen (2024) added quotient distance rationalization to the Verified Modular Construction Framework (VMCF) in Isabelle/HOL, with a transfer theorem from a rule to its quotient rule, but without an instance. This thesis asks whether the VMCF's modular proof infrastructure can be extended to work on election quotients, and answers it with two contributions.

First, I define a quotient Kemeny rule and prove in Isabelle that it equals the quotient of a variant of the Kemeny rule, namely the one rationalized by the normalized swap distance and strong unanimity restricted to a fixed candidate set. To do so, I weaken the simplicity premise of the transfer theorem. That this variant elects the same candidates as the Kemeny rule of the VMCF is shown on paper. Second, I prove in Isabelle a lifting theorem: a distance-rationalized rule that is invariant under an equivalence relation and equivariant under transformations compatible with that relation has an equivariant quotient rule. For neutrality on the anonymity–homogeneity quotient, the lift is proved in Isabelle for the quotient function. Its combination with the lifting theorem into an inference rule for quotient rules is shown on paper. Reversal symmetry and anonymity are treated the same way. In both contributions the existing infrastructure carried over after one definition had been restricted to a fixed candidate set.

## Main results

Indices refer to the thesis. Appendix A.5 lists the Isabelle names of all
other statements that are proved in Isabelle.

| | Isabelle name | Theory |
|---|---|---|
| Thm. 3, transfer theorem with consensus-simplicity | `invar_dr_simple_on_dist_imp_quotient_dr` (and `…_winners`) | `Quotient_Distance_Rationalization_Ext` |
| Lemma 5, equivariance passes to the quotient | `pass_to_quotient_equivar'` | `Relation_Quotients_Ext` |
| Thm. 6, lifting theorem for DR rules | `equivar_dr_simple_dist_imp_equivar_quotient_dr` | `Quotient_Distance_Rationalization_Symmetry` |
| Thm. 11, quotient Kemeny rule | `kemeny_rule⇩𝒬_is_quotient_dr`, `kemeny_rule⇩𝒬_winners` | `Quotient_Kemeny_Rule` |
| Thm. 18, neutrality lifts to the quotient function | `neutrality_lifts_to_anon_hom_quotient` | `Quotient_Voting_Symmetry` |

## Structure

`theories/` is one Isabelle session, `Quotient_DR_Voting_Rules`, with the VMCF session as parent. The five `_Ext` theories are meant as extensions of their imports. The other four theories are new.

| Theory | Content |
|---|---|
| `Norm_Ext` | the normalized ℓ¹ norm `l_one_avg` |
| `Votewise_Distance_Ext` | votewise distance with `l_one_avg` = ℓ¹ votewise distance / number of voters |
| `Relation_Quotients_Ext` | compatible maps send classes to classes; equivariance passes to quotient functions |
| `Election_Quotients_Ext` | the anonymity–homogeneity relation is an equivalence on `elections_𝒜 C` |
| `Quotient_Distance_Rationalization_Ext` | consensus-simplicity `simple_on`; the transfer theorem with this weaker premise |
| `Quotient_Voting_Symmetry` | stabilizer of a candidate set; neutrality, reversal symmetry and anonymity on the quotient |
| `Quotient_Distance_Rationalization_Symmetry` | the lifting theorem |
| `Quotient_Swapwise_Rules_Helpers` | strong unanimity over a fixed candidate set, the counting formula for the normalized swap distance, and the lemmas that discharge the transfer premises for it |
| `Quotient_Kemeny_Rule` | the quotient Kemeny rule and Theorem 11 |

In `Quotient_Distance_Rationalization_Ext`: Some theorems were taken from the original repository with minor adaptions.
Precisely, Appelhagen's transfer theorems
`invar_dr_simple_dist_imp_quotient_dr` and `…_winners` are stated a second
time under the names with `simple_on`, with the premise `simple r X d` weakened to
`simple_on (elections_𝒦 C) r X d`. The proofs are her proofs with small changes at
the point where the premise is used (marked in the file). Original results in
`upstream/` are untouched and follow from the new versions by `simple_imp_simple_on`.

## Build

Needed: Isabelle2025-2, the AFP release for it (the VMCF imports `List-Index` and
`Collections`), and LaTeX, because the VMCF session generates its documentation.

```
git clone --recurse-submodules https://github.com/rosabauer/quotient-dr-voting-rules.git
cd quotient-dr-voting-rules
isabelle build -d . -b -v Quotient_DR_Voting_Rules
```

This builds the VMCF session from the submodule first, which takes a while, then
the nine theories, which take about two minutes. For jEdit, from the same directory:

```
isabelle jedit -d . -l Verified_Voting_Rule_Construction theories/Quotient_Kemeny_Rule.thy
```

The theories were developed inside a copy of the VMCF,
<https://github.com/rosabauer/vvrc-thesis> (branch `refactor`) and moved here later.

## Citing

```bibtex
@thesis{Bauer2026,
  author = {Rosa Bauer},
  title  = {Verified Quotient Reasoning for Distance-Rationalizable Voting Rules},
  type   = {Bachelor's thesis},
  school = {Ludwig-Maximilians-Universit{\"a}t M{\"u}nchen},
  year   = {2026}
}
```
