# Verified Quotient Reasoning for Distance-Rationalizable Voting Rules on the Simplex

Isabelle/HOL theories of the Bachelor's thesis by Rosa Bauer (LMU Munich, 2026;
supervisor Prof. Dr. Jasmin Blanchette, advisor Dr. Michael Kirsten).

The theories extend the *Verified Voting Rule Construction* framework (VVRC,
<https://github.com/VeriVote/verifiedVotingRuleConstruction>). The framework is
included unchanged as the git submodule `upstream/`, pinned to commit `1d4225f`.
Everything written for the thesis is in `theories/`; nothing in `upstream/` is
modified.

## Layout

```
ROOTS               Isabelle session catalogue: lists upstream/theories and theories
upstream/           git submodule: VVRC at commit 1d4225f (parent session)
theories/ROOT       the session Quotient_DR_Voting_Rules, built on top of the VVRC session
theories/*.thy      the nine theories of the thesis
```

## What is where

Extensions of upstream theories. Each file imports the upstream theory it
extends and contains only what the thesis adds to it.

| Theory | Extends | Contents |
|---|---|---|
| `Norm_Ext` | `Norm` | the averaged norm `l_one_avg` |
| `Votewise_Distance_Ext` | `Votewise_Distance` | `dist_avg_norm_eq_normalized_dist`: votewise distance with `l_one_avg` is the `l_one` distance divided by the number of voters |
| `Relation_Quotients_Ext` | `Relation_Quotients` | `quotient_subset`; equivariance passes to the quotient (`pass_to_quotient_equivar`, `pass_to_quotient_equivar'`) and compatible actions map classes to classes (`rel_compat_imp_act_maps_classes`, `act_maps_classes_into_quotient`) |
| `Election_Quotients_Ext` | `Election_Quotients` | `anon_hom_equiv`: the anonymity-homogeneity relation is an equivalence on the elections over a fixed alternative set |
| `Quotient_Distance_Rationalization_Ext` | `Quotient_Distance_Rationalization` | consensus-simplicity `simple_on` with `inner_inf_const_imp_simple_on`, `simple_imp_simple_on`; the transfer theorems `invar_dr_simple_on_dist_imp_quotient_dr_winners` and `invar_dr_simple_on_dist_imp_quotient_dr`, which restate the upstream theorems `invar_dr_simple_dist_imp_quotient_dr_winners` and `invar_dr_simple_dist_imp_quotient_dr` with the weaker premise `simple_on (elections_K C) r X d` in place of `simple r X d`. Their proofs are A. Appelhagen's upstream proofs, changed only where the premise is used |

New theories.

| Theory | Contents |
|---|---|
| `Quotient_Voting_Symmetry` | neutrality, reversal symmetry and anonymity on the anonymity-homogeneity quotient: stabilizer, compatibility lemmas, `neutrality_lifts_to_anon_hom_quotient`, `anon_acts_trivially_on_quotient` |
| `Quotient_Distance_Rationalization_Symmetry` | the lifting theorem `equivar_dr_simple_dist_imp_equivar_quotient_dr` |
| `Quotient_Swapwise_Rules_Helpers` | strong unanimity over a fixed candidate set, the counting formula for the normalized swap distance, consensus-simplicity and score invariance of `votewise_distance swap l_one_avg` |
| `Quotient_Kemeny_Rule` | the quotient Kemeny rule and `kemeny_rule_Q_is_quotient_dr`, `kemeny_rule_Q_winners` |

## Building

Requirements: Isabelle2025-2 (the version the pinned upstream commit targets) and a
LaTeX installation, since the upstream session builds its PDF document.

```
git clone --recurse-submodules https://github.com/rosabauer/quotient-dr-voting-rules.git
cd quotient-dr-voting-rules
isabelle build -d . -b -v Quotient_DR_Voting_Rules
```

The build first produces the parent session `Verified_Voting_Rule_Construction`
from `upstream/`, then checks the nine thesis theories. For interactive use:

```
isabelle jedit -d . -l Verified_Voting_Rule_Construction theories/Quotient_Kemeny_Rule.thy
```

If the repository was cloned without `--recurse-submodules`, run
`git submodule update --init` first.

## Development history

The theories were developed inside a working copy of the upstream repository,
<https://github.com/rosabauer/vvrc-thesis> (branch `refactor`), where the
additions sit at the end of the extended upstream files. This repository is the
cleaned-up result: the same content, separated from upstream.
