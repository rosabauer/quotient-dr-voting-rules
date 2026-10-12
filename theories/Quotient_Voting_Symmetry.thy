(*  File:  theories/Compositional_Structures/Basic_Modules/Component_Types/
           Quotients/Quotient_Voting_Symmetry.thy
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Symmetry of Quotient Voting Rules\<close>

theory Quotient_Voting_Symmetry
  imports "Verified_Voting_Rule_Construction.Electoral_Module"
          Election_Quotients_Ext
          Relation_Quotients_Ext
begin

text \<open>
  This theory transfers the symmetry properties of electoral modules from
  well-formed elections to the quotient of the elections over a fixed
  alternative set \<open>A\<close> under the anonymity-homogeneity relation. For
  neutrality and reversal symmetry it establishes the premises of
  \<open>pass_to_quotient_equivar'\<close>: the transformations are compatible with the
  relation, they are invertible on \<open>elections_\<A> A\<close>, and the property on
  well-formed elections restricts to an equivariance on \<open>elections_\<A> A\<close>.
  For neutrality, the transformations have to be restricted to the
  stabilizer of \<open>A\<close>, since only those keep the alternative set fixed; the
  main result is \<open>neutrality_lifts_to_anon_hom_quotient\<close>. Voter renamings
  act trivially on the quotient (\<open>anon_acts_trivially_on_quotient\<close>), so
  anonymity is built into the quotient rather than being a symmetry of it.
\<close>

subsection \<open>The Alternative-Set Stabilizer\<close>

text \<open>
  In group theory, stabilizers are restrictions on a set 
  that state that an operation never maps the elements of a set, 
  in this case the election alternatives, outside of the set,
  but only switches them bijectively within the set.
  They are  the neutrality symmetries that descend to
  the anon-hom quotient over A (and thus to the simplex).
\<close>

definition alt_stabilizer :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) set" where
  "alt_stabilizer A = {\<pi> \<in> carrier bijection\<^sub>\<A>\<^sub>\<G>. \<pi> ` A = A}"

lemma alt_stabilizer_rewrite:
  fixes A :: "'a set"
  shows "alt_stabilizer A = {\<pi>. bij \<pi> \<and> \<pi> ` A = A}"
  unfolding alt_stabilizer_def bijection\<^sub>\<A>\<^sub>\<G>_def
  using rewrite_carrier
  by blast

lemma \<phi>_neutral_apply:
  fixes
    \<X> :: "('a, 'v) Election set" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    E :: "('a, 'v) Election"
  assumes "E \<in> \<X>"
  shows "\<phi>_neutral \<X> \<pi> E = alts_rename \<pi> E"
  by (simp only: \<phi>_neutral.simps extensional_continuation.simps if_P[OF assms])
  
subsection \<open>Auxiliary Lemmas on Renaming\<close>

lemma rel_rename_id: "rel_rename id = id"
proof
  fix r :: "'a rel"
  show "rel_rename id r = id r"
    unfolding rel_rename.simps
    by force
qed

lemma rel_rename_empty: "rel_rename \<pi> {} = {}"
  unfolding rel_rename.simps
  by blast

lemma alts_rename_id:
  fixes E :: "('a, 'v) Election"
  shows "alts_rename id E = E"
  by (cases E) (simp add: rel_rename_id)

lemma bij_the_inv_comp:
  fixes \<pi> :: "'a \<Rightarrow> 'a"
  assumes bij_\<pi>: "bij \<pi>"
  shows
    "the_inv \<pi> \<circ> \<pi> = id" and
    "\<pi> \<circ> the_inv \<pi> = id"
proof -
  show "the_inv \<pi> \<circ> \<pi> = id"
    using bij_\<pi>
    by (simp add: fun_eq_iff bij_is_inj the_inv_f_f)
  show "\<pi> \<circ> the_inv \<pi> = id"
  proof
    fix x :: "'a"
    show "(\<pi> \<circ> the_inv \<pi>) x = id x"
      using bij_\<pi> f_the_inv_into_f_bij_betw
      by fastforce 
  qed
qed

lemma alt_stabilizer_the_inv_closed:
  fixes
    A :: "'a set" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes "\<pi> \<in> alt_stabilizer A"
  shows "the_inv \<pi> \<in> alt_stabilizer A"
proof -
  have bij_\<pi>: "bij \<pi>" and img_A: "\<pi> ` A = A"
    using assms
    unfolding alt_stabilizer_rewrite
    by simp_all
  have "bij (the_inv \<pi>)"
    using bij_\<pi> bij_betw_the_inv_into
    by blast
  moreover have "the_inv \<pi> ` A = A"
  proof -
    have "the_inv \<pi> ` A = the_inv \<pi> ` (\<pi> ` A)"
      using img_A
      by simp
    also have "\<dots> = (the_inv \<pi> \<circ> \<pi>) ` A"
      by (simp add: image_comp)
    also have "\<dots> = A"
      using bij_the_inv_comp[OF bij_\<pi>]
      by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis
    using alt_stabilizer_rewrite
    by blast
qed

subsection \<open>Stabilizer Renaming Preserves Fixed-Alternative Elections\<close>

lemma stabilizer_preserves_elections_\<A>:
  fixes
    A :: "'a set" and
    \<pi> :: "'a \<Rightarrow> 'a" and
    E :: "('a, 'v) Election"
  assumes
    stab: "\<pi> \<in> alt_stabilizer A" and
    elect: "E \<in> elections_\<A> A"
  shows "alts_rename \<pi> E \<in> elections_\<A> A"
proof -
  have bij_\<pi>: "bij \<pi>" and img_A: "\<pi> ` A = A"
    using assms
    unfolding alt_stabilizer_rewrite
    by simp_all
  obtain B :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
    E_eq: "E = (B, V, p)"
    using prod_cases3
    by blast
  have B_eq_A: "B = A" and
       fin_V: "finite V" and
       def_prof: "\<forall> v. v \<notin> V \<longrightarrow> p v = {}" and
       wf: "(B, V, p) \<in> well_formed_elections"
    using elect E_eq
    unfolding elections_\<A>.simps
    by auto
  have ren_eq: "(\<pi> ` B, V, rel_rename \<pi> \<circ> p) = alts_rename \<pi> (B, V, p)"
    by simp
  have wf': "(\<pi> ` B, V, rel_rename \<pi> \<circ> p) \<in> well_formed_elections"
    using alternatives_rename_sound[OF bij_\<pi> wf ren_eq] .
   have img_B: "\<pi> ` B = A"
    using B_eq_A img_A
    by simp
  have def_prof': "\<forall> v. v \<notin> V \<longrightarrow> (rel_rename \<pi> \<circ> p) v = {}"
    using def_prof rel_rename_empty
    by simp
  have ren_E: "alts_rename \<pi> E = (\<pi> ` B, V, rel_rename \<pi> \<circ> p)"
    unfolding E_eq
    by simp
  show ?thesis
    unfolding ren_E elections_\<A>.simps
    using wf' img_B fin_V def_prof'
    by simp
qed

subsection \<open>Ballot Maps and Vote Fractions\<close>

text \<open>
  All transformations considered below leave the voters untouched and act on
  the ballots by a map \<open>\<tau>\<close> with a two-sided inverse \<open>\<sigma>\<close>. Such a map only
  permutes which ballot has which vote count, so vote counts and vote fractions
  are carried along, and related elections stay related.
\<close>

lemma vote_count_profile_map:
  fixes
    \<tau> \<sigma> :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation" and
    q :: "'a Preference_Relation" and
    E E' :: "('a, 'v) Election"
  assumes
    inv_\<sigma>\<tau>: "\<And> s. \<sigma> (\<tau> s) = s" and
    inv_\<tau>\<sigma>: "\<And> s. \<tau> (\<sigma> s) = s" and
    voters: "voters_\<E> E' = voters_\<E> E" and
    prof: "profile_\<E> E' = \<tau> \<circ> profile_\<E> E"
  shows "vote_count q E' = vote_count (\<sigma> q) E"
proof -
  have set_eq: "{v \<in> voters_\<E> E. \<tau> (profile_\<E> E v) = q} = {v \<in> voters_\<E> E. profile_\<E> E v = \<sigma> q}"
  proof (rule Collect_cong)
    fix v :: "'v"
    show "(v \<in> voters_\<E> E \<and> \<tau> (profile_\<E> E v) = q) = (v \<in> voters_\<E> E \<and> profile_\<E> E v = \<sigma> q)"
      using inv_\<sigma>\<tau> inv_\<tau>\<sigma>
      by metis
  qed
  have "vote_count q E' = card {v \<in> voters_\<E> E. \<tau> (profile_\<E> E v) = q}"
    unfolding vote_count.simps voters prof
    by (simp add: comp_def)
  also have "\<dots> = card {v \<in> voters_\<E> E. profile_\<E> E v = \<sigma> q}"
    by (simp only: set_eq)
  also have "\<dots> = vote_count (\<sigma> q) E"
    by (simp only: vote_count.simps)
  finally show ?thesis .
qed

lemma vote_fraction_profile_map:
  fixes
    \<tau> \<sigma> :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation" and
    q :: "'a Preference_Relation" and
    E E' :: "('a, 'v) Election"
  assumes
    inv_\<sigma>\<tau>: "\<And> s. \<sigma> (\<tau> s) = s" and
    inv_\<tau>\<sigma>: "\<And> s. \<tau> (\<sigma> s) = s" and
    voters: "voters_\<E> E' = voters_\<E> E" and
    prof: "profile_\<E> E' = \<tau> \<circ> profile_\<E> E"
  shows "vote_fraction q E' = vote_fraction (\<sigma> q) E"
  by (simp only: vote_fraction.simps voters vote_count_profile_map[OF inv_\<sigma>\<tau> inv_\<tau>\<sigma> voters prof])

lemma profile_map_compat:
  fixes
    A :: "'a set" and
    F :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election" and
    \<tau> \<sigma> :: "'a Preference_Relation \<Rightarrow> 'a Preference_Relation" and
    E E' :: "('a, 'v) Election"
  assumes
    inv_\<sigma>\<tau>: "\<And> s. \<sigma> (\<tau> s) = s" and
    inv_\<tau>\<sigma>: "\<And> s. \<tau> (\<sigma> s) = s" and
    voters: "\<And> E. voters_\<E> (F E) = voters_\<E> E" and
    prof: "\<And> E. profile_\<E> (F E) = \<tau> \<circ> profile_\<E> E" and
    closed: "\<And> E. E \<in> elections_\<A> A \<Longrightarrow> F E \<in> elections_\<A> A" and
    rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "(F E, F E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
proof -
  have E_in: "E \<in> elections_\<A> A" and
       E'_in: "E' \<in> elections_\<A> A" and
       fin_eq: "finite (voters_\<E> E) = finite (voters_\<E> E')" and
       frac_eq: "\<forall> q. vote_fraction q E = vote_fraction q E'"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have "\<forall> q. vote_fraction q (F E) = vote_fraction q (F E')"
    using vote_fraction_profile_map[OF inv_\<sigma>\<tau> inv_\<tau>\<sigma> voters prof] frac_eq
    by metis
  moreover have "finite (voters_\<E> (F E)) = finite (voters_\<E> (F E'))"
    using fin_eq
    unfolding voters .
  ultimately show ?thesis
    using closed[OF E_in] closed[OF E'_in]
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast
qed

subsection \<open>Vote Counts and Fractions under Renaming\<close>

text \<open>
  Renaming the alternatives with a bijection \<pi> permutes the ballots:
  the voters casting ballot r after renaming are exactly the voters casting
  the preimage ballot before renaming. Voters are untouched.
\<close>

lemma rel_rename_the_inv_left:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    q :: "'a Preference_Relation"
  assumes bij_\<pi>: "bij \<pi>"
  shows "rel_rename (the_inv \<pi>) (rel_rename \<pi> q) = q"
proof -
  have "rel_rename (the_inv \<pi>) \<circ> rel_rename \<pi> = id"
    using rel_rename_compositional[of "the_inv \<pi>" \<pi>]
          bij_the_inv_comp(1)[OF bij_\<pi>] rel_rename_id
    by metis
  thus ?thesis
    by (metis comp_apply id_apply)
qed

lemma rel_rename_the_inv_right:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    q :: "'a Preference_Relation"
  assumes bij_\<pi>: "bij \<pi>"
  shows "rel_rename \<pi> (rel_rename (the_inv \<pi>) q) = q"
proof -
  have "rel_rename \<pi> \<circ> rel_rename (the_inv \<pi>) = id"
    using rel_rename_compositional[of \<pi> "the_inv \<pi>"]
          bij_the_inv_comp(2)[OF bij_\<pi>] rel_rename_id
    by metis
  thus ?thesis
    by (metis comp_apply id_apply)
qed

lemma alts_rename_voters:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    E :: "('a, 'v) Election"
  shows "voters_\<E> (alts_rename \<pi> E) = voters_\<E> E"
  by simp

lemma alts_rename_profile:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    E :: "('a, 'v) Election"
  shows "profile_\<E> (alts_rename \<pi> E) = rel_rename \<pi> \<circ> profile_\<E> E"
  by simp

lemma vote_count_alts_rename:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    r :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_\<pi>: "bij \<pi>"
  shows "vote_count r (alts_rename \<pi> E) = vote_count (rel_rename (the_inv \<pi>) r) E"
  by (rule vote_count_profile_map[OF rel_rename_the_inv_left[OF bij_\<pi>]
        rel_rename_the_inv_right[OF bij_\<pi>] alts_rename_voters alts_rename_profile])

lemma vote_fraction_alts_rename:
  fixes
    \<pi> :: "'a \<Rightarrow> 'a" and
    r :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_\<pi>: "bij \<pi>"
  shows "vote_fraction r (alts_rename \<pi> E) = vote_fraction (rel_rename (the_inv \<pi>) r) E"
  by (rule vote_fraction_profile_map[OF rel_rename_the_inv_left[OF bij_\<pi>]
        rel_rename_the_inv_right[OF bij_\<pi>] alts_rename_voters alts_rename_profile])

subsection \<open>Neutrality Action Descends to Anon-Hom Classes\<close>


text \<open>
  Compatibility: stabilizer renamings map anonhom-related
  elections to related elections, since they permute vote fractions over
  ballots and leave the voters unchanged.
\<close>

lemma \<phi>_neutral_elections_\<A>_compat:
  fixes A :: "'a set"
  shows "\<forall> \<pi> \<in> alt_stabilizer A. \<forall> E E'.
      (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A) \<longrightarrow>
        (\<phi>_neutral (elections_\<A> A) \<pi> E, \<phi>_neutral (elections_\<A> A) \<pi> E')
          \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
proof (intro ballI allI impI)
  fix
    \<pi> :: "'a \<Rightarrow> 'a" and
    E E' :: "('a, 'v) Election"
  assume
    stab: "\<pi> \<in> alt_stabilizer A" and
    rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  have bij_\<pi>: "bij \<pi>"
    using stab
    unfolding alt_stabilizer_rewrite
    by simp
  have E_in: "E \<in> elections_\<A> A" and E'_in: "E' \<in> elections_\<A> A"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have "(alts_rename \<pi> E, alts_rename \<pi> E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    by (rule profile_map_compat[OF rel_rename_the_inv_left[OF bij_\<pi>]
          rel_rename_the_inv_right[OF bij_\<pi>] alts_rename_voters alts_rename_profile
          stabilizer_preserves_elections_\<A>[OF stab] rel])
  thus "(\<phi>_neutral (elections_\<A> A) \<pi> E, \<phi>_neutral (elections_\<A> A) \<pi> E')
          \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    unfolding \<phi>_neutral_apply[OF E_in] \<phi>_neutral_apply[OF E'_in] .
qed

text \<open>
  Invertibility in the stabilizer: on elections over A, the renaming by
  \<open>the_inv \<pi>\<close> undoes the renaming by \<pi> and vice versa.
\<close>

lemma \<phi>_neutral_elections_\<A>_invertible:
  fixes A :: "'a set"
  shows "\<forall> \<pi> \<in> alt_stabilizer A. \<exists> \<sigma> \<in> alt_stabilizer A. \<forall> E \<in> elections_\<A> A.
      \<phi>_neutral (elections_\<A> A) \<sigma> (\<phi>_neutral (elections_\<A> A) \<pi> E) = E
    \<and> \<phi>_neutral (elections_\<A> A) \<pi> (\<phi>_neutral (elections_\<A> A) \<sigma> E) = E"
proof (intro ballI)
  fix \<pi> :: "'a \<Rightarrow> 'a"
  assume stab_\<pi>: "\<pi> \<in> alt_stabilizer A"
  hence stab_\<sigma>: "the_inv \<pi> \<in> alt_stabilizer A"
    using alt_stabilizer_the_inv_closed
    by blast
   have bij_\<pi>: "bij \<pi>"
    using stab_\<pi>
    unfolding alt_stabilizer_rewrite
    by simp
  have "\<forall> E \<in> elections_\<A> A.
      \<phi>_neutral (elections_\<A> A) (the_inv \<pi>) (\<phi>_neutral (elections_\<A> A) \<pi> E) = E
    \<and> \<phi>_neutral (elections_\<A> A) \<pi> (\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) E) = E"
  proof (intro ballI)
    fix E :: "('a, 'v) Election"
    assume E_in: "E \<in> elections_\<A> A"
    have img_\<pi>: "alts_rename \<pi> E \<in> elections_\<A> A"
      using stabilizer_preserves_elections_\<A> stab_\<pi> E_in
      by blast
    have img_\<sigma>: "alts_rename (the_inv \<pi>) E \<in> elections_\<A> A"
      using stabilizer_preserves_elections_\<A> stab_\<sigma> E_in
      by blast
        have eq_1:
      "\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) (\<phi>_neutral (elections_\<A> A) \<pi> E) = E"
    proof -
      have "\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) (\<phi>_neutral (elections_\<A> A) \<pi> E)
          = alts_rename (the_inv \<pi>) (alts_rename \<pi> E)"
        by (simp only: \<phi>_neutral_apply[OF E_in] \<phi>_neutral_apply[OF img_\<pi>])
      also have "\<dots> = alts_rename (the_inv \<pi> \<circ> \<pi>) E"
        by (metis alts_rename_compositional comp_apply)
      also have "\<dots> = E"
        unfolding bij_the_inv_comp(1)[OF bij_\<pi>]
        by (rule alts_rename_id)
      finally show ?thesis .
    qed
    have eq_2:
      "\<phi>_neutral (elections_\<A> A) \<pi> (\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) E) = E"
    proof -
      have "\<phi>_neutral (elections_\<A> A) \<pi> (\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) E)
          = alts_rename \<pi> (alts_rename (the_inv \<pi>) E)"
        by (simp only: \<phi>_neutral_apply[OF E_in] \<phi>_neutral_apply[OF img_\<sigma>])
      also have "\<dots> = alts_rename (\<pi> \<circ> the_inv \<pi>) E"
        by (metis alts_rename_compositional comp_apply)
      also have "\<dots> = E"
        unfolding bij_the_inv_comp(2)[OF bij_\<pi>]
        by (rule alts_rename_id)
      finally show ?thesis .
    qed
    show
      "\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) (\<phi>_neutral (elections_\<A> A) \<pi> E) = E
      \<and> \<phi>_neutral (elections_\<A> A) \<pi> (\<phi>_neutral (elections_\<A> A) (the_inv \<pi>) E) = E"
      using eq_1 eq_2
      by blast
qed
  thus "\<exists> \<sigma> \<in> alt_stabilizer A. \<forall> E \<in> elections_\<A> A.
      \<phi>_neutral (elections_\<A> A) \<sigma> (\<phi>_neutral (elections_\<A> A) \<pi> E) = E
    \<and> \<phi>_neutral (elections_\<A> A) \<pi> (\<phi>_neutral (elections_\<A> A) \<sigma> E) = E"
    using stab_\<sigma>
    by blast
qed

subsection \<open>Transfer of Neutrality to the Stabilizer Action\<close>

text \<open>
  A rule that is neutral on all well-formed elections is in particular
  equivariant on \<open>elections_\<A> A\<close> under the stabilizer of A, with the action
  parameterized by \<open>elections_\<A> A\<close> (the two continuations of
  \<open>alts_rename\<close> match up on \<open>elections_\<A> A\<close>).
\<close>

lemma (in result_properties) neutrality_in_stabilizer:
  fixes
    m :: "('a, 'v, 'b Result) Electoral_Module" and
    A :: "'a set"
  assumes "neutrality_in well_formed_elections m"
  shows "is_symmetry (fun\<^sub>\<E> m)
      (action_induced_equivariance (alt_stabilizer A) (elections_\<A> A)
          (\<phi>_neutral (elections_\<A> A)) (result_action \<psi>))"
proof -
  have pairs_sub:
    "{(\<phi>_neutral well_formed_elections z, result_action \<psi> z) | z.
          z \<in> alt_stabilizer A}
      \<subseteq> {(\<phi>_neutral well_formed_elections z, result_action \<psi> z) | z.
          z \<in> carrier bijection\<^sub>\<A>\<^sub>\<G>}"
    unfolding alt_stabilizer_def
    by blast
  have sub_dom: "elections_\<A> A \<subseteq> well_formed_elections"
    unfolding elections_\<A>.simps
    by blast
  from assms have
    "is_symmetry (fun\<^sub>\<E> m) (Equivariance well_formed_elections
        {(\<phi>_neutral well_formed_elections z, result_action \<psi> z) | z.
            z \<in> carrier bijection\<^sub>\<A>\<^sub>\<G>})"
    unfolding neutrality_in.simps action_induced_equivariance_def
    by simp
  hence "is_symmetry (fun\<^sub>\<E> m) (Equivariance well_formed_elections
      {(\<phi>_neutral well_formed_elections z, result_action \<psi> z) | z.
          z \<in> alt_stabilizer A})"
    using equivar_under_subset' pairs_sub
    by blast
  hence "is_symmetry (fun\<^sub>\<E> m) (Equivariance (elections_\<A> A)
      {(\<phi>_neutral well_formed_elections z, result_action \<psi> z) | z.
          z \<in> alt_stabilizer A})"
    using equivar_under_subset sub_dom
    by blast
  hence wfe_act: "is_symmetry (fun\<^sub>\<E> m)
      (action_induced_equivariance (alt_stabilizer A) (elections_\<A> A)
          (\<phi>_neutral well_formed_elections) (result_action \<psi>))"
    unfolding action_induced_equivariance_def
    by simp
  moreover have "\<forall> \<pi> \<in> alt_stabilizer A. \<forall> E \<in> elections_\<A> A.
      \<phi>_neutral well_formed_elections \<pi> E = \<phi>_neutral (elections_\<A> A) \<pi> E"
    using sub_dom
    by auto
  ultimately show ?thesis
    using equivar_ind_by_act_coincide
    by blast
qed

subsection \<open>Theorem: Neutrality Lifts to the Quotient\<close>

text \<open>
  If an electoral module is invariant under the
  anon-hom relation on elections over A (so it induces a
  well-defined quotient rule via \<pi>\<Q>) and neutral on well-formed elections,
  then the quotient rule is equivariant on the anon-hom classes
  with the stabilizer of A, ie neutral as a rule on the quotient
  (so also on the simplex).
\<close>

theorem (in result_properties) neutrality_lifts_to_anon_hom_quotient:
  fixes
    m :: "('a, 'v, 'b Result) Electoral_Module" and
    A :: "'a set"
  assumes
    invar_m: "is_symmetry (fun\<^sub>\<E> m)
        (Invariance (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)))" and
    neutral_m: "neutrality_in well_formed_elections m"
  shows "is_symmetry (\<pi>\<^sub>\<Q> (fun\<^sub>\<E> m))
      (action_induced_equivariance (alt_stabilizer A)
          (elections_\<A> A // anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
          (set_action (\<phi>_neutral (elections_\<A> A))) (result_action \<psi>))"
  using pass_to_quotient_equivar'[OF
          anon_hom_equiv
          invar_m
          neutrality_in_stabilizer[OF neutral_m]
          \<phi>_neutral_elections_\<A>_compat
          \<phi>_neutral_elections_\<A>_invertible] .

subsection \<open>Auxiliary Lemmas on Ballot Reversal\<close>

text \<open>
  Reversing all ballots is the map \<open>rel_app g\<close> for g in the two-element
  group \<open>reversal\<^sub>\<G>\<close> = {reverse ballots, do nothing}. The lemmas below
  record the obvious computation rules: doing nothing changes nothing,
  two applications compose, and an election
  (alternatives, voters, ballots) transforms as expected.
\<close>

lemma rel_app_id:
  fixes E :: "('a, 'v) Election"
  shows "rel_app id E = E"
  by (cases E) simp

lemma rel_app_comp:
  fixes
    f f' :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'v) Election"
  shows "rel_app f (rel_app f' E) = rel_app (f \<circ> f') E"
  by (cases E) (simp add: comp_assoc)

lemma rel_app_alts:
  fixes
    f :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'v) Election"
  shows "alternatives_\<E> (rel_app f E) = alternatives_\<E> E"
  by (cases E) simp

lemma rel_app_voters:
  fixes
    f :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'v) Election"
  shows "voters_\<E> (rel_app f E) = voters_\<E> E"
  by (cases E) simp

lemma rel_app_profile:
  fixes
    f :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'v) Election"
  shows "profile_\<E> (rel_app f E) = f \<circ> profile_\<E> E"
  by (cases E) simp

lemma reverse_rel_empty: "reverse_rel {} = {}"
  unfolding reverse_rel.simps
  by blast

lemma \<phi>_reverse_apply:
  fixes
    \<X> :: "('a, 'v) Election set" and
    g :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'v) Election"
  assumes "E \<in> \<X>"
  shows "\<phi>_reverse \<X> g E = rel_app g E"
  by (simp only: \<phi>_reverse.simps extensional_continuation.simps if_P[OF assms])

lemma reversal_carrier_elems:
  fixes g :: "'a rel \<Rightarrow> 'a rel"
  assumes "g \<in> carrier reversal\<^sub>\<G>"
  shows "g = reverse_rel \<or> g = id"
  using assms
  unfolding reversal\<^sub>\<G>_def
  by auto 

lemma reversal_carrier_invol:
  fixes g :: "'a rel \<Rightarrow> 'a rel"
  assumes "g \<in> carrier reversal\<^sub>\<G>"
  shows "g \<circ> g = id"
  using reversal_carrier_elems[OF assms] reverse_reverse_id
  by fastforce 

lemma reversal_carrier_invol_pointwise:
  fixes
    g :: "'a rel \<Rightarrow> 'a rel" and
    s :: "'a rel"
  assumes "g \<in> carrier reversal\<^sub>\<G>"
  shows "g (g s) = s"
  using reversal_carrier_invol[OF assms] comp_apply id_apply
  by metis

lemma reversal_carrier_empty:
  fixes g :: "'a rel \<Rightarrow> 'a rel"
  assumes "g \<in> carrier reversal\<^sub>\<G>"
  shows "g {} = {}"
  using reversal_carrier_elems[OF assms] reverse_rel_empty
  by fastforce 

subsection \<open>Reversal Action on Anon-Hom Classes\<close>

text \<open>
  Reversing ballots keeps an election over A inside the elections over A:
  the alternatives and voters are untouched, a reversed linear order over A
  is again a linear order over A, and empty ballots stay empty.
  The well-formedness part is inherited from the existing group action
  of \<open>reversal\<^sub>\<G>\<close> on all well-formed elections.
\<close>

lemma reversal_preserves_elections_\<A>:
  fixes
    A :: "'a set" and
    g :: "'a rel \<Rightarrow> 'a rel" and
    E :: "('a, 'v) Election"
  assumes
    g_in: "g \<in> carrier reversal\<^sub>\<G>" and
    elect: "E \<in> elections_\<A> A"
  shows "rel_app g E \<in> elections_\<A> A"
proof -
  have wfe_E: "E \<in> well_formed_elections" and
       alt_E: "alternatives_\<E> E = A" and
       fin_E: "finite (voters_\<E> E)" and
       def_E: "\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {}"
    using elect
    unfolding elections_\<A>.simps
    by auto
  have "\<phi>_reverse well_formed_elections g E \<in> well_formed_elections"
    using \<phi>_reverse_action.element_image g_in wfe_E
    by metis
  moreover have "\<phi>_reverse well_formed_elections g E = rel_app g E"
    by (rule \<phi>_reverse_apply[OF wfe_E])
  ultimately have wf': "rel_app g E \<in> well_formed_elections"
    by simp
  have alts': "alternatives_\<E> (rel_app g E) = A"
    by (simp only: rel_app_alts alt_E)
  have fin': "finite (voters_\<E> (rel_app g E))"
    using fin_E
    by (cases E) simp
  have def': "\<forall> v. v \<notin> voters_\<E> (rel_app g E) \<longrightarrow> profile_\<E> (rel_app g E) v = {}"
  proof (intro allI impI)
    fix v :: "'v"
    assume "v \<notin> voters_\<E> (rel_app g E)"
    hence "profile_\<E> E v = {}"
      using def_E
      by (cases E) simp
    thus "profile_\<E> (rel_app g E) v = {}"
      using reversal_carrier_empty[OF g_in]
      by (cases E) simp
  qed
  show ?thesis
    unfolding elections_\<A>.simps
    using wf' alts' fin' def'
    by blast
qed

text \<open>
  Counting: the voters who cast ballot q after all ballots are reversed
  are exactly the voters who cast the reversed ballot before, since
  reversing twice is doing nothing. The voter set itself stays the same,
  so the same holds for vote fractions.
\<close>

lemma vote_count_rel_app:
  fixes
    g :: "'a rel \<Rightarrow> 'a rel" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes g_in: "g \<in> carrier reversal\<^sub>\<G>"
  shows "vote_count q (rel_app g E) = vote_count (g q) E"
  by (rule vote_count_profile_map[where \<sigma> = g and \<tau> = g, OF reversal_carrier_invol_pointwise[OF g_in]
        reversal_carrier_invol_pointwise[OF g_in] rel_app_voters rel_app_profile])

lemma vote_fraction_rel_app:
  fixes
    g :: "'a rel \<Rightarrow> 'a rel" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes g_in: "g \<in> carrier reversal\<^sub>\<G>"
  shows "vote_fraction q (rel_app g E) = vote_fraction (g q) E"
  by (rule vote_fraction_profile_map[where \<sigma> = g and \<tau> = g, OF reversal_carrier_invol_pointwise[OF g_in]
        reversal_carrier_invol_pointwise[OF g_in] rel_app_voters rel_app_profile])

text \<open>
  Compatibility: if two elections have the same vote fractions, then so do
  their reversed versions, since reversal only permutes which ballot has
  which fraction. So reversal maps related elections to related elections.
\<close>

lemma \<phi>_reverse_elections_\<A>_compat:
  fixes A :: "'a set"
  shows "\<forall> g \<in> carrier reversal\<^sub>\<G>. \<forall> E E'.
      (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A) \<longrightarrow>
        (\<phi>_reverse (elections_\<A> A) g E, \<phi>_reverse (elections_\<A> A) g E')
          \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
proof (intro ballI allI impI)
  fix
    g :: "'a rel \<Rightarrow> 'a rel" and
    E E' :: "('a, 'v) Election"
  assume
    g_in: "g \<in> carrier reversal\<^sub>\<G>" and
    rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  have E_in: "E \<in> elections_\<A> A" and E'_in: "E' \<in> elections_\<A> A"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have "(rel_app g E, rel_app g E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    by (rule profile_map_compat[OF reversal_carrier_invol_pointwise[OF g_in]
          reversal_carrier_invol_pointwise[OF g_in] rel_app_voters rel_app_profile
          reversal_preserves_elections_\<A>[OF g_in] rel])
  thus "(\<phi>_reverse (elections_\<A> A) g E, \<phi>_reverse (elections_\<A> A) g E')
          \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    unfolding \<phi>_reverse_apply[OF E_in] \<phi>_reverse_apply[OF E'_in] .
qed

text \<open>
  Invertibility: reversal undoes itself, so every carrier element is its
  own inverse on the elections over A.
\<close>

lemma \<phi>_reverse_elections_\<A>_invertible:
  fixes A :: "'a set"
  shows "\<forall> g \<in> carrier reversal\<^sub>\<G>. \<exists> h \<in> carrier reversal\<^sub>\<G>.
      \<forall> E \<in> elections_\<A> A.
        \<phi>_reverse (elections_\<A> A) h (\<phi>_reverse (elections_\<A> A) g E) = E
      \<and> \<phi>_reverse (elections_\<A> A) g (\<phi>_reverse (elections_\<A> A) h E) = E"
proof (intro ballI)
  fix g :: "'a rel \<Rightarrow> 'a rel"
  assume g_in: "g \<in> carrier reversal\<^sub>\<G>"
  have "\<forall> E \<in> elections_\<A> A.
      \<phi>_reverse (elections_\<A> A) g (\<phi>_reverse (elections_\<A> A) g E) = E"
  proof (intro ballI)
    fix E :: "('a, 'v) Election"
    assume E_in: "E \<in> elections_\<A> A"
    have img: "rel_app g E \<in> elections_\<A> A"
      by (rule reversal_preserves_elections_\<A>[OF g_in E_in])
    have "\<phi>_reverse (elections_\<A> A) g (\<phi>_reverse (elections_\<A> A) g E)
        = rel_app g (rel_app g E)"
      by (simp only: \<phi>_reverse_apply[OF E_in] \<phi>_reverse_apply[OF img])
    also have "\<dots> = rel_app (g \<circ> g) E"
      by (rule rel_app_comp)
    also have "\<dots> = rel_app id E"
      by (simp only: reversal_carrier_invol[OF g_in])
    also have "\<dots> = E"
      by (rule rel_app_id)
    finally show
      "\<phi>_reverse (elections_\<A> A) g (\<phi>_reverse (elections_\<A> A) g E) = E" .
  qed
  thus "\<exists> h \<in> carrier reversal\<^sub>\<G>. \<forall> E \<in> elections_\<A> A.
      \<phi>_reverse (elections_\<A> A) h (\<phi>_reverse (elections_\<A> A) g E) = E
    \<and> \<phi>_reverse (elections_\<A> A) g (\<phi>_reverse (elections_\<A> A) h E) = E"
    using g_in
    by blast
qed

text \<open>
  Transfer: a rule with reversal symmetry on all well-formed elections is
  in particular reversal-equivariant on the elections over A, with the
  action parameterized by \<open>elections_\<A> A\<close>. Unlike neutrality, no
  restriction of the transformation set is needed, since reversal never
  moves the alternative set.
\<close>

lemma reversal_symmetry_in_elections_\<A>:
  fixes
    m :: "('a, 'v, 'a rel Result) Electoral_Module" and
    A :: "'a set"
  assumes "reversal_symmetry_in well_formed_elections m"
  shows "is_symmetry (fun\<^sub>\<E> m)
      (action_induced_equivariance (carrier reversal\<^sub>\<G>) (elections_\<A> A)
          (\<phi>_reverse (elections_\<A> A)) (result_action \<psi>_reverse))"
proof -
  have sub_dom: "elections_\<A> A \<subseteq> well_formed_elections"
    unfolding elections_\<A>.simps
    by blast
  from assms have
    "is_symmetry (fun\<^sub>\<E> m) (Equivariance well_formed_elections
        {(\<phi>_reverse well_formed_elections z, result_action \<psi>_reverse z) | z.
            z \<in> carrier reversal\<^sub>\<G>})"
    unfolding reversal_symmetry_in_def action_induced_equivariance_def
    by simp
  hence "is_symmetry (fun\<^sub>\<E> m) (Equivariance (elections_\<A> A)
      {(\<phi>_reverse well_formed_elections z, result_action \<psi>_reverse z) | z.
          z \<in> carrier reversal\<^sub>\<G>})"
    using equivar_under_subset sub_dom
    by blast
  hence wfe_act: "is_symmetry (fun\<^sub>\<E> m)
      (action_induced_equivariance (carrier reversal\<^sub>\<G>) (elections_\<A> A)
          (\<phi>_reverse well_formed_elections) (result_action \<psi>_reverse))"
    unfolding action_induced_equivariance_def
    by simp
  moreover have "\<forall> g \<in> carrier reversal\<^sub>\<G>. \<forall> E \<in> elections_\<A> A.
      \<phi>_reverse well_formed_elections g E = \<phi>_reverse (elections_\<A> A) g E"
    using sub_dom
    by auto
  ultimately show ?thesis
    using equivar_ind_by_act_coincide
    by blast
qed

subsection \<open>Anonymity Acts Trivially on the Quotient\<close>

text \<open>
  Renaming voters with a bijection changes who casts which ballot, but not
  how many voters cast each ballot: counting is blind to voter names.
  So a renamed election has exactly the same vote fractions as the
  original and therefore lands in the same anon-hom class. Consequently,
  voter renaming does not move the classes at all: it acts as the
  identity on the quotient. Anonymity does not survive as a symmetry of
  the quotient; it is built into the quotient itself.
\<close>

lemma anon_preserves_elections_\<A>:
  fixes
    A :: "'a set" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    E :: "('a, 'v) Election"
  assumes
    bij_\<pi>: "bij \<pi>" and
    elect: "E \<in> elections_\<A> A"
  shows "rename \<pi> E \<in> elections_\<A> A"
proof -
  obtain B :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
    E_eq: "E = (B, V, p)"
    using prod_cases3
    by blast
  have B_eq_A: "B = A" and
       fin_V: "finite V" and
       def_prof: "\<forall> v. v \<notin> V \<longrightarrow> p v = {}" and
       wf: "(B, V, p) \<in> well_formed_elections"
    using elect E_eq
    unfolding elections_\<A>.simps
    by auto
  have prof: "profile V B p"
    using wf
    unfolding well_formed_elections_def
    by simp
  have ren_eq: "(B, \<pi> ` V, p \<circ> the_inv \<pi>) = rename \<pi> (B, V, p)"
    by simp
  have "profile (\<pi> ` V) B (p \<circ> the_inv \<pi>)"
    using rename_prof[OF prof ren_eq bij_\<pi>] .
  hence wf': "(B, \<pi> ` V, p \<circ> the_inv \<pi>) \<in> well_formed_elections"
    unfolding well_formed_elections_def
    by simp
  have fin': "finite (\<pi> ` V)"
    using fin_V
    by blast
  have def': "\<forall> v'. v' \<notin> \<pi> ` V \<longrightarrow> (p \<circ> the_inv \<pi>) v' = {}"
  proof (intro allI impI)
    fix v' :: "'v"
    assume nin: "v' \<notin> \<pi> ` V"
    have "the_inv \<pi> v' \<notin> V"
    proof
      assume "the_inv \<pi> v' \<in> V"
      hence "\<pi> (the_inv \<pi> v') \<in> \<pi> ` V"
        by blast
      moreover have "\<pi> (the_inv \<pi> v') = v'"
        using bij_\<pi> f_the_inv_into_f_bij_betw
        by fastforce
      ultimately show "False"
        using nin
        by simp
    qed
    thus "(p \<circ> the_inv \<pi>) v' = {}"
      using def_prof
      by simp
  qed
  have ren_E: "rename \<pi> E = (B, \<pi> ` V, p \<circ> the_inv \<pi>)"
    unfolding E_eq
    by simp
  show ?thesis
    unfolding ren_E elections_\<A>.simps
    using wf' B_eq_A fin' def'
    by auto
qed

lemma \<phi>_anon_apply:
  fixes
    \<X> :: "('a, 'v) Election set" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    E :: "('a, 'v) Election"
  assumes "E \<in> \<X>"
  shows "\<phi>_anon \<X> \<pi> E = rename \<pi> E"
  by (simp only: \<phi>_anon.simps extensional_continuation.simps if_P[OF assms])

lemma vote_count_rename:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes
    bij_\<pi>: "bij \<pi>" and
    fin: "finite (voters_\<E> E)"
  shows "vote_count q (rename \<pi> E) = vote_count q E"
proof -
  have "(E, rename \<pi> E) \<in> anonymity\<^sub>\<R> UNIV"
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps \<phi>_anon.simps
              simp_extensional_univ bijection\<^sub>\<V>\<^sub>\<G>_def
    using bij_\<pi> case_prodI rewrite_carrier
    by auto
  hence "\<forall> p. vote_count p E = vote_count p (rename \<pi> E)"
    using anon_rel_vote_count[OF fin]
    by blast
  thus ?thesis
    by metis
qed

lemma vote_fraction_rename:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_\<pi>: "bij \<pi>"
  shows "vote_fraction q (rename \<pi> E) = vote_fraction q E"
proof -
  have inj_V: "inj_on \<pi> (voters_\<E> E)"
    by (rule inj_on_subset[OF bij_is_inj[OF bij_\<pi>] subset_UNIV])
  have vtrs: "voters_\<E> (rename \<pi> E) = \<pi> ` voters_\<E> E"
    by (cases E) simp
  have fin_eq: "finite (voters_\<E> (rename \<pi> E)) = finite (voters_\<E> E)"
    unfolding vtrs
    by (rule finite_image_iff[OF inj_V])
  have emp_eq: "(voters_\<E> (rename \<pi> E) = {}) = (voters_\<E> E = {})"
    unfolding vtrs
    by (rule image_is_empty)
  have card_eq: "card (voters_\<E> (rename \<pi> E)) = card (voters_\<E> E)"
    unfolding vtrs
    by (rule card_image[OF inj_V])
  show ?thesis
  proof (cases "finite (voters_\<E> E)")
    case True
    thus ?thesis
      by (simp only: vote_fraction.simps fin_eq emp_eq card_eq vote_count_rename[OF bij_\<pi> True])
  next
    case False
    thus ?thesis
      using fin_eq
      by simp
  qed
qed

text \<open>
  The key step: an election and its voter-renamed version have the same
  fractions and both lie over A, so they are in the same anon-hom class.
\<close>

lemma anon_rename_in_own_class:
  fixes
    A :: "'a set" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    E :: "('a, 'v) Election"
  assumes
    bij_\<pi>: "bij \<pi>" and
    E_in: "E \<in> elections_\<A> A"
  shows "(E, rename \<pi> E) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
proof -
  have img: "rename \<pi> E \<in> elections_\<A> A"
    by (rule anon_preserves_elections_\<A>[OF bij_\<pi> E_in])
  have fracs: "\<forall> q. vote_fraction q E = vote_fraction q (rename \<pi> E)"
    using vote_fraction_rename[OF bij_\<pi>]
    by metis
  have inj_V: "inj_on \<pi> (voters_\<E> E)"
    using bij_\<pi> bij_is_inj subset_UNIV inj_on_subset
    by metis
  have "voters_\<E> (rename \<pi> E) = \<pi> ` voters_\<E> E"
    by (cases E) simp
  hence "finite (voters_\<E> E) = finite (voters_\<E> (rename \<pi> E))"
    using finite_image_iff[OF inj_V]
    by simp
  thus ?thesis
    using E_in img fracs
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast
qed

text \<open>
  Voter renaming maps every anon-hom class to itself: each renamed member
  stays in the class, and each member w of the class is hit, namely as
  the renaming of its own inverse-renaming, which also lies in the class.
\<close>

lemma anon_acts_trivially_on_quotient:
  fixes
    A :: "'a set" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    CLS :: "('a, 'v) Election set"
  assumes
    bij_\<pi>: "bij \<pi>" and
    cls: "CLS \<in> elections_\<A> A // anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "\<phi>_anon (elections_\<A> A) \<pi> ` CLS = CLS"
proof -
  let ?X = "elections_\<A> A"
  let ?r = "anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  have equiv_r: "equiv ?X ?r"
    by (rule anon_hom_equiv)
  have trans_r: "Relation.trans ?r"
    using equiv_r
    unfolding equiv_def
    by blast
  obtain x :: "('a, 'v) Election" where
    CLS_eq: "CLS = ?r `` {x}" and
    x_in: "x \<in> ?X"
    using cls quotientE
    by blast
  have sub_X: "CLS \<subseteq> ?X"
    using CLS_eq equiv_type[OF equiv_r]
    by blast
  show ?thesis
  proof (intro equalityI subsetI)
    fix w :: "('a, 'v) Election"
    assume "w \<in> \<phi>_anon ?X \<pi> ` CLS"
    then obtain E :: "('a, 'v) Election" where
      E_in_CLS: "E \<in> CLS" and
      w_eq: "w = \<phi>_anon ?X \<pi> E"
      by blast
    have E_in_X: "E \<in> ?X"
      using E_in_CLS sub_X
      by blast
    have w_ren: "w = rename \<pi> E"
      unfolding w_eq
      by (rule \<phi>_anon_apply[OF E_in_X])
    have "(x, E) \<in> ?r"
      using E_in_CLS CLS_eq
      by blast
    moreover have "(E, w) \<in> ?r"
      unfolding w_ren
      by (rule anon_rename_in_own_class[OF bij_\<pi> E_in_X])
    ultimately have "(x, w) \<in> ?r"
       by (rule transD[OF trans_r])
    thus "w \<in> CLS"
      unfolding CLS_eq
      by (simp only: Image_singleton_iff)
  next
    fix w :: "('a, 'v) Election"
    assume w_CLS: "w \<in> CLS"
    have x_w: "(x, w) \<in> ?r"
      using w_CLS CLS_eq
      by blast
    have w_X: "w \<in> ?X"
      using w_CLS sub_X
      by blast
    have bij_\<sigma>: "bij (the_inv \<pi>)"
      using bij_\<pi> bij_betw_the_inv_into
      by blast
    have u_X: "rename (the_inv \<pi>) w \<in> ?X"
      by (rule anon_preserves_elections_\<A>[OF bij_\<sigma> w_X])
    have "(w, rename (the_inv \<pi>) w) \<in> ?r"
      by (rule anon_rename_in_own_class[OF bij_\<sigma> w_X])
    hence "(x, rename (the_inv \<pi>) w) \<in> ?r"
      by (rule transD[OF trans_r x_w])
    hence u_CLS: "rename (the_inv \<pi>) w \<in> CLS"
      unfolding CLS_eq
      by blast
    obtain B :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
      w_eq: "w = (B, V, p)"
      using prod_cases3
      by blast
    have "rename \<pi> (rename (the_inv \<pi>) w) = w"
      unfolding w_eq
      by (rule rename_inv[OF bij_\<pi>])
    moreover have "\<phi>_anon ?X \<pi> (rename (the_inv \<pi>) w)
        = rename \<pi> (rename (the_inv \<pi>) w)"
      by (rule \<phi>_anon_apply[OF u_X])
    ultimately have "w = \<phi>_anon ?X \<pi> (rename (the_inv \<pi>) w)"
      by simp
    thus "w \<in> \<phi>_anon ?X \<pi> ` CLS"
      by (rule image_eqI[OF _ u_CLS])
  qed
qed


end