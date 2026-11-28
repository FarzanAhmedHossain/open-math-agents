import H2Dev.Bridge
import H2Dev.Alt2Bridge
import H2Dev.Breadth

/-! # CNT3: the statement of the class-3 Sims count, and its part (a)

Li-Qiao, Theorem 6.3 / (55) / (54) at `c = 3`, `p = 2`, with the parameter constraints of
Lemma 2.3, Lemma 6.1 and (126).

## The parameter set

`cnt3Set m r1 r2 s lam m2 m3 r3` is the set of `FiniteGrp.{0}` objects `G` with (all written
inline, with Mathlib notions only)

* `|G| = 2 ^ m`;
* `γ_3 ≠ 1` and `γ_4 = 1` (class exactly `3`; `γ_3` nontrivial and central);
* `d(G) = r1`;
* `d(γ_2 / γ_3) = r2`;
* Sims rank `s` (Def 2.1 / (17), as an `sInf` over subgroups `H` with `γ_2 = [H, H] γ_3`);
* `|G : γ_2| = 2 ^ (r1 + lam)`;
* `|γ_2| = 2 ^ m2`, `|γ_3| = 2 ^ m3`;
* `d(γ_3) = r3` (the rank of the third layer `L_3 = γ_3`, needed by the power word term).

Here `(⊤ : Subgroup G).lowerCentralSeries n` is `γ_{n+1}` (this is `OMA.SimsLite.lcs G n`).
The relative-order data are not parameters: Theorem 3.1 only needs the layer ranks
`r_1, r_2, r_3` and the layer sizes `s_1 = r1 + lam`, `s_2 = m2 - m3`, `s_3 = m3`, which are fixed
by the parameters. `cnt3Classes` is the set of isomorphism classes, as in `Bridge`.

## Bridging lemmas (inline forms = library forms)

* `simsRankInl_eq` : the inline Sims rank (17) is `simsRank G` (`SimsGen.lean`);
* `rankQuot_eq_r2` : `d(γ_2/γ_3) = r2 2 G` (`Frame.rank_lcs_quot_eq_r2`);
* `lam_eq_lambdaPar` : `|G : γ_2| = 2 ^ (d(G) + lam)` iff `lam = lambdaPar 2 G` (`Frame`);
* `mem_cnt3Set_iff` : membership in library terms;
* `cnt3_m_eq` : `m = r1 + lam + m2`;
* `cnt3Classes_finite` : the class set is finite (`Bridge.classes_finite`).

## Part (a) (proved): `cnt3_partA`

The class set is empty unless `2 ≤ s ≤ r1`, `s - 1 ≤ r2 ≤ C(s, 2)`, `m2 - m3 - r2 ≤ C(lam, 2)`
(Lemma 6.1) and `m2 - m3 ≤ r2 (lam + 1)` (126).

## Part (b) (stated only): `CNT3Stmt`

`∃ C, ∀ parameters, (set nonempty) → ∃ b2` with `m3 ≤ s b2`, `b2 ≤ m2 - m3`, `b2 ≤ m3` (the
admissible breadths, (48)/(51)) and
`log_2 #classes ≤ C m (log_2 m + 1) + PW + min (A b2) (B b2)`, where

* `PW = cnt3PW = r1 m2 + (r1 - 1) lam + r2 m3 + (r2 - 1)(m2 - m3 - r2) + (r3 - 1)(m3 - r3)`, the
  right side of (47) at `c = 3`;
* `A b2 = cnt3A = (C(r1,2) - r2) m2 + b2 (s (r2 + m3 - b2 + 1) - C(r1 - s, 2))`, i.e. (55) at
  `c = 3` (the sum `Σ_{i=2}^{c-2}` is empty);
* `B b2 = cnt3B = logN2 r1 r2 s + (C(r1,2) - r2)(m2 - m3 - r2) + (C(r1,2) - r2) m3
  + s b2 (r2 + m3 - b2 + 1)`, i.e. (55) with the leading-layer exponent replaced by the second
  alternative of (54) (equivalently (55) + `Δ_2` of (86) when `Δ_2 < 0`).

The existential `b2` is equivalent to the maximum over admissible `b2` of `min (A b2) (B b2)`,
which is at most the plan's `min (max A) (max B)`.

What feeds each term of (b) (library lemma, status):
* the sum over recorded data and the `2 ^ PW` factor: `Bridge.ncard_classes_le_fiber_pw` (with
  `liqiao_thm_3_1`), and the data count `C m log m`: `DataCount.card_recData_le` (Prop 2.5).
  Missing: the identification of `pwBound2 (fibAk D)` with `cnt3PW` for the data `D` of a group of
  `cnt3Set` (needs: `nL = 3` at class 3, `r 2 = d(γ_3)`, and the layer sums of the relative orders
  `Σ_v a(i, v) = s_i`, i.e. `p ^ (Σ_v a(i,v)) = |γ_i : γ_{i+1}|` from the normal forms).
* the `A` term, leading layer: `Breadth.br_prop43_fin` / `br_eq53` / `br_eq53_breadth` /
  `br_eq53_sum` (Props 4.2, 4.3, Lemma 4.1, (53)), the transport `brT1`, `brT2`,
  `brT1_coeff_eq`, `brT2_coeff_eq`, the breadth facts `brBreadth_le_s2`, `brBreadth_le_s3`,
  `br_s3_le_breadth` (admissibility of `b2`), Rem 4.4 lift `br_rem44_lift`; deeper coefficients
  `(C(r1,2) - r2) m3`: `br_deeper_count_fin`. Missing: the group-level map from
  `realizedC hp T D` (commutator coefficient arrays) to (transported bracket, deeper data) and
  its injectivity, i.e. that the commutator coefficient array of a Sims code is determined by the
  transported brackets of `G` plus the deeper coefficients on the non-defining pairs, with the
  `r2` defining pairs fixed by `D` (the class-3 instance of Theorem 5.1).
* the `B` term: `Alt2Bridge.exists_tuple_of_group` / `tuple_mem_N2`, `Alt2.N2_eq_ncard`,
  `logN2`, and `br_rem44_lift` (lifts mod 2 with `|p L_2| = 2 ^ (s2 - r2)` from
  `Breadth.br_card_L2`). Missing: the same coefficient-array map, now factored through the
  reduction `β_G` (the leading-layer values mod `pL_2`), and its compatibility with the fixed
  bases of `V`, `W` carried by the recorded data.
* the final real-arithmetic assembly (`log_2` of a sum over `D` and `b2`, `Nat.log` bounds):
  missing, routine. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

/-! ### The statement -/

section CNT3Defs

/-- The class-3 parameter set of CNT3 (all parameters bound; inline definitions). -/
def cnt3Set (m r1 r2 s lam m2 m3 r3 : ℕ) : Set FiniteGrp.{0} :=
  {G | Nat.card G = 2 ^ m ∧
    (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧
    (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
    Group.rank G = r1 ∧
    Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
      ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
        ((⊤ : Subgroup G).lowerCentralSeries 1)) = r2 ∧
    sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
      ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} = s ∧
    ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ (r1 + lam) ∧
    Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ m2 ∧
    Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3 ∧
    Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = r3}

/-- The isomorphism classes of the groups of `cnt3Set`. -/
def cnt3Classes (m r1 r2 s lam m2 m3 r3 : ℕ) :
    Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' cnt3Set m r1 r2 s lam m2 m3 r3

/-- The power word exponent (47) at `c = 3`:
`Σ_i [r_i m_{i+1} + (r_i - 1)(s_i - r_i)]` with `s_1 = r1 + lam`, `s_2 = m2 - m3`, `s_3 = m3`,
`m_4 = 0`. -/
def cnt3PW (r1 r2 r3 lam m2 m3 : ℕ) : ℕ :=
  (r1 * m2 + (r1 - 1) * lam) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) + (r3 - 1) * (m3 - r3)

/-- The breadth bound (55) at `c = 3`, for breadth `b2`. -/
noncomputable def cnt3A (r1 r2 s m2 m3 b2 : ℕ) : ℝ :=
  ((r1.choose 2 : ℝ) - r2) * m2 +
    (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))

/-- (55) with the leading-layer count replaced by the second alternative of (54). -/
noncomputable def cnt3B (r1 r2 s m2 m3 b2 : ℕ) : ℝ :=
  Alt2.logN2 r1 r2 s + ((r1.choose 2 : ℝ) - r2) * ((m2 : ℝ) - m3 - r2) +
    ((r1.choose 2 : ℝ) - r2) * m3 + (s : ℝ) * b2 * ((r2 : ℝ) + m3 - b2 + 1)

/-- CNT3 (b): the class-3 Sims count. -/
def CNT3Stmt : Prop :=
  ∃ C : ℝ, ∀ m r1 r2 s lam m2 m3 r3 : ℕ, (cnt3Set m r1 r2 s lam m2 m3 r3).Nonempty →
    ∃ b2 : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧
      Real.logb 2 ((cnt3Classes m r1 r2 s lam m2 m3 r3).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) + (cnt3PW r1 r2 r3 lam m2 m3 : ℝ) +
          min (cnt3A r1 r2 s m2 m3 b2) (cnt3B r1 r2 s m2 m3 b2)

/-- The parameter constraints of CNT3 (a). -/
def cnt3Constraints (r1 r2 s lam m2 m3 : ℕ) : Prop :=
  2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ m2 - m3 - r2 ≤ lam.choose 2 ∧
    m2 - m3 ≤ r2 * (lam + 1)

/-- CNT3 (a): the class set is empty unless the parameter constraints hold. -/
def CNT3PartA : Prop :=
  ∀ m r1 r2 s lam m2 m3 r3 : ℕ, ¬ cnt3Constraints r1 r2 s lam m2 m3 →
    cnt3Classes m r1 r2 s lam m2 m3 r3 = ∅

end CNT3Defs

/-! ### Bridging lemmas -/

section CNT3Bridge

variable (G : Type u) [Group G] [Finite G]

/-- The Sims rank (17) written inline, over subgroups. -/
noncomputable def simsRankInl : ℕ :=
  sInf {k | ∃ H : Subgroup G, lcs G 1 = ⁅H, H⁆ ⊔ lcs G 2 ∧ Group.rank H = k}

lemma cnt3_comm_sup_le (H : Subgroup G) : ⁅H, H⁆ ⊔ lcs G 2 ≤ lcs G 1 := by
  refine sup_le ?_ (lcs_antitone (by norm_num))
  rw [← commutator_eq_lcs_one, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

/-- The inline Sims rank (17) is the library `simsRank` (an `sInf` over generating tuples). -/
theorem simsRankInl_eq : simsRankInl G = simsRank G := by
  apply le_antisymm
  · have hne : {k | ∃ u : Fin k → G,
        lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
          lcs G 2}.Nonempty := by
      let e : Fin (Nat.card G) → G := (Finite.equivFin G).symm
      have he : Set.range e = Set.univ := Equiv.range_eq_univ _
      refine ⟨Nat.card G, e, ?_⟩
      rw [he, Subgroup.closure_univ]
      exact le_sup_left
    obtain ⟨u, hu⟩ := Nat.sInf_mem hne
    have hmem : Group.rank (Subgroup.closure (Set.range u)) ∈
        {k | ∃ H : Subgroup G, lcs G 1 = ⁅H, H⁆ ⊔ lcs G 2 ∧ Group.rank H = k} :=
      ⟨_, le_antisymm hu (cnt3_comm_sup_le G _), rfl⟩
    have h1 := Nat.sInf_le hmem
    have h2 := (Subgroup.rank_congr (congrArg Subgroup.closure (range_extF u))).le.trans
      (rank_closure_image_Iio_le (extF u) _)
    unfold simsRankInl simsRank
    exact h1.trans h2
  · have hneA : {k | ∃ H : Subgroup G, lcs G 1 = ⁅H, H⁆ ⊔ lcs G 2 ∧ Group.rank H = k}.Nonempty :=
      ⟨_, ⊤, (sup_eq_left.mpr (lcs_antitone (by norm_num) : lcs G 2 ≤ lcs G 1)).symm, rfl⟩
    obtain ⟨H, hH, hk⟩ := Nat.sInf_mem hneA
    obtain ⟨x, hx⟩ := exists_enum_closure H
    unfold simsRankInl simsRank
    apply Nat.sInf_le
    refine ⟨fun i => x i.val, ?_⟩
    have e : Set.range (fun i : Fin (sInf {k | ∃ H : Subgroup G,
        lcs G 1 = ⁅H, H⁆ ⊔ lcs G 2 ∧ Group.rank H = k}) => x i.val) =
        x '' Set.Iio (Group.rank H) := by
      rw [hk]
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.isLt, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [e, hx]
    exact hH.le

variable {G}

/-- `d(γ_2 / γ_3) = r2 2 G` (`Frame.rank_lcs_quot_eq_r2`). -/
theorem rankQuot_eq_r2 [Fact (Nat.Prime 2)] (hG : IsPGroup 2 G) :
    Group.rank (lcs G 1 ⧸ (lcs G 2).subgroupOf (lcs G 1)) = r2 2 G :=
  rank_lcs_quot_eq_r2 hG

/-- `|G : γ_2| = 2 ^ (d(G) + lam)` determines `lam = lambdaPar 2 G`. -/
theorem lam_eq_lambdaPar [Fact (Nat.Prime 2)] (hG : IsPGroup 2 G) (lam : ℕ) :
    (lcs G 1).index = 2 ^ (Group.rank G + lam) ↔ lambdaPar 2 G = lam := by
  constructor
  · intro h
    have h' := (index_lcs_one_eq hG).symm.trans h
    have := Nat.pow_right_injective (le_refl 2) h'
    omega
  · rintro rfl
    exact index_lcs_one_eq hG

end CNT3Bridge

section CNT3Mem

variable {m r1 r2 s lam m2 m3 r3 : ℕ}

/-- Membership in `cnt3Set` in terms of the library definitions. -/
theorem mem_cnt3Set_iff [Fact (Nat.Prime 2)] (G : FiniteGrp.{0}) :
    G ∈ cnt3Set m r1 r2 s lam m2 m3 r3 ↔
      Nat.card G = 2 ^ m ∧ lcs G 2 ≠ ⊥ ∧ lcs G 3 = ⊥ ∧ Group.rank G = r1 ∧ OMA.SimsLite.r2 2 G = r2 ∧
        simsRank G = s ∧ lambdaPar 2 G = lam ∧ Nat.card (lcs G 1) = 2 ^ m2 ∧
        Nat.card (lcs G 2) = 2 ^ m3 ∧ Group.rank (lcs G 2) = r3 := by
  unfold cnt3Set
  constructor
  · rintro ⟨hc, h3, h4, hr1, hr2, hs, hidx, hm2, hm3, hr3⟩
    have hp : IsPGroup 2 G := IsPGroup.of_card hc
    refine ⟨hc, h3, h4, hr1, (rankQuot_eq_r2 hp).symm.trans hr2,
      (simsRankInl_eq G).symm.trans hs, ?_, hm2, hm3, hr3⟩
    have h : (lcs G 1).index = 2 ^ (Group.rank G + lam) := by
      rw [hr1]
      exact hidx
    exact (lam_eq_lambdaPar hp lam).mp h
  · rintro ⟨hc, h3, h4, hr1, hr2, hs, hl, hm2, hm3, hr3⟩
    have hp : IsPGroup 2 G := IsPGroup.of_card hc
    refine ⟨hc, h3, h4, hr1, (rankQuot_eq_r2 hp).trans hr2, (simsRankInl_eq G).trans hs, ?_,
      hm2, hm3, hr3⟩
    have h := (lam_eq_lambdaPar hp lam).mpr hl
    rw [hr1] at h
    exact h

/-- `m = r1 + lam + m2` on `cnt3Set`. -/
theorem cnt3_m_eq {G : FiniteGrp.{0}} (hG : G ∈ cnt3Set m r1 r2 s lam m2 m3 r3) :
    m = r1 + lam + m2 := by
  obtain ⟨hc, -, -, -, -, -, hidx, hm2, -, -⟩ := hG
  have h := Subgroup.card_mul_index ((⊤ : Subgroup G).lowerCentralSeries 1)
  rw [hidx, hm2, hc, ← pow_add] at h
  have := Nat.pow_right_injective (le_refl 2) h
  omega

/-- The class set is finite. -/
theorem cnt3Classes_finite : (cnt3Classes m r1 r2 s lam m2 m3 r3).Finite := by
  unfold cnt3Classes
  refine classes_finite (m := m) Nat.prime_two _ ?_
  intro G hG
  refine ⟨hG.1, ?_⟩
  intro h
  apply hG.2.1
  rw [eq_bot_iff, ← h]
  exact lcs_antitone (by norm_num)

end CNT3Mem

/-! ### Part (a) -/

section CNT3PartA

/-- The CNT3 constraints at group level, in library terms. -/
theorem cnt3_group_constraints [Fact (Nat.Prime 2)] {G : Type u} [Group G] [Finite G] {m : ℕ}
    (hcard : Nat.card G = 2 ^ m) (h3 : lcs G 2 ≠ ⊥) :
    2 ≤ simsRank G ∧ simsRank G ≤ Group.rank G ∧ simsRank G - 1 ≤ r2 2 G ∧
      r2 2 G ≤ (simsRank G).choose 2 ∧
      Nat.card (lcs G 1) ≤ Nat.card (lcs G 2) * 2 ^ (r2 2 G + (lambdaPar 2 G).choose 2) ∧
      Nat.card (lcs G 1) ≤ Nat.card (lcs G 2) * 2 ^ (r2 2 G * (lambdaPar 2 G + 1)) := by
  have hG : IsPGroup 2 G := IsPGroup.of_card hcard
  have hna : lcs G 1 ≠ ⊥ := by
    intro h
    apply h3
    rw [eq_bot_iff, ← h]
    exact lcs_antitone (by norm_num)
  obtain ⟨u, d, X, r, hs2, -⟩ := exists_sims_gen Nat.prime_two hcard hna
  obtain ⟨h1, h2, h3'⟩ := Alt2.simsRank_bounds (p := 2) hG
  exact ⟨hs2, h3', by omega, h2, br_lemma61_group hG, br_s2_le_group hG⟩

variable {m r1 r2 s lam m2 m3 r3 : ℕ}

/-- CNT3 (a) for a member of `cnt3Set`. -/
theorem cnt3_constraints_of_mem {G : FiniteGrp.{0}} (hG : G ∈ cnt3Set m r1 r2 s lam m2 m3 r3) :
    cnt3Constraints r1 r2 s lam m2 m3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG' := (mem_cnt3Set_iff G).mp hG
  obtain ⟨hc, h3, -, hr1, hr2, hs, hl, hm2, hm3, -⟩ := hG'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cnt3_group_constraints hc h3
  rw [hs] at c1 c2 c3 c4
  rw [hr1] at c2
  rw [hr2] at c3 c4 c5 c6
  rw [hl] at c5 c6
  rw [hm2, hm3, ← pow_add] at c5 c6
  have e5 := OMA.SimsLite.pow_le_pow_cancel (p := 2) (le_refl 2) c5
  have e6 := OMA.SimsLite.pow_le_pow_cancel (p := 2) (le_refl 2) c6
  refine ⟨c1, c2, c3, c4, ?_, ?_⟩ <;> omega

/-- CNT3 (a): the class set is empty unless `2 ≤ s ≤ r1`, `s - 1 ≤ r2 ≤ C(s, 2)`,
`m2 - m3 - r2 ≤ C(lam, 2)` and `m2 - m3 ≤ r2 (lam + 1)`. -/
theorem cnt3_partA : CNT3PartA := by
  intro m r1 r2 s lam m2 m3 r3 hnot
  unfold cnt3Classes
  apply Set.subset_empty_iff.mp
  rintro _ ⟨G, hG, rfl⟩
  exact (hnot (cnt3_constraints_of_mem hG)).elim

/-- CNT3 (a), nonempty form. -/
theorem cnt3_constraints_of_nonempty
    (h : (cnt3Classes m r1 r2 s lam m2 m3 r3).Nonempty) : cnt3Constraints r1 r2 s lam m2 m3 := by
  unfold cnt3Classes at h
  obtain ⟨_, G, hG, rfl⟩ := h
  exact cnt3_constraints_of_mem hG

end CNT3PartA

end OMA.SimsLite

#print axioms OMA.SimsLite.cnt3_partA
#print axioms OMA.SimsLite.simsRankInl_eq
#print axioms OMA.SimsLite.mem_cnt3Set_iff
#print axioms OMA.SimsLite.cnt3_m_eq
#print axioms OMA.SimsLite.cnt3Classes_finite
