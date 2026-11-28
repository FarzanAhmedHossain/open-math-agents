import Mathlib

/-!
# Reduction A of the class-three, rank > m/7 leaf (Li-Qiao, arXiv:2610.14509v3)

Dev draft of `reductions/Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.H1.R1.lean`.
The target is `H1` of `...R1.H3.R2`: eventually in `m`,
`(24 N)^27 2^(9 m^2) ≤ 2^(2 m^3)` for the number `N` of isomorphism classes of groups of order
`2^m` of class exactly three with `|γ_3| > 2` and `d(G) > m/7`, i.e.
`log_2 N ≤ (2/27) m^3 - m^2/3 - log_2 24`.  In this dev module the target body is restated
verbatim (the final file imports the parent module and states `main` against its `H1`).

Notation in all statements (Li-Qiao Secs. 2, 6, 12, written inline with Mathlib notions):
`γ_{n+1} = (⊤ : Subgroup G).lowerCentralSeries n`; `r1 = d(G)`, `r2 = d(γ_2/γ_3)`,
`r3 = d(γ_3)`; `s` the Sims rank (17)/(20) (p.11-12), as an `sInf` over subgroups `H` with
`γ_2 = [H, H] γ_3`; `s1 = log_2 |G : γ_2|` (so `δ = s1 - r1`, (75)); `m2 = log_2 |γ_2|`,
`m3 = log_2 |γ_3|` (so `s2 = m2 - m3`, `e = s2 - r2`).  The tuple set is the set of `r2`-tuples
of alternating `F_2`-matrices on `F_2^r1` whose values span `F_2^r2` and whose Sims rank (91) is
`s`, i.e. the surjective alternating maps `β : ∧² F_2^r1 → F_2^r2` of Sims rank `s` of (21)
(p.12); its `log_2` is the paper's `N_2(r1, r2, s)`.

Hypotheses:
* `H1` (CNT3): Theorem 6.3 / (55) / (54) at class `3`, with Lemma 2.3, Lemma 6.1 and (126).
* `H2` (MULT3): Corollary 14.1 (Props 13.1, 13.2, Remark 6.4) at class `3`, `δ ≤ 1`.
* `H3` (N2A): Theorem 7.1 (i) at `p = 2`.
* `H4` (N2B): Theorem 7.1 (ii) (`p = 2`, binary endpoint `r2 = C(s-1, 2)`).
`main` is the Part III arithmetic (Thm 11.3, Lemmas 11.1, 11.2, (129)-(130), Prop 12.1 (ii),
(145)-(146), Lemma 14.2, (157), the case split of Thm 14.3) at class `3`, plus the sum over the
parameters and the `24`-factor glue.
-/

open Subgroup Filter CategoryTheory
open scoped commutatorElement Matrix

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1

/-- CNT3, the class-three Sims count (Li-Qiao, Theorem 6.3 (p.42) through (55) (p.26) and the
alternative leading-layer count of (54) (Remark 4.4, pp.25-26), with the power word count (47)
of Theorem 3.1 (p.22) and the data count of Proposition 2.5 (pp.14-15)).

For the class-three groups `G` of order `2^m` with the parameters `(r1, r2, s, s1, m2, m3, r3)`
(the set `S`), if `S` is nonempty then
* the parameters satisfy `r1 ≤ s1` (`δ ≥ 0`, Burnside basis theorem, (18)),
  `2 ≤ s ≤ r1` (p.11), `s - 1 ≤ r2 ≤ C(s, 2)` (Lemma 2.3, p.12), `r2 ≤ s2` (p.72),
  `e ≤ C(δ, 2)` (Lemma 6.1, p.40) and `s2 ≤ r2 (δ + 1)` (proof of Lemma 11.2, p.69);
* for some core breadth `b2` with `m3 ≤ s b2` and `b2 ≤ min (s2, m3)` ((48), (51), (80),
  pp.24-25, 41), `log_2 #classes ≤ C m (log_2 m + 1) + PW + min (A b2) (B b2)`, where
  `PW = Σ_i [r_i m_{i+1} + (r_i - 1)(s_i - r_i)]` is (47) at `c = 3`,
  `A b2 = (C(r1,2) - r2) m2 + b2 (s (r2 + m3 - b2 + 1) - C(r1 - s, 2))` is (55) at `c = 3`, and
  `B b2` is (55) with the leading-layer exponent replaced by the second alternative of (54),
  `N_2(r1, r2, s) + (C(r1,2) - r2)(s2 - r2)`.
The term `C m (log_2 m + 1)` absorbs the `2^{O(m log m)}` recorded data and breadth choices. -/
def H1 : Prop :=
  ∃ C : ℝ, ∀ m r1 r2 s s1 m2 m3 r3 : ℕ, ∀ S : Set FiniteGrp.{0},
    S = {G : FiniteGrp.{0} | Nat.card G = 2 ^ m ∧
        (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧
        (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
        Group.rank G = r1 ∧
        Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
          ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
            ((⊤ : Subgroup G).lowerCentralSeries 1)) = r2 ∧
        sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
          ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} = s ∧
        ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ s1 ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ m2 ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3 ∧
        Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = r3} →
    S.Nonempty →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) ∧
    ∃ b2 : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧
      Real.logb 2 ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' S).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) +
        ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
          (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
        min (((r1.choose 2 : ℝ) - r2) * m2 +
            (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ)))
          (Real.logb 2 ({β : Fin r2 → Matrix (Fin r1) (Fin r1) (ZMod 2) |
              (∀ k, (∀ i, β k i i = 0) ∧ ∀ i j, β k j i = -β k i j) ∧
              Submodule.span (ZMod 2) {w : Fin r2 → ZMod 2 |
                ∃ x ∈ (⊤ : Submodule (ZMod 2) (Fin r1 → ZMod 2)),
                  ∃ y ∈ (⊤ : Submodule (ZMod 2) (Fin r1 → ZMod 2)), w = fun k => x ⬝ᵥ (β k *ᵥ y)} = ⊤ ∧
              sInf {d | ∃ U : Submodule (ZMod 2) (Fin r1 → ZMod 2), Module.finrank (ZMod 2) U = d ∧
                Submodule.span (ZMod 2) {w : Fin r2 → ZMod 2 |
                  ∃ x ∈ U, ∃ y ∈ U, w = fun k => x ⬝ᵥ (β k *ᵥ y)} = ⊤} = s}.ncard : ℝ) +
            ((r1.choose 2 : ℝ) - r2) * ((m2 : ℝ) - m3 - r2) + ((r1.choose 2 : ℝ) - r2) * m3 +
            (s : ℝ) * b2 * ((r2 : ℝ) + m3 - b2 + 1))

/-- MULT3, the class-three multiplicity count (Li-Qiao, Corollary 14.1, (153), pp.81-82, from
Proposition 13.1 (p.80), Proposition 13.2 (pp.80-81) and Remark 6.4 (p.43)), in the saturated
range `C(s-1, 2) < r2` (134) with defect `δ = s1 - r1 ≤ 1`.

The bound is stated with the class-three commutator exponent `A b2` of (55) (the exponent from
which (85) is derived) in place of `F_{1/2} + 2 m2 e + r1 δ`: for some core breadth `b2`, some
`z = dim Z_0` with `max {0, r1 - s - δ} ≤ z ≤ r1 - s` and some `k = dim K ≤ r1 - s`,
`log_2 #classes ≤ C m (log_2 m + 1) + PW + A b2 - z^2 + k (r1 + z - k - s r2)`.
The term `C m (log_2 m + 1)` absorbs the data, breadth, `dim Z_0`, `dim K` choices and the
constant `2 log_2 π_∞(2)^{-1}`. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ m r1 r2 s s1 m2 m3 r3 : ℕ, ∀ S : Set FiniteGrp.{0},
    S = {G : FiniteGrp.{0} | Nat.card G = 2 ^ m ∧
        (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧
        (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
        Group.rank G = r1 ∧
        Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
          ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
            ((⊤ : Subgroup G).lowerCentralSeries 1)) = r2 ∧
        sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
          ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} = s ∧
        ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ s1 ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ m2 ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3 ∧
        Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = r3} →
    s1 ≤ r1 + 1 → (s - 1).choose 2 < r2 → S.Nonempty →
    ∃ b2 z k : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧
      r1 - s - (s1 - r1) ≤ z ∧ z ≤ r1 - s ∧ k ≤ r1 - s ∧
      Real.logb 2 ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' S).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) +
        ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
          (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
        (((r1.choose 2 : ℝ) - r2) * m2 +
          (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) -
        (z : ℝ) ^ 2 + (k : ℝ) * ((r1 : ℝ) + z - k - (s : ℝ) * r2)

/-- N2A: Li-Qiao, Theorem 7.1 (i) (p.44; proof p.66 via (123) and Proposition 9.2) at `p = 2`:
for `2 ≤ s ≤ r1` and `s - 1 ≤ r2 < C(s-1, 2)`, the number of surjective alternating maps
`∧² F_2^r1 → F_2^r2` of Sims rank `s` is at most `2^((r2 - s + 1) C(r1,2) + O(r1^2 + r2^2))`. -/
def H3 : Prop :=
  ∃ C3 : ℕ, ∀ r1 r2 s : ℕ, 2 ≤ s → s ≤ r1 → s - 1 ≤ r2 → r2 < (s - 1).choose 2 →
    {β : Fin r2 → Matrix (Fin r1) (Fin r1) (ZMod 2) |
      (∀ k, (∀ i, β k i i = 0) ∧ ∀ i j, β k j i = -β k i j) ∧
      Submodule.span (ZMod 2) {w : Fin r2 → ZMod 2 |
        ∃ x ∈ (⊤ : Submodule (ZMod 2) (Fin r1 → ZMod 2)),
          ∃ y ∈ (⊤ : Submodule (ZMod 2) (Fin r1 → ZMod 2)), w = fun k => x ⬝ᵥ (β k *ᵥ y)} = ⊤ ∧
      sInf {d | ∃ U : Submodule (ZMod 2) (Fin r1 → ZMod 2), Module.finrank (ZMod 2) U = d ∧
        Submodule.span (ZMod 2) {w : Fin r2 → ZMod 2 |
          ∃ x ∈ U, ∃ y ∈ U, w = fun k => x ⬝ᵥ (β k *ᵥ y)} = ⊤} = s}.ncard ≤
      2 ^ ((r2 + 1 - s) * r1.choose 2 + C3 * (r1 ^ 2 + r2 ^ 2))

/-- N2B: Li-Qiao, Theorem 7.1 (ii) (p.44, (90); proof pp.66-67 via (123), Proposition 10.1 (p.53)
and Proposition 10.4 (p.54)): for `2 ≤ s ≤ r1`, `s - 1 ≤ r2 = C(s-1, 2)` and
`a_* = min (⌊2 (s-1)^2 / 5⌋, ⌊r1 / 2⌋)`, the number of surjective alternating maps
`∧² F_2^r1 → F_2^r2` of Sims rank `s` is at most
`2^((r2 - s + 1) C(r1,2) + (s - 1) a_* (2 r1 - 2 a_* - 1) + O(r1^2 + r2^2))`. -/
def H4 : Prop :=
  ∃ C4 : ℕ, ∀ r1 r2 s a : ℕ, 2 ≤ s → s ≤ r1 → s - 1 ≤ r2 → r2 = (s - 1).choose 2 →
    a = min (2 * (s - 1) ^ 2 / 5) (r1 / 2) →
    {β : Fin r2 → Matrix (Fin r1) (Fin r1) (ZMod 2) |
      (∀ k, (∀ i, β k i i = 0) ∧ ∀ i j, β k j i = -β k i j) ∧
      Submodule.span (ZMod 2) {w : Fin r2 → ZMod 2 |
        ∃ x ∈ (⊤ : Submodule (ZMod 2) (Fin r1 → ZMod 2)),
          ∃ y ∈ (⊤ : Submodule (ZMod 2) (Fin r1 → ZMod 2)), w = fun k => x ⬝ᵥ (β k *ᵥ y)} = ⊤ ∧
      sInf {d | ∃ U : Submodule (ZMod 2) (Fin r1 → ZMod 2), Module.finrank (ZMod 2) U = d ∧
        Submodule.span (ZMod 2) {w : Fin r2 → ZMod 2 |
          ∃ x ∈ U, ∃ y ∈ U, w = fun k => x ⬝ᵥ (β k *ᵥ y)} = ⊤} = s}.ncard ≤
      2 ^ ((r2 + 1 - s) * r1.choose 2 + (s - 1) * a * (2 * r1 - 2 * a - 1) +
        C4 * (r1 ^ 2 + r2 ^ 2))

/-! ## Lemmas for `main` (stated, `sorry` in this draft)

### Group-level glue (Mathlib only) -/

/-- Class exactly three in the target's form: `¬ γ_2 ≤ Z(G)` and `γ_3 ≤ Z(G)` give
`γ_3 ≠ 1` and `γ_4 = 1`. -/
lemma class_three {G : Type} [Group G] (h1 : ¬commutator G ≤ Subgroup.center G)
    (h2 : (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G) :
    (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧ (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ := by
  sorry

/-- Order facts on a member of a parameter set: `m = s1 + m2`, `m3 ≤ m2`, `m3 ≥ 1`. -/
lemma param_facts {m s1 m2 m3 : ℕ} (G : FiniteGrp.{0}) (hc : Nat.card G = 2 ^ m)
    (h3 : (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥)
    (hi : ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ s1)
    (hm2 : Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ m2)
    (hm3 : Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3) :
    s1 + m2 = m ∧ m3 ≤ m2 ∧ 1 ≤ m3 := by
  sorry

/-- The target classes are covered by the parameter sets, with `r1, r2, s, r3 ≤ 2^m`
(`Group.rank_le` on `Finset.univ`, and `s ≤ r1` from `H = ⊤`) and `s1, m2, m3 ≤ m`
(`Nat.dvd_prime_pow` for subgroup orders and indices). -/
lemma target_le_sum (m : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
        2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
        m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G}).ncard ≤
    ∑ r1 ∈ Finset.range (2 ^ m + 1), ∑ r2 ∈ Finset.range (2 ^ m + 1),
      ∑ s ∈ Finset.range (2 ^ m + 1), ∑ s1 ∈ Finset.range (m + 1),
      ∑ m2 ∈ Finset.range (m + 1), ∑ m3 ∈ Finset.range (m + 1),
      ∑ r3 ∈ Finset.range (2 ^ m + 1),
        (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = 2 ^ m ∧
            (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧
            (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
            Group.rank G = r1 ∧
            Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
              ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
                ((⊤ : Subgroup G).lowerCentralSeries 1)) = r2 ∧
            sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
              ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} = s ∧
            ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ s1 ∧
            Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ m2 ∧
            Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3 ∧
            Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = r3}).ncard := by
  sorry

/-! ### Real-arithmetic glue -/

/-- `n ≤ 2^E` gives `log_2 n ≤ E` (also for `n = 0`, where `logb 2 0 = 0`). -/
lemma logb_le_of_le_pow {n E : ℕ} (h : n ≤ 2 ^ E) : Real.logb 2 (n : ℝ) ≤ E := by
  sorry

/-- `log_2 n ≤ E` gives `n ≤ 2^E`. -/
lemma le_rpow_of_logb_le {n : ℕ} {E : ℝ} (h : Real.logb 2 (n : ℝ) ≤ E) : (n : ℝ) ≤ 2 ^ E := by
  sorry

/-- The final inequality: a total of `2^(8m+8)` parameter tuples, each contributing at most
`2^((2/27) m^3 - (7/18) m^2 + C m (log_2 m + 1))` classes, fits the target
`log_2 N ≤ (2/27) m^3 - m^2/3 - log_2 24` (`7/18 > 1/3`). -/
lemma final_ineq (C : ℝ) : ∀ᶠ m : ℕ in atTop, ∀ N : ℕ,
    (N : ℝ) ≤ 2 ^ (8 * (m : ℝ) + 8) *
      2 ^ (2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 + C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1)) →
    (24 * N) ^ 27 * 2 ^ (9 * m ^ 2) ≤ 2 ^ (2 * m ^ 3) := by
  sorry

/-- The number of parameter tuples in `target_le_sum`. -/
lemma box_card (m : ℕ) : ((2 ^ m + 1) ^ 4 * (m + 1) ^ 3 : ℝ) ≤ 2 ^ (8 * (m : ℝ) + 8) := by
  sorry

/-! ### Part III arithmetic at class three

Common hypotheses: the constraints of `H1`, `m = s1 + m2`, `1 ≤ m3 ≤ m2`, and an admissible
breadth `b2`.  `PW`, `A`, `B` are as in `H1`. -/

/-- Nonsaturated range, large Sims rank (Li-Qiao, Theorem 11.3 (pp.69-71) for `h = s - 1 ≥ H`):
with `N_2` bounded by Theorem 7.1 (i)/(ii), `PW + B ≤ (2/27) m^3 - (s - 1) m^2 / 200 + C' m^2`.
Case (i): `B ≤ ½ r1² (m - r1 - h) + h m2²/4 + O(m²)` and
`min_x (φ(x)/x - ψ(x)) > 1/20` for `φ(x) = 2/27 - x²(1-x)/2`, `ψ(x) = (1-x)²/4 - x²/2`
(the analogue of (129)-(130) for `B`, `h ≤ r1`).  Case (ii): `h² ≤ 3m`, so `B` is at most the
(42)-expression of p.70 plus `O(m²)`, and Lemma 11.1 (p.67, (124)) gives `11/1602 > 1/200`. -/
lemma nonsat_large (C3 C4 : ℕ) : ∃ C' : ℝ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ, ∀ N : ℝ,
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    r2 ≤ (s - 1).choose 2 →
    (r2 < (s - 1).choose 2 → N ≤ (((r2 + 1 - s) * r1.choose 2 + C3 * (r1 ^ 2 + r2 ^ 2) : ℕ) : ℝ)) →
    (r2 = (s - 1).choose 2 → N ≤ (((r2 + 1 - s) * r1.choose 2 +
        (s - 1) * min (2 * (s - 1) ^ 2 / 5) (r1 / 2) * (2 * r1 - 2 * min (2 * (s - 1) ^ 2 / 5) (r1 / 2) - 1) +
        C4 * (r1 ^ 2 + r2 ^ 2) : ℕ) : ℝ)) →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) + (N +
      ((r1.choose 2 : ℝ) - r2) * ((m2 : ℝ) - m3 - r2) + ((r1.choose 2 : ℝ) - r2) * m3 +
      (s : ℝ) * b2 * ((r2 : ℝ) + m3 - b2 + 1)) ≤
      2 / 27 * (m : ℝ) ^ 3 - ((s : ℝ) - 1) * (m : ℝ) ^ 2 / 200 + C' * (m : ℝ) ^ 2 := by
  sorry

/-- Bounded second-layer rank (Li-Qiao, Lemma 11.2, pp.68-69, at class three, through `A`):
`PW + A ≤ (2/27) (K/(K+1)) m^3 + C' m^2` when `r2 ≤ K` (uses `s ≤ r2 + 1`, `m3 ≤ s b2`,
`s2 ≤ r2 (δ + 1)`, (125)-(126)). -/
lemma bounded_r2 (K : ℕ) : ∃ C' : ℝ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ,
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    r2 ≤ K →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) + (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) ≤
      2 / 27 * ((K : ℝ) / (K + 1)) * (m : ℝ) ^ 3 + C' * (m : ℝ) ^ 2 := by
  sorry

/-- Saturated range, defect `δ ≥ 2` (Li-Qiao, Prop 12.1 (ii) (p.74), (139), (145)-(146) (p.77),
first step of the proof of Thm 14.3 (p.84)): `PW + A ≤ F_{1/2} + 2 m2 e + r1 δ` at class three,
and then `≤ (2/27) m^3 - (7/18) m^2` for large `m` (`(2/27)·3δ ≥ 4/9 > 7/18`). -/
lemma sat_defect_two : ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ, m0 ≤ m →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    (s - 1).choose 2 < r2 → r1 + 2 ≤ s1 →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) + (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) ≤
      2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 := by
  sorry

/-- Saturated range, small core (Li-Qiao, Lemma 14.2 (pp.82-84) with `Λ = 2`, `D = 1`):
`δ ≤ 1` and `s r2 < 2 r1` give `PW + A ≤ (2/27) m^3 - (7/18) m^2` for large `m`. -/
lemma small_core : ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ, m0 ≤ m →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    (s - 1).choose 2 < r2 → s1 ≤ r1 + 1 → s * r2 < 2 * r1 →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) + (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) ≤
      2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 := by
  sorry

/-- Saturated range with multiplicities (Li-Qiao, proof of Thm 14.3, pp.84-86: (152), (156),
identity (157), (158) and Prop 12.1 (ii) at `η = -5/6`): `δ ≤ 1`, `2 r1 ≤ s r2`,
`max {0, r1 - s - δ} ≤ z ≤ r1 - s`, `k ≤ r1 - s` give
`PW + A - z^2 + k (r1 + z - k - s r2) ≤ (2/27) m^3 - (7/18) m^2` for large `m`. -/
lemma mult_case : ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 b2 z k : ℕ, m0 ≤ m →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    (s - 1).choose 2 < r2 → s1 ≤ r1 + 1 → 2 * r1 ≤ s * r2 →
    r1 - s - (s1 - r1) ≤ z → z ≤ r1 - s → k ≤ r1 - s →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) + (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) -
      (z : ℝ) ^ 2 + (k : ℝ) * ((r1 : ℝ) + z - k - (s : ℝ) * r2) ≤
      2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 := by
  sorry

/-- The per-parameter bound: the case split of Li-Qiao's proof of Thm 14.3 at class three
(nonsaturated with `s - 1 ≥ H` by `nonsat_large`, `H3`, `H4`; nonsaturated with `s - 1 < H`,
so `r2 ≤ C(H-1, 2)`, by `bounded_r2`; saturated with `δ ≥ 2` by `sat_defect_two`; saturated with
`δ ≤ 1` by `small_core` or, through `H2`, by `mult_case`). -/
lemma per_param (h1 : H1) (h2 : H2) (h3 : H3) (h4 : H4) :
    ∃ C : ℝ, ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 : ℕ, m0 ≤ m → ∀ S : Set FiniteGrp.{0},
    S = {G : FiniteGrp.{0} | Nat.card G = 2 ^ m ∧
        (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧
        (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
        Group.rank G = r1 ∧
        Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
          ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
            ((⊤ : Subgroup G).lowerCentralSeries 1)) = r2 ∧
        sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
          ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} = s ∧
        ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ s1 ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ m2 ∧
        Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3 ∧
        Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = r3} →
    Real.logb 2 ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' S).ncard : ℝ) ≤
      2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 + C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) := by
  sorry

/-- Reduction A: CNT3, MULT3, N2A and N2B give the class-three, rank `> m/7` estimate.
(Dev draft: the target body of `...R1.H3.R2.H1` is restated; proof: `per_param`,
`target_le_sum`, `le_rpow_of_logb_le`, `box_card`, `final_ineq`.) -/
theorem main : H1 → H2 → H3 → H4 →
    ∀ᶠ m : ℕ in atTop,
      (24 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
          2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
          m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G}).ncard)^27 *
          2^(9*m^2) ≤ 2^(2*m^3) := by
  sorry

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1
