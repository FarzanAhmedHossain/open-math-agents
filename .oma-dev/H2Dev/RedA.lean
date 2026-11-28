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
* `H2` (MULT3): Propositions 13.1 and 13.2 with Remark 6.4 (the argument of Corollary 14.1) at
  class `3` and defect `δ = 0`, for `C(s-1, 2) ≤ r2` (saturated range or binary endpoint).
* `H3` (N2A): Theorem 7.1 (i) at `p = 2`.
Theorem 7.1 (ii) (Section 10) is not needed: at the binary endpoint `r2 = C(s-1, 2)` the
multiplicity bound `H2` is used instead.
`H2` is stated for `C(s-1, 2) ≤ r2`, while Corollary 14.1 states only `C(s-1, 2) < r2`;
the ingredients (Props 13.1, 13.2, Remark 6.4) carry no saturation hypothesis.  If a reviewer
rejects the endpoint, the Option I fallback (`H2Dev/RedAOptI.lean`: `H2s` with strict saturation,
`H4` = Theorem 7.1 (ii), and Lemma 11.1 in `main`) replaces `H2`.

`main` is the Part III arithmetic at class `3` (class-three forms of Theorem 11.3, (129)-(130),
Prop 12.1 (ii), Lemma 14.2, (157) and the case split of Theorem 14.3), plus the sum over the
parameters and the `24`-factor glue.  The case split (`per_param`):
* `r2 < C(s-1, 2)` and `s > H`: `H1` with the `B` term and `H3` (`ns_assembly`, `ns_cubic`);
* otherwise `s^2 ≤ 8 m` (`sq_le_of_sat`, or `s ≤ H`), and
  * `δ ≥ 1`: `H1` with the `A` term (`lam_pos_case`: `sat_A_bound`, `psi_bound`, `lam_close`);
  * `δ = 0`, `s r2 < 2 r1`: `H1` with the `A` term (`small_core`, `small_core_size`,
    `core_small_of_le`);
  * `δ = 0`, `2 r1 ≤ s r2` (so `s > H` and `C(s-1, 2) ≤ r2`): `H2` (`mult_case`: `sat_A_bound`,
    `mult_close`, `psi_bound`).
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


/-- MULT3, the class-three multiplicity count at defect `δ = s1 - r1 = 0`, for
`C(s-1, 2) ≤ r2` (the saturated range `C(s-1, 2) < r2` of (134) together with the binary
endpoint `r2 = C(s-1, 2)`).

Source: Li-Qiao, Proposition 13.1 (p.80; multiplicity `≥ π_∞(2) 2^((dim Z_0)^2 - dim Z_0 dim K)`
of the family (148) of Section 13.1), Proposition 13.2 (pp.80-81, (151); the core-centralizer
`K` of (149), `dim K ≤ r1 - s` (150), and the saving `s (dim K) r2` of Remark 6.4, p.43) and
Proposition 2.4, assembled as in the proof of Corollary 14.1 ((153), pp.81-82).  None of
Section 13.1, Propositions 13.1, 13.2 or Remark 6.4 uses saturation (Remark 6.4 states the saving
for the commutator exponent (55) and for (85) with `Δ_p` omitted, in every range); Corollary 14.1
states the saturated range only because it is applied there.  At class three the commutator
exponent is `A b2` of (55) (`H1`), and at `δ = 0` the group `L_1 = G/γ_2` is elementary abelian,
so `Z_≥2 = 0`, `dim Z_core = s` and `dim Z_0 = r1 - s` exactly (Section 13.1).  With
`k = dim K ≤ r1 - s` the exponent is `PW + A b2 - (r1 - s)^2 + k (2 r1 - s - k - s r2)`, i.e.
(153) with `z = dim Z_0 = r1 - s` and `PW + A b2` in place of `F_(1/2) + 2 m2 e + r1 δ`.

Citation chain (this statement is not literally a displayed result; it is assembled as follows).
The starting bound is (87) (p.42, proof of Theorem 6.3): the power word count (47) of
Theorem 3.1 plus the commutator exponent (55), with `Δ_p` omitted; at class three this is
`PW + A b2` per fixed recorded data and breadth.  (85) is the range-free relaxation of (87), and
(151)/(153) are written with (85); here the unrelaxed (87) is kept.  By Remark 6.4 (p.43,
`q` may be 'subtracted from the commutator exponent in (55)'), the rank `q = s (dim K) r2` of
the core-outside equations from the proof of Proposition 13.2 (pp.80-81) is subtracted; that
proof also counts the subspaces `K` of dimension `k` by `π_∞(2)^(-1) 2^(k (r1 - k))`
(Lemma 2.7 (i)).  Proposition 13.1 (p.80) gives the multiplicity
`≥ π_∞(2) 2^((dim Z_0)^2 - (dim Z_0) k)`, and at `δ = 0` the bounds
`max{0, r1 - s - δ} ≤ dim Z_0 ≤ r1 - s` (p.79) give `dim Z_0 = r1 - s`.  Proposition 2.4 (the
array pair determines the group) and Proposition 2.5 (the data count) finish the count, as in the
proof of Corollary 14.1.  Algebra: `-Z_0^2 + Z_0 k + k (r1 - k) - s k r2` with `Z_0 = r1 - s`
equals `-(r1 - s)^2 + k (2 r1 - s - k - s r2)`.
The term `C m (log_2 m + 1)` absorbs the recorded data, the breadth, `dim K`, and the constant
`2 log_2 π_∞(2)^(-1)`. -/
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
    s1 = r1 → (s - 1).choose 2 ≤ r2 → S.Nonempty →
    ∃ b2 k : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧ k ≤ r1 - s ∧
      Real.logb 2 ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' S).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) +
        ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
          (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
        (((r1.choose 2 : ℝ) - r2) * m2 +
          (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) -
        ((r1 - s : ℕ) : ℝ) ^ 2 + (k : ℝ) * (2 * (r1 : ℝ) - s - k - (s : ℝ) * r2)

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


/-! ## Lemmas for `main` (stated, `sorry` in this draft)

`PW`, `A b2`, `B b2` are the three exponents of `H1`; `e = m2 - m3 - r2`, `λ = δ = s1 - r1`,
`h = s - 1`, `Ψ(r1, m2) = r1^2 m2 / 2 + r1 m2 / 2 - m2^2 - r1^2 / 2`.

### L0 group-level glue (Mathlib only) -/

/-- Class exactly three in the target's form: `¬ γ_2 ≤ Z(G)` and `γ_3 ≤ Z(G)` give
`γ_3 ≠ 1` and `γ_4 = 1`. -/
lemma class_three {G : Type} [Group G] (h1 : ¬commutator G ≤ Subgroup.center G)
    (h2 : (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G) :
    (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧ (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ := by
  sorry

/-- A member of a parameter set has `m3 ≥ 1` (`γ_3 ≠ 1`). -/
lemma param_m3_pos {m s1 m2 m3 : ℕ} (G : FiniteGrp.{0})
    (h3 : (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥)
    (hm3 : Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3) : 1 ≤ m3 := by
  sorry

/-- L0 + L1: the target classes are covered by the parameter sets with `m/7 < r1 ≤ 2^m`,
`r2, s, r3 ≤ 2^m` (`Group.rank_le` on `Finset.univ`) and `s1, m2, m3 ≤ m` (`Nat.dvd_prime_pow`
for subgroup orders and indices, `Subgroup.card_mul_index`), each class lying in the set of its
own parameters (`class_three`); hence a uniform bound `X` on the class counts of these sets
gives `N ≤ (2^m + 1)^4 (m + 1)^3 X`. -/
lemma target_le_box (m : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (h : ∀ r1 r2 s s1 m2 m3 r3 : ℕ, m / 7 < r1 →
      ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = 2 ^ m ∧
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
          Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = r3}).ncard : ℝ) ≤ X) :
    ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
        2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
        m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G}).ncard : ℝ) ≤
      ((2 ^ m + 1) ^ 4 * (m + 1) ^ 3 : ℝ) * X := by
  sorry

/-! ### L1 real-arithmetic glue -/

/-- `n ≤ 2^E` gives `log_2 n ≤ E` (also for `n = 0`, where `logb 2 0 = 0`). -/
lemma logb_le_of_le_pow {n E : ℕ} (h : n ≤ 2 ^ E) : Real.logb 2 (n : ℝ) ≤ E := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h' : (n : ℝ) ≤ (2 : ℝ) ^ E := by exact_mod_cast h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ E) :=
          Real.logb_le_logb_of_le (by norm_num) hn' h'
      _ = E := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- `log_2 n ≤ E` gives `n ≤ 2^E` (for `n = 0` trivially). -/
lemma le_rpow_of_logb_le {n : ℕ} {E : ℝ} (h : Real.logb 2 (n : ℝ) ≤ E) :
    (n : ℝ) ≤ 2 ^ E := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero]
    positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (n : ℝ) = 2 ^ Real.logb 2 (n : ℝ) := (Real.rpow_logb (by norm_num) (by norm_num) hn').symm
      _ ≤ 2 ^ E := Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- The number of parameter tuples in `target_le_box`. -/
lemma box_card (m : ℕ) : ((2 ^ m + 1) ^ 4 * (m + 1) ^ 3 : ℝ) ≤ 2 ^ (8 * (m : ℝ) + 8) := by
  sorry

/-- The final inequality: `2^(8m+8)` parameter tuples, each contributing at most
`2^((2/27) m^3 - (7/18) m^2 + C m (log_2 m + 1))` classes, fit the target
`log_2 N ≤ (2/27) m^3 - m^2/3 - log_2 24` for large `m` (`7/18 > 1/3`). -/
lemma final_ineq (C : ℝ) : ∀ᶠ m : ℕ in atTop, ∀ N : ℕ,
    (N : ℝ) ≤ 2 ^ (8 * (m : ℝ) + 8) *
      2 ^ (2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 + C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1)) →
    (24 * N) ^ 27 * 2 ^ (9 * m ^ 2) ≤ 2 ^ (2 * m ^ 3) := by
  sorry

/-! ### L2-L10 Part III arithmetic at class three

Common hypotheses: the constraints of `H1`, `s1 + m2 = m`, `1 ≤ m3 ≤ m2`, and an admissible
breadth `b2`. -/

/-- L2, the power word exponent: `(r1 - 1) δ ≤ r1 δ`, `(r2 - 1) e = r2 e - e` (`r2 ≥ 1`) and
`(r3 - 1)(m3 - r3) ≤ (m3 - 1)^2 / 4`. -/
lemma pw_le : ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ,
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) ≤
      (r1 : ℝ) * m2 + (r1 : ℝ) * ((s1 - r1 : ℕ) : ℝ) + (r2 : ℝ) * m3 +
        (r2 : ℝ) * ((m2 - m3 - r2 : ℕ) : ℝ) - ((m2 - m3 - r2 : ℕ) : ℝ) + ((m3 : ℝ) - 1) ^ 2 / 4 := by
  intro m r1 r2 s s1 m2 m3 r3 b2 hc _ _ hm3 _
  obtain ⟨_, h2, _, h4, _, _, _, _⟩ := hc
  generalize hp : r1 - 1 = p
  generalize hd : s1 - r1 = d
  generalize he : m2 - m3 - r2 = e
  generalize hq : r2 - 1 = q
  generalize ha : r3 - 1 = a
  generalize hb : m3 - r3 = b
  have hpd : p * d ≤ r1 * d := Nat.mul_le_mul_right _ (by omega)
  have hqr : (q : ℝ) + 1 = r2 := by exact_mod_cast (show q + 1 = r2 by omega)
  have hab : a = 0 ∨ b = 0 ∨ a + b + 1 = m3 := by omega
  have hpd' : (p : ℝ) * d ≤ r1 * d := by exact_mod_cast hpd
  have hab' : (a : ℝ) * b ≤ ((m3 : ℝ) - 1) ^ 2 / 4 := by
    rcases hab with h | h | h
    · rw [h, Nat.cast_zero, zero_mul]; positivity
    · rw [h, Nat.cast_zero, mul_zero]; positivity
    · have h' : (a : ℝ) + b + 1 = m3 := by exact_mod_cast h
      rw [← h']
      nlinarith [sq_nonneg ((a : ℝ) - b)]
  have hqe : (q : ℝ) * e = r2 * e - e := by rw [← hqr]; ring
  push_cast
  linarith

/-- L3, the nonsaturated cubic (class-three analogue of (129)-(130)): for `0 ≤ h ≤ r` and
`h ≤ m - r`, `(r^2/2)(m - r - h) + h (m - r)^2 / 4 + h m^2 / 20 ≤ (2/27) m^3`.  Identity:
`(2/27) m^3 - (r^2/2)(m - r) = (1/2)(r - 2m/3)^2 (r + m/3)`; the minimum of the slack over the
admissible `h/m` is about `0.0529 m^3 > m^3/20 ·(h/m)`. -/
lemma ns_cubic (m r h : ℝ) (h0 : 0 ≤ h) (hr : h ≤ r) (hm : h ≤ m - r) :
    r ^ 2 / 2 * (m - r - h) + h * (m - r) ^ 2 / 4 + h * m ^ 2 / 20 ≤ 2 / 27 * m ^ 3 := by
  have ha : 0 ≤ r - h := by linarith
  have hb : 0 ≤ m - r - h := by linarith
  nlinarith [mul_nonneg ha (sq_nonneg ((r - h) - 2 * (m - r - h) - 11 / 4 * h)),
    mul_nonneg ha (sq_nonneg ((r - h) - 2 * (m - r - h) + 2 * h)),
    mul_nonneg ha (sq_nonneg ((r - h) - 2 * (m - r - h) + 11 / 4 * h)),
    mul_nonneg hb (sq_nonneg ((r - h) - 2 * (m - r - h) + 5 / 4 * h)),
    mul_nonneg h0 (sq_nonneg ((r - h) + (m - r - h) / 4)),
    mul_nonneg h0 (sq_nonneg ((r - h) + (m - r - h) / 2)),
    mul_nonneg h0 (sq_nonneg ((r - h) - 2 * (m - r - h) + 3 / 2 * h)),
    mul_nonneg h0 (sq_nonneg ((r - h) - 2 * (m - r - h) + 7 / 4 * h))]

/-- L4, nonsaturated assembly (class-three form of Theorem 11.3 (pp.69-71)): with
`N_2 ≤ (r2 - s + 1) C(r1, 2) + Cn (r1^2 + r2^2)` (`H3`),
`PW + B b2 ≤ (2/27) m^3 - (s - 1) m^2 / 20 + K m^2`.  Steps:
`N_2 + (C(r1,2) - r2)(s2 - r2) + (C(r1,2) - r2) m3 ≤ C(r1,2)(m2 - h) + 2 Cn m^2`,
`s b2 (r2 + m3 + 1 - b2) ≤ s (m2 + 1)^2 / 4`, `h ≤ r2 ≤ m2 ≤ m - r1`, `h ≤ r1`, then `ns_cubic`
with `r = r1`. -/
lemma ns_assembly (Cn : ℕ) : ∃ K : ℝ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ, ∀ N : ℝ,
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    r2 < (s - 1).choose 2 →
    N ≤ (((r2 + 1 - s) * r1.choose 2 + Cn * (r1 ^ 2 + r2 ^ 2) : ℕ) : ℝ) →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
    (N +
      ((r1.choose 2 : ℝ) - r2) * ((m2 : ℝ) - m3 - r2) + ((r1.choose 2 : ℝ) - r2) * m3 +
      (s : ℝ) * b2 * ((r2 : ℝ) + m3 - b2 + 1)) ≤
      2 / 27 * (m : ℝ) ^ 3 - ((s : ℝ) - 1) * (m : ℝ) ^ 2 / 20 + K * (m : ℝ) ^ 2 := by
  sorry

/-- L5, the `A` term in the saturated regime (class-three form of Prop 12.1 (ii), (139)): if
`P = C(r1 - s, 2) - s (m2 + 1) ≥ 3 s m2`, then
`PW + A b2 ≤ Ψ(r1, m2) + 2 m2 e + r1 δ + 5 s m`.  Steps: `m2 = r2 + e + m3`,
`-r2^2 ≤ -m2^2 + 2 m2 (m3 + e)`, `X ≤ -b2 P ≤ -P - 3 (b2 - 1) s m2` with `s b2 ≥ m3`,
`r1^2/2 - C(r1 - s, 2) ≤ r1 s + r1/2`. -/
lemma sat_A_bound : ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ,
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    3 * s * m2 + s * (m2 + 1) ≤ (r1 - s).choose 2 →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
    (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) ≤
      (r1 : ℝ) ^ 2 * m2 / 2 + (r1 : ℝ) * m2 / 2 - (m2 : ℝ) ^ 2 - (r1 : ℝ) ^ 2 / 2 +
        2 * (m2 : ℝ) * ((m2 - m3 - r2 : ℕ) : ℝ) + (r1 : ℝ) * ((s1 - r1 : ℕ) : ℝ) +
        5 * (s : ℝ) * m := by
  sorry

/-- L6, the cubic for `Ψ` (class-three form of (145)-(146)), with `n = r1 + m2`:
`Ψ ≤ (2/27) n^3 - (2/9) n^2 + n/24` and `Ψ - r1^2 ≤ (2/27) n^3 - (2/3) n^2 + 4 n`
(slacks `n (2d + 1)^2 / 24 + d^2 r1 / 2 + 2 d^2` and `d^2 r1 / 2 + 3 d^2 + n (d^2/6 + 3d/2 + 4)`,
up to the exact forms, for `d = r1 - 2n/3`). -/
lemma psi_bound (r1 m2 : ℝ) (h1 : 0 ≤ r1) (h2 : 0 ≤ m2) :
    r1 ^ 2 * m2 / 2 + r1 * m2 / 2 - m2 ^ 2 - r1 ^ 2 / 2 ≤
        2 / 27 * (r1 + m2) ^ 3 - 2 / 9 * (r1 + m2) ^ 2 + (r1 + m2) / 24 ∧
      r1 ^ 2 * m2 / 2 + r1 * m2 / 2 - m2 ^ 2 - r1 ^ 2 / 2 - r1 ^ 2 ≤
        2 / 27 * (r1 + m2) ^ 3 - 2 / 3 * (r1 + m2) ^ 2 + 4 * (r1 + m2) := by
  constructor
  · nlinarith [sq_nonneg (r1 - 2 * m2), mul_nonneg h1 (sq_nonneg (r1 - 2 * m2 + 3 / 4)),
      mul_nonneg h2 (sq_nonneg (r1 - 2 * m2 - 3 / 2))]
  · nlinarith [sq_nonneg (r1 - 2 * m2), mul_nonneg h1 (sq_nonneg (r1 - 2 * m2 + 9 / 2)),
      mul_nonneg h2 (sq_nonneg (r1 - 2 * m2 + 9 / 2))]

/-- L7, closing for `δ ≥ 1` (`m^3 - n^3 = λ (m^2 + m n + n^2)`; split `λ < 32`, where
`e ≤ 465`, from `λ ≥ 32`, where `2 m2 e ≤ 2 m^2`). -/
lemma lam_close (m lam r1 m2 e : ℝ) (hl : 1 ≤ lam) (hn : r1 + m2 = m - lam) (h1 : 0 ≤ r1)
    (h2 : 0 ≤ m2) (he0 : 0 ≤ e) (he : e ≤ lam * (lam - 1) / 2) (hem : e ≤ m2) :
    2 / 27 * (m - lam) ^ 3 - 2 / 9 * (m - lam) ^ 2 + (m - lam) / 24 + 2 * m2 * e + r1 * lam ≤
      2 / 27 * m ^ 3 - 4 / 9 * m ^ 2 + 40 * m := by
  have hm : m = r1 + m2 + lam := by linarith
  subst hm
  have hl0 : (0 : ℝ) ≤ lam := by linarith
  have hK : 0 ≤ lam * (2 / 27 * lam ^ 2 - 4 / 9 * lam + 40) :=
    mul_nonneg hl0 (by nlinarith [sq_nonneg (lam - 3)])
  rcases le_total lam 10 with hl10 | hl10
  · have hE : 0 ≤ lam * (lam - 1) / 2 - e := by linarith
    have hq : 0 ≤ 2 / 9 * lam ^ 2 - 17 / 9 * lam + 40 - 1 / 24 := by
      nlinarith [sq_nonneg (lam - 17 / 4)]
    have hp : 0 ≤ lam ^ 3 / 9 - lam ^ 2 + 2 / 9 * lam + 959 / 24 := by
      nlinarith [mul_nonneg hl0 (sq_nonneg (lam - 6)), sq_nonneg (lam - 17 / 3)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ lam - 1) h2)
        (by linarith : (0 : ℝ) ≤ m2 - e),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 10 - lam) h2) hE,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ lam - 1) h1)
        (by linarith : (0 : ℝ) ≤ r1 + 2 * m2),
      mul_nonneg h2 hp, mul_nonneg h1 hq]
  · have hq : 0 ≤ 2 / 9 * lam ^ 2 - 17 / 9 * lam + 39 := by
      nlinarith [sq_nonneg (lam - 17 / 4)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ lam - 10) (sq_nonneg (r1 + m2)),
      mul_nonneg h1 (by linarith : (0 : ℝ) ≤ r1 + 2 * m2),
      mul_nonneg h2 (by linarith : (0 : ℝ) ≤ m2 - e),
      mul_nonneg (by linarith : (0 : ℝ) ≤ r1 + m2) hq, mul_nonneg hl0 h2]

/-- L8, the multiplicity saving at `δ = 0` (Li-Qiao (156)-(158)): if `2 r1 ≤ s r2` and
`0 ≤ k ≤ r1 - s` then `-(r1 - s)^2 + k (2 r1 - s - k - s r2) ≤ -r1^2 + 2 r1 s`. -/
lemma mult_close (r1 s r2 k : ℝ) (hs : 0 ≤ s) (hk0 : 0 ≤ k) (hk : k ≤ r1 - s)
    (hsr : 2 * r1 ≤ s * r2) :
    -(r1 - s) ^ 2 + k * (2 * r1 - s - k - s * r2) ≤ -r1 ^ 2 + 2 * r1 * s := by
  have h1 : 0 ≤ k * (s * r2 - 2 * r1) := mul_nonneg hk0 (sub_nonneg.mpr hsr)
  nlinarith [mul_nonneg hk0 hs, sq_nonneg s, sq_nonneg k]

/-- L9, small core at `δ = 0` (class-three form of Lemma 14.2 (pp.82-84)): if `m < 7 r1` and
`12 s^2 ≤ m` then `PW + A b2 ≤ (2/27) m^3 - m^2` for large `m`.  Split: `m2 < m/12` gives a cubic
gap `7 m^3 / 216`; otherwise `m3 = m2 - r2 ≥ m/24` (`e = 0`, `r2 ≤ s^2/2`), so
`X ≤ -(m3 / s) P ≤ -c m^(5/2)`. -/
lemma small_core : ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ, m0 ≤ m →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    s1 = r1 → m < 7 * r1 → 12 * s ^ 2 ≤ m →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
    (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) ≤
      2 / 27 * (m : ℝ) ^ 3 - (m : ℝ) ^ 2 := by
  sorry

/-- L10 (a): `C(s-1, 2) ≤ r2 ≤ m` gives `s^2 ≤ 8 m` (for `m ≥ 2`). -/
lemma sq_le_of_sat (m s r2 : ℕ) (hm : 2 ≤ m) (h : (s - 1).choose 2 ≤ r2) (hr : r2 ≤ m) :
    s ^ 2 ≤ 8 * m := by
  rcases Nat.lt_or_ge s 4 with hs | hs
  · have h9 : s ^ 2 ≤ 9 := by interval_cases s <;> norm_num
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 4 := ⟨s - 4, by omega⟩
    have e1 : t + 4 - 1 = t + 3 := by omega
    rw [e1, Nat.choose_two_right] at h
    have e2 : t + 3 - 1 = t + 2 := by omega
    rw [e2] at h
    generalize hx : (t + 3) * (t + 2) = x at h
    have hx2 : x ≤ 2 * m + 1 := by omega
    nlinarith [Nat.zero_le (t * t)]

/-- L10 (b): `C(s-1, 2) ≤ r2`, `s r2 < 2 r1 ≤ 2 m` give `(s - 2)^3 < 4 m`, hence `12 s^2 ≤ m`
for large `m`. -/
lemma small_core_size : ∃ m0 : ℕ, ∀ m s r1 r2 : ℕ, m0 ≤ m → (s - 1).choose 2 ≤ r2 →
    s * r2 < 2 * r1 → r1 ≤ m → 12 * s ^ 2 ≤ m := by
  refine ⟨31212, fun m s r1 r2 hm hc hsr hr1 => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hs : 52 ≤ s := by
    by_contra h
    rw [not_le] at h
    have h51 : s ^ 2 ≤ 2601 :=
      calc s ^ 2 ≤ 51 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 2601 := by norm_num
    omega
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  have e1 : t + 2 - 1 = t + 1 := by omega
  rw [e1, Nat.choose_two_right] at hc
  have e2 : t + 1 - 1 = t := by omega
  rw [e2] at hc
  generalize hx : (t + 1) * t = x at hc
  have hx2 : x + 1 ≤ (r2 + 1) * 2 := by omega
  have A := Nat.mul_le_mul_left (t + 2) hx2
  have ht : 50 ≤ t := by omega
  have B : 48 * t + 98 ≤ (t + 1) * t := by nlinarith [Nat.mul_le_mul_left t ht]
  have C := Nat.mul_le_mul_left (t + 2) B
  rw [hx] at C
  nlinarith

/-- L10 (c): bounded Sims rank forces a small core: `s ≤ H`, `r2 ≤ C(s, 2)`, `m < 7 r1` and
`7 H^3 < 4 m` give `s r2 < 2 r1`. -/
lemma core_small_of_le (H m s r1 r2 : ℕ) (hs : s ≤ H) (hr : r2 ≤ s.choose 2) (h7 : m < 7 * r1)
    (hH : 7 * H ^ 3 < 4 * m) : s * r2 < 2 * r1 := by
  rw [Nat.choose_two_right] at hr
  generalize hx : s * (s - 1) = x at hr
  have h1 : r2 * 2 ≤ x := by omega
  have h2 : s * (s - 1) ≤ s * s := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 : s * s * s ≤ H * H * H := Nat.mul_le_mul (Nat.mul_le_mul hs hs) hs
  have h4 : s * (r2 * 2) ≤ s * (s * s) :=
    Nat.mul_le_mul_left _ (h1.trans (by rw [← hx]; exact h2))
  have h5 : H ^ 3 = H * H * H := by ring
  have h6 : s * (s * s) = s * s * s := by ring
  have h8 : s * (r2 * 2) = 2 * (s * r2) := by ring
  omega

/-! ### Regime bounds -/

/-- Defect `δ ≥ 1` (CNT3 alone; class-three form of the first step of the proof of Thm 14.3):
`sat_A_bound` (its `P`-condition holds for large `m` from `m < 7 r1`, `s^2 ≤ 8 m`), `psi_bound`
with `n = m - δ`, `lam_close`, and `40 m + 5 s m ≤ m^2 / 18`. -/
lemma lam_pos_case : ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 b2 : ℕ, m0 ≤ m →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    r1 + 1 ≤ s1 → m < 7 * r1 → s ^ 2 ≤ 8 * m →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
    (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) ≤
      2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 := by
  sorry

/-- Defect `δ = 0` with multiplicities (`H2`; class-three form of (152)-(158) and Prop 12.1 (ii)
at `η = -5/6`): `sat_A_bound`, `mult_close`, the second bound of `psi_bound` with `n = m`, and
`4 m + 7 s m ≤ (2/3 - 7/18) m^2`. -/
lemma mult_case : ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 b2 k : ℕ, m0 ≤ m →
    (r1 ≤ s1 ∧ 2 ≤ s ∧ s ≤ r1 ∧ s - 1 ≤ r2 ∧ r2 ≤ s.choose 2 ∧ r2 ≤ m2 - m3 ∧
      m2 - m3 - r2 ≤ (s1 - r1).choose 2 ∧ m2 - m3 ≤ r2 * (s1 - r1 + 1)) →
    s1 + m2 = m → m3 ≤ m2 → 1 ≤ m3 → (m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3) →
    s1 = r1 → m < 7 * r1 → s ^ 2 ≤ 8 * m → 2 * r1 ≤ s * r2 → k ≤ r1 - s →
    ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
      (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
    (((r1.choose 2 : ℝ) - r2) * m2 +
      (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) -
      ((r1 - s : ℕ) : ℝ) ^ 2 + (k : ℝ) * (2 * (r1 : ℝ) - s - k - (s : ℝ) * r2) ≤
      2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 := by
  sorry

/-- L11, the per-parameter bound (the case split of the proof of Thm 14.3 at class three).
Take `C`, `C'` from `H1`, `H2`, `Cn` from `H3`, `K` from `ns_assembly Cn`, and
`H = ⌈20 (K + 1)⌉ + 2`.  For large `m` and a nonempty set (constraints from `H1`,
`param_m3_pos`, `cnt3`'s `m = s1 + m2`, `r2 ≤ m`):
* `r2 < C(s-1, 2)`, `s > H`: `H1` (`min ≤ B`), `H3`, `logb_le_of_le_pow`, `ns_assembly`;
* else `s^2 ≤ 8 m` (`sq_le_of_sat`, or `s ≤ H`), and `δ ≥ 1`: `H1` (`min ≤ A`), `lam_pos_case`;
* `δ = 0`, `s r2 < 2 r1`: `12 s^2 ≤ m` (`small_core_size`, or `s ≤ H`), `H1`, `small_core`;
* `δ = 0`, `2 r1 ≤ s r2`: `s > H` (`core_small_of_le`), so `C(s-1, 2) ≤ r2`; `H2`, `mult_case`.
An empty set has `logb 2 0 = 0`. -/
lemma per_param (h1 : H1) (h2 : H2) (h3 : H3) :
    ∃ C : ℝ, ∃ m0 : ℕ, ∀ m r1 r2 s s1 m2 m3 r3 : ℕ, m0 ≤ m → m / 7 < r1 →
    ∀ S : Set FiniteGrp.{0},
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

/-- Reduction A: CNT3, MULT3 and N2A give the class-three, rank `> m/7` estimate.
(Dev draft: the target body of `...R1.H3.R2.H1` is restated.) -/
theorem main : H1 → H2 → H3 →
    ∀ᶠ m : ℕ in atTop,
      (24 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
          2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
          m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G}).ncard)^27 *
          2^(9*m^2) ≤ 2^(2*m^3) := by
  intro h1 h2 h3
  obtain ⟨C, m0, hC⟩ := per_param h1 h2 h3
  filter_upwards [final_ineq C, eventually_ge_atTop m0] with m hfin hm
  apply hfin
  have hX : (0 : ℝ) ≤ 2 ^ (2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 +
      C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1)) := by positivity
  refine (target_le_box m _ hX fun r1 r2 s s1 m2 m3 r3 hr1 =>
    le_rpow_of_logb_le (hC m r1 r2 s s1 m2 m3 r3 hm hr1 _ rfl)).trans ?_
  exact mul_le_mul_of_nonneg_right (box_card m) hX

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1
