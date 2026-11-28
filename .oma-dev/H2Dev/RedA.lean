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
  refine ⟨fun hb => h1 ?_, Subgroup.lowerCentralSeries_succ_eq_bot _ h2⟩
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have h2eq : (⊤ : Subgroup G).lowerCentralSeries 2 =
      ⁅(⊤ : Subgroup G).lowerCentralSeries 1, ⊤⁆ := Subgroup.lowerCentralSeries_succ _ 1
  have hx1 : x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := hx
  have hc : ⁅x, g⁆ ∈ ⁅(⊤ : Subgroup G).lowerCentralSeries 1, ⊤⁆ :=
    Subgroup.commutator_mem_commutator hx1 (Subgroup.mem_top g)
  rw [← h2eq, hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

/-- A member of a parameter set has `m3 ≥ 1` (`γ_3 ≠ 1`). -/
lemma param_m3_pos {m s1 m2 m3 : ℕ} (G : FiniteGrp.{0})
    (h3 : (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥)
    (hm3 : Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ m3) : 1 ≤ m3 := by
  by_contra hc
  have h0 : m3 = 0 := by omega
  apply h3
  rw [← Subgroup.card_eq_one, hm3, h0, pow_zero]

/-- A finite group has rank at most its order (`Group.rank_le` on `Finset.univ`). -/
lemma lqmg_rank_le_card (H : Type*) [Group H] [Finite H] : Group.rank H ≤ Nat.card H := by
  classical
  letI := Fintype.ofFinite H
  calc Group.rank H ≤ (Finset.univ : Finset H).card := Group.rank_le (by simp)
    _ = Nat.card H := by rw [Finset.card_univ, Nat.card_eq_fintype_card]

/-- The rank of a subgroup is at most the order of the ambient finite group. -/
lemma lqmg_rank_sub_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Group.rank H ≤ Nat.card G :=
  (lqmg_rank_le_card H).trans (Subgroup.card_le_card_group H)

/-- The rank of a quotient of a subgroup is at most the order of the ambient finite group. -/
lemma lqmg_rank_quot_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) (N : Subgroup H)
    [N.Normal] : Group.rank (H ⧸ N) ≤ Nat.card G := by
  calc Group.rank (H ⧸ N) ≤ Nat.card (H ⧸ N) := lqmg_rank_le_card _
    _ ≤ Nat.card H := Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    _ ≤ Nat.card G := Subgroup.card_le_card_group H

/-- The isomorphism classes of a set of finite groups of a fixed order `n` form a finite set
(a group of order `n` is determined up to isomorphism by a multiplication table on `Fin n`). -/
lemma lqmg_classes_finite (n : ℕ) (S : Set FiniteGrp.{0}) (hS : ∀ G ∈ S, Nat.card G = n) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' S).Finite := by
  have hsub : ∀ t : Fin n → Fin n → Fin n, Set.Subsingleton {q | ∃ G ∈ S,
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G = q ∧
        ∃ e : G ≃ Fin n, ∀ a b, e.symm (t a b) = e.symm a * e.symm b} := by
    intro t
    rintro q₁ ⟨G₁, -, rfl, e₁, h₁⟩ q₂ ⟨G₂, -, rfl, e₂, h₂⟩
    let f : G₁ ≃* G₂ := MulEquiv.mk (e₁.trans e₂.symm) (by
      intro x y
      show e₂.symm (e₁ (x * y)) = e₂.symm (e₁ x) * e₂.symm (e₁ y)
      rw [← h₂]
      congr 1
      apply e₁.symm.injective
      rw [h₁]
      simp)
    exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso f)⟩
  refine Set.Finite.subset (Set.finite_iUnion fun t : Fin n → Fin n → Fin n => (hsub t).finite) ?_
  rintro q ⟨G, hG, rfl⟩
  let e : G ≃ Fin n := (Finite.equivFin G).trans (finCongr (hS G hG))
  exact Set.mem_iUnion.mpr ⟨fun a b => e (e.symm a * e.symm b), G, hG, rfl, e, fun a b => by simp⟩

/-- `ncard` of a finite union is at most the sum of the `ncard`s. -/
lemma lqmg_ncard_biUnion_le {ι α : Type*} [DecidableEq ι] (I : Finset ι) (T : ι → Set α) :
    (⋃ i ∈ I, T i).ncard ≤ ∑ i ∈ I, (T i).ncard := by
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro a J ha ih
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

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
  classical
  let Sp : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Set FiniteGrp.{0} := fun p =>
    {G : FiniteGrp.{0} | Nat.card G = 2 ^ m ∧
      (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ ∧
      (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
      Group.rank G = p.1 ∧
      Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
        ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
          ((⊤ : Subgroup G).lowerCentralSeries 1)) = p.2.1 ∧
      sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
        ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} = p.2.2.1 ∧
      ((⊤ : Subgroup G).lowerCentralSeries 1).index = 2 ^ p.2.2.2.1 ∧
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) = 2 ^ p.2.2.2.2.1 ∧
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) = 2 ^ p.2.2.2.2.2.1 ∧
      Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) = p.2.2.2.2.2.2}
  let R1 : Finset ℕ := Finset.range (2 ^ m + 1)
  let R2 : Finset ℕ := Finset.range (m + 1)
  let B0 : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := R1 ×ˢ R1 ×ˢ R1 ×ˢ R2 ×ˢ R2 ×ˢ R2 ×ˢ R1
  let B : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := B0.filter (fun p => m / 7 < p.1)
  have hsub : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
        2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
        m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G} ⊆
      ⋃ p ∈ B, Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' Sp p := by
    rintro q ⟨G, ⟨hcard, hnc, -, hr, hcen⟩, rfl⟩
    obtain ⟨hne, hbot⟩ := class_three hnc hcen
    have hd1 : ((⊤ : Subgroup G).lowerCentralSeries 1).index ∣ 2 ^ m := by
      rw [← hcard]; exact Subgroup.index_dvd_card _
    have hd2 : Nat.card ((⊤ : Subgroup G).lowerCentralSeries 1) ∣ 2 ^ m := by
      rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
    have hd3 : Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∣ 2 ^ m := by
      rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨s1, hs1m, hs1⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    obtain ⟨m2, hm2m, hm2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
    obtain ⟨m3, hm3m, hm3⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd3
    have hcG : Nat.card G ≤ 2 ^ m := hcard.le
    have b1 : Group.rank G ≤ 2 ^ m := (lqmg_rank_le_card G).trans hcG
    have b2 : Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
        ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
          ((⊤ : Subgroup G).lowerCentralSeries 1)) ≤ 2 ^ m :=
      (lqmg_rank_quot_le _ _).trans hcG
    have hle : (⊤ : Subgroup G).lowerCentralSeries 2 ≤ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      Subgroup.lowerCentralSeries_antitone _ (by norm_num : 1 ≤ 2)
    have hle' : (⊤ : Subgroup G).lowerCentralSeries 2 ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := hle
    have hsI : sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
        ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} ≤
        Group.rank (⊤ : Subgroup G) :=
      Nat.sInf_le (Set.mem_setOf.mpr ⟨⊤, (sup_eq_left.mpr hle').symm, rfl⟩)
    have b3 : sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
        ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k} ≤ 2 ^ m :=
      hsI.trans ((lqmg_rank_sub_le _).trans hcG)
    have b7 : Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2) ≤ 2 ^ m :=
      (lqmg_rank_sub_le _).trans hcG
    refine Set.mem_iUnion₂.mpr ⟨(Group.rank G, Group.rank ((⊤ : Subgroup G).lowerCentralSeries 1 ⧸
        ((⊤ : Subgroup G).lowerCentralSeries 2).subgroupOf
          ((⊤ : Subgroup G).lowerCentralSeries 1)),
        sInf {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
          ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k},
        s1, m2, m3, Group.rank ((⊤ : Subgroup G).lowerCentralSeries 2)), ?_,
        G, ⟨hcard, hne, hbot, rfl, rfl, rfl, hs1, hm2, hm3, rfl⟩, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le b1),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le b2),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le b3),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hs1m),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm2m),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm3m),
        Finset.mem_range.mpr (Nat.lt_succ_of_le b7)⟩⟩⟩⟩⟩⟩, hr⟩
  have hfin : (⋃ p ∈ B, Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' Sp p).Finite :=
    Set.Finite.subset ((Finset.finite_toSet B).biUnion fun p _ =>
      lqmg_classes_finite (2 ^ m) (Sp p) fun G hG => hG.1) (fun x hx => by
        simp only [Set.mem_iUnion, Finset.mem_coe] at hx ⊢
        exact hx)
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := lqmg_ncard_biUnion_le B (fun p => Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' Sp p)
  have h3 : ∑ p ∈ B, (((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' Sp p).ncard : ℕ) : ℝ) ≤
      ∑ p ∈ B, X := Finset.sum_le_sum fun p hp =>
    h p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 (Finset.mem_filter.mp hp).2
  have hB0 : B0.card = (2 ^ m + 1) ^ 4 * (m + 1) ^ 3 := by
    simp only [B0, R1, R2, Finset.card_product, Finset.card_range]
    ring
  have h4 : (B.card : ℝ) ≤ ((2 ^ m + 1) ^ 4 * (m + 1) ^ 3 : ℝ) := by
    have : B.card ≤ (2 ^ m + 1) ^ 4 * (m + 1) ^ 3 := hB0 ▸ Finset.card_filter_le _ _
    exact_mod_cast this
  calc _ ≤ (((⋃ p ∈ B, Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' Sp p).ncard : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ p ∈ B, (((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' Sp p).ncard : ℕ) : ℝ) := by
        exact_mod_cast h2
    _ ≤ ∑ p ∈ B, X := h3
    _ = (B.card : ℝ) * X := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 hX

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
  have hn : (2 ^ m + 1) ^ 4 * (m + 1) ^ 3 ≤ 2 ^ (8 * m + 8) := by
    have h2 : m + 1 ≤ 2 ^ m := by
      induction m with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ]; linarith
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h1 : 2 ^ m + 1 ≤ 2 ^ (m + 1) := by rw [pow_succ]; linarith
    calc (2 ^ m + 1) ^ 4 * (m + 1) ^ 3 ≤ (2 ^ (m + 1)) ^ 4 * (2 ^ m) ^ 3 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left h1 4) (Nat.pow_le_pow_left h2 3)
      _ = 2 ^ (7 * m + 4) := by ring
      _ ≤ 2 ^ (8 * m + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : ((8 * m + 8 : ℕ) : ℝ) = 8 * (m : ℝ) + 8 := by push_cast; ring
  rw [← e, Real.rpow_natCast]
  exact_mod_cast hn

/-- `k^2 ≤ 2^k + 16` for all `k` (`k^2 ≤ 2^k` from `k = 4` on). -/
lemma lqmg_sq_le_two_pow (k : ℕ) : k ^ 2 ≤ 2 ^ k + 16 := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> norm_num
  · have h : k ^ 2 ≤ 2 ^ k := by
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        have h4 : 4 * n ≤ n * n := Nat.mul_le_mul_right n hn
        rw [pow_succ 2 n]
        nlinarith [ih, h4]
    linarith

/-- `(log_2 m)^2 ≤ m + 16`. -/
lemma lqmg_log_sq_le (m : ℕ) : (Nat.log 2 m) ^ 2 ≤ m + 16 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 := Nat.pow_log_le_self 2 hm.ne'
    have h2 := lqmg_sq_le_two_pow (Nat.log 2 m)
    linarith

/-- The exponent comparison behind `final_ineq`, with `x = m`, `L = log_2 m`, `L^2 ≤ x + 16`
and the threshold `x ≥ ⌈2 (27 |C|)^2⌉ + 500` (so `27 |C| (L + 1) ≤ x` and `x ≥ 500`). -/
lemma lqmg_final_exp (C x L : ℝ) (hx : ((Nat.ceil (2 * (27 * |C|) ^ 2) : ℕ) : ℝ) + 500 ≤ x)
    (hL0 : 0 ≤ L) (hL : L ^ 2 ≤ x + 16) :
    135 + 27 * (8 * x + 8 + (2 / 27 * x ^ 3 - 7 / 18 * x ^ 2 + C * x * (L + 1))) + 9 * x ^ 2 ≤
      2 * x ^ 3 := by
  have hceil : 2 * (27 * |C|) ^ 2 ≤ ((Nat.ceil (2 * (27 * |C|) ^ 2) : ℕ) : ℝ) := Nat.le_ceil _
  have hc0 : (0 : ℝ) ≤ ((Nat.ceil (2 * (27 * |C|) ^ 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ 27 * |C| := by positivity
  have hx500 : 500 ≤ x := by linarith
  have h2a : 2 * (27 * |C|) ^ 2 ≤ x - 500 := by linarith
  have hL1 : (L + 1) ^ 2 ≤ 2 * x + 34 := by nlinarith [sq_nonneg (L - 1)]
  have e1 := mul_le_mul_of_nonneg_left hL1 (sq_nonneg (27 * |C|))
  have e2 := mul_le_mul_of_nonneg_right h2a (by linarith : (0 : ℝ) ≤ x + 17)
  have hsq : (27 * |C| * (L + 1)) ^ 2 ≤ x ^ 2 := by nlinarith [e1, e2]
  have haL : 27 * |C| * (L + 1) ≤ x := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_self_lt_mul_self (by linarith : (0 : ℝ) ≤ x) hcon]
  have hCa : 27 * C ≤ 27 * |C| := by linarith [le_abs_self C]
  have hxL : 0 ≤ x * (L + 1) := mul_nonneg (by linarith) (by linarith)
  have h3 : 27 * C * (x * (L + 1)) ≤ 27 * |C| * (x * (L + 1)) :=
    mul_le_mul_of_nonneg_right hCa hxL
  have h4 : 27 * |C| * (L + 1) * x ≤ x * x := mul_le_mul_of_nonneg_right haL (by linarith)
  have h5 : 500 * x ≤ x * x := mul_le_mul_of_nonneg_right hx500 (by linarith)
  nlinarith [h3, h4, h5]

/-- The final inequality: `2^(8m+8)` parameter tuples, each contributing at most
`2^((2/27) m^3 - (7/18) m^2 + C m (log_2 m + 1))` classes, fit the target
`log_2 N ≤ (2/27) m^3 - m^2/3 - log_2 24` for large `m` (`7/18 > 1/3`). -/
lemma final_ineq (C : ℝ) : ∀ᶠ m : ℕ in atTop, ∀ N : ℕ,
    (N : ℝ) ≤ 2 ^ (8 * (m : ℝ) + 8) *
      2 ^ (2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 + C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1)) →
    (24 * N) ^ 27 * 2 ^ (9 * m ^ 2) ≤ 2 ^ (2 * m ^ 3) := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (2 * (27 * |C|) ^ 2) + 500)] with m hm N hN
  have hexp := lqmg_final_exp C (m : ℝ) (Nat.log 2 m : ℝ) (by exact_mod_cast hm)
    (Nat.cast_nonneg _) (by exact_mod_cast lqmg_log_sq_le m)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hN
  set F : ℝ := 8 * (m : ℝ) + 8 + (2 / 27 * (m : ℝ) ^ 3 - 7 / 18 * (m : ℝ) ^ 2 +
    C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1)) with hF
  have hu0 : (0 : ℝ) ≤ (2 : ℝ) ^ F := Real.rpow_nonneg (by norm_num) _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have e1 : ((32 : ℝ) * (2 : ℝ) ^ F) ^ 27 = (2 : ℝ) ^ ((135 : ℝ) + 27 * F) := by
    rw [mul_pow, Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast ((2 : ℝ) ^ F) 27,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h135 : (2 : ℝ) ^ (135 : ℝ) = (32 : ℝ) ^ 27 := by
      rw [show (135 : ℝ) = ((135 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h135]
    congr 2
    push_cast
    ring
  have e2 : (2 : ℝ) ^ (9 * m ^ 2) = (2 : ℝ) ^ (((9 * m ^ 2 : ℕ)) : ℝ) :=
    (Real.rpow_natCast _ _).symm
  have key : (((24 * N) ^ 27 * 2 ^ (9 * m ^ 2) : ℕ) : ℝ) ≤ ((2 ^ (2 * m ^ 3) : ℕ) : ℝ) := by
    push_cast
    calc (24 * (N : ℝ)) ^ 27 * (2 : ℝ) ^ (9 * m ^ 2) ≤
          ((32 : ℝ) * (2 : ℝ) ^ F) ^ 27 * (2 : ℝ) ^ (9 * m ^ 2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 27)
            (by positivity)
      _ = (2 : ℝ) ^ ((135 : ℝ) + 27 * F + ((9 * m ^ 2 : ℕ) : ℝ)) := by
          rw [e1, e2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (((2 * m ^ 3 : ℕ)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = (2 : ℝ) ^ (2 * m ^ 3) := Real.rpow_natCast _ _
  exact_mod_cast key

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
  sorry

/-- L3, the nonsaturated cubic (class-three analogue of (129)-(130)): for `0 ≤ h ≤ r` and
`h ≤ m - r`, `(r^2/2)(m - r - h) + h (m - r)^2 / 4 + h m^2 / 20 ≤ (2/27) m^3`.  Identity:
`(2/27) m^3 - (r^2/2)(m - r) = (1/2)(r - 2m/3)^2 (r + m/3)`; the minimum of the slack over the
admissible `h/m` is about `0.0529 m^3 > m^3/20 ·(h/m)`. -/
lemma ns_cubic (m r h : ℝ) (h0 : 0 ≤ h) (hr : h ≤ r) (hm : h ≤ m - r) :
    r ^ 2 / 2 * (m - r - h) + h * (m - r) ^ 2 / 4 + h * m ^ 2 / 20 ≤ 2 / 27 * m ^ 3 := by
  sorry

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
  sorry

/-- L7, closing for `δ ≥ 1` (`m^3 - n^3 = λ (m^2 + m n + n^2)`; split `λ < 32`, where
`e ≤ 465`, from `λ ≥ 32`, where `2 m2 e ≤ 2 m^2`). -/
lemma lam_close (m lam r1 m2 e : ℝ) (hl : 1 ≤ lam) (hn : r1 + m2 = m - lam) (h1 : 0 ≤ r1)
    (h2 : 0 ≤ m2) (he0 : 0 ≤ e) (he : e ≤ lam * (lam - 1) / 2) (hem : e ≤ m2) :
    2 / 27 * (m - lam) ^ 3 - 2 / 9 * (m - lam) ^ 2 + (m - lam) / 24 + 2 * m2 * e + r1 * lam ≤
      2 / 27 * m ^ 3 - 4 / 9 * m ^ 2 + 40 * m := by
  sorry

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
  sorry

/-- L10 (b): `C(s-1, 2) ≤ r2`, `s r2 < 2 r1 ≤ 2 m` give `(s - 2)^3 < 4 m`, hence `12 s^2 ≤ m`
for large `m`. -/
lemma small_core_size : ∃ m0 : ℕ, ∀ m s r1 r2 : ℕ, m0 ≤ m → (s - 1).choose 2 ≤ r2 →
    s * r2 < 2 * r1 → r1 ≤ m → 12 * s ^ 2 ≤ m := by
  sorry

/-- L10 (c): bounded Sims rank forces a small core: `s ≤ H`, `r2 ≤ C(s, 2)`, `m < 7 r1` and
`7 H^3 < 4 m` give `s r2 < 2 r1`. -/
lemma core_small_of_le (H m s r1 r2 : ℕ) (hs : s ≤ H) (hr : r2 ≤ s.choose 2) (h7 : m < 7 * r1)
    (hH : 7 * H ^ 3 < 4 * m) : s * r2 < 2 * r1 := by
  sorry

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
