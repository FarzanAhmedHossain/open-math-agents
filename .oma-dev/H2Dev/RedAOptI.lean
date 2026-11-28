import H2Dev.RedA

/-!
# Option I fallback for reduction A (dev only, not part of the submission)

If the reviewer rejects `RedA.H2` (MULT3) because it is stated for `C(s-1, 2) ≤ r2`, while
Corollary 14.1 of Li-Qiao is stated only in the saturated range `C(s-1, 2) < r2`, the split
becomes four hypotheses:
* `H1` (CNT3) and `H3` (N2A, Theorem 7.1 (i)) unchanged (from `RedA`);
* `H2s`: `RedA.H2` with the strict saturation hypothesis `C(s-1, 2) < r2`;
* `H4`: Theorem 7.1 (ii) (p.44, (90); proof Section 10, pp.60-67, via Prop 10.1 and Prop 10.4)
  at the binary endpoint `r2 = C(s-1, 2)`, pure `F_2`.
`main` then additionally needs Lemma 11.1 (endpoint absorption, (124), p.67; stated below as
`endpoint_absorption`), with Theorem 11.3 at class three, for the case `δ = 0`,
`r2 = C(s-1, 2)`, `2 r1 ≤ s r2`: `H1` with the `B` term, `H4` bounds `N_2`, and
`endpoint_absorption` closes the cubic (with `R = r1 - s + 1`, `h = s - 1`).  The remaining
cases of `RedA.per_param` are unchanged (`H2s` is used only when `C(s-1, 2) < r2`).
The statements here are drafts; `main_optI` and `endpoint_absorption` are `sorry`.
-/

open Subgroup Filter CategoryTheory
open scoped commutatorElement Matrix

namespace OMA.RedAOptI

open OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1

/-- MULT3 in the saturated range only: `RedA.H2` with `C(s-1, 2) < r2`, matching the range of
Corollary 14.1 (Li-Qiao, pp.81-82).  Same citation chain as `RedA.H2`: (87) (p.42) with `Δ_p`
omitted, minus `s (dim K) r2` by Remark 6.4 (p.43), the `k (r1 - k)` subspace count and the
multiplicity of Proposition 13.1 (p.80) with `dim Z_0 = r1 - s` at `δ = 0` (p.79), as in the
proofs of Proposition 13.2 and Corollary 14.1. -/
def H2s : Prop :=
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
    s1 = r1 → (s - 1).choose 2 < r2 → S.Nonempty →
    ∃ b2 k : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧ k ≤ r1 - s ∧
      Real.logb 2 ((Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' S).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) +
        ((r1 * m2 + (r1 - 1) * (s1 - r1) + (r2 * m3 + (r2 - 1) * (m2 - m3 - r2)) +
          (r3 - 1) * (m3 - r3) : ℕ) : ℝ) +
        (((r1.choose 2 : ℝ) - r2) * m2 +
          (b2 : ℝ) * ((s : ℝ) * ((r2 : ℝ) + m3 - b2 + 1) - ((r1 - s).choose 2 : ℝ))) -
        ((r1 - s : ℕ) : ℝ) ^ 2 + (k : ℝ) * (2 * (r1 : ℝ) - s - k - (s : ℝ) * r2)

/-- N2B: Li-Qiao, Theorem 7.1 (ii) (p.44, (90); proof in Section 10) at the binary endpoint
`r2 = C(s-1, 2)`: with `a = min (⌊2 (s-1)^2 / 5⌋, ⌊r1 / 2⌋)`, the number of surjective alternating
maps `∧² F_2^r1 → F_2^r2` of Sims rank `s` is at most
`2^((r2 - s + 1) C(r1, 2) + (s - 1) a (2 r1 - 2 a - 1) + O(r1^2 + r2^2))`. -/
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

/-- `H2s` is the specialization of `RedA.H2`, so Option I is never stronger than Option II
in this hypothesis. -/
lemma H2s_of_H2 (h : H2) : H2s := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun m r1 r2 s s1 m2 m3 r3 S hS hd hr hne =>
    hC m r1 r2 s s1 m2 m3 r3 S hS hd hr.le hne⟩

/-- Lemma 11.1 (endpoint absorption, Li-Qiao (124), p.67), part of `main` in Option I:
for `m ≥ 2`, `h ≥ 1`, `R + C(h, 2) ≤ m`, `w = m - R - C(h, 2)` and `0 ≤ θ ≤ 4/5`,
`R^2 (m - R - h)/2 + (h^3/2 - h^2) w + h w^2 / 2 + θ h^3 R - θ^2 h^5 / 2
  ≤ (2/27) m^3 - (11/1602) h m^2 + O(m^2)`. -/
lemma endpoint_absorption : ∃ C : ℝ, ∀ m R h : ℕ, ∀ θ : ℝ, 2 ≤ m → 1 ≤ h →
    R + h.choose 2 ≤ m → 0 ≤ θ → θ ≤ 4 / 5 →
    (R : ℝ) ^ 2 * ((m : ℝ) - R - h) / 2 +
      ((h : ℝ) ^ 3 / 2 - (h : ℝ) ^ 2) * ((m : ℝ) - R - (h.choose 2 : ℝ)) +
      (h : ℝ) / 2 * ((m : ℝ) - R - (h.choose 2 : ℝ)) ^ 2 + θ * (h : ℝ) ^ 3 * R -
      θ ^ 2 / 2 * (h : ℝ) ^ 5 ≤
      2 / 27 * (m : ℝ) ^ 3 - 11 / 1602 * (h : ℝ) * (m : ℝ) ^ 2 + C * (m : ℝ) ^ 2 := by
  sorry

/-- Reduction A, Option I: CNT3, MULT3 (saturated), N2A and N2B give the target.
(Dev draft; the target body of `...R1.H3.R2.H1` is restated.) -/
theorem main_optI : H1 → H2s → H3 → H4 →
    ∀ᶠ m : ℕ in atTop,
      (24 * (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = 2^m ∧ ¬commutator G ≤ Subgroup.center G ∧
          2 < Nat.card ((⊤ : Subgroup G).lowerCentralSeries 2) ∧
          m / 7 < Group.rank G ∧ (⊤ : Subgroup G).lowerCentralSeries 2 ≤ Subgroup.center G}).ncard)^27 *
          2^(9*m^2) ≤ 2^(2*m^3) := by
  sorry

end OMA.RedAOptI
