import H2Dev.RedA
import H2Dev.CNT3Final

/-! # RedABridge: the reduction's `H1` follows from the library's `cnt3_stmt`

The inline `H1` of `RedA` is `CNT3Stmt` together with part (a) (`cnt3_partA`), reparametrized by
`s1 = log_2 |G : γ_2|` in place of `λ = s1 - r1` (`index_lcs_one_eq`), with the extra
constraints `r1 ≤ s1` (`index_lcs_one_eq`) and `r2 ≤ m2 - m3` (`cnt3_setup`). -/

namespace OMA.SimsLite

open scoped commutatorElement

theorem redA_H1 :
    OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1.H1 := by
  obtain ⟨C, hC⟩ := cnt3_stmt
  refine ⟨C, fun m r1 r2 s s1 m2 m3 r3 S hS hne => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨G, hG⟩ := hne
  have hle : r1 ≤ s1 := by
    have hG' := hG
    rw [hS] at hG'
    obtain ⟨hc, -, -, hr1, -, -, hi, -⟩ := hG'
    have hp : IsPGroup 2 G := IsPGroup.of_card hc
    have h := hi.symm.trans (index_lcs_one_eq hp)
    have h' := Nat.pow_right_injective (le_refl 2) h
    omega
  have hSeq : S = cnt3Set m r1 r2 s (s1 - r1) m2 m3 r3 := by
    rw [hS, cnt3Set, Nat.add_sub_of_le hle]
  have hne : (cnt3Set m r1 r2 s (s1 - r1) m2 m3 r3).Nonempty := ⟨G, hSeq ▸ hG⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cnt3_constraints_of_mem hne.some_mem
  obtain ⟨-, -, -, -, hr2s2, -, -⟩ := cnt3_setup hypPW hne
  refine ⟨⟨hle, c1, c2, c3, c4, hr2s2, c5, c6⟩, ?_⟩
  obtain ⟨b2, h1, h2, h3, hlog⟩ := hC m r1 r2 s (s1 - r1) m2 m3 r3 hne
  refine ⟨b2, h1, h2, h3, ?_⟩
  have e1 : cnt3Classes m r1 r2 s (s1 - r1) m2 m3 r3 =
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' S := by
    unfold cnt3Classes
    rw [hSeq]
  rw [e1, cnt3B, Alt2.logN2, Alt2.N2_eq_ncard] at hlog
  exact hlog

end OMA.SimsLite
