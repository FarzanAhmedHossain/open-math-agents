import H2Dev.CNT3Main
import H2Dev.CNT3PW
import H2Dev.CNT3B

/-! # CNT3: the unconditional class-3 Sims count

`hypPW` discharges `HypPW` from `CNT3PW` (`cnt3_hI`, `cnt3_codes_lf`, `cnt3_pw_le`).
`cnt3_cfactor_min` is the per-breadth `min (A b) (B b)` count of the commutator arrays, from
`cbt_realizedCB_ncard_le_min_two` (with `s0 = s`, since every group of `cnt3Set` has Sims rank
`s`, and `cnt3Layers` pins the code core size `D.2.1.val = s`).
`cnt3_stmt : CNT3Stmt` follows as in `cnt3_main`, with the summed per-breadth minimum in place
of the stratified cover. -/

namespace OMA.SimsLite

open scoped commutatorElement

section CNT3Final

/-- The power word input `HypPW`, proved. -/
theorem hypPW : HypPW := by
  intro m r1 r2 s lam m2 m3 r3 G hG
  obtain ⟨D, hc, hD⟩ := cnt3_hI G hG
  have h3 : D.1.1.val = 3 := (cnt3_codes_facts hD).1
  have h2 : 2 < D.1.1.val := by omega
  obtain ⟨hr1, hr2, -, hs, -, -, hs2, hs3⟩ := cnt3_codes_lf hD h2
  exact ⟨D, hc, ⟨h2, h3, hs, hr1, hr2, hs2, hs3⟩, cnt3_pw_le hD⟩

variable {m r1 r2 s lam m2 m3 r3 : ℕ}

lemma cnt3_min_mul_le (a b c : ℕ) : min a b * c ≤ min (a * c) (b * c) :=
  le_min (Nat.mul_le_mul_right _ (min_le_left _ _)) (Nat.mul_le_mul_right _ (min_le_right _ _))

/-- The per-breadth `min (A b) (B b)` commutator count (`cbt_realizedCB_ncard_le_min_two` after
the layer identifications). -/
theorem cnt3_cfactor_min (D : RecData m) (hL : cnt3Layers r1 r2 s m2 m3 D)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)) :
    (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard ≤
      ∑ β ∈ cnt3Adm s m2 m3,
        min (cnt3Aterm r1 r2 s m2 m3 β) (cnt3Bterm r1 r2 s m2 m3 β) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h2, h3, hs, hr1, hr2, hs2, hs3⟩ := hL
  have hT : ∀ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3, IsPGroup 2 G ∧ simsRank G = s := by
    intro G hG
    have hG' := (mem_cnt3Set_iff G).mp hG
    exact ⟨IsPGroup.of_card hG'.1, hG'.2.2.2.2.2.1⟩
  have h := cbt_realizedCB_ncard_le_min_two (cnt3Set m r1 r2 s lam m2 m3 r3) D h2 h3 B s hT
  rw [hs2, hs3, hr1, hr2] at h
  refine h.trans ?_
  rw [hs, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro β _
  refine (cnt3_min_mul_le _ _ _).trans (min_le_min (le_of_eq ?_) (le_of_eq ?_))
  · unfold cnt3Aterm
    ring
  · unfold cnt3Bterm
    rw [Nat.mul_comm (m2 - m3 - r2)]
    ring

/-- CNT3 (b), unconditionally. -/
theorem cnt3_stmt : CNT3Stmt := by
  obtain ⟨C0, hC0⟩ := hypData
  refine ⟨C0 + 1, fun m r1 r2 s lam m2 m3 r3 hne => ?_⟩
  obtain ⟨hm, hsr, hr2C, h32, hr2s2, hadm, hN⟩ := cnt3_setup hypPW hne
  obtain ⟨b2, hb2, hmax⟩ := Finset.exists_max_image (cnt3Adm s m2 m3)
    (fun β => min (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β)) hadm
  obtain ⟨hb2a, hb2b⟩ := cnt3Adm_mem.mp hb2
  refine ⟨b2, hb2b, (le_min_iff.mp hb2a).1, (le_min_iff.mp hb2a).2, ?_⟩
  set n := min (m2 - m3) m3 with hn
  have hcard := cnt3Adm_card_le s m2 m3
  have hM : ∀ D : RecData m, cnt3Layers r1 r2 s m2 m3 D →
      ∀ B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m),
        ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
          ((n : ℝ) + 1) * (2 : ℝ) ^ (min (cnt3A r1 r2 s m2 m3 b2) (cnt3B r1 r2 s m2 m3 b2)) := by
    intro D hL B
    have h1 := cnt3_cfactor_min (lam := lam) (r3 := r3) D hL B
    have h1' : ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
        ∑ β ∈ cnt3Adm s m2 m3,
          ((min (cnt3Aterm r1 r2 s m2 m3 β) (cnt3Bterm r1 r2 s m2 m3 β) : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h1'.trans (cnt3_sum_rpow_le hcard _
      (fun β => min (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β)) b2 (fun β hβ => ?_) hmax)
    obtain ⟨hβa, -⟩ := cnt3Adm_mem.mp hβ
    have eA := cnt3Aterm_cast (β := β) hsr hr2C h32 (le_min_iff.mp hβa).1 (le_min_iff.mp hβa).2
    have eB := cnt3Bterm_le (β := β) hsr hr2C h32 hr2s2 (le_min_iff.mp hβa).2
    have hSA' : ((min (cnt3Aterm r1 r2 s m2 m3 β) (cnt3Bterm r1 r2 s m2 m3 β) : ℕ) : ℝ) ≤
        (cnt3Aterm r1 r2 s m2 m3 β : ℝ) := by exact_mod_cast min_le_left _ _
    have hSB' : ((min (cnt3Aterm r1 r2 s m2 m3 β) (cnt3Bterm r1 r2 s m2 m3 β) : ℕ) : ℝ) ≤
        (cnt3Bterm r1 r2 s m2 m3 β : ℝ) := by exact_mod_cast min_le_right _ _
    show ((min (cnt3Aterm r1 r2 s m2 m3 β) (cnt3Bterm r1 r2 s m2 m3 β) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (min (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β))
    rcases le_total (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β) with hle | hle
    · rw [min_eq_left hle, ← eA]
      exact hSA'
    · rw [min_eq_right hle]
      exact hSB'.trans eB
  have hcount := cnt3_count_le hypPW _ (by positivity) hM
  have hnm : n ≤ m := by
    have := cnt3_m_eq hne.some_mem
    omega
  exact cnt3_final hC0 hm hnm hN hcount

end CNT3Final

end OMA.SimsLite
