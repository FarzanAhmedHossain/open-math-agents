import H2Dev.CNT3PW
import H2Dev.CNT3B
import H2Dev.LiftStrat
import H2Dev.CNT3Main

/-! # CNT3: the unconditional class-3 Sims count (route B)

* `cbt_realizedCBb_ncard_le` : term B at fixed core breadth `b` on the canonical strata
  `realizedCBb ... b` of `H2Dev.LiftStrat` (the per-breadth form of `cbt_realizedCB_ncard_le`:
  the leading pairs of breadth `lfsBr = b` are counted by `cbt_lead_B_breadth`, their breadth
  `cbtBrL` being `b` by `cbtBrV_eq` and `LfIdent.lfs_breadth_eq`).
* `cbt_realizedCBb_ncard_le_two` : the same at `p = 2` with `Alt2.N2`.
* `hypBStrat` : `HypBStrat` (the core size `D.2.1.val = s` is pinned by `cnt3Layers`, and every
  group of `cnt3Set` has Sims rank `s`).
* `hypPW` : `HypPW` (from `cnt3_hI`, `cnt3_codes_lf`, `cnt3_codes_facts`, `cnt3_pw_le`).
* `cnt3_stmt : CNT3Stmt` (from `cnt3_main_strat`). -/

namespace OMA.SimsLite

open scoped commutatorElement

section CbtStrat

/-- Term B at fixed core breadth `b` on the canonical strata. -/
theorem cbt_realizedCBb_ncard_le {p m : ℕ} [Fact p.Prime] (hp : p.Prime)
    (T : Set FiniteGrp.{0}) (D : RecData m) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) (s0 : ℕ)
    (hT : ∀ G ∈ T, IsPGroup p G ∧ simsRank G = s0) (b : ℕ) :
    (realizedCBb hp T D B b).ncard ≤
      (p ^ (D.2.1.val * (b * (fibRk D (lfI1 h2) + (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1 - b))) *
          ({t : Fin (fibRk D (lfI1 h2)) →
              Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
              (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0}.ncard *
            p ^ (((∑ v, fibAk D ⟨lfI1 h2, v⟩) - fibRk D (lfI1 h2)) *
              ((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2))))) *
        p ^ (((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2)) *
          ∑ v, fibAk D ⟨lfI2 h2, v⟩) := by
  rcases (realizedCBb hp T D B b).eq_empty_or_nonempty with hE | ⟨C0, hC0⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0, hG0T, u0, d0, X0, r0, hS0, hnm0, hs0, hsum0, e0, -⟩ := hC0
  obtain ⟨c1, c2, c3, -, -, -, c7, c8⟩ := hS0.lf_code hp hnm0 hs0 hsum0 e0
  have hn0 : d0.n = fOff r0 D.1.val := by rw [← c1]; exact hS0.nL_spec.symm
  have hr00 : r0 0 = fibR D 0 := c3 0 (by rw [c1]; omega)
  have hr01 : r0 1 = fibR D 1 := c3 1 (by rw [c1]; omega)
  have hsr0 := (hS0.lf_core hn0 (by omega) hS0.lf_hcore).1
  have hsr : D.2.1.val ≤ fibRk D (lfI0 h2) := by
    show D.2.1.val ≤ fibR D 0
    rw [← c2, ← hr00]
    exact hsr0
  have hgood : ∀ C ∈ realizedCBb hp T D B b, LfGood p hp.pos D h2 B (brCo d0 r0) C := by
    rintro C ⟨G, -, u, d, X, r, hS, hnm, hs2, hsum, e, -⟩
    obtain ⟨g1, g2, g3, -, -, -, g7, -⟩ := hS.lf_code hp hnm hs2 hsum e
    refine hS.lf_good hp hnm hs2 hsum e h2 h3 _
      (lf_brCo_common hS hS0 hs2 (g2.trans c2.symm) ?_ ?_)
    · rw [g3 1 (by rw [g1]; omega), hr01]
    · intro k hk
      rw [g7 k hk, c7 k (by rw [c2, ← g2]; exact hk)]
  have hleadB : ∀ C ∈ realizedCBb hp T D B b, ∃ x ∈ lfLamB p D h2 (lfBB D B (lfI0 h2))
      (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2)) (lfDp D h2 (lfFa D) (brCo d0 r0))
      (lfW D h2 (lfFa D) (brCo d0 r0)) b, lfPhi1 D h2 C = lfTrunc D h2 (brCo d0 r0) x := by
    rintro C ⟨G, -, u, d, X, r, hS, hnm, hs2, hsum, e, hb⟩
    obtain ⟨g1, g2, g3, -, -, -, g7, -⟩ := hS.lf_code hp hnm hs2 hsum e
    rw [← hb]
    refine hS.lfs_lead hp hnm hs2 hsum e h2 h3 _
      (lf_brCo_common hS hS0 hs2 (g2.trans c2.symm) ?_ ?_)
    · rw [g3 1 (by rw [g1]; omega), hr01]
    · intro k hk
      rw [g7 k hk, c7 k (by rw [c2, ← g2]; exact hk)]
  have htup : ∀ C ∈ realizedCBb hp T D B b, cbtTup p (lfPhi1 D h2 C).1 ∈
      {t : Fin (fibRk D (lfI1 h2)) →
        Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
        (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0} := by
    rintro C ⟨G, hGT, u, d, X, r, hS, hnm, hs2, hsum, e, -⟩
    obtain ⟨hpG, hsG⟩ := hT G hGT
    obtain ⟨⟨t1, t2, t3⟩, -⟩ := hS.cbt_tuple hp hnm hs2 hsum e h2 hpG
    exact ⟨t1, t2, t3.trans hsG⟩
  have hb1div : ∀ j v, p ∣ lfBB D B (lfI1 h2) j v :=
    (hS0.cbt_tuple hp hnm0 hs0 hsum0 e0 h2 (hT G0 hG0T).1).2
  have hjr : ∀ j : Fin (fibRk D (lfI1 h2)), j.val < r0 1 := fun j => by
    have : j.val < fibR D 1 := j.isLt
    omega
  have hDp : ∀ q ∈ lfDp D h2 (lfFa D) (brCo d0 r0), q.1 < q.2 ∧ (q.1 : ℕ) < D.2.1.val := by
    intro q hq
    obtain ⟨j, hj1, hj2⟩ := (Finset.mem_filter.mp hq).2
    rw [← c8 _ (hjr j)] at hj1
    refine ⟨?_, ?_⟩
    · show q.1.val < q.2.val
      rw [hj1, hj2]
      exact hS0.lf_brPa_lt_brCo hs0 (hjr j)
    · rw [hj1, ← c2]
      have := hS0.brPa_lt hs0 j.val (hjr j)
      omega
  have hb1 : ∀ j : Fin (fibRk D (lfI1 h2)), lfFa D j.val < fibRk D (lfI0 h2) := by
    intro j
    show lfFa D j.val < fibR D 0
    rw [← c8 _ (hjr j), ← hr00]
    have := hS0.brPa_lt hs0 j.val (hjr j)
    omega
  have hb2 : ∀ j : Fin (fibRk D (lfI1 h2)), brCo d0 r0 j.val < fibRk D (lfI0 h2) := by
    intro j
    show brCo d0 r0 j.val < fibR D 0
    rw [← hr00]
    have := hS0.brCo_bounds hs0 j.val (hjr j)
    omega
  obtain ⟨F, hF⟩ : ∃ F : Fin (fibRk D (lfI1 h2)) →
      Fin (fibRk D (lfI0 h2)) × Fin (fibRk D (lfI0 h2)),
      ∀ j, (F j).1.val = lfFa D j.val ∧ (F j).2.val = brCo d0 r0 j.val :=
    ⟨fun j => (⟨_, hb1 j⟩, ⟨_, hb2 j⟩), fun j => ⟨rfl, rfl⟩⟩
  have hFinj : Function.Injective F := by
    intro j j' hjj
    have e1 : lfFa D j.val = lfFa D j'.val := by rw [← (hF j).1, ← (hF j').1, hjj]
    have e2 : brCo d0 r0 j.val = brCo d0 r0 j'.val := by rw [← (hF j).2, ← (hF j').2, hjj]
    rw [← c8 _ (hjr j), ← c8 _ (hjr j')] at e1
    exact Fin.ext (hS0.lf_pair_inj hs0 (hjr j) (hjr j') e1 e2)
  have himg : lfDp D h2 (lfFa D) (brCo d0 r0) = Finset.univ.image F := by
    ext q
    simp only [lfDp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨j, h1, h2'⟩
      exact ⟨j, Prod.ext (Fin.ext ((hF j).1.trans h1.symm)) (Fin.ext ((hF j).2.trans h2'.symm))⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, (hF j).1, (hF j).2⟩
  have hDcard : (lfDp D h2 (lfFa D) (brCo d0 r0)).card = fibRk D (lfI1 h2) := by
    rw [himg, Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_fin]
  -- the counted leading pairs: those of breadth `b` with an admissible matrix tuple
  obtain ⟨ΛB, hΛB⟩ : ∃ Λ : Set (LfLeadT D h2), Λ =
      {x | x ∈ lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2))
        (lfDp D h2 (lfFa D) (brCo d0 r0)) (lfW D h2 (lfFa D) (brCo d0 r0)) b ∧
        cbtTup p x.1 ∈ {t : Fin (fibRk D (lfI1 h2)) →
          Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
          (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0}} := ⟨_, rfl⟩
  have hΛsub : ∀ x ∈ ΛB, x ∈ lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2))
      (lfBB D B (lfI2 h2)) (lfDp D h2 (lfFa D) (brCo d0 r0))
      (lfW D h2 (lfFa D) (brCo d0 r0)) b ∧
      cbtTup p x.1 ∈ {t : Fin (fibRk D (lfI1 h2)) →
        Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
        (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0} := by
    intro x hx
    rw [hΛB] at hx
    exact hx
  have hΛfin : ΛB.Finite := by
    refine (Set.finite_range (fun y : (Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI0 h2)) →
        (v : Fin (fibRk D (lfI1 h2))) → Fin (p ^ fibAk D ⟨lfI1 h2, v⟩)) ×
        (Fin (fibRk D (lfI1 h2)) → Fin (fibRk D (lfI0 h2)) →
          (v : Fin (fibRk D (lfI2 h2))) → Fin (p ^ fibAk D ⟨lfI2 h2, v⟩)) =>
        ((fun j k v => (y.1 j k v).val, fun j k v => (y.2 j k v).val) : LfLeadT D h2))).subset ?_
    intro x hx
    obtain ⟨⟨-, hx1, hx2⟩, -⟩ := hΛsub x hx
    exact ⟨(fun j k v => ⟨x.1 j k v, hx1 j k v⟩, fun j k v => ⟨x.2 j k v, hx2 j k v⟩), rfl⟩
  -- term B at breadth `b`
  have hLead := cbt_lead_B_breadth (p := p) (c := D.1.val) (r := fibRk D) (a := fibAk D) hp h2
    (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2)) hb1div hsr
    (lfDp D h2 (lfFa D) (brCo d0 r0)) hDp (lfW D h2 (lfFa D) (brCo d0 r0))
    {t : Fin (fibRk D (lfI1 h2)) →
      Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
      (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0} ΛB
    (fun x hx => by
      obtain ⟨⟨G, i1, i2, g, S, q0, q1, q2, ql, qc, qD, -, qe⟩, -, -⟩ := (hΛsub x hx).1
      exact ⟨G, i1, i2, g, S, q0, q1, q2, ql, qc, qD, qe⟩)
    (fun x hx => (hΛsub x hx).2) b
    (fun x hx => by
      obtain ⟨⟨G, i1, i2, g, S, q0, q1, q2, ql, -, -, qbr, rfl⟩, -, -⟩ := (hΛsub x hx).1
      obtain ⟨I⟩ := S.lf_ident_nonempty hp.pos h2 ql (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2))
        (lfBB D B (lfI2 h2)) q0 q1 q2
      exact (cbtBrV_eq p D.2.1.val
        (cbtGen_closure p (fun v => fibAk D ⟨lfI0 h2, v⟩) (lfBB D B (lfI0 h2)))
        (cbtGen_closure p (fun v => fibAk D ⟨lfI1 h2, v⟩) (lfBB D B (lfI1 h2)))
        (fun j k => cbtVec p (fun v => fibAk D ⟨lfI2 h2, v⟩) (lfBB D B (lfI2 h2))
          (S.lfLead2 h2 j k))
        (brT2 (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)) I.cbt_val2).trans
        ((I.lfs_breadth_eq D.2.1.val).trans qbr))
  rw [hDcard] at hLead
  -- the deeper count
  have hDeep := br_deeper_count_fin (Γ := LfDeepG p D h2)
    (lf_card_box (p := p) (fun v : Fin (fibRk D (lfI2 h2)) => fibAk D ⟨lfI2 h2, v⟩))
    (lfDp D h2 (lfFa D) (brCo d0 r0)) (fun q hq => (hDp q hq).1)
    (fun _ _ => ⟨0, pow_pos hp.pos _⟩)
  rw [hDcard] at hDeep
  have hinj : Set.InjOn (fun C => (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C))
      (realizedCBb hp T D B b) := by
    intro C hC C' hC' he
    exact lf_phi_inj hp.pos h2 (hgood C hC) (hgood C' hC') (congrArg Prod.fst he)
      (congrArg Prod.snd he)
  have hmaps : ∀ C ∈ realizedCBb hp T D B b,
      (fun C => (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C)) C ∈
      (lfTrunc D h2 (brCo d0 r0) '' ΛB) ×ˢ
        lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0)) := by
    intro C hC
    obtain ⟨x, hx, hxe⟩ := hleadB C hC
    have hxB : x ∈ ΛB := by
      rw [hΛB]
      refine ⟨hx, ?_⟩
      have h := htup C hC
      rw [hxe, cbt_tup_trunc] at h
      exact h
    show (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C) ∈ _
    exact Set.mk_mem_prod ⟨x, hxB, hxe.symm⟩ (hgood C hC).deep
  calc (realizedCBb hp T D B b).ncard
      ≤ ((lfTrunc D h2 (brCo d0 r0) '' ΛB) ×ˢ
          lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
          ((hΛfin.image (lfTrunc D h2 (brCo d0 r0))).prod (Set.toFinite _))
    _ = (lfTrunc D h2 (brCo d0 r0) '' ΛB).ncard *
          (lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard := Set.ncard_prod
    _ ≤ ΛB.ncard * (lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard :=
        Nat.mul_le_mul_right _ (Set.ncard_image_le hΛfin)
    _ ≤ _ := Nat.mul_le_mul hLead hDeep

/-- `cbt_realizedCBb_ncard_le` at `p = 2` with the count `N_2(r_1, r_2, s0)`. -/
theorem cbt_realizedCBb_ncard_le_two {m : ℕ} (T : Set FiniteGrp.{0})
    (D : RecData m) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)) (s0 : ℕ)
    (hT : ∀ G ∈ T, IsPGroup 2 G ∧ simsRank G = s0) (b : ℕ) :
    (realizedCBb Nat.prime_two T D B b).ncard ≤
      (2 ^ (D.2.1.val * (b * (fibRk D (lfI1 h2) + (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1 - b))) *
          (Alt2.N2 (fibRk D (lfI0 h2)) (fibRk D (lfI1 h2)) s0 *
            2 ^ (((∑ v, fibAk D ⟨lfI1 h2, v⟩) - fibRk D (lfI1 h2)) *
              ((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2))))) *
        2 ^ (((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2)) *
          ∑ v, fibAk D ⟨lfI2 h2, v⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Alt2.N2_eq_ncard]
  exact cbt_realizedCBb_ncard_le Nat.prime_two T D h2 h3 B s0 hT b

end CbtStrat

section CNT3Final

/-- The per-breadth term-B input on the canonical strata. -/
theorem hypBStrat : HypBStrat := by
  intro m r1 r2 s lam m2 m3 r3 D hL B β _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h2, h3, hs, hr1, hr2, hs2, hs3⟩ := hL
  have hT : ∀ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3, IsPGroup 2 G ∧ simsRank G = s := by
    intro G hG
    exact ⟨IsPGroup.of_card hG.1, ((mem_cnt3Set_iff G).mp hG).2.2.2.2.2.1⟩
  have h := cbt_realizedCBb_ncard_le_two (cnt3Set m r1 r2 s lam m2 m3 r3) D h2 h3 B s hT β
  rw [hs2, hs3, hr1, hr2] at h
  refine h.trans (le_of_eq ?_)
  rw [hs]
  unfold cnt3Bterm
  ring

/-- The power word input. -/
theorem hypPW : HypPW := by
  intro m r1 r2 s lam m2 m3 r3 G hG
  obtain ⟨D, hc, hD⟩ := cnt3_hI G hG
  have h3 : D.1.1.val = 3 := (cnt3_codes_facts hD).1
  have h2 : 2 < D.1.1.val := by omega
  obtain ⟨hR0, hR1, -, hs, -, -, hS1, hS2⟩ := cnt3_codes_lf hD h2
  exact ⟨D, hc, ⟨h2, h3, hs, hR0, hR1, hS1, hS2⟩, cnt3_pw_le hD⟩

/-- CNT3 (b), unconditional. -/
theorem cnt3_stmt : CNT3Stmt :=
  cnt3_main_strat hypPW hypBStrat

end CNT3Final

end OMA.SimsLite

#print axioms OMA.SimsLite.cnt3_stmt
