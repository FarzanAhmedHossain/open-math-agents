import H2Dev.CNT3Stmt
import H2Dev.Lift

/-! # CNT3: the power word term and the data count

The two terms of CNT3 (b) that do not involve the commutator coefficients: the power word factor
`2 ^ cnt3PW` (Theorem 3.1 at `c = 3`) and the count `2 ^ O(m log m)` of the recorded data
(Proposition 2.5). `p = 2` throughout.

## Deliverables (exact statements)

The index set of recorded data:

* `cnt3Codes m r1 r2 s lam m2 m3 r3 : Finset (RecData m)`, the recorded data `D` with core size
  `D.2.1.val = s` for which some group of `cnt3Set m r1 r2 s lam m2 m3 r3` has a Sims code
  `⟨D, x⟩`; `mem_cnt3Codes`. The core size is pinned to the true `s = simsRank G`, since the
  bound of `lf_realizedCB_ncard_le` is stated with `D.2.1.val` and grows with it.
* `cnt3_hI : ∀ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3, ∃ D : FullData 2 m,
    SimsCode Nat.prime_two m G D ∧ D.1 ∈ cnt3Codes m r1 r2 s lam m2 m3 r3`
  (the hypothesis `hI` of `Bridge.ncard_classes_le_fiber_pw` / `Lift.lf_ncard_classes_le_fiberB_pw`),
  proved from `exists_sims_gen`, whose Sims data have `d.s = simsRank G`.

(1) The power word term:

* `cnt3_code_facts` (for a group `G ∈ cnt3Set ...` with a Sims code `⟨D, (B, C)⟩`) and
  `cnt3_codes_facts` (for `D ∈ cnt3Codes ...`):
  `D.1.val = 3 ∧ fibR D 0 = r1 ∧ fibR D 1 = r2 ∧ fibR D 2 = r3 ∧ s ≤ D.2.1.val ∧ m3 ≤ m2 ∧
    (∀ h : 0 < D.1.val, sL (fibAk D) ⟨0, h⟩ = r1 + lam) ∧
    (∀ h : 1 < D.1.val, sL (fibAk D) ⟨1, h⟩ = m2 - m3) ∧
    (∀ h : 2 < D.1.val, sL (fibAk D) ⟨2, h⟩ = m3)`
  (`sL a i = Σ_v a ⟨i, v⟩`; `s ≤ D.2.1.val` is `simsRank G ≤ d.s` for the code's Sims data);
  in `cnt3_codes_facts` the conjunct `s ≤ D.2.1.val` is strengthened to `D.2.1.val = s`;
* `cnt3_codes_lf` : the same (with `D.2.1.val = s`) in the `lfI0 / lfI1 / lfI2` form used by
  `lf_realizedCB_ncard_le`;
* `cnt3_pw_eq : D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3 →
    pwBound2 (fibAk D) = cnt3PW r1 r2 r3 lam m2 m3` and `cnt3_pw_le` (the `≤` form);
* `cnt3_ncard_le_pw` : for `M : RecData m → ℕ` with
  `∀ D ∈ cnt3Codes .., ∀ B ∈ realizedB Nat.prime_two (cnt3Set ..) D,
    (realizedCB Nat.prime_two (cnt3Set ..) D B).ncard ≤ M D`,
  `(cnt3Classes ..).ncard ≤ Σ_{D ∈ cnt3Codes ..} 2 ^ cnt3PW r1 r2 r3 lam m2 m3 * M D`.

(2) The data count, with the explicit constant `C0 = 7`:

* `card_recData_le_log m : Fintype.card (RecData m) ≤ 2 ^ (7 * m * (Nat.log 2 m + 1))`;
* `cnt3_data_le (I : Finset (RecData m)) : I.card ≤ 2 ^ (7 * m * (Nat.log 2 m + 1))` (the
  uniform data count with `C0 = 7`, valid for any index set, in particular `cnt3Codes`);
* `cnt3_ncard_le_uniform` : for a uniform bound `M0` on the fibres,
  `(cnt3Classes ..).ncard ≤ 2 ^ (7 * m * (Nat.log 2 m + 1)) * (2 ^ cnt3PW .. * M0)`;
* `cnt3_logb_le : n ≤ 2 ^ k → Real.logb 2 n ≤ k` (for the final real assembly).

Group-level ingredients (for any `SimsGen p u d X r` of a finite group): `SimsGen.c3_nL_eq`
(`nL = 3` at class exactly 3), `SimsGen.c3_r0_eq` (`r 0 = d(G)`), `SimsGen.c3_r1_eq`
(`r 1 = r2 p G`), `SimsGen.c3_r2_eq` (`r 2 = d(γ_3)` when `γ_4 = 1`, by Burnside for `γ_3`),
`SimsGen.c3_simsRank_le`, and `c3_code_layer_card` (`|γ_{i+1} / γ_{i+2}| = p ^ Σ_v a(i, v)` read
off the code). -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

/-! ### Theorem 3.1's exponent at three layers -/

section C3PWArith

/-- `pwBound2` at `c = 3`, in terms of the layer ranks `R_i` and layer sums `S_i`. -/
theorem c3_pwBound2_three {c : ℕ} {r : Fin c → ℕ} (a : SimsIdx c r → ℕ) (hc : c = 3)
    (R0 R1 R2 S0 S1 S2 : ℕ)
    (hr : ∀ i : Fin c, r i = if i.val = 0 then R0 else if i.val = 1 then R1 else R2)
    (hs : ∀ i : Fin c, sL a i = if i.val = 0 then S0 else if i.val = 1 then S1 else S2) :
    pwBound2 a = (R0 * (S1 + S2) + (R0 - 1) * (S0 - R0)) + (R1 * S2 + (R1 - 1) * (S1 - R1)) +
      (R2 - 1) * (S2 - R2) := by
  subst hc
  have hr0 : r 0 = R0 := by simp (config := {decide := true}) [hr]
  have hr1 : r 1 = R1 := by simp (config := {decide := true}) [hr]
  have hr2 : r 2 = R2 := by simp (config := {decide := true}) [hr]
  have hs0 : sL a 0 = S0 := by simp (config := {decide := true}) [hs]
  have hs1 : sL a 1 = S1 := by simp (config := {decide := true}) [hs]
  have hs2 : sL a 2 = S2 := by simp (config := {decide := true}) [hs]
  have hm0 : mAbove a 0 = S1 + S2 := by
    unfold mAbove
    rw [Finset.sum_filter, Fin.sum_univ_three]
    simp (config := {decide := true}) [hs1, hs2]
  have hm1 : mAbove a 1 = S2 := by
    unfold mAbove
    rw [Finset.sum_filter, Fin.sum_univ_three]
    simp (config := {decide := true}) [hs2]
  have hm2 : mAbove a 2 = 0 := by
    unfold mAbove
    rw [Finset.sum_filter, Fin.sum_univ_three]
    simp (config := {decide := true})
  unfold pwBound2
  simp only [Fin.sum_univ_three, hm0, hm1, hm2, hs0, hs1, hs2, hr0, hr1, hr2]
  ring

end C3PWArith

/-! ### Layer orders read off a code -/

section C3Layer

/-- `|γ_{i+1} / γ_{i+2}| |γ_{i+2}| = |γ_{i+1}|`. -/
theorem c3_card_layerQ_mul {H : Type u} [Group H] (i : ℕ) :
    Nat.card (LayerQ H i) * Nat.card (lcs H (i + 1)) = Nat.card (lcs H i) := by
  have h1 := Subgroup.card_mul_index ((lcs H (i + 1)).subgroupOf (lcs H i))
  have h2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (lcs_antitone (Nat.le_succ i) : lcs H (i + 1) ≤ lcs H i)).toEquiv
  rw [h2] at h1
  rw [mul_comm]
  exact h1

/-- The order of a layer from a Sims code: `|γ_{i+1} / γ_{i+2}| = p ^ Σ_v a(i, v)`, with the
relative orders `a(i, v)` recorded in `D`. -/
theorem c3_code_layer_card {p m : ℕ} (hp : p.Prime) {H : Type u} [Group H] [Finite H]
    {D : RecData m} {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    (hc : SimsCode hp m H (⟨D, (B, C)⟩ : FullData p m)) (i : Fin D.1.val)
    (hlast : i.val + 1 < D.1.val ∨ lcs H (i.val + 1) = ⊥) :
    Nat.card (LayerQ H i.val) = p ^ sL (fibAk D) i := by
  obtain ⟨u, d, X, r, hS, hnm, hs2, hsum, e⟩ := hc
  obtain ⟨c1, -, c3, c4, -⟩ := hS.lf_code hp hnm hs2 hsum e
  have hn : d.n = fOff r hS.nL := hS.nL_spec.symm
  have hi : i.val < hS.nL := by rw [c1]; exact i.isLt
  have hl : i.val + 1 < hS.nL ∨ lcs H (i.val + 1) = ⊥ := by rw [c1]; exact hlast
  have h := (hS.toSimsGenSet hp hn).lf_card_layer hp.pos ⟨i.val, hi⟩ hl
  refine h.trans ?_
  congr 1
  show ∑ v : Fin (r i.val), d.a (hS.brEquiv hn ⟨⟨i.val, hi⟩, v⟩) =
    ∑ v : Fin (fibR D i.val), fibA D (fOff (fibR D) i.val + v.val)
  have e1 : ∑ v : Fin (r i.val), d.a (hS.brEquiv hn ⟨⟨i.val, hi⟩, v⟩) =
      ∑ v : Fin (r i.val), brA d (fOff r i.val + v.val) :=
    Finset.sum_congr rfl (fun v _ => (hS.brA_brEquiv hn ⟨⟨i.val, hi⟩, v⟩).symm)
  rw [e1, Fin.sum_univ_eq_sum_range (fun v => brA d (fOff r i.val + v)) (r i.val),
    Fin.sum_univ_eq_sum_range (fun v => fibA D (fOff (fibR D) i.val + v)) (fibR D i.val),
    c3 i.val hi, fOff_congr (c := i.val) (fun w hw => c3 w (by omega)) i.val le_rfl, c4]

end C3Layer

/-! ### Layer ranks of a Sims generating set at class 3 -/

section C3Ranks

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {u : ℕ → G} {d : SimsData}
  {X : Fin d.n → G} {r : ℕ → ℕ}

/-- At class exactly 3 (`γ_3 ≠ 1`, `γ_4 = 1`) a Sims generating set has exactly 3 layers. -/
theorem SimsGen.c3_nL_eq (hp : p.Prime) (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s)
    (h3 : lcs G 2 ≠ ⊥) (h4 : lcs G 3 = ⊥) : hS.nL = 3 := by
  have h1 := hS.one_lt_nL hs2
  rcases Nat.lt_or_ge hS.nL 4 with hlt | hge
  · rcases (show hS.nL = 2 ∨ hS.nL = 3 by omega) with h | h
    · exfalso
      have hb := hS.lf_lcs_bot hS.nL_spec.symm (by omega)
      rw [h] at hb
      exact h3 hb
    · exact h
  · exfalso
    have hpos := hS.nL_pos hp 3 (by omega)
    have hcard := hS.layer_card 3
    rw [h4, Subgroup.card_bot] at hcard
    have hK : 1 ≤ Nat.card (layK p G 3) := Nat.card_pos
    have hP : p ≤ p ^ r 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ r 3 := Nat.pow_le_pow_right hp.pos hpos
    have hm := Nat.mul_le_mul hP hK
    rw [mul_one, hcard] at hm
    have := hp.two_le
    omega

/-- The first layer rank is `d(G)` (Burnside). -/
theorem SimsGen.c3_r0_eq (hp : p.Prime) (hS : SimsGen p u d X r) : r 0 = Group.rank G := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card hS.realizes.card
  have h1 : p ^ r 0 * Nat.card (pPhi p G) = Nat.card (lcs G 0) := hS.layer_card 0
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini G)
  rw [card_quot_frattini hpg, frattini_eq_pPhi hpg] at h2
  have h3 : Nat.card (lcs G 0) = Nat.card G := by rw [lcs_zero, Subgroup.card_top]
  have h4 : 0 < Nat.card (pPhi p G) := Nat.card_pos
  have h6 : p ^ r 0 * Nat.card (pPhi p G) = p ^ Group.rank G * Nat.card (pPhi p G) := by
    rw [← h2, ← h3, h1]
  exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_right h4 h6)

/-- The second layer rank is `r_2 = d(γ_2 / γ_3 γ_2^p)`. -/
theorem SimsGen.c3_r1_eq [hp : Fact p.Prime] (hS : SimsGen p u d X r) : r 1 = r2 p G := by
  have h1 : p ^ r 1 * Nat.card (pN p G) = Nat.card (lcs G 1) := hS.layer_card 1
  have h2 : Nat.card (lcs G 1) = Nat.card (pN p G) * p ^ r2 p G := card_lcs_one_eq
  have h4 : 0 < Nat.card (pN p G) := Nat.card_pos
  have h6 : p ^ r 1 * Nat.card (pN p G) = p ^ r2 p G * Nat.card (pN p G) := by
    rw [h1, h2, mul_comm]
  exact Nat.pow_right_injective hp.out.two_le (Nat.eq_of_mul_eq_mul_right h4 h6)

omit [Finite G] in
/-- `γ_3` is abelian when `γ_4 = 1`. -/
theorem c3_commutator_lcs_two_eq_bot (h4 : lcs G 3 = ⊥) : commutator (lcs G 2) = ⊥ := by
  rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_bot]
  have h : ⁅(x : G), (y : G)⁆ ∈ lcs G 3 := commElem_mem_lcs_succ x.2 (y : G)
  rw [h4, Subgroup.mem_bot] at h
  have e : ((⁅x, y⁆ : lcs G 2) : G) = ⁅(x : G), (y : G)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subtype.ext (e.trans h)

/-- The third layer rank is `d(γ_3)` when `γ_4 = 1` (Burnside for the abelian group `γ_3`). -/
theorem SimsGen.c3_r2_eq (hp : p.Prime) (hS : SimsGen p u d X r) (h4 : lcs G 3 = ⊥) :
    r 2 = Group.rank (lcs G 2) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card hS.realizes.card
  have hK : IsPGroup p (lcs G 2) := hpg.to_subgroup _
  have hcomm := c3_commutator_lcs_two_eq_bot h4
  have hmap : (pPhi p (lcs G 2)).map (lcs G 2).subtype = layK p G 2 := by
    show (Subgroup.closure (Set.range (fun g : lcs G 2 => g ^ p)) ⊔
        commutator (lcs G 2)).map (lcs G 2).subtype =
      lcs G 3 ⊔ Subgroup.closure (Set.range (fun g : lcs G 2 => (g : G) ^ p))
    rw [hcomm, sup_bot_eq, h4, bot_sup_eq, MonoidHom.map_closure, ← Set.range_comp]
    refine congrArg Subgroup.closure (congrArg Set.range ?_)
    funext g
    exact map_pow (lcs G 2).subtype g p
  have hc1 : Nat.card ((pPhi p (lcs G 2)).map (lcs G 2).subtype) =
      Nat.card (pPhi p (lcs G 2)) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (lcs G 2).subtype_injective).toEquiv).symm
  rw [hmap] at hc1
  have h1 : p ^ r 2 * Nat.card (layK p G 2) = Nat.card (lcs G 2) := hS.layer_card 2
  have h2 := Subgroup.card_mul_index (pPhi p (lcs G 2))
  have h3 : (pPhi p (lcs G 2)).index = p ^ Group.rank (lcs G 2) := card_quot_pPhi hK
  rw [h3] at h2
  have h5 : 0 < Nat.card (pPhi p (lcs G 2)) := Nat.card_pos
  have h6 : p ^ r 2 * Nat.card (pPhi p (lcs G 2)) =
      p ^ Group.rank (lcs G 2) * Nat.card (pPhi p (lcs G 2)) :=
    calc p ^ r 2 * Nat.card (pPhi p (lcs G 2)) = p ^ r 2 * Nat.card (layK p G 2) := by rw [hc1]
      _ = Nat.card (lcs G 2) := h1
      _ = Nat.card (pPhi p (lcs G 2)) * p ^ Group.rank (lcs G 2) := h2.symm
      _ = p ^ Group.rank (lcs G 2) * Nat.card (pPhi p (lcs G 2)) := mul_comm _ _
  exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_right h5 h6)

omit [Finite G] in
/-- The Sims rank is at most the core size `d.s` of any Sims generating set. -/
theorem SimsGen.c3_simsRank_le (hS : SimsGen p u d X r) : simsRank G ≤ d.s := by
  unfold simsRank
  apply Nat.sInf_le
  refine ⟨fun i : Fin d.s => u i.val, ?_⟩
  have e : Set.range (fun i : Fin d.s => u i.val) = u '' Set.Iio d.s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [e]
  exact hS.lf_hcore

end C3Ranks

/-! ### The codes of `cnt3Set` -/

section CNT3Codes

variable {m r1 r2 s lam m2 m3 r3 : ℕ}

/-- The recorded data, with core size `s`, of the Sims codes of the groups of `cnt3Set`. -/
noncomputable def cnt3Codes (m r1 r2 s lam m2 m3 r3 : ℕ) : Finset (RecData m) := by
  classical
  exact Finset.univ.filter (fun D => D.2.1.val = s ∧ ∃ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3,
    ∃ x : (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)) ×
      (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)),
      SimsCode Nat.prime_two m G (⟨D, x⟩ : FullData 2 m))

theorem mem_cnt3Codes {D : RecData m} :
    D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3 ↔ D.2.1.val = s ∧ ∃ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3,
      ∃ x : (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)) ×
        (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)),
        SimsCode Nat.prime_two m G (⟨D, x⟩ : FullData 2 m) := by
  simp only [cnt3Codes, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every group of `cnt3Set` has a Sims code whose recorded data lie in `cnt3Codes` (the code of
the Sims generating set of `exists_sims_gen`, whose core size is `simsRank G = s`). -/
theorem cnt3_hI : ∀ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3, ∃ D : FullData 2 m,
    SimsCode Nat.prime_two m G D ∧ D.1 ∈ cnt3Codes m r1 r2 s lam m2 m3 r3 := by
  intro G hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsG : simsRank G = s := ((mem_cnt3Set_iff G).mp hG).2.2.2.2.2.1
  have hna : lcs G 1 ≠ ⊥ := by
    intro h
    apply hG.2.1
    rw [eq_bot_iff, ← h]
    exact lcs_antitone (by norm_num)
  obtain ⟨u, d, X, r, hs2, hds, -, -, -, -, hnm, -, hS⟩ := exists_sims_gen Nat.prime_two hG.1 hna
  have hsum : ∑ t, d.a t = m := by
    have h1 := hS.realizes.card
    rw [hG.1] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  have hs2' : 2 ≤ d.s := by rw [hds]; exact hs2
  have hc : SimsCode Nat.prime_two m G (hS.enc Nat.prime_two m hnm hs2' hsum) :=
    ⟨u, d, X, r, hS, hnm, hs2', hsum, rfl⟩
  have hDs : (hS.enc Nat.prime_two m hnm hs2' hsum).1.2.1.val = s := hds.trans hsG
  exact ⟨_, hc, mem_cnt3Codes.mpr ⟨hDs, G, hG, (hS.enc Nat.prime_two m hnm hs2' hsum).2, hc⟩⟩

/-- The recorded data of a Sims code of a group of `cnt3Set`: three layers of ranks
`r1, r2, r3`, core size at least `s`, and layer sums `r1 + lam`, `m2 - m3`, `m3`. -/
theorem cnt3_code_facts {G : FiniteGrp.{0}} (hG : G ∈ cnt3Set m r1 r2 s lam m2 m3 r3)
    {D : RecData m} {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)}
    (hc : SimsCode Nat.prime_two m G (⟨D, (B, C)⟩ : FullData 2 m)) :
    D.1.val = 3 ∧ fibR D 0 = r1 ∧ fibR D 1 = r2 ∧ fibR D 2 = r3 ∧ s ≤ D.2.1.val ∧ m3 ≤ m2 ∧
      (∀ h : 0 < D.1.val, sL (fibAk D) ⟨0, h⟩ = r1 + lam) ∧
      (∀ h : 1 < D.1.val, sL (fibAk D) ⟨1, h⟩ = m2 - m3) ∧
      (∀ h : 2 < D.1.val, sL (fibAk D) ⟨2, h⟩ = m3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, h3, h4, hr1, hr2, hs, -, hm2, hm3, hr3⟩ := (mem_cnt3Set_iff G).mp hG
  have hm := cnt3_m_eq hG
  have hc' := hc
  obtain ⟨u, d, X, r, hS, hnm, hs2, hsum, e⟩ := hc
  obtain ⟨c1, c2, c3, -⟩ := hS.lf_code Nat.prime_two hnm hs2 hsum e
  have hnL := hS.c3_nL_eq Nat.prime_two hs2 h3 h4
  have hD3 : D.1.val = 3 := c1.symm.trans hnL
  have L1 : ∀ h : 1 < D.1.val, sL (fibAk D) ⟨1, h⟩ + m3 = m2 := by
    intro h
    have a1 : Nat.card (LayerQ G 1) = 2 ^ sL (fibAk D) ⟨1, h⟩ :=
      c3_code_layer_card Nat.prime_two hc' ⟨1, h⟩ (Or.inl (show 1 + 1 < D.1.val by omega))
    have a2 : Nat.card (LayerQ G 1) * Nat.card (lcs G 2) = Nat.card (lcs G 1) :=
      c3_card_layerQ_mul 1
    rw [a1, hm2, hm3, ← pow_add] at a2
    exact Nat.pow_right_injective (le_refl 2) a2
  have h1D : 1 < D.1.val := by omega
  have hm32 : m3 ≤ m2 := by
    have := L1 h1D
    omega
  refine ⟨hD3, ?_, ?_, ?_, ?_, hm32, ?_, ?_, ?_⟩
  · rw [← c3 0 (by omega), hS.c3_r0_eq Nat.prime_two, hr1]
  · rw [← c3 1 (by omega), hS.c3_r1_eq, hr2]
  · rw [← c3 2 (by omega), hS.c3_r2_eq Nat.prime_two h4, hr3]
  · rw [← c2, ← hs]
    exact hS.c3_simsRank_le
  · intro h
    have a1 : Nat.card (LayerQ G 0) = 2 ^ sL (fibAk D) ⟨0, h⟩ :=
      c3_code_layer_card Nat.prime_two hc' ⟨0, h⟩ (Or.inl (show 0 + 1 < D.1.val by omega))
    have a2 : Nat.card (LayerQ G 0) * Nat.card (lcs G 1) = Nat.card (lcs G 0) :=
      c3_card_layerQ_mul 0
    rw [a1, hm2, lcs_zero, Subgroup.card_top, hcard, ← pow_add] at a2
    have := Nat.pow_right_injective (le_refl 2) a2
    omega
  · intro h
    have := L1 h
    omega
  · intro h
    have a1 : Nat.card (LayerQ G 2) = 2 ^ sL (fibAk D) ⟨2, h⟩ :=
      c3_code_layer_card Nat.prime_two hc' ⟨2, h⟩ (Or.inr h4)
    have a2 : Nat.card (LayerQ G 2) * Nat.card (lcs G 3) = Nat.card (lcs G 2) :=
      c3_card_layerQ_mul 2
    rw [a1, h4, Subgroup.card_bot, mul_one, hm3] at a2
    exact Nat.pow_right_injective (le_refl 2) a2

/-- `cnt3_code_facts` for the recorded data in `cnt3Codes`, with the core size `D.2.1.val = s`. -/
theorem cnt3_codes_facts {D : RecData m} (hD : D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3) :
    D.1.val = 3 ∧ fibR D 0 = r1 ∧ fibR D 1 = r2 ∧ fibR D 2 = r3 ∧ D.2.1.val = s ∧ m3 ≤ m2 ∧
      (∀ h : 0 < D.1.val, sL (fibAk D) ⟨0, h⟩ = r1 + lam) ∧
      (∀ h : 1 < D.1.val, sL (fibAk D) ⟨1, h⟩ = m2 - m3) ∧
      (∀ h : 2 < D.1.val, sL (fibAk D) ⟨2, h⟩ = m3) := by
  obtain ⟨hDs, G, hG, ⟨B, C⟩, hc⟩ := mem_cnt3Codes.mp hD
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := cnt3_code_facts hG hc
  exact ⟨a1, a2, a3, a4, hDs, a6⟩

/-- The facts of `cnt3_codes_facts` in the form used by `lf_realizedCB_ncard_le`. -/
theorem cnt3_codes_lf {D : RecData m} (hD : D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3)
    (h2 : 2 < D.1.val) :
    fibRk D (lfI0 h2) = r1 ∧ fibRk D (lfI1 h2) = r2 ∧ fibRk D (lfI2 h2) = r3 ∧
      D.2.1.val = s ∧ m3 ≤ m2 ∧
      ∑ v, fibAk D ⟨lfI0 h2, v⟩ = r1 + lam ∧ ∑ v, fibAk D ⟨lfI1 h2, v⟩ = m2 - m3 ∧
      ∑ v, fibAk D ⟨lfI2 h2, v⟩ = m3 := by
  obtain ⟨-, hR0, hR1, hR2, hs, hm, hS0, hS1, hS2⟩ := cnt3_codes_facts hD
  exact ⟨hR0, hR1, hR2, hs, hm, hS0 (by omega), hS1 (by omega), hS2 h2⟩

/-- (1) The power word exponent of Theorem 3.1 for the recorded data of a group of `cnt3Set` is
the right side `cnt3PW` of (47) at `c = 3`. -/
theorem cnt3_pw_eq {D : RecData m} (hD : D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3) :
    pwBound2 (fibAk D) = cnt3PW r1 r2 r3 lam m2 m3 := by
  obtain ⟨h3, hR0, hR1, hR2, -, hm, hS0, hS1, hS2⟩ := cnt3_codes_facts hD
  rw [c3_pwBound2_three (fibAk D) h3 r1 r2 r3 (r1 + lam) (m2 - m3) m3 ?_ ?_]
  · unfold cnt3PW
    rw [Nat.sub_add_cancel hm, Nat.add_sub_cancel_left]
  · rintro ⟨i, hi⟩
    have : i < 3 := by omega
    interval_cases i
    · show fibR D 0 = _
      simp [hR0]
    · show fibR D 1 = _
      simp [hR1]
    · show fibR D 2 = _
      simp [hR2]
  · rintro ⟨i, hi⟩
    have : i < 3 := by omega
    interval_cases i
    · rw [hS0 hi]
      simp
    · rw [hS1 hi]
      simp
    · rw [hS2 hi]
      simp

/-- (1), inequality form. -/
theorem cnt3_pw_le {D : RecData m} (hD : D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3) :
    pwBound2 (fibAk D) ≤ cnt3PW r1 r2 r3 lam m2 m3 :=
  (cnt3_pw_eq hD).le

/-- The fibrewise count of `Lift.lf_ncard_classes_le_fiberB_pw` over `cnt3Codes`, with the power
word factor `2 ^ cnt3PW`. -/
theorem cnt3_ncard_le_pw (M : RecData m → ℕ)
    (hM : ∀ D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3,
      ∀ B ∈ realizedB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D,
        (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard ≤ M D) :
    (cnt3Classes m r1 r2 s lam m2 m3 r3).ncard ≤
      ∑ D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3, 2 ^ cnt3PW r1 r2 r3 lam m2 m3 * M D := by
  have h := lf_ncard_classes_le_fiberB_pw Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3)
    (cnt3Codes m r1 r2 s lam m2 m3 r3) cnt3_hI M hM
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun D hD => ?_))
  rw [cnt3_pw_eq hD]

end CNT3Codes

/-! ### (2) The data count -/

section CNT3Data

/-- Proposition 2.5 with the explicit constant `7`:
`#RecData m ≤ 2 ^ (7 m (log_2 m + 1))`. -/
theorem card_recData_le_log (m : ℕ) :
    Fintype.card (RecData m) ≤ 2 ^ (7 * m * (Nat.log 2 m + 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine (card_recData_le 0).trans ?_
    norm_num
  · refine (card_recData_le_pow m hm).trans ?_
    have hlt : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    calc (m + 1) ^ (5 * m + 2) ≤ (2 ^ (Nat.log 2 m + 1)) ^ (5 * m + 2) :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt hlt) _
      _ ≤ (2 ^ (Nat.log 2 m + 1)) ^ (7 * m) :=
          Nat.pow_le_pow_right (pow_pos (by norm_num) _) (by omega)
      _ = 2 ^ (7 * m * (Nat.log 2 m + 1)) := by
          rw [← pow_mul]
          congr 1
          ring

/-- (2) Any set of recorded data (e.g. the index set `cnt3Codes` of the fibrewise count) has at
most `2 ^ (7 m (log_2 m + 1))` elements. This is the uniform data count (constant `C0 = 7`),
`Finset.card_le_univ` composed with `card_recData_le_log`; nothing in it is specific to CNT3. -/
theorem cnt3_data_le {m : ℕ} (I : Finset (RecData m)) :
    I.card ≤ 2 ^ (7 * m * (Nat.log 2 m + 1)) :=
  (Finset.card_le_univ I).trans (card_recData_le_log m)

/-- The fibrewise count with a uniform fibre bound `M0`. -/
theorem cnt3_ncard_le_uniform {m r1 r2 s lam m2 m3 r3 : ℕ} (M0 : ℕ)
    (hM : ∀ D ∈ cnt3Codes m r1 r2 s lam m2 m3 r3,
      ∀ B ∈ realizedB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D,
        (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard ≤ M0) :
    (cnt3Classes m r1 r2 s lam m2 m3 r3).ncard ≤
      2 ^ (7 * m * (Nat.log 2 m + 1)) * (2 ^ cnt3PW r1 r2 r3 lam m2 m3 * M0) := by
  refine (cnt3_ncard_le_pw (fun _ => M0) hM).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (cnt3_data_le _)

/-- `n ≤ 2 ^ k` gives `log_2 n ≤ k` in the reals. -/
theorem cnt3_logb_le {n k : ℕ} (h : n ≤ 2 ^ k) : Real.logb 2 (n : ℝ) ≤ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (n : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast h
    have h2 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (k : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn) h1
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h2

end CNT3Data

end OMA.SimsLite
