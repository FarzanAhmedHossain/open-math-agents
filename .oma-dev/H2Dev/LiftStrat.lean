import H2Dev.Lift

/-! # The class-3 term-A count at fixed core breadth

Li-Qiao, Theorem 5.1 / eq. (53) at `c = 3` and fixed breadth `b_2` (48): the stratified form of
`lf_realizedCB_ncard_le`, built on `br_eq53_breadth` instead of `br_eq53_sum`.

* `lfsBr p X s` : the core breadth (48) of a group, `max_{u ∈ C} log_p |im [-, u]|` for the core
  subgroup `C = ⟨X_0, ..., X_{s-1}⟩ G' ≤ G^ab` and the bracket `brB2 G : L_2 × G^ab → L_3`.
* `lfs_breadth_transport` : the breadth is unchanged by the transport `brT2 e1 e2 e3`.
* `realizedCBb hp T D B b` : the commutator arrays of the realised codes (`realizedCB`) of a
  group whose Sims code has core breadth `b` (the canonical strata).
* `lf_realizedCB_subset_strata` : the realised arrays are covered by the strata with admissible
  `b` (`s_3 ≤ s b ≤ s min(s_2, s_3)`, (48)-(51)).
* `lf_realizedCBb_ncard_le` : each stratum has at most the term-A summand of breadth `b`
  (`br_eq53_breadth` with `|D| = r_2` defining pairs, times the deeper factor
  `p ^ ((C(r_1, 2) - r_2) s_3)`). -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section LfsTransport

variable {G : Type u} [Group G] {L1 L2 L3 : Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]

/-- The core breadth (48) of a group with core generators `X_t`, `t < s`. -/
noncomputable def lfsBr (p : ℕ) {n : ℕ} (X : Fin n → G) (s : ℕ) : ℕ :=
  brBreadth p (brB2 G)
    (Subgroup.closure ((fun t => Abelianization.of (X t)) '' {t | (t : ℕ) < s}))

/-- The slices of the transported bracket have the sizes of the slices of `brB2 G`. -/
theorem lfs_card_range (e1 : Abelianization G ≃* L1) (e2 : brL2 G ≃* L2) (e3 : brL3 G ≃* L3)
    (v : L1) :
    Nat.card ((brT2 e1 e2 e3).flip v).range = Nat.card ((brB2 G).flip (e1.symm v)).range := by
  have h : ∀ z, (brT2 e1 e2 e3).flip v z = e3 ((brB2 G).flip (e1.symm v) (e2.symm z)) :=
    fun z => rfl
  have e : (((brT2 e1 e2 e3).flip v).range : Set L3) =
      e3 '' (((brB2 G).flip (e1.symm v)).range : Set (brL3 G)) := by
    rw [MonoidHom.coe_range, MonoidHom.coe_range]
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨e2.symm z, rfl⟩, (h z).symm⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨e2 z, by rw [h, MulEquiv.symm_apply_apply]⟩
  calc Nat.card ((brT2 e1 e2 e3).flip v).range
      = Nat.card (((brT2 e1 e2 e3).flip v).range : Set L3) := rfl
    _ = Nat.card (e3 '' (((brB2 G).flip (e1.symm v)).range : Set (brL3 G))) := by rw [e]
    _ = Nat.card (((brB2 G).flip (e1.symm v)).range : Set (brL3 G)) :=
        Nat.card_image_of_injective e3.injective _
    _ = Nat.card ((brB2 G).flip (e1.symm v)).range := rfl

/-- The breadth (48) is unchanged by the transport along `e_1, e_2, e_3`. -/
theorem lfs_breadth_transport (p : ℕ) (e1 : Abelianization G ≃* L1) (e2 : brL2 G ≃* L2)
    (e3 : brL3 G ≃* L3) (A : Set (Abelianization G)) :
    brBreadth p (brT2 e1 e2 e3) (Subgroup.closure (e1 '' A)) =
      brBreadth p (brB2 G) (Subgroup.closure A) := by
  have h1 : Subgroup.closure (e1 '' A) ≤ (Subgroup.closure A).comap e1.symm.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show e1.symm (e1 a) ∈ Subgroup.closure A
    rw [MulEquiv.symm_apply_apply]
    exact Subgroup.subset_closure ha
  have h2 : Subgroup.closure A ≤ (Subgroup.closure (e1 '' A)).comap e1.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure ⟨a, ha, rfl⟩
  unfold brBreadth
  congr 1
  ext k
  constructor
  · rintro ⟨v, hv, hk⟩
    refine ⟨e1.symm v, Subgroup.mem_comap.mp (h1 hv), ?_⟩
    rwa [lfs_card_range] at hk
  · rintro ⟨x, hx, hk⟩
    refine ⟨e1 x, Subgroup.mem_comap.mp (h2 hx), ?_⟩
    rwa [lfs_card_range, MulEquiv.symm_apply_apply]

end LfsTransport

section LfsIdent

variable {G : Type u} [Group G] {p c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ}
  {g : SimsIdx c r → G} {S : SimsGenSet p a g} {h2 : 2 < c}
  {b0 : Fin (r (lfI0 h2)) → Fin (r (lfI0 h2)) → ℕ}
  {b1 : Fin (r (lfI1 h2)) → Fin (r (lfI1 h2)) → ℕ} {b2 : Fin (r (lfI2 h2)) → Fin (r (lfI2 h2)) → ℕ}

/-- In the coordinate model the breadth of the transported bracket is the core breadth of the
group. -/
theorem SimsGenSet.LfIdent.lfs_breadth_eq (I : S.LfIdent h2 b0 b1 b2) (s : ℕ) :
    brBreadth p (brT2 (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3))
        (Subgroup.closure ((fun j : Fin (r (lfI0 h2)) => Multiplicative.ofAdd
          (QuotientAddGroup.mk (Pi.single j (1 : ℤ)) : LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0)) ''
          {j | (j : ℕ) < s})) =
      lfsBr p (fun j : Fin (r (lfI0 h2)) => g ⟨lfI0 h2, j⟩) s := by
  have hset : (fun j : Fin (r (lfI0 h2)) => Multiplicative.ofAdd
        (QuotientAddGroup.mk (Pi.single j (1 : ℤ)) : LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0)) ''
        {j | (j : ℕ) < s} =
      lfMulE I.φ1 '' ((fun j : Fin (r (lfI0 h2)) => Abelianization.of (g ⟨lfI0 h2, j⟩)) ''
        {j | (j : ℕ) < s}) := by
    rw [Set.image_image]
    exact congrArg (fun f : Fin (r (lfI0 h2)) →
        Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0) => f '' {j | (j : ℕ) < s})
      (funext fun j => (I.e1_gen j).symm)
  rw [hset, lfs_breadth_transport]
  rfl

end LfsIdent

section LfsLeadCount

variable {p c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ}

/-- The set of graded bracket pairs of fixed breadth `b` counted by `br_eq53_breadth`. -/
def lfBrSetB {L1 L2 : Type*} [CommGroup L1] [CommGroup L2] (L3 : Type*) [CommGroup L3] {r : ℕ}
    (p s : ℕ) (g : Fin r → L1) (D : Finset (Fin r × Fin r)) (v : Fin r × Fin r → L2) (b : ℕ) :
    Set ((L1 →* L1 →* L2) × (L2 →* L1 →* L3)) :=
  {β | brAlt β.1 ∧
    Subgroup.closure {w | ∃ u ∈ Subgroup.closure (g '' {j | (j : ℕ) < s}),
      ∃ u' ∈ Subgroup.closure (g '' {j | (j : ℕ) < s}), β.1 u u' = w} = ⊤ ∧
    brJacobi β.1 β.2 ∧
    brBreadth p β.2 (Subgroup.closure (g '' {j | (j : ℕ) < s})) = b ∧
    ∀ q ∈ D, β.1 (g q.1) (g q.2) = v q}

/-- `lf_ncard_lead_le` at fixed core breadth `b`: the leading commutator coefficient arrays of
groups of core breadth `b` number at most the `br_eq53_breadth` bound. -/
theorem lfs_ncard_lead_le (hp : p.Prime) (h2 : 2 < c)
    (b0 : Fin (r (lfI0 h2)) → Fin (r (lfI0 h2)) → ℕ)
    (b1 : Fin (r (lfI1 h2)) → Fin (r (lfI1 h2)) → ℕ)
    (b2 : Fin (r (lfI2 h2)) → Fin (r (lfI2 h2)) → ℕ) {s : ℕ} (hs : s ≤ r (lfI0 h2))
    (D : Finset (Fin (r (lfI0 h2)) × Fin (r (lfI0 h2))))
    (hD : ∀ q ∈ D, q.1 < q.2 ∧ (q.1 : ℕ) < s)
    (w : Fin (r (lfI0 h2)) × Fin (r (lfI0 h2)) → Fin (r (lfI1 h2)) → ℕ) (b : ℕ)
    (Λ : Set ((Fin (r (lfI0 h2)) → Fin (r (lfI0 h2)) → Fin (r (lfI1 h2)) → ℕ) ×
      (Fin (r (lfI1 h2)) → Fin (r (lfI0 h2)) → Fin (r (lfI2 h2)) → ℕ)))
    (hΛ : ∀ x ∈ Λ, ∃ (G : Type u) (_ : Group G) (_ : Finite G) (g : SimsIdx c r → G)
      (S : SimsGenSet p a g),
      (∀ j v, (S.powerWords ⟨lfI0 h2, j⟩ ⟨lfI0 h2, v⟩).val = b0 j v) ∧
      (∀ j v, (S.powerWords ⟨lfI1 h2, j⟩ ⟨lfI1 h2, v⟩).val = b1 j v) ∧
      (∀ j v, (S.powerWords ⟨lfI2 h2, j⟩ ⟨lfI2 h2, v⟩).val = b2 j v) ∧
      (3 < c ∨ lcs G 3 = ⊥) ∧
      lcs G 1 ≤ ⁅Subgroup.closure ((fun j => g ⟨lfI0 h2, j⟩) '' {j | (j : ℕ) < s}),
        Subgroup.closure ((fun j => g ⟨lfI0 h2, j⟩) '' {j | (j : ℕ) < s})⁆ ⊔ lcs G 2 ∧
      (∀ q ∈ D, S.lfLead1 h2 q.1 q.2 = w q) ∧
      lfsBr p (fun j : Fin (r (lfI0 h2)) => g ⟨lfI0 h2, j⟩) s = b ∧
      x = (S.lfLead1 h2, S.lfLead2 h2)) :
    Λ.ncard ≤ p ^ (s * (b * (r (lfI1 h2) + (∑ v, a ⟨lfI2 h2, v⟩) + 1 - b))) *
        p ^ (((r (lfI0 h2)).choose 2 - D.card) * (∑ v, a ⟨lfI1 h2, v⟩) -
          (r (lfI0 h2) - s).choose 2 * b) := by
  classical
  have hp0 := hp.pos
  have : Finite (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0) := (lf_card_quot_le hp0 _ b0).1
  have : Finite (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1) := (lf_card_quot_le hp0 _ b1).1
  have : Finite (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2) := (lf_card_quot_le hp0 _ b2).1
  have : Finite (Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0)) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  have : Finite (Multiplicative (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1)) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  have : Finite (Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2)) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  rcases Λ.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0, _, _, g0, S0, hb0, hb1, hb2, hl, -, -, -, -⟩ := hΛ x0 hx0
  obtain ⟨I0⟩ := S0.lf_ident_nonempty hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
  have hL2 := lf_card_mulQ I0.φ2 I0.card2
  have hL3 := lf_card_mulQ I0.φ3 I0.card3
  have := br_finite_pairs (L1 := Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0))
    (L2 := Multiplicative (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1))
    (L3 := Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2))
  let gg : Fin (r (lfI0 h2)) → Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0) :=
    fun j => Multiplicative.ofAdd (QuotientAddGroup.mk (Pi.single j (1 : ℤ)))
  let yy : Fin (r (lfI1 h2)) → Multiplicative (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1) :=
    fun j => Multiplicative.ofAdd (QuotientAddGroup.mk (Pi.single j (1 : ℤ)))
  let vv : Fin (r (lfI0 h2)) × Fin (r (lfI0 h2)) →
      Multiplicative (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1) :=
    fun q => Multiplicative.ofAdd (QuotientAddGroup.mk (fun v => ((w q v : ℕ) : ℤ)))
  obtain ⟨R, hR⟩ : ∃ R : ((Fin (r (lfI0 h2)) → Fin (r (lfI0 h2)) → Fin (r (lfI1 h2)) → ℕ) ×
      (Fin (r (lfI1 h2)) → Fin (r (lfI0 h2)) → Fin (r (lfI2 h2)) → ℕ)) →
      ((Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0) →*
          Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0) →*
            Multiplicative (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1)) ×
        (Multiplicative (LfQ p (fun v => a ⟨lfI1 h2, v⟩) b1) →*
          Multiplicative (LfQ p (fun v => a ⟨lfI0 h2, v⟩) b0) →*
            Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2))) → Prop, R =
    fun x β => ∃ (G : Type u) (_ : Group G) (g : SimsIdx c r → G) (S : SimsGenSet p a g)
      (I : S.LfIdent h2 b0 b1 b2), x = (S.lfLead1 h2, S.lfLead2 h2) ∧
        β = (brT1 (lfMulE I.φ1) (lfMulE I.φ2), brT2 (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)) :=
    ⟨_, rfl⟩
  have hfun : ∀ x x' β, R x β → R x' β → x = x' := by
    intro x x' β h h'
    rw [hR] at h h'
    obtain ⟨G, _, g, S, I, rfl, rfl⟩ := h
    obtain ⟨G', _, g', S', I', rfl, hβ⟩ := h'
    obtain ⟨h1, h2'⟩ := Prod.mk.inj hβ
    obtain ⟨e1, e2⟩ := SimsGenSet.lf_lead_eq hp0 I I' h1 h2'
    rw [e1, e2]
  have hex : ∀ x ∈ Λ, ∃ β, β ∈ lfBrSetB (Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2))
      p s gg D vv b ∧ R x β := by
    intro x hx
    obtain ⟨G, _, _, g, S, hb0, hb1, hb2, hl, hcore, hDw, hbr, rfl⟩ := hΛ x hx
    obtain ⟨I⟩ := S.lf_ident_nonempty hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
    have hv : ∀ q ∈ D, lfMulE I.φ2 (brq2 G (cw (g ⟨lfI0 h2, q.1⟩) (g ⟨lfI0 h2, q.2⟩))) =
        vv q := by
      intro q hq
      refine (I.e2_coord (cw (g ⟨lfI0 h2, q.1⟩) (g ⟨lfI0 h2, q.2⟩)).2).trans ?_
      show _ = Multiplicative.ofAdd (QuotientAddGroup.mk (fun v => ((w q v : ℕ) : ℤ)))
      rw [← hDw q hq]
      rfl
    have hm := lf_brT_mem (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)
      (fun j => g ⟨lfI0 h2, j⟩) gg (fun j => I.e1_gen j) hcore D vv hv
    rw [lfBrSet, Set.mem_setOf_eq] at hm
    obtain ⟨hA, hgen, hJ, -, hDv⟩ := hm
    refine ⟨(brT1 (lfMulE I.φ1) (lfMulE I.φ2),
      brT2 (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)), ?_, ?_⟩
    · rw [lfBrSetB, Set.mem_setOf_eq]
      exact ⟨hA, hgen, hJ, (I.lfs_breadth_eq s).trans hbr, hDv⟩
    · rw [hR]
      exact ⟨G, inferInstance, g, S, I, rfl, rfl⟩
  let F := fun x => if h : x ∈ Λ then Classical.choose (hex x h) else 1
  have hF : ∀ x (h : x ∈ Λ), F x = Classical.choose (hex x h) := fun x h => dif_pos h
  have hmaps : ∀ x ∈ Λ, F x ∈ lfBrSetB (Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2))
      p s gg D vv b := fun x h => by
    rw [hF x h]
    exact (Classical.choose_spec (hex x h)).1
  have hinj : Set.InjOn F Λ := by
    intro x hx x' hx' he
    refine hfun x x' (F x) ?_ ?_
    · rw [hF x hx]
      exact (Classical.choose_spec (hex x hx)).2
    · rw [he, hF x' hx']
      exact (Classical.choose_spec (hex x' hx')).2
  refine (Set.ncard_le_ncard_of_injOn F hmaps hinj (Set.toFinite _)).trans ?_
  exact br_eq53_breadth (b := b) hp hs hL2 hL3 yy (lf_closure_single p _ b1) gg
    (lf_closure_single p _ b0) D hD vv

end LfsLeadCount

section LfsGroup

variable {G : Type u} [Group G] {p : ℕ} {u : ℕ → G} {d : SimsData} {X : Fin d.n → G}
  {r : ℕ → ℕ}

/-- `lf_reindex`, also identifying the reindexed first-layer generators with the `X_t`. -/
theorem SimsGen.lfs_reindex [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {c : ℕ}
    (hn : d.n = fOff r c) (h2 : 2 < c) (r' : Fin c → ℕ) (hr : ∀ i : Fin c, r i.val = r' i)
    (a' : SimsIdx c r' → ℕ) (ha : ∀ k : SimsIdx c r', a' k = brA d (fOff r k.1.val + k.2.val)) :
    ∃ (g' : SimsIdx c r' → G) (S : SimsGenSet p a' g'),
      (∀ (i : Fin c) (j v : Fin (r' i)), (S.powerWords ⟨i, j⟩ ⟨i, v⟩).val =
        brB d (fOff r i.val + j.val) (fOff r i.val + v.val)) ∧
      (∀ (j k : Fin (r' (lfI0 h2))) (v : Fin (r' (lfI1 h2))), j < k →
        S.lfLead1 h2 j k v = brCm d (fOff r 0 + j.val) (fOff r 0 + k.val) (fOff r 1 + v.val)) ∧
      (∀ (j : Fin (r' (lfI1 h2))) (k : Fin (r' (lfI0 h2))) (v : Fin (r' (lfI2 h2))),
        k.val ≤ brCo d r j.val →
        S.lfLead2 h2 j k v = brCm d (fOff r 1 + j.val) (fOff r 0 + k.val) (fOff r 2 + v.val)) ∧
      lcs G 1 ≤ ⁅Subgroup.closure ((fun j => g' ⟨lfI0 h2, j⟩) '' {j | (j : ℕ) < d.s}),
        Subgroup.closure ((fun j => g' ⟨lfI0 h2, j⟩) '' {j | (j : ℕ) < d.s})⁆ ⊔ lcs G 2 ∧
      ∀ (j : Fin (r' (lfI0 h2))) (t : Fin d.n), t.val = j.val → g' ⟨lfI0 h2, j⟩ = X t := by
  have hr' : brR r c = r' := funext hr
  subst hr'
  have ha' : a' = fun k => d.a (hS.brEquiv hn k) :=
    funext fun k => (ha k).trans (hS.brA_brEquiv hn k)
  subst ha'
  refine ⟨fun k => X (hS.brEquiv hn k), hS.toSimsGenSet hp hn, fun i j v => ?_,
    fun j k v hjk => ?_, fun j k v hk => ?_, ?_, fun j t hjt => ?_⟩
  · exact (hS.brB_eq_powerWords hp hn ⟨i, j⟩ ⟨i, v⟩).symm
  · exact (hS.lf_lead1_eq_brCm hp hn h2 j k hjk v).symm
  · have hk' : (k : ℕ) ≤ (d.df (hS.brEquiv hn ⟨lfI1 h2, j⟩)).2.val := by
      rw [← brCo_eq d r (hS.brEquiv hn ⟨lfI1 h2, j⟩) j.val rfl]
      exact hk
    exact (hS.lf_lead2_eq_brCm hp hn h2 j k hk' v).symm
  · exact (hS.lf_core hn (by omega) hS.lf_hcore).2
  · show X (hS.brEquiv hn ⟨lfI0 h2, j⟩) = X t
    congr 1
    apply Fin.ext
    rw [hS.val_brEquiv]
    show fOff r 0 + j.val = t.val
    have e0 : fOff r 0 = 0 := rfl
    rw [e0, Nat.zero_add, hjt]

end LfsGroup

section LfsCount

/-- The leading coefficient pairs of groups of core breadth `b` (`lfLam` with the breadth). -/
def lfLamB (p : ℕ) {m : ℕ} (D : RecData m) (h2 : 2 < D.1.val)
    (b0 : Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI0 h2)) → ℕ)
    (b1 : Fin (fibRk D (lfI1 h2)) → Fin (fibRk D (lfI1 h2)) → ℕ)
    (b2 : Fin (fibRk D (lfI2 h2)) → Fin (fibRk D (lfI2 h2)) → ℕ)
    (Dp : Finset (Fin (fibRk D (lfI0 h2)) × Fin (fibRk D (lfI0 h2))))
    (w : Fin (fibRk D (lfI0 h2)) × Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI1 h2)) → ℕ)
    (b : ℕ) : Set (LfLeadT D h2) :=
  {x | (∃ (G : Type) (_ : Group G) (_ : Finite G) (g : SimsIdx D.1.val (fibRk D) → G)
      (S : SimsGenSet p (fibAk D) g),
      (∀ j v, (S.powerWords ⟨lfI0 h2, j⟩ ⟨lfI0 h2, v⟩).val = b0 j v) ∧
      (∀ j v, (S.powerWords ⟨lfI1 h2, j⟩ ⟨lfI1 h2, v⟩).val = b1 j v) ∧
      (∀ j v, (S.powerWords ⟨lfI2 h2, j⟩ ⟨lfI2 h2, v⟩).val = b2 j v) ∧
      (3 < D.1.val ∨ lcs G 3 = ⊥) ∧
      lcs G 1 ≤ ⁅Subgroup.closure ((fun j => g ⟨lfI0 h2, j⟩) '' {j | (j : ℕ) < D.2.1.val}),
        Subgroup.closure ((fun j => g ⟨lfI0 h2, j⟩) '' {j | (j : ℕ) < D.2.1.val})⁆ ⊔ lcs G 2 ∧
      (∀ q ∈ Dp, S.lfLead1 h2 q.1 q.2 = w q) ∧
      lfsBr p (fun j : Fin (fibRk D (lfI0 h2)) => g ⟨lfI0 h2, j⟩) D.2.1.val = b ∧
      x = (S.lfLead1 h2, S.lfLead2 h2)) ∧
    (∀ j k v, x.1 j k v < p ^ fibAk D ⟨lfI1 h2, v⟩) ∧
    (∀ j k v, x.2 j k v < p ^ fibAk D ⟨lfI2 h2, v⟩)}

/-- The canonical strata: the commutator arrays of realised codes whose Sims generators have
core breadth `b` (48). -/
def realizedCBb {p m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0}) (D : RecData m)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) (b : ℕ) :
    Set (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) :=
  {C | ∃ G ∈ T, ∃ (u : ℕ → G) (d : SimsData) (X : Fin d.n → G) (r : ℕ → ℕ)
    (hS : SimsGen p u d X r) (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) (hsum : ∑ t, d.a t = m),
    hS.enc hp m hnm hs2 hsum = (⟨D, (B, C)⟩ : FullData p m) ∧ lfsBr p X d.s = b}

theorem realizedCBb_subset {p m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0}) (D : RecData m)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) (b : ℕ) :
    realizedCBb hp T D B b ⊆ realizedCB hp T D B := by
  rintro C ⟨G, hG, u, d, X, r, hS, hnm, hs2, hsum, e, -⟩
  exact ⟨G, hG, u, d, X, r, hS, hnm, hs2, hsum, e⟩

/-- The breadth of a counted leading pair is admissible ((48)-(51)). -/
theorem lfs_lamB_adm {p m : ℕ} (hp : p.Prime) {D : RecData m} {h2 : 2 < D.1.val}
    {b0 : Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI0 h2)) → ℕ}
    {b1 : Fin (fibRk D (lfI1 h2)) → Fin (fibRk D (lfI1 h2)) → ℕ}
    {b2 : Fin (fibRk D (lfI2 h2)) → Fin (fibRk D (lfI2 h2)) → ℕ}
    {Dp : Finset (Fin (fibRk D (lfI0 h2)) × Fin (fibRk D (lfI0 h2)))}
    {w : Fin (fibRk D (lfI0 h2)) × Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI1 h2)) → ℕ}
    {b : ℕ} {x : LfLeadT D h2} (hx : x ∈ lfLamB p D h2 b0 b1 b2 Dp w b)
    (hs : D.2.1.val ≤ fibRk D (lfI0 h2)) :
    (∑ v, fibAk D ⟨lfI2 h2, v⟩) ≤ D.2.1.val * b ∧
      b ≤ min (∑ v, fibAk D ⟨lfI1 h2, v⟩) (∑ v, fibAk D ⟨lfI2 h2, v⟩) := by
  obtain ⟨⟨G, _, _, g, S, hb0, hb1, hb2, hl, hcore, -, hbr, -⟩, -, -⟩ := hx
  obtain ⟨I⟩ := S.lf_ident_nonempty hp.pos h2 hl b0 b1 b2 hb0 hb1 hb2
  have : Finite (LfQ p (fun v => fibAk D ⟨lfI1 h2, v⟩) b1) := (lf_card_quot_le hp.pos _ b1).1
  have : Finite (LfQ p (fun v => fibAk D ⟨lfI2 h2, v⟩) b2) := (lf_card_quot_le hp.pos _ b2).1
  have : Finite (Multiplicative (LfQ p (fun v => fibAk D ⟨lfI1 h2, v⟩) b1)) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  have : Finite (Multiplicative (LfQ p (fun v => fibAk D ⟨lfI2 h2, v⟩) b2)) :=
    Finite.of_equiv _ Multiplicative.ofAdd
  have hL2 := lf_card_mulQ I.φ2 I.card2
  have hL3 := lf_card_mulQ I.φ3 I.card3
  have hm := lf_brT_mem (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)
    (fun j => g ⟨lfI0 h2, j⟩) (fun j : Fin (fibRk D (lfI0 h2)) => Multiplicative.ofAdd
      (QuotientAddGroup.mk (Pi.single j (1 : ℤ)) : LfQ p (fun v => fibAk D ⟨lfI0 h2, v⟩) b0))
    (fun j => I.e1_gen j) hcore ∅ (fun _ => 1) (fun q hq => by simp at hq)
  rw [lfBrSet, Set.mem_setOf_eq] at hm
  obtain ⟨-, -, -, hgen3, -⟩ := hm
  obtain ⟨h51, hmin⟩ := br_breadth_range hp hs hL2 hL3
    (brT2 (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)) _ hgen3
  rw [← hbr, ← I.lfs_breadth_eq D.2.1.val]
  exact ⟨h51, hmin⟩

/-- The leading part of a realised commutator array is the truncation of a counted leading pair
of the core breadth of the realising Sims generators. -/
theorem SimsGen.lfs_lead {G : Type} [Group G] [Finite G] {p : ℕ} {u : ℕ → G} {d : SimsData}
    {X : Fin d.n → G} {r : ℕ → ℕ} (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) (hsum : ∑ t, d.a t = m) {D : RecData m}
    {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    (e : hS.enc hp m hnm hs2 hsum = ⟨D, (B, C)⟩) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (co : ℕ → ℕ) (hco : ∀ j < r 1, brCo d r j = co j) :
    ∃ x ∈ lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2))
        (lfDp D h2 (lfFa D) co) (lfW D h2 (lfFa D) co) (lfsBr p X d.s),
      lfPhi1 D h2 C = lfTrunc D h2 co x := by
  obtain ⟨cf1, cf2, cf3, cf4, cf5, cf6, -, cf8⟩ := hS.lf_code hp hnm hs2 hsum e
  have hn : d.n = fOff r D.1.val := by rw [← cf1]; exact hS.nL_spec.symm
  have hfo : ∀ w ≤ D.1.val, fOff r w = fOff (fibR D) w :=
    fOff_congr (fun w hw => cf3 w (by rw [cf1]; exact hw))
  have hn3 : d.n = fOff r 3 := by rw [hn, h3]
  have f1 := hfo 1 (by omega)
  have f2 := hfo 2 (by omega)
  have e0 : fOff r 0 = 0 := rfl
  have e0' : fOff (fibR D) 0 = 0 := rfl
  have e01 : fOff r 1 = fOff r 0 + r 0 := fOff_succ r 0
  have e12 : fOff r 2 = fOff r 1 + r 1 := fOff_succ r 1
  have e23 : fOff r 3 = fOff r 2 + r 2 := fOff_succ r 2
  have hr0 : r 0 = fibR D 0 := cf3 0 (by rw [cf1]; omega)
  have hr1 : r 1 = fibR D 1 := cf3 1 (by rw [cf1]; omega)
  have hsr : d.s ≤ r 0 := (hS.lf_core hn (by omega) hS.lf_hcore).1
  obtain ⟨g', S, hpw, hl1, hl2, hcore, hX0⟩ := hS.lfs_reindex hp hn h2 (fibRk D)
    (fun i => cf3 i.val (by rw [cf1]; exact i.isLt)) (fibAk D) (fun k => by
      show fibA D (fOff (fibR D) k.1.val + k.2.val) = _
      rw [cf4, hfo _ k.1.isLt.le])
  have hpwB : ∀ (i : Fin D.1.val) (j v : Fin (fibRk D i)),
      (S.powerWords ⟨i, j⟩ ⟨i, v⟩).val = lfBB D B i j v := by
    intro i j v
    rw [hpw, ← cf6]
    unfold lfBB
    rw [hfo _ i.isLt.le]
  refine ⟨(S.lfLead1 h2, S.lfLead2 h2), ⟨⟨G, inferInstance, inferInstance, g', S, hpwB (lfI0 h2),
      hpwB (lfI1 h2), hpwB (lfI2 h2), ?_, ?_, ?_, ?_, rfl⟩, fun j k v => Fin.isLt _,
      fun j k v => Fin.isLt _⟩, ?_⟩
  · -- class 3
    have hb := hS.lf_lcs_bot hn (by omega)
    rw [h3] at hb
    exact Or.inr hb
  · -- the core
    rw [← cf2]
    exact hcore
  · -- the defining pairs
    intro q hq
    obtain ⟨j, hj1, hj2⟩ := (Finset.mem_filter.mp hq).2
    have hjr : j.val < r 1 := by
      have : j.val < fibR D 1 := j.isLt
      have hr1 : r 1 = fibR D 1 := cf3 1 (by rw [cf1]; omega)
      omega
    rw [← cf8 _ hjr] at hj1
    rw [← hco _ hjr] at hj2
    have hlt : q.1 < q.2 := by
      show q.1.val < q.2.val
      rw [hj1, hj2]
      exact hS.lf_brPa_lt_brCo hs2 hjr
    funext v
    have hv : v.val < r 1 := by
      have : v.val < fibR D 1 := v.isLt
      have hr1 : r 1 = fibR D 1 := cf3 1 (by rw [cf1]; omega)
      omega
    rw [hl1 q.1 q.2 v hlt, e0, Nat.zero_add, Nat.zero_add, hj1, hj2,
      hS.lf_defpair hp hs2 hjr]
    unfold lfW
    rw [hj1, hj2, ← cf8 _ hv, ← hco _ hv]
    by_cases hvj : v.val = j.val
    · rw [if_pos (by omega), if_pos ⟨by rw [hvj], by rw [hvj]⟩]
    · rw [if_neg (by omega), if_neg]
      rintro ⟨h1', h2'⟩
      exact hvj (hS.lf_pair_inj hs2 hv hjr h1'.symm h2'.symm)
  · -- the core breadth
    have hset : (fun t : Fin (fibRk D (lfI0 h2)) => Abelianization.of (g' ⟨lfI0 h2, t⟩)) ''
          {t | (t : ℕ) < D.2.1.val} =
        (fun t : Fin d.n => Abelianization.of (X t)) '' {t | (t : ℕ) < d.s} := by
      ext z
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hj' : j.val < D.2.1.val := hj
        have hjn : j.val < d.n := by omega
        refine ⟨⟨j.val, hjn⟩, (show j.val < d.s by omega), ?_⟩
        show Abelianization.of (X ⟨j.val, hjn⟩) = Abelianization.of (g' ⟨lfI0 h2, j⟩)
        rw [hX0 j ⟨j.val, hjn⟩ rfl]
      · rintro ⟨t, ht, rfl⟩
        have ht' : t.val < d.s := ht
        have htr : t.val < fibR D 0 := by omega
        refine ⟨⟨t.val, htr⟩, (show t.val < D.2.1.val by omega), ?_⟩
        show Abelianization.of (g' ⟨lfI0 h2, ⟨t.val, htr⟩⟩) = Abelianization.of (X t)
        rw [hX0 ⟨t.val, htr⟩ t rfl]
    exact congrArg (fun A => brBreadth p (brB2 G) (Subgroup.closure A)) hset
  · -- the leading part is the truncation of the leading pair
    refine Prod.ext (funext fun j => funext fun k => funext fun v => ?_)
      (funext fun j => funext fun k => funext fun v => ?_)
    · show lfCn D C (fOff (fibR D) 0 + j.val) (fOff (fibR D) 0 + k.val)
          (fOff (fibR D) 1 + v.val) = if j < k then S.lfLead1 h2 j k v else 0
      rw [cf5, e0', ← f1]
      split_ifs with hjk
      · rw [hl1 j k v hjk, e0]
      · by_contra hne
        have hj0 : j.val < fibR D 0 := j.isLt
        rcases hS.lf_brCm_ne hn3 hne with ⟨a1, -⟩ | ⟨b1, -⟩
        · exact hjk (by show j.val < k.val; omega)
        · omega
    · show lfCn D C (fOff (fibR D) 1 + j.val) (fOff (fibR D) 0 + k.val)
          (fOff (fibR D) 2 + v.val) = if k.val ≤ co j.val then S.lfLead2 h2 j k v else 0
      have hj1 : j.val < r 1 := by
        have : j.val < fibR D 1 := j.isLt
        have hr1 : r 1 = fibR D 1 := cf3 1 (by rw [cf1]; omega)
        omega
      rw [cf5, e0', ← f1, ← f2, ← hco j.val hj1]
      split_ifs with hk
      · rw [hl2 j k v hk, e0]
      · by_contra hne
        have hk0 : k.val < fibR D 0 := k.isLt
        rcases hS.lf_brCm_ne hn3 hne with ⟨a1, a2, -, -⟩ | ⟨-, -, -, b4, -, -⟩
        · omega
        · rw [Nat.add_sub_cancel_left] at b4
          exact hk (by omega)

/-- The realised commutator arrays are covered by the strata of admissible breadth. -/
theorem lf_realizedCB_subset_strata {p m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0})
    (D : RecData m) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) :
    realizedCB hp T D B ⊆ ⋃ β ∈ (Finset.range (min (∑ v, fibAk D ⟨lfI1 h2, v⟩)
        (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1)).filter
        (fun β => (∑ v, fibAk D ⟨lfI2 h2, v⟩) ≤ D.2.1.val * β), realizedCBb hp T D B β := by
  rintro C ⟨G, hG, u, d, X, r, hS, hnm, hs2, hsum, e⟩
  obtain ⟨c1, c2, c3, -, -, -, -, -⟩ := hS.lf_code hp hnm hs2 hsum e
  have hn : d.n = fOff r D.1.val := by rw [← c1]; exact hS.nL_spec.symm
  have hr0 : r 0 = fibR D 0 := c3 0 (by rw [c1]; omega)
  have hsr : d.s ≤ r 0 := (hS.lf_core hn (by omega) hS.lf_hcore).1
  obtain ⟨x, hx, -⟩ := hS.lfs_lead hp hnm hs2 hsum e h2 h3 (brCo d r) (fun _ _ => rfl)
  have hadm := lfs_lamB_adm hp hx (by show D.2.1.val ≤ fibR D 0; rw [← c2, ← hr0]; exact hsr)
  refine Set.mem_iUnion₂.2 ⟨lfsBr p X d.s, ?_, G, hG, u, d, X, r, hS, hnm, hs2, hsum, e, rfl⟩
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hadm.2, hadm.1⟩

/-- `lf_realizedCB_ncard_le` at fixed core breadth `b`: the stratum `realizedCBb ... b` has at
most the term-A summand of breadth `b` (`br_eq53_breadth` with `|D| = r_2`, times the deeper
count `p ^ ((C(r_1, 2) - r_2) s_3)`). -/
theorem lf_realizedCBb_ncard_le {p m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0})
    (D : RecData m) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) (b : ℕ) :
    (realizedCBb hp T D B b).ncard ≤
      p ^ (D.2.1.val * (b * (fibRk D (lfI1 h2) + (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1 - b))) *
        p ^ (((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2)) *
            (∑ v, fibAk D ⟨lfI1 h2, v⟩) - (fibRk D (lfI0 h2) - D.2.1.val).choose 2 * b) *
        p ^ (((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2)) *
          ∑ v, fibAk D ⟨lfI2 h2, v⟩) := by
  rcases (realizedCBb hp T D B b).eq_empty_or_nonempty with hE | ⟨C0, hC0⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0, -, u0, d0, X0, r0, hS0, hnm0, hs0, hsum0, e0, -⟩ := hC0
  obtain ⟨c1, c2, c3, -, -, -, c7, c8⟩ := hS0.lf_code hp hnm0 hs0 hsum0 e0
  have hn0 : d0.n = fOff r0 D.1.val := by rw [← c1]; exact hS0.nL_spec.symm
  have hr00 : r0 0 = fibR D 0 := c3 0 (by rw [c1]; omega)
  have hr01 : r0 1 = fibR D 1 := c3 1 (by rw [c1]; omega)
  have hsr0 := (hS0.lf_core hn0 (by omega) hS0.lf_hcore).1
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
  -- term A at breadth `b`
  have hLead := lfs_ncard_lead_le (p := p) (c := D.1.val) (r := fibRk D) (a := fibAk D) hp h2
    (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2)) (s := D.2.1.val)
    (by show D.2.1.val ≤ fibR D 0; rw [← c2, ← hr00]; exact hsr0)
    (lfDp D h2 (lfFa D) (brCo d0 r0)) hDp (lfW D h2 (lfFa D) (brCo d0 r0)) b
    (lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2))
      (lfDp D h2 (lfFa D) (brCo d0 r0)) (lfW D h2 (lfFa D) (brCo d0 r0)) b) (fun x hx => hx.1)
  rw [hDcard] at hLead
  -- the deeper count
  have hDeep := br_deeper_count_fin (Γ := LfDeepG p D h2)
    (lf_card_box (p := p) (fun v : Fin (fibRk D (lfI2 h2)) => fibAk D ⟨lfI2 h2, v⟩))
    (lfDp D h2 (lfFa D) (brCo d0 r0)) (fun q hq => (hDp q hq).1)
    (fun _ _ => ⟨0, pow_pos hp.pos _⟩)
  rw [hDcard] at hDeep
  have hΛfin : (lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2))
      (lfDp D h2 (lfFa D) (brCo d0 r0)) (lfW D h2 (lfFa D) (brCo d0 r0)) b).Finite := by
    refine (Set.finite_range (fun y : (Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI0 h2)) →
        (v : Fin (fibRk D (lfI1 h2))) → Fin (p ^ fibAk D ⟨lfI1 h2, v⟩)) ×
        (Fin (fibRk D (lfI1 h2)) → Fin (fibRk D (lfI0 h2)) →
          (v : Fin (fibRk D (lfI2 h2))) → Fin (p ^ fibAk D ⟨lfI2 h2, v⟩)) =>
        ((fun j k v => (y.1 j k v).val, fun j k v => (y.2 j k v).val) : LfLeadT D h2))).subset ?_
    rintro x ⟨-, hx1, hx2⟩
    exact ⟨(fun j k v => ⟨x.1 j k v, hx1 j k v⟩, fun j k v => ⟨x.2 j k v, hx2 j k v⟩), rfl⟩
  have hinj : Set.InjOn (fun C => (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C))
      (realizedCBb hp T D B b) := by
    intro C hC C' hC' he
    exact lf_phi_inj hp.pos h2 (hgood C hC) (hgood C' hC') (congrArg Prod.fst he)
      (congrArg Prod.snd he)
  have hmaps : ∀ C ∈ realizedCBb hp T D B b,
      (fun C => (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C)) C ∈
      (lfTrunc D h2 (brCo d0 r0) '' lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2))
        (lfBB D B (lfI2 h2)) (lfDp D h2 (lfFa D) (brCo d0 r0))
        (lfW D h2 (lfFa D) (brCo d0 r0)) b) ×ˢ
        lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0)) := by
    intro C hC
    obtain ⟨x, hx, hxe⟩ := hleadB C hC
    show (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C) ∈ _
    exact Set.mk_mem_prod ⟨x, hx, hxe.symm⟩ (hgood C hC).deep
  calc (realizedCBb hp T D B b).ncard
      ≤ ((lfTrunc D h2 (brCo d0 r0) '' lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2))
          (lfBB D B (lfI2 h2)) (lfDp D h2 (lfFa D) (brCo d0 r0))
          (lfW D h2 (lfFa D) (brCo d0 r0)) b) ×ˢ
          lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
          ((hΛfin.image (lfTrunc D h2 (brCo d0 r0))).prod (Set.toFinite _))
    _ = (lfTrunc D h2 (brCo d0 r0) '' lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2))
          (lfBB D B (lfI2 h2)) (lfDp D h2 (lfFa D) (brCo d0 r0))
          (lfW D h2 (lfFa D) (brCo d0 r0)) b).ncard *
          (lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard := Set.ncard_prod
    _ ≤ (lfLamB p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2))
          (lfBB D B (lfI2 h2)) (lfDp D h2 (lfFa D) (brCo d0 r0))
          (lfW D h2 (lfFa D) (brCo d0 r0)) b).ncard *
          (lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard :=
        Nat.mul_le_mul_right _ (Set.ncard_image_le hΛfin)
    _ ≤ _ := Nat.mul_le_mul hLead hDeep

end LfsCount

end OMA.SimsLite
