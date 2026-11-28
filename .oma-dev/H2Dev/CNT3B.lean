import H2Dev.CNT3Stmt
import H2Dev.Lift
import H2Dev.Alt2Bridge

/-! # CNT3B: the B-term of the class-3 Sims count

Li-Qiao, Remark 4.4 (second alternative), eq. (54) second alternative, (42), (86): the
commutator coefficient factor at class 3 counted through the reduction of the leading layer
modulo `p L_2`, i.e. through the `r_2`-tuple of alternating matrices of `β_G` (counted by
`N_2(r_1, r_2, s)`), the lifts of the reduced values (`|p L_2| = p ^ (s_2 - r_2)` per non-defining
pair, Remark 4.4), the core bracket `L_2 × C_core → L_3` (sharp Proposition 4.2, summed over the
breadth `b_2`), and the deeper coefficients `p ^ ((C(r_1, 2) - r_2) s_3)`.

## Main statements (pinned)

* `cbt_realizedCB_ncard_le` (any prime `p`, groups of `T` are `p`-groups of Sims rank `s0`):
  at exactly 3 layers,
  `(realizedCB hp T D B).ncard ≤
    (Σ_{b ∈ range (min s2 s3 + 1), s3 ≤ s b} p ^ (s (b (r2 + s3 + 1 - b))) *
      (#{β : r2-tuples of alternating r1 × r1 matrices over ZMod p | GensOn β ⊤, simsRk β = s0} *
        p ^ ((s2 - r2) (C(r1, 2) - r2)))) * p ^ ((C(r1, 2) - r2) s3)`
  with `r1 = fibRk D (lfI0 h2)`, `r2 = fibRk D (lfI1 h2)`, `s = D.2.1.val`,
  `s2 = Σ_v fibAk D ⟨lfI1 h2, v⟩`, `s3 = Σ_v fibAk D ⟨lfI2 h2, v⟩`.
* `cbt_realizedCB_ncard_le_two` : the same at `p = 2` with the count `Alt2.N2 r1 r2 s0`; the
  exponent of the `b`-th summand times the deeper factor is exactly `cnt3B` at breadth `b`
  (`logN2 + (C(r1,2) - r2)(s2 - r2) + (C(r1,2) - r2) s3 + s b (r2 + s3 - b + 1)`), since `b ≤ s3`.

## Structure

* Abstract count (any commutative layers): `cbtP` (the pairs `j < k`), `cbtRed` (the reduced
  value tuple), `cbt_eq53B_breadth` (fixed breadth: Prop 4.2 sharp, Lemma 4.1 and
  `br_rem44_lift`), `cbt_eq53B_sum` (summed over the admissible breadths, (51)).
* The reduction of the coordinate group (37) modulo `p`: `cbtCoordHom`, `cbt_span_le_ker`
  (needs `a ≥ 1` and `p ∣ b`), `cbtRedAdd`, `cbt_card_ker_le` (`|ker| ≤ p ^ (s2 - n)`).
* Matrix tuples: `cbtTupZ`, `cbtTup`, `cbtZ`, `cbtTupZ_congr`, `cbtTupZ_eq_of_alt`,
  `cbtTupZ_inj`, `cbt_tup_trunc`.
* `cbt_ncard_lead_le` : the B-analogue of `lf_ncard_lead_le`.
* Group level: `SimsGenSet.cbt_basisW`, `SimsGenSet.cbt_basisV` (bases of `W`, `V` from the
  Sims generators, with the coordinates of `W` the weight-1 Sims coordinates mod `p`),
  `SimsGen.cbt_tuple` (the leading coefficients of a code give the matrix tuple of `β_G`,
  alternating, spanning, of Sims rank `simsRank G`; the same-layer power words of layer 2 are
  divisible by `p`).
-/

namespace OMA.SimsLite

open scoped commutatorElement

open Module

universe u

section CbtAbstract

variable {L1 L2 L3 : Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]

/-- The pairs `j < k` of generator indices. -/
abbrev cbtP (r : ℕ) : Finset (Fin r × Fin r) := Finset.univ.filter (fun q => q.1 < q.2)

lemma cbt_card_P (r : ℕ) : (cbtP r).card = r.choose 2 := by
  have h0 := br_card_pairs_fin r 0
  rw [Nat.sub_zero] at h0
  rw [← h0]
  congr 1
  ext q
  simp

lemma cbt_cov (r : ℕ) (i j : Fin r) : i = j ∨ (i, j) ∈ cbtP r ∨ (j, i) ∈ cbtP r := by
  rcases lt_trichotomy i j with h | h | h
  · exact Or.inr (Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))

/-- The reduced values `π(β_1(g_j, g_k))` on the pairs `j < k`. -/
def cbtRed {r : ℕ} {W : Type*} [Group W] (π : L2 →* W) (g : Fin r → L1)
    (β1 : L1 →* L1 →* L2) : ↥(cbtP r) → W :=
  fun q => π (β1 (g q.1.1) (g q.1.2))

/-- Eq. (53) at `c = 3` for a fixed breadth `b`, with Remark 4.4 (second alternative): graded
bracket pairs with prescribed values on `D` whose reduced value tuples lie in `Z` number at most
`p ^ (s b (n + s_3 + 1 - b)) · |Z| · p ^ (k (C(r, 2) - |D|))` when `|ker π| ≤ p ^ k`. -/
theorem cbt_eq53B_breadth [Finite L1] [Finite L2] [Finite L3] {W : Type*} [Group W] [Finite W]
    {p r s s3 n b k : ℕ} (hp : p.Prime) (hsr : s ≤ r) (hL3 : Nat.card L3 = p ^ s3)
    (y : Fin n → L2) (hy : Subgroup.closure (Set.range y) = ⊤) (g : Fin r → L1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (D : Finset (Fin r × Fin r))
    (hD : ∀ q ∈ D, q.1 < q.2) (v : Fin r × Fin r → L2)
    (π : L2 →* W) (hk : Nat.card π.ker ≤ p ^ k) (Z : Set (↥(cbtP r) → W))
    (S : Set ((L1 →* L1 →* L2) × (L2 →* L1 →* L3)))
    (hS : ∀ β ∈ S, brAlt β.1 ∧ brJacobi β.1 β.2 ∧
        Subgroup.closure {w | ∃ u ∈ Subgroup.closure (g '' {j | (j : ℕ) < s}),
          ∃ u' ∈ Subgroup.closure (g '' {j | (j : ℕ) < s}), β.1 u u' = w} = ⊤ ∧
        brBreadth p β.2 (Subgroup.closure (g '' {j | (j : ℕ) < s})) = b ∧
        (∀ q ∈ D, β.1 (g q.1) (g q.2) = v q) ∧ cbtRed π g β.1 ∈ Z) :
    S.ncard ≤ p ^ (s * (b * (n + s3 + 1 - b))) * (Z.ncard * p ^ (k * (r.choose 2 - D.card))) := by
  have := br_finite_pairs (L1 := L1) (L2 := L2) (L3 := L3)
  haveI : Finite (L2 →* L3) :=
    Finite.of_injective (fun f : L2 →* L3 => (f : L2 → L3)) DFunLike.coe_injective
  haveI : Finite (L1 →* L2) :=
    Finite.of_injective (fun f : L1 →* L2 => (f : L1 → L2)) DFunLike.coe_injective
  haveI : Finite (L1 →* L1 →* L2) :=
    Finite.of_injective (fun f : L1 →* L1 →* L2 => (f : L1 → (L1 →* L2))) DFunLike.coe_injective
  set C := Subgroup.closure (g '' {j | (j : ℕ) < s}) with hCdef
  let c : Fin s → L1 := fun i => g (Fin.castLE hsr i)
  rcases S.eq_empty_or_nonempty with hSe | ⟨β1, hβ1⟩
  · rw [hSe, Set.ncard_empty]
    exact Nat.zero_le _
  have hbs3 : b ≤ s3 := by
    obtain ⟨-, -, -, hb, -⟩ := hS β1 hβ1
    rw [← hb]
    exact brBreadth_le_s3 hp hL3 β1.2 _
  let ρ : (L1 →* L1 →* L2) × (L2 →* L1 →* L3) → (Fin s → (L2 →* L3)) :=
    fun β i => β.2.flip (c i)
  have himg : (ρ '' S).ncard ≤ p ^ (s * (b * (n + s3 + 1 - b))) := by
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
      (br_prop42 hp hL3 hbs3 y hy s (b := b))
    rintro _ ⟨β, hβ, rfl⟩ i
    obtain ⟨-, -, -, hb, -⟩ := hS β hβ
    have hmem : c i ∈ C := Subgroup.subset_closure ⟨Fin.castLE hsr i, by simp, rfl⟩
    have h := br_card_range_le_breadth hp hL3 β.2 C hmem
    rw [hb] at h
    exact h
  have hfib : ∀ a, (S ∩ ρ ⁻¹' {a}).ncard ≤ Z.ncard * p ^ (k * (r.choose 2 - D.card)) := by
    intro a
    rcases (S ∩ ρ ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0, hβ0, hβ0a⟩
    · rw [he, Set.ncard_empty]
      exact Nat.zero_le _
    have hβ0a' : ρ β0 = a := hβ0a
    have hsl : ∀ β ∈ S ∩ ρ ⁻¹' {a}, ∀ z, ∀ u ∈ C, β.2 z u = β0.2 z u := by
      rintro β ⟨-, hβa⟩ z u hu
      have hβa' : ρ β = a := hβa
      have hgen : ∀ j : Fin r, (j : ℕ) < s → β.2.flip (g j) = β0.2.flip (g j) := by
        intro j hj
        have e := congrFun (hβa'.trans hβ0a'.symm) ⟨(j : ℕ), hj⟩
        change β.2.flip (c ⟨(j : ℕ), hj⟩) = β0.2.flip (c ⟨(j : ℕ), hj⟩) at e
        have e2 : c ⟨(j : ℕ), hj⟩ = g j := congrArg g (Fin.ext rfl)
        rw [e2] at e
        exact e
      have hle : C ≤ (β.2 z).eqLocus (β0.2 z) := by
        rw [hCdef, Subgroup.closure_le]
        rintro _ ⟨j, hj, rfl⟩
        show β.2 z (g j) = β0.2 z (g j)
        have := congrArg (fun φ : L2 →* L3 => φ z) (hgen j hj)
        simpa [MonoidHom.flip_apply] using this
      exact hle hu
    have hinj : Set.InjOn Prod.fst (S ∩ ρ ⁻¹' {a}) := by
      intro β hβ β' hβ' h1
      obtain ⟨hA, hJ, hgen, -⟩ := hS β hβ.1
      obtain ⟨hA', hJ', -⟩ := hS β' hβ'.1
      have h1' : β.1 = β'.1 := h1
      have h2 : β.2 = β'.2 := br_lemma41 C hA hA' hJ hJ' hgen (fun x u _ => by rw [h1'])
        (fun z u hu => (hsl β hβ z u hu).trans (hsl β' hβ' z u hu).symm)
      exact Prod.ext h1' h2
    have hF1 : ∀ β1 ∈ Prod.fst '' (S ∩ ρ ⁻¹' {a}),
        brAlt β1 ∧ ∀ q ∈ D, β1 (g q.1) (g q.2) = v q := by
      rintro _ ⟨β, hβ, rfl⟩
      obtain ⟨hA, -, -, -, hDv, -⟩ := hS β hβ.1
      exact ⟨hA, hDv⟩
    have hrem := br_rem44_lift g hg (cbtP r) D (cbt_cov r) v π
      (Prod.fst '' (S ∩ ρ ⁻¹' {a})) hF1
    have hZsub : (fun β : L1 →* L1 →* L2 => fun q : ↥(cbtP r) => π (β (g q.1.1) (g q.1.2))) ''
        (Prod.fst '' (S ∩ ρ ⁻¹' {a})) ⊆ Z := by
      rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
      exact (hS β hβ.1).2.2.2.2.2
    have hsd : (cbtP r \ D).card = r.choose 2 - D.card := by
      have hDP : D ⊆ cbtP r := fun q hq => Finset.mem_filter.2 ⟨Finset.mem_univ _, hD q hq⟩
      have h := Finset.card_sdiff_add_card_eq_card hDP
      rw [cbt_card_P] at h
      omega
    calc (S ∩ ρ ⁻¹' {a}).ncard ≤ (Prod.fst '' (S ∩ ρ ⁻¹' {a})).ncard :=
          Set.ncard_le_ncard_of_injOn Prod.fst (fun β hβ => ⟨β, hβ, rfl⟩) hinj (Set.toFinite _)
      _ ≤ _ := hrem
      _ ≤ Z.ncard * p ^ (k * (r.choose 2 - D.card)) := by
          rw [hsd, pow_mul]
          exact Nat.mul_le_mul (Set.ncard_le_ncard hZsub (Set.toFinite Z))
            (Nat.pow_le_pow_left hk _)
  calc S.ncard ≤ (ρ '' S).ncard * (Z.ncard * p ^ (k * (r.choose 2 - D.card))) :=
        br_ncard_le_image_mul S ρ _ hfib
    _ ≤ _ := Nat.mul_le_mul_right _ himg

/-- Eq. (53) at `c = 3` with Remark 4.4 (second alternative), summed over the admissible
breadths `s_3 ≤ s b ≤ s min(s_2, s_3)` ((51)). -/
theorem cbt_eq53B_sum [Finite L1] [Finite L2] [Finite L3] {W : Type*} [Group W] [Finite W]
    {p r s s2 s3 n k : ℕ} (hp : p.Prime) (hsr : s ≤ r) (hL2 : Nat.card L2 = p ^ s2)
    (hL3 : Nat.card L3 = p ^ s3)
    (y : Fin n → L2) (hy : Subgroup.closure (Set.range y) = ⊤) (g : Fin r → L1)
    (hg : Subgroup.closure (Set.range g) = ⊤) (D : Finset (Fin r × Fin r))
    (hD : ∀ q ∈ D, q.1 < q.2) (v : Fin r × Fin r → L2)
    (π : L2 →* W) (hk : Nat.card π.ker ≤ p ^ k) (Z : Set (↥(cbtP r) → W))
    (S : Set ((L1 →* L1 →* L2) × (L2 →* L1 →* L3)))
    (hS : ∀ β ∈ S, β ∈ lfBrSet L3 s g D v ∧ cbtRed π g β.1 ∈ Z) :
    S.ncard ≤ ∑ b ∈ (Finset.range (min s2 s3 + 1)).filter (fun b => s3 ≤ s * b),
      p ^ (s * (b * (n + s3 + 1 - b))) * (Z.ncard * p ^ (k * (r.choose 2 - D.card))) := by
  have := br_finite_pairs (L1 := L1) (L2 := L2) (L3 := L3)
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Set ((L1 →* L1 →* L2) × (L2 →* L1 →* L3)), T = fun b =>
      S ∩ {β | brBreadth p β.2 (Subgroup.closure (g '' {j | (j : ℕ) < s})) = b} := ⟨_, rfl⟩
  have hsub : S ⊆ ⋃ b ∈ (Finset.range (min s2 s3 + 1)).filter (fun b => s3 ≤ s * b), T b := by
    intro β hβ
    obtain ⟨⟨-, -, -, hgen3, -⟩, -⟩ := hS β hβ
    obtain ⟨h51, hmin⟩ := br_breadth_range hp hsr hL2 hL3 β.2 g hgen3
    refine Set.mem_iUnion₂.2 ⟨brBreadth p β.2 (Subgroup.closure (g '' {j | (j : ℕ) < s})),
      ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hmin, h51⟩
    · rw [hT]
      exact ⟨hβ, rfl⟩
  calc S.ncard ≤ (⋃ b ∈ (Finset.range (min s2 s3 + 1)).filter (fun b => s3 ≤ s * b),
        T b).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ b ∈ (Finset.range (min s2 s3 + 1)).filter (fun b => s3 ≤ s * b), (T b).ncard :=
        br_ncard_biUnion_le _ T
    _ ≤ _ := Finset.sum_le_sum fun b _ => by
        rw [hT]
        refine cbt_eq53B_breadth hp hsr hL3 y hy g hg D hD v π hk Z _ ?_
        rintro β ⟨hβ, hβb⟩
        obtain ⟨⟨hA, hgen, hJ, -, hDv⟩, hZ⟩ := hS β hβ
        exact ⟨hA, hJ, hgen, hβb, hDv, hZ⟩

end CbtAbstract

section CbtRed

/-! ### The reduction of the coordinate group (37) modulo `p` -/

/-- Coordinates modulo `p`. -/
def cbtCoordHom (n p : ℕ) : (Fin n → ℤ) →+ (Fin n → ZMod p) where
  toFun x v := (x v : ZMod p)
  map_zero' := by
    funext v
    simp
  map_add' x y := by
    funext v
    simp

lemma cbtCoordHom_apply {n p : ℕ} (x : Fin n → ℤ) (v : Fin n) :
    cbtCoordHom n p x v = (x v : ZMod p) := rfl

/-- The relations (37) vanish modulo `p` when the relative orders are positive and the
same-layer power words are divisible by `p`. -/
lemma cbt_span_le_ker {n : ℕ} (p : ℕ) (a : Fin n → ℕ) (b : Fin n → Fin n → ℕ)
    (ha : ∀ j, 1 ≤ a j) (hb : ∀ j v, p ∣ b j v) : lfSpan p a b ≤ (cbtCoordHom n p).ker := by
  rw [lfSpan, AddSubgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  refine AddMonoidHom.mem_ker.2 (funext fun i => ?_)
  show ((lfRel p a b j i : ℤ) : ZMod p) = 0
  unfold lfRel
  split_ifs with h1 h2
  · rw [Int.cast_pow, Int.cast_natCast, CharP.cast_eq_zero (ZMod p) p,
      zero_pow (by have := ha j; omega)]
  · rw [Int.cast_neg, Int.cast_natCast, (CharP.cast_eq_zero_iff (ZMod p) p _).2 (hb j i),
      neg_zero]
  · exact Int.cast_zero

/-- The reduction `L_2 → L_2 / p L_2 = F_p ^ n` on the coordinate group. -/
def cbtRedAdd {n : ℕ} (p : ℕ) (a : Fin n → ℕ) (b : Fin n → Fin n → ℕ)
    (hs : lfSpan p a b ≤ (cbtCoordHom n p).ker) : LfQ p a b →+ (Fin n → ZMod p) :=
  QuotientAddGroup.lift (lfSpan p a b) (cbtCoordHom n p) hs

lemma cbtRedAdd_mk {n : ℕ} (p : ℕ) (a : Fin n → ℕ) (b : Fin n → Fin n → ℕ)
    (hs : lfSpan p a b ≤ (cbtCoordHom n p).ker) (x : Fin n → ℤ) :
    cbtRedAdd p a b hs (QuotientAddGroup.mk x) = cbtCoordHom n p x := rfl

/-- `|ker π| ≤ p ^ (s_2 - n)` for the reduction of a coordinate group of order `p ^ s_2`. -/
theorem cbt_card_ker_le {n p : ℕ} (hp : p.Prime) (a : Fin n → ℕ) (b : Fin n → Fin n → ℕ)
    (hs : lfSpan p a b ≤ (cbtCoordHom n p).ker) {s2 : ℕ}
    (hL : Nat.card (Multiplicative (LfQ p a b)) = p ^ s2) :
    Nat.card (AddMonoidHom.toMultiplicative (cbtRedAdd p a b hs)).ker ≤ p ^ (s2 - n) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (Multiplicative (LfQ p a b)) :=
    Nat.finite_of_card_ne_zero (by rw [hL]; exact (pow_pos hp.pos _).ne')
  have hsurj : Function.Surjective (AddMonoidHom.toMultiplicative (cbtRedAdd p a b hs)) := by
    intro f
    refine ⟨Multiplicative.ofAdd (QuotientAddGroup.mk
      (fun v => ((Multiplicative.toAdd f v).val : ℤ))), ?_⟩
    apply Multiplicative.toAdd.injective
    funext v
    show (((Multiplicative.toAdd f v).val : ℤ) : ZMod p) = Multiplicative.toAdd f v
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hW : Nat.card (Multiplicative (Fin n → ZMod p)) = p ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod p),
      ZMod.card, Nat.card_fin]
  have h1 := Subgroup.card_mul_index (AddMonoidHom.toMultiplicative (cbtRedAdd p a b hs)).ker
  have h2 : (AddMonoidHom.toMultiplicative (cbtRedAdd p a b hs)).ker.index = p ^ n := by
    rw [← hW]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  rw [h2, hL] at h1
  have hpos : 0 < Nat.card (AddMonoidHom.toMultiplicative (cbtRedAdd p a b hs)).ker :=
    Nat.card_pos
  have hn : n ≤ s2 := by
    refine br_pow_le_cancel hp.one_lt ?_
    calc p ^ n = 1 * p ^ n := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hpos
      _ = p ^ s2 := h1
  have e : p ^ s2 = p ^ (s2 - n) * p ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
  rw [e] at h1
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n) h1).le

end CbtRed

section CbtTup

/-! ### Matrix tuples from coefficient arrays -/

/-- The alternating matrix tuple with entries `y j k v` above the diagonal. -/
def cbtTupZ {r n : ℕ} {M : Type*} [Neg M] [Zero M] (y : Fin r → Fin r → Fin n → M) :
    Fin n → Matrix (Fin r) (Fin r) M :=
  fun v j k => if j < k then y j k v else if k < j then -y k j v else 0

/-- The matrix tuple of a leading coefficient array, modulo `p`. -/
def cbtTup (p : ℕ) {r n : ℕ} (x : Fin r → Fin r → Fin n → ℕ) :
    Fin n → Matrix (Fin r) (Fin r) (ZMod p) :=
  cbtTupZ (fun j k v => (x j k v : ZMod p))

/-- The coordinate array of a reduced value tuple (zero off the pairs `j < k`). -/
def cbtZ {r n : ℕ} {M : Type*} [Zero M] (z : ↥(cbtP r) → Multiplicative (Fin n → M)) :
    Fin r → Fin r → Fin n → M :=
  fun j k v => if h : j < k then
    Multiplicative.toAdd (z ⟨(j, k), Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩) v else 0

lemma cbtTupZ_congr {r n : ℕ} {M : Type*} [Neg M] [Zero M] {y y' : Fin r → Fin r → Fin n → M}
    (h : ∀ j k, j < k → ∀ v, y j k v = y' j k v) : cbtTupZ y = cbtTupZ y' := by
  funext v
  ext j k
  show (if j < k then y j k v else if k < j then -y k j v else 0) =
    (if j < k then y' j k v else if k < j then -y' k j v else 0)
  split_ifs with h1 h2
  · exact h j k h1 v
  · rw [h k j h2 v]
  · rfl

lemma cbtTupZ_eq_of_alt {F : Type*} [Field F] {r n : ℕ} (y : Fin r → Fin r → Fin n → F)
    (M : Fin n → Matrix (Fin r) (Fin r) F) (hA : ∀ v, Alt2.IsAltMat (M v))
    (h : ∀ j k, j < k → ∀ v, M v j k = y j k v) : cbtTupZ y = M := by
  funext v
  ext j k
  show (if j < k then y j k v else if k < j then -y k j v else 0) = M v j k
  split_ifs with h1 h2
  · exact (h j k h1 v).symm
  · rw [(hA v).2 k j, h k j h2 v]
  · have hjk : j = k := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    subst hjk
    exact ((hA v).1 _).symm

lemma cbtTupZ_inj {r n : ℕ} {M : Type*} [AddGroup M]
    {z z' : ↥(cbtP r) → Multiplicative (Fin n → M)}
    (h : cbtTupZ (cbtZ z) = cbtTupZ (cbtZ z')) : z = z' := by
  funext q
  have hq : q.1.1 < q.1.2 := (Finset.mem_filter.1 q.2).2
  apply Multiplicative.toAdd.injective
  funext v
  have e := congrFun (congrFun (congrFun h v) q.1.1) q.1.2
  simp only [cbtTupZ, cbtZ, if_pos hq, dif_pos hq] at e
  exact e

lemma cbt_tup_trunc (p : ℕ) {m : ℕ} (D : RecData m) (h2 : 2 < D.1.val) (co : ℕ → ℕ)
    (x : LfLeadT D h2) : cbtTup p (lfTrunc D h2 co x).1 = cbtTup p x.1 :=
  cbtTupZ_congr fun j k hjk v => by
    show (((if j < k then x.1 j k v else 0 : ℕ)) : ZMod p) = _
    rw [if_pos hjk]

end CbtTup

section CbtLead

variable {p c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ}

/-- The B-analogue of `lf_ncard_lead_le` (Remark 4.4, second alternative, with (54)): the
leading commutator coefficient arrays of groups with Sims generating sets of common shape,
common same-layer power words (those of layer 2 divisible by `p`), a Sims core, prescribed
coefficients on the defining pairs `D`, and whose matrix tuples mod `p` lie in `Z'`, number at
most `Σ_b p ^ (s b (r_2 + s_3 + 1 - b)) · |Z'| · p ^ ((s_2 - r_2) (C(r_1, 2) - |D|))`. -/
theorem cbt_ncard_lead_le (hp : p.Prime) (h2 : 2 < c)
    (b0 : Fin (r (lfI0 h2)) → Fin (r (lfI0 h2)) → ℕ)
    (b1 : Fin (r (lfI1 h2)) → Fin (r (lfI1 h2)) → ℕ)
    (b2 : Fin (r (lfI2 h2)) → Fin (r (lfI2 h2)) → ℕ) (hb1 : ∀ j v, p ∣ b1 j v)
    {s : ℕ} (hs : s ≤ r (lfI0 h2))
    (D : Finset (Fin (r (lfI0 h2)) × Fin (r (lfI0 h2))))
    (hD : ∀ q ∈ D, q.1 < q.2 ∧ (q.1 : ℕ) < s)
    (w : Fin (r (lfI0 h2)) × Fin (r (lfI0 h2)) → Fin (r (lfI1 h2)) → ℕ)
    (Z' : Set (Fin (r (lfI1 h2)) → Matrix (Fin (r (lfI0 h2))) (Fin (r (lfI0 h2))) (ZMod p)))
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
      x = (S.lfLead1 h2, S.lfLead2 h2))
    (hΛZ : ∀ x ∈ Λ, cbtTup p x.1 ∈ Z') :
    Λ.ncard ≤ ∑ β ∈ (Finset.range (min (∑ v, a ⟨lfI1 h2, v⟩) (∑ v, a ⟨lfI2 h2, v⟩) + 1)).filter
        (fun β => (∑ v, a ⟨lfI2 h2, v⟩) ≤ s * β),
      p ^ (s * (β * (r (lfI1 h2) + (∑ v, a ⟨lfI2 h2, v⟩) + 1 - β))) *
        (Z'.ncard * p ^ (((∑ v, a ⟨lfI1 h2, v⟩) - r (lfI1 h2)) *
          ((r (lfI0 h2)).choose 2 - D.card))) := by
  classical
  have hp0 := hp.pos
  haveI : NeZero p := ⟨hp.ne_zero⟩
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
  obtain ⟨G0, _, _, g0, S0, hb0, hb1', hb2, hl, -, -, -⟩ := hΛ x0 hx0
  obtain ⟨I0⟩ := S0.lf_ident_nonempty hp0 h2 hl b0 b1 b2 hb0 hb1' hb2
  have hL2 := lf_card_mulQ I0.φ2 I0.card2
  have hL3 := lf_card_mulQ I0.φ3 I0.card3
  have hspan := cbt_span_le_ker p (fun v => a ⟨lfI1 h2, v⟩) b1 (fun v => S0.pos _) hb1
  let π := AddMonoidHom.toMultiplicative (cbtRedAdd p (fun v => a ⟨lfI1 h2, v⟩) b1 hspan)
  have hk : Nat.card π.ker ≤ p ^ ((∑ v, a ⟨lfI1 h2, v⟩) - r (lfI1 h2)) :=
    cbt_card_ker_le hp _ b1 hspan hL2
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
  obtain ⟨Z, hZ⟩ : ∃ Z : Set (↥(cbtP (r (lfI0 h2))) → Multiplicative (Fin (r (lfI1 h2)) → ZMod p)),
      Z = {z | cbtTupZ (cbtZ z) ∈ Z'} := ⟨_, rfl⟩
  have hZcard : Z.ncard ≤ Z'.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun z => cbtTupZ (cbtZ z)) ?_ ?_ (Set.toFinite _)
    · intro z hz
      rw [hZ] at hz
      exact hz
    · intro z _ z' _ he
      exact cbtTupZ_inj he
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
  have hex : ∀ x ∈ Λ, ∃ β, (β ∈ lfBrSet (Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2))
      s gg D vv ∧ cbtRed π gg β.1 ∈ Z) ∧ R x β := by
    intro x hx
    obtain ⟨G, _, _, g, S, hb0, hb1, hb2, hl, hcore, hDw, rfl⟩ := hΛ x hx
    obtain ⟨I⟩ := S.lf_ident_nonempty hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
    refine ⟨_, ⟨lf_brT_mem (lfMulE I.φ1) (lfMulE I.φ2) (lfMulE I.φ3)
      (fun j => g ⟨lfI0 h2, j⟩) gg (fun j => I.e1_gen j) hcore D vv (fun q hq => ?_), ?_⟩, ?_⟩
    · refine (I.e2_coord (cw (g ⟨lfI0 h2, q.1⟩) (g ⟨lfI0 h2, q.2⟩)).2).trans ?_
      show _ = Multiplicative.ofAdd (QuotientAddGroup.mk (fun v => ((w q v : ℕ) : ℤ)))
      rw [← hDw q hq]
      rfl
    · have hval : ∀ j k : Fin (r (lfI0 h2)), brT1 (lfMulE I.φ1) (lfMulE I.φ2) (gg j) (gg k) =
          Multiplicative.ofAdd (QuotientAddGroup.mk
            (fun v => ((S.lfLead1 h2 j k v : ℕ) : ℤ))) := by
        intro j k
        have e1 : gg j = lfMulE I.φ1 (Abelianization.of (g ⟨lfI0 h2, j⟩)) := (I.e1_gen j).symm
        have e2 : gg k = lfMulE I.φ1 (Abelianization.of (g ⟨lfI0 h2, k⟩)) := (I.e1_gen k).symm
        rw [e1, e2, brT1_of]
        exact I.e2_coord (cw (g ⟨lfI0 h2, j⟩) (g ⟨lfI0 h2, k⟩)).2
      rw [hZ]
      show cbtTupZ (cbtZ (cbtRed π gg (brT1 (lfMulE I.φ1) (lfMulE I.φ2)))) ∈ Z'
      have he : cbtTupZ (cbtZ (cbtRed π gg (brT1 (lfMulE I.φ1) (lfMulE I.φ2)))) =
          cbtTup p (S.lfLead1 h2) := by
        refine cbtTupZ_congr fun j k hjk v => ?_
        show (if h : j < k then Multiplicative.toAdd (π (brT1 (lfMulE I.φ1) (lfMulE I.φ2)
          (gg j) (gg k))) v else 0) = ((S.lfLead1 h2 j k v : ℕ) : ZMod p)
        rw [dif_pos hjk, hval j k]
        show (((S.lfLead1 h2 j k v : ℕ) : ℤ) : ZMod p) = _
        exact Int.cast_natCast _
      rw [he]
      exact hΛZ _ hx
    · rw [hR]
      exact ⟨G, inferInstance, g, S, I, rfl, rfl⟩
  let F := fun x => if h : x ∈ Λ then Classical.choose (hex x h) else 1
  have hF : ∀ x (h : x ∈ Λ), F x = Classical.choose (hex x h) := fun x h => dif_pos h
  have hmaps : ∀ x ∈ Λ, F x ∈ {β | β ∈ lfBrSet
      (Multiplicative (LfQ p (fun v => a ⟨lfI2 h2, v⟩) b2)) s gg D vv ∧ cbtRed π gg β.1 ∈ Z} :=
    fun x h => by
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
  refine (cbt_eq53B_sum hp hs hL2 hL3 yy (lf_closure_single p _ b1) gg (lf_closure_single p _ b0)
    D (fun q hq => (hD q hq).1) vv π hk Z _ (fun β hβ => hβ)).trans ?_
  refine Finset.sum_le_sum fun β _ => Nat.mul_le_mul_left _ ?_
  exact Nat.mul_le_mul_right _ hZcard

end CbtLead

section CbtBasis

/-! ### Bases of `V` and `W` from a Sims generating set -/

variable {G : Type u} [Group G] {p c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ}
  {g : SimsIdx c r → G}

/-- The images of the weight-1 Sims generators form a basis of `W = γ_2 / γ_3 γ_2^p`, and the
coordinates of the class of `x ∈ γ_2` are its weight-1 Sims coordinates modulo `p`. -/
theorem SimsGenSet.cbt_basisW [hp : Fact p.Prime] [Finite G] (S : SimsGenSet p a g)
    (h1 : 1 < c) (hr1 : p ^ r ⟨1, h1⟩ * Nat.card (pN p G) = Nat.card (lcs G 1)) :
    ∃ bW : Basis (Fin (r ⟨1, h1⟩)) (ZMod p) (Additive (WQ p G)),
      ∀ (x : G) (hx : x ∈ lcs G 1) (v : Fin (r ⟨1, h1⟩)),
        bW.repr (Additive.ofMul (piW p G ⟨x, hx⟩)) v =
          ((S.nf.coord x ⟨⟨1, h1⟩, v⟩ : ℕ) : ZMod p) := by
  have : Finite (WQ p G) := Finite.of_surjective _ piW_surjective
  have : Finite (Additive (WQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (WQ p G)) := inferInstance
  let w : Fin (r ⟨1, h1⟩) → Additive (WQ p G) := fun v =>
    Additive.ofMul (piW p G ⟨g ⟨⟨1, h1⟩, v⟩, S.mem ⟨⟨1, h1⟩, v⟩⟩)
  have key : ∀ (x : G) (hx : x ∈ lcs G 1), Additive.ofMul (piW p G ⟨x, hx⟩) =
      ∑ v, ((S.nf.coord x ⟨⟨1, h1⟩, v⟩ : ℕ) : ZMod p) • w v := by
    intro x hx
    have hb := S.lf_pi_block ⟨1, h1⟩ (piW p G) (fun y hy => piW_eq_one_of (lcs_two_le_pN p hy))
      (fun v => (S.nf.coord x ⟨⟨1, h1⟩, v⟩).val)
      (deeper_mem g S.mem (fun h => (S.nf.coord x h).val) ⟨1, h1⟩) hx
      (S.lf_sims_lift ⟨1, h1⟩ hx)
    calc Additive.ofMul (piW p G ⟨x, hx⟩) = Additive.ofMul (∏ v : Fin (r ⟨1, h1⟩),
          piW p G ⟨g ⟨⟨1, h1⟩, v⟩, S.mem ⟨⟨1, h1⟩, v⟩⟩ ^ (S.nf.coord x ⟨⟨1, h1⟩, v⟩).val) :=
          congrArg Additive.ofMul hb
      _ = ∑ v, ((S.nf.coord x ⟨⟨1, h1⟩, v⟩ : ℕ) : ZMod p) • w v := by
          rw [ofMul_prod]
          exact Finset.sum_congr rfl fun v _ =>
            (ofMul_pow _ _).trans (Nat.cast_smul_eq_nsmul (ZMod p) _ _).symm
  have hspan : ⊤ ≤ Submodule.span (ZMod p) (Set.range w) := by
    intro y _
    obtain ⟨⟨x, hxm⟩, hx⟩ := piW_surjective (p := p) (G := G) (Additive.toMul y)
    have e : y = Additive.ofMul (piW p G ⟨x, hxm⟩) := by
      rw [hx]
      rfl
    rw [e, key x hxm]
    exact sum_mem fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  have hcard : Fintype.card (Fin (r ⟨1, h1⟩)) = Module.finrank (ZMod p) (Additive (WQ p G)) := by
    rw [Fintype.card_fin]
    have h := card_lcs_one_eq (p := p) (G := G)
    rw [← hr1, mul_comm (p ^ r ⟨1, h1⟩)] at h
    have hpos : 0 < Nat.card (pN p G) := Nat.card_pos
    exact Nat.pow_right_injective hp.out.two_le (Nat.eq_of_mul_eq_mul_left hpos h)
  have hbw : ∀ v, basisOfTopLeSpanOfCardEqFinrank w hspan hcard v = w v := fun v => by
    rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  refine ⟨basisOfTopLeSpanOfCardEqFinrank w hspan hcard, fun x hx v => ?_⟩
  have hs : (∑ v, ((S.nf.coord x ⟨⟨1, h1⟩, v⟩ : ℕ) : ZMod p) • w v) =
      ∑ v, ((S.nf.coord x ⟨⟨1, h1⟩, v⟩ : ℕ) : ZMod p) •
        basisOfTopLeSpanOfCardEqFinrank w hspan hcard v :=
    Finset.sum_congr rfl fun v _ => by rw [hbw v]
  rw [key x hx, hs, Basis.repr_sum_self]

/-- The images of the weight-0 Sims generators form a basis of `V = G / Φ(G)`. -/
theorem SimsGenSet.cbt_basisV [hp : Fact p.Prime] [Finite G] (S : SimsGenSet p a g)
    (h0 : 0 < c) (hr0 : p ^ r ⟨0, h0⟩ * Nat.card (pPhi p G) = Nat.card G) :
    ∃ bV : Basis (Fin (r ⟨0, h0⟩)) (ZMod p) (Additive (VQ p G)),
      ∀ j, bV j = Additive.ofMul (piV p G (g ⟨⟨0, h0⟩, j⟩)) := by
  have : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have : Finite (Additive (VQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (VQ p G)) := inferInstance
  let w : Fin (r ⟨0, h0⟩) → Additive (VQ p G) := fun j =>
    Additive.ofMul (piV p G (g ⟨⟨0, h0⟩, j⟩))
  have key : ∀ x : G, Additive.ofMul (piV p G x) ∈ Submodule.span (ZMod p) (Set.range w) := by
    intro x
    have hx : x ∈ lcs G ((⟨0, h0⟩ : Fin c) : ℕ) := Subgroup.mem_top x
    have hb := S.lf_pi_block ⟨0, h0⟩ ((piV p G).comp (lcs G ((⟨0, h0⟩ : Fin c) : ℕ)).subtype)
      (fun y hy => by
        show piV p G (y : G) = 1
        refine (MonoidHom.mem_ker).1 ?_
        rw [ker_piV]
        exact lcs_succ_le_layK p 0 hy)
      (fun v => (S.nf.coord x ⟨⟨0, h0⟩, v⟩).val)
      (deeper_mem g S.mem (fun h => (S.nf.coord x h).val) ⟨0, h0⟩) hx
      (S.lf_sims_lift ⟨0, h0⟩ hx)
    have e : Additive.ofMul (piV p G x) = ∑ v, (S.nf.coord x ⟨⟨0, h0⟩, v⟩).val • w v := by
      calc Additive.ofMul (piV p G x) = Additive.ofMul
            ((piV p G).comp (lcs G ((⟨0, h0⟩ : Fin c) : ℕ)).subtype ⟨x, hx⟩) := rfl
        _ = Additive.ofMul (∏ v : Fin (r ⟨0, h0⟩),
            (piV p G).comp (lcs G ((⟨0, h0⟩ : Fin c) : ℕ)).subtype
              ⟨g ⟨⟨0, h0⟩, v⟩, S.mem ⟨⟨0, h0⟩, v⟩⟩ ^ (S.nf.coord x ⟨⟨0, h0⟩, v⟩).val) :=
            congrArg Additive.ofMul hb
        _ = _ := by
            rw [ofMul_prod]
            exact Finset.sum_congr rfl fun v _ => ofMul_pow _ _
    rw [e]
    exact sum_mem fun v _ => nsmul_mem (Submodule.subset_span (Set.mem_range_self (f := w) v) :
      w v ∈ Submodule.span (ZMod p) (Set.range w)) _
  have hspan : ⊤ ≤ Submodule.span (ZMod p) (Set.range w) := by
    intro y _
    obtain ⟨x, hx⟩ := piV_surjective (p := p) (G := G) (Additive.toMul y)
    have e : y = Additive.ofMul (piV p G x) := by
      rw [hx]
      rfl
    rw [e]
    exact key x
  have hcard : Fintype.card (Fin (r ⟨0, h0⟩)) = Module.finrank (ZMod p) (Additive (VQ p G)) := by
    rw [Fintype.card_fin]
    have h1 := card_eq_pow_finrank_elemQ (p := p) (pPhi p G)
    rw [card_V_eq_index (p := p) (G := G)] at h1
    have h3 := Subgroup.card_mul_index (pPhi p G)
    rw [h1, ← hr0, mul_comm (p ^ r ⟨0, h0⟩)] at h3
    have hpos : 0 < Nat.card (pPhi p G) := Nat.card_pos
    exact (Nat.pow_right_injective hp.out.two_le (Nat.eq_of_mul_eq_mul_left hpos h3)).symm
  refine ⟨basisOfTopLeSpanOfCardEqFinrank w hspan hcard, fun j => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]

end CbtBasis

section CbtTuple

variable {G : Type} [Group G] [Finite G] {p : ℕ} {u : ℕ → G} {d : SimsData} {X : Fin d.n → G}
  {r : ℕ → ℕ}

/-- The leading coefficients of a code determine the matrix tuple of `β_G` mod `p` (in the bases
of `V`, `W` given by the Sims generators): it is alternating, spanning and of Sims rank
`simsRank G`. Moreover the same-layer power words of the second layer are divisible by `p`. -/
theorem SimsGen.cbt_tuple [Fact p.Prime] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) (hsum : ∑ t, d.a t = m) {D : RecData m}
    {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    (e : hS.enc hp m hnm hs2 hsum = ⟨D, (B, C)⟩) (h2 : 2 < D.1.val) (hG : IsPGroup p G) :
    ((∀ k, Alt2.IsAltMat (cbtTup p (lfPhi1 D h2 C).1 k)) ∧
      Alt2.GensOn (cbtTup p (lfPhi1 D h2 C).1) ⊤ ∧
      Alt2.simsRk (cbtTup p (lfPhi1 D h2 C).1) = simsRank G) ∧
    ∀ j v, p ∣ lfBB D B (lfI1 h2) j v := by
  obtain ⟨cf1, -, cf3, cf4, cf5, cf6, -, -⟩ := hS.lf_code hp hnm hs2 hsum e
  have hn : d.n = fOff r D.1.val := by rw [← cf1]; exact hS.nL_spec.symm
  have hfo : ∀ w ≤ D.1.val, fOff r w = fOff (fibR D) w :=
    fOff_congr (fun w hw => cf3 w (by rw [cf1]; exact hw))
  have f1 := hfo 1 (by omega)
  have e0 : fOff r 0 = 0 := rfl
  have e0' : fOff (fibR D) 0 = 0 := rfl
  obtain ⟨g', S, hpw, hl1, -, -⟩ := hS.lf_reindex hp hn h2 (fibRk D)
    (fun i => cf3 i.val (by rw [cf1]; exact i.isLt)) (fibAk D) (fun k => by
      show fibA D (fOff (fibR D) k.1.val + k.2.val) = _
      rw [cf4, hfo _ k.1.isLt.le])
  have hpwB : ∀ (i : Fin D.1.val) (j v : Fin (fibRk D i)),
      (S.powerWords ⟨i, j⟩ ⟨i, v⟩).val = lfBB D B i j v := by
    intro i j v
    rw [hpw, ← cf6]
    unfold lfBB
    rw [hfo _ i.isLt.le]
  have hr0 : p ^ fibRk D ⟨0, by omega⟩ * Nat.card (pPhi p G) = Nat.card G := by
    have h := hS.layer_card 0
    rw [cf3 0 (by rw [cf1]; omega), lcs_zero, Subgroup.card_top] at h
    exact h
  have hr1 : p ^ fibRk D ⟨1, by omega⟩ * Nat.card (pN p G) = Nat.card (lcs G 1) := by
    have h := hS.layer_card 1
    rw [cf3 1 (by rw [cf1]; omega)] at h
    exact h
  obtain ⟨bW, hbW⟩ := S.cbt_basisW (by omega) hr1
  obtain ⟨bV, hbV⟩ := S.cbt_basisV (by omega) hr0
  have hlead : ∀ j k : Fin (fibRk D (lfI0 h2)), j < k → ∀ v : Fin (fibRk D (lfI1 h2)),
      (lfPhi1 D h2 C).1 j k v = S.lfLead1 h2 j k v := by
    intro j k hjk v
    rw [hl1 j k v hjk]
    show lfCn D C (fOff (fibR D) 0 + j.val) (fOff (fibR D) 0 + k.val)
      (fOff (fibR D) 1 + v.val) = _
    rw [cf5, e0', ← f1, e0]
  have hM := Alt2.simsRk_lamLin_tuple hG bV bW
  have heq : cbtTup p (lfPhi1 D h2 C).1 = Alt2.matTuple (lamLin (p := p) (G := G)) bV bW := by
    refine cbtTupZ_eq_of_alt _ _ hM.1 fun j k hjk v => ?_
    show bW.repr (lamLin (bV j) (bV k)) v = (((lfPhi1 D h2 C).1 j k v : ℕ) : ZMod p)
    rw [hbV j, hbV k, lamLin_mk]
    refine (hbW _ (cw (g' ⟨lfI0 h2, j⟩) (g' ⟨lfI0 h2, k⟩)).2 v).trans ?_
    rw [hlead j k hjk v]
    rfl
  refine ⟨by rw [heq]; exact hM, fun j v => ?_⟩
  have hmem : g' ⟨lfI1 h2, j⟩ ^ p ^ fibAk D ⟨lfI1 h2, j⟩ ∈ lcs G 1 :=
    Subgroup.pow_mem _ (S.mem ⟨lfI1 h2, j⟩) _
  have hone : piW p G ⟨g' ⟨lfI1 h2, j⟩ ^ p ^ fibAk D ⟨lfI1 h2, j⟩, hmem⟩ = 1 := by
    have e1 : (⟨g' ⟨lfI1 h2, j⟩ ^ p ^ fibAk D ⟨lfI1 h2, j⟩, hmem⟩ : lcs G 1) =
        (⟨g' ⟨lfI1 h2, j⟩, S.mem ⟨lfI1 h2, j⟩⟩ : lcs G 1) ^ (p ^ fibAk D ⟨lfI1 h2, j⟩) :=
      Subtype.ext (SubgroupClass.coe_pow _ _).symm
    obtain ⟨t, ht⟩ : ∃ t, fibAk D ⟨lfI1 h2, j⟩ = t + 1 :=
      ⟨fibAk D ⟨lfI1 h2, j⟩ - 1, by have := S.pos ⟨lfI1 h2, j⟩; omega⟩
    rw [e1, map_pow, ht, pow_succ, pow_mul, W_pow_p]
  have h := hbW _ hmem v
  rw [hone] at h
  simp only [ofMul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [← hpwB (lfI1 h2) j v]
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).1 h.symm

end CbtTuple

section CbtCount

/-- Term B of the class-3 count: the commutator coefficient factor at class 3 for a prime `p`,
when the groups of `T` are `p`-groups of Sims rank `s0`. The count is the sum over the
admissible breadths `b` of the sharp Proposition 4.2 factor `p ^ (s b (r_2 + s_3 + 1 - b))`, times
the number of alternating `r_2`-tuples mod `p` with values spanning and Sims rank `s0` (the
reduced leading layer, (54)), times the lifts `p ^ ((s_2 - r_2)(C(r_1,2) - r_2))` of Remark 4.4,
times the deeper count `p ^ ((C(r_1, 2) - r_2) s_3)`. -/
theorem cbt_realizedCB_ncard_le {p m : ℕ} [Fact p.Prime] (hp : p.Prime) (T : Set FiniteGrp.{0})
    (D : RecData m) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) (s0 : ℕ)
    (hT : ∀ G ∈ T, IsPGroup p G ∧ simsRank G = s0) :
    (realizedCB hp T D B).ncard ≤
      (∑ β ∈ (Finset.range (min (∑ v, fibAk D ⟨lfI1 h2, v⟩)
          (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1)).filter
          (fun β => (∑ v, fibAk D ⟨lfI2 h2, v⟩) ≤ D.2.1.val * β),
        p ^ (D.2.1.val * (β * (fibRk D (lfI1 h2) + (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1 - β))) *
          ({t : Fin (fibRk D (lfI1 h2)) →
              Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
              (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0}.ncard *
            p ^ (((∑ v, fibAk D ⟨lfI1 h2, v⟩) - fibRk D (lfI1 h2)) *
              ((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2))))) *
        p ^ (((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2)) *
          ∑ v, fibAk D ⟨lfI2 h2, v⟩) := by
  rcases (realizedCB hp T D B).eq_empty_or_nonempty with hE | ⟨C0, hC0⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0, hG0T, u0, d0, X0, r0, hS0, hnm0, hs0, hsum0, e0⟩ := hC0
  obtain ⟨c1, c2, c3, -, -, -, c7, c8⟩ := hS0.lf_code hp hnm0 hs0 hsum0 e0
  have hn0 : d0.n = fOff r0 D.1.val := by rw [← c1]; exact hS0.nL_spec.symm
  have hr00 : r0 0 = fibR D 0 := c3 0 (by rw [c1]; omega)
  have hr01 : r0 1 = fibR D 1 := c3 1 (by rw [c1]; omega)
  have hsr0 := (hS0.lf_core hn0 (by omega) hS0.lf_hcore).1
  -- every realised commutator array is good, with the core indices of `G0`
  have hgood : ∀ C ∈ realizedCB hp T D B, LfGood p hp.pos D h2 B (brCo d0 r0) C := by
    rintro C ⟨G, -, u, d, X, r, hS, hnm, hs2, hsum, e⟩
    obtain ⟨g1, g2, g3, -, -, -, g7, -⟩ := hS.lf_code hp hnm hs2 hsum e
    refine hS.lf_good hp hnm hs2 hsum e h2 h3 _
      (lf_brCo_common hS hS0 hs2 (g2.trans c2.symm) ?_ ?_)
    · rw [g3 1 (by rw [g1]; omega), hr01]
    · intro k hk
      rw [g7 k hk, c7 k (by rw [c2, ← g2]; exact hk)]
  -- the matrix tuples of the realised arrays
  have htup : ∀ C ∈ realizedCB hp T D B, cbtTup p (lfPhi1 D h2 C).1 ∈
      {t : Fin (fibRk D (lfI1 h2)) →
        Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
        (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0} := by
    rintro C ⟨G, hGT, u, d, X, r, hS, hnm, hs2, hsum, e⟩
    obtain ⟨hpG, hsG⟩ := hT G hGT
    obtain ⟨⟨t1, t2, t3⟩, -⟩ := hS.cbt_tuple hp hnm hs2 hsum e h2 hpG
    exact ⟨t1, t2, t3.trans hsG⟩
  have hb1div : ∀ j v, p ∣ lfBB D B (lfI1 h2) j v :=
    (hS0.cbt_tuple hp hnm0 hs0 hsum0 e0 h2 (hT G0 hG0T).1).2
  -- the defining pairs of `G0`: distinct, `f(j) < co(j)`, `f(j) < s`
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
  -- the counted leading pairs: realised ones with an admissible matrix tuple
  obtain ⟨ΛB, hΛB⟩ : ∃ Λ : Set (LfLeadT D h2), Λ =
      {x | x ∈ lfLam p D h2 (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2))
        (lfDp D h2 (lfFa D) (brCo d0 r0)) (lfW D h2 (lfFa D) (brCo d0 r0)) ∧
        cbtTup p x.1 ∈ {t : Fin (fibRk D (lfI1 h2)) →
          Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
          (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0}} := ⟨_, rfl⟩
  -- term B for the leading pairs
  have hLead := cbt_ncard_lead_le (p := p) (c := D.1.val) (r := fibRk D) (a := fibAk D) hp h2
    (lfBB D B (lfI0 h2)) (lfBB D B (lfI1 h2)) (lfBB D B (lfI2 h2)) hb1div (s := D.2.1.val)
    (by show D.2.1.val ≤ fibR D 0; rw [← c2, ← hr00]; exact hsr0)
    (lfDp D h2 (lfFa D) (brCo d0 r0)) hDp (lfW D h2 (lfFa D) (brCo d0 r0))
    {t : Fin (fibRk D (lfI1 h2)) →
      Matrix (Fin (fibRk D (lfI0 h2))) (Fin (fibRk D (lfI0 h2))) (ZMod p) |
      (∀ k, Alt2.IsAltMat (t k)) ∧ Alt2.GensOn t ⊤ ∧ Alt2.simsRk t = s0} ΛB
    (fun x hx => by rw [hΛB] at hx; exact hx.1.1) (fun x hx => by rw [hΛB] at hx; exact hx.2)
  rw [hDcard] at hLead
  -- the deeper count
  have hDeep := br_deeper_count_fin (Γ := LfDeepG p D h2)
    (lf_card_box (p := p) (fun v : Fin (fibRk D (lfI2 h2)) => fibAk D ⟨lfI2 h2, v⟩))
    (lfDp D h2 (lfFa D) (brCo d0 r0)) (fun q hq => (hDp q hq).1)
    (fun _ _ => ⟨0, pow_pos hp.pos _⟩)
  rw [hDcard] at hDeep
  -- finiteness of the counted leading pairs
  have hΛfin : ΛB.Finite := by
    refine (Set.finite_range (fun y : (Fin (fibRk D (lfI0 h2)) → Fin (fibRk D (lfI0 h2)) →
        (v : Fin (fibRk D (lfI1 h2))) → Fin (p ^ fibAk D ⟨lfI1 h2, v⟩)) ×
        (Fin (fibRk D (lfI1 h2)) → Fin (fibRk D (lfI0 h2)) →
          (v : Fin (fibRk D (lfI2 h2))) → Fin (p ^ fibAk D ⟨lfI2 h2, v⟩)) =>
        ((fun j k v => (y.1 j k v).val, fun j k v => (y.2 j k v).val) : LfLeadT D h2))).subset ?_
    intro x hx
    rw [hΛB] at hx
    obtain ⟨⟨-, hx1, hx2⟩, -⟩ := hx
    exact ⟨(fun j k v => ⟨x.1 j k v, hx1 j k v⟩, fun j k v => ⟨x.2 j k v, hx2 j k v⟩), rfl⟩
  have hinj : Set.InjOn (fun C => (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C))
      (realizedCB hp T D B) := by
    intro C hC C' hC' he
    exact lf_phi_inj hp.pos h2 (hgood C hC) (hgood C' hC') (congrArg Prod.fst he)
      (congrArg Prod.snd he)
  have hmaps : ∀ C ∈ realizedCB hp T D B, (fun C => (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C)) C ∈
      (lfTrunc D h2 (brCo d0 r0) '' ΛB) ×ˢ
        lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0)) := by
    intro C hC
    obtain ⟨x, hx, hxe⟩ := (hgood C hC).lead
    have hxB : x ∈ ΛB := by
      rw [hΛB]
      refine ⟨hx, ?_⟩
      have h := htup C hC
      rw [hxe, cbt_tup_trunc] at h
      exact h
    show (lfPhi1 D h2 C, lfPhi3 hp.pos D h2 C) ∈ _
    exact Set.mk_mem_prod ⟨x, hxB, hxe.symm⟩ (hgood C hC).deep
  calc (realizedCB hp T D B).ncard
      ≤ ((lfTrunc D h2 (brCo d0 r0) '' ΛB) ×ˢ
          lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
          ((hΛfin.image (lfTrunc D h2 (brCo d0 r0))).prod (Set.toFinite _))
    _ = (lfTrunc D h2 (brCo d0 r0) '' ΛB).ncard *
          (lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard := Set.ncard_prod
    _ ≤ ΛB.ncard * (lfDset p hp.pos D h2 (lfDp D h2 (lfFa D) (brCo d0 r0))).ncard :=
        Nat.mul_le_mul_right _ (Set.ncard_image_le hΛfin)
    _ ≤ _ := Nat.mul_le_mul hLead hDeep

/-- Term B at `p = 2` with the count `N_2(r_1, r_2, s0)` (Alt2.N2): the input `M(D)` for
`lf_ncard_classes_le_fiberB_pw` matching `cnt3B` (the exponent of the `b`-th summand times the
deeper factor is `log_2 N_2 + (C(r_1,2) - r_2)(s_2 - r_2) + (C(r_1,2) - r_2) s_3 +
s b (r_2 + s_3 - b + 1)`). -/
theorem cbt_realizedCB_ncard_le_two {m : ℕ} (T : Set FiniteGrp.{0})
    (D : RecData m) (h2 : 2 < D.1.val) (h3 : D.1.val = 3)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)) (s0 : ℕ)
    (hT : ∀ G ∈ T, IsPGroup 2 G ∧ simsRank G = s0) :
    (realizedCB Nat.prime_two T D B).ncard ≤
      (∑ β ∈ (Finset.range (min (∑ v, fibAk D ⟨lfI1 h2, v⟩)
          (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1)).filter
          (fun β => (∑ v, fibAk D ⟨lfI2 h2, v⟩) ≤ D.2.1.val * β),
        2 ^ (D.2.1.val * (β * (fibRk D (lfI1 h2) + (∑ v, fibAk D ⟨lfI2 h2, v⟩) + 1 - β))) *
          (Alt2.N2 (fibRk D (lfI0 h2)) (fibRk D (lfI1 h2)) s0 *
            2 ^ (((∑ v, fibAk D ⟨lfI1 h2, v⟩) - fibRk D (lfI1 h2)) *
              ((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2))))) *
        2 ^ (((fibRk D (lfI0 h2)).choose 2 - fibRk D (lfI1 h2)) *
          ∑ v, fibAk D ⟨lfI2 h2, v⟩) := by
  rw [Alt2.N2_eq_ncard]
  exact cbt_realizedCB_ncard_le Nat.prime_two T D h2 h3 B s0 hT

end CbtCount

end OMA.SimsLite
