import Mathlib

/-! # Alt2: Li-Qiao Part II, linear algebra of alternating forms (pure, no group theory)

Li-Qiao (arXiv:2610.14509v3), Part II, Sec. 7-8, over an arbitrary field `F` (the paper's `F_q`;
the target is `F = ZMod 2`).  `X = Fin R → F`, alternating forms are `R × R` matrices.

* D.Alt : `IsAltMat`, the subspace `altSub F R = Alt(X)` with `finrank_altSub : dim = C(R,2)` and
  `card_altSub`; the form `bfL x y A = x ⬝ A y`; `Isotropic A U` (`A|_{U×U} = 0`),
  `FaithfulOn 𝒜 U` (the restriction map `res_U` is injective on `𝒜`), `IsHollowing 𝒜 h`,
  `IsMinHollowing`, `IsFaithfulDim 𝒜 d` (`d`-faithful); `rad A`, the isotropic locus
  `isoLocus A h = Z_h(A)` and `isoCount A h = I_h(A)`.
* An alternating map `β : ∧²X → W = F^M` is an `M`-tuple of alternating matrices.  `GensOn β U` is
  `β(∧²U) = W`; `simsRk β = s(β)` is eq. (91); `dualSpan β = A_β = β*(W*)`.
* Prop 7.2 : `gensOn_iff` (dual description), `gensOn_top_iff` (`β` surjective iff the tuple is
  linearly independent), `prop72_i`, `prop72_ii`, `prop72_iii`.
* `N2 r1 r2 s` : the number of `r2`-tuples of alternating `ZMod 2` matrices on `F_2^r1` whose values
  span `F_2^r2` and whose Sims rank is `s` (eq. (21) at `p = 2`); `N2_support` (empty unless
  `s ≤ r1`, `r2 ≤ C(r1,2)` and `2 ≤ s` when `r2 ≥ 1`) and `N2_le` (`N2 ≤ 2^(r2 C(r1,2))`).
* Lemma 2.7 (crude forms) : `card_GL_le` (`|GL_d(q)| ≤ q^(d^2)`, part (iii)), `ncard_grass_le`
  (at most `q^(n k)` subspaces of dimension `k` in `F^n`), `exists_pivots` (pivot coordinates) and
  `ncard_grass_le_pivot` (`[n, k]_q ≤ 2^n q^(k(n-k))`, part (i) up to the constant), and
  `ncard_alt_rank_le` (part (ii) with constant `2^R`: at most `2^R q^((R-ρ)ρ + C(ρ,2))` alternating
  forms with `dim rad ≥ R - ρ`).
* Lemma 8.1 (structural part) : `isotropic_of_le_rad`, `isoLocus_smul` (`Z_h(cA) = Z_h(A)`),
  `isoCount_le_grass`, and `two_mul_finrank_le_of_isotropic` (an isotropic `h`-space satisfies
  `2h ≤ R + dim rad A`, so `Z_h(A) = ∅` for `h > R - a` when `rank A = 2a`).
-/

namespace OMA.SimsLite.Alt2

open Module Matrix

section Defs

variable {F : Type*} [Field F] {R M : ℕ}

/-- `A` is an alternating matrix: zero diagonal and `A j i = - A i j`. -/
def IsAltMat (A : Matrix (Fin R) (Fin R) F) : Prop :=
  (∀ i, A i i = 0) ∧ ∀ i j, A j i = -A i j

lemma isAltMat_iff_transpose (A : Matrix (Fin R) (Fin R) F) :
    IsAltMat A ↔ (∀ i, A i i = 0) ∧ A.transpose = -A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by ext i j; exact h2 i j⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    have := congrArg (fun B : Matrix (Fin R) (Fin R) F => B i j) h2
    simpa using this

variable (F R) in
/-- `Alt(X)`: the subspace of alternating matrices. -/
def altSub : Submodule F (Matrix (Fin R) (Fin R) F) where
  carrier := {A | IsAltMat A}
  add_mem' := by
    intro A B hA hB
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · show A i i + B i i = 0
      rw [hA.1 i, hB.1 i, add_zero]
    · show A j i + B j i = -(A i j + B i j)
      rw [hA.2 i j, hB.2 i j]
      ring
  zero_mem' := ⟨fun i => rfl, fun i j => by simp⟩
  smul_mem' := by
    intro c A hA
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · show c * A i i = 0
      rw [hA.1 i, mul_zero]
    · show c * A j i = -(c * A i j)
      rw [hA.2 i j]
      ring

lemma mem_altSub {A : Matrix (Fin R) (Fin R) F} : A ∈ altSub F R ↔ IsAltMat A := Iff.rfl

variable (R) in
/-- Index set `{(i, j) : i < j}` of the free entries of an alternating matrix. -/
abbrev TPairs : Type := {p : Fin R × Fin R // p.1 < p.2}

/-- The alternating matrix with prescribed entries above the diagonal. -/
def altOf (f : TPairs R → F) : Matrix (Fin R) (Fin R) F := fun i j =>
  if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0

lemma altOf_isAlt (f : TPairs R → F) : IsAltMat (altOf f) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp [altOf]
  · rcases lt_trichotomy i j with h | h | h
    · have h' : ¬ j < i := not_lt.2 h.le
      simp only [altOf, dif_pos h, dif_neg h']
    · subst h
      simp [altOf]
    · have h' : ¬ i < j := not_lt.2 h.le
      simp only [altOf, dif_pos h, dif_neg h', neg_neg]

variable (F R) in
/-- `Alt(X) ≃ F^{pairs i<j}`. -/
def altEquiv : altSub F R ≃ₗ[F] (TPairs R → F) where
  toFun A p := (A : Matrix (Fin R) (Fin R) F) p.1.1 p.1.2
  map_add' A B := rfl
  map_smul' c A := rfl
  invFun f := ⟨altOf f, altOf_isAlt f⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    have hA := (mem_altSub.1 A.2)
    show altOf (fun p : TPairs R => (A : Matrix (Fin R) (Fin R) F) p.1.1 p.1.2) i j =
      (A : Matrix (Fin R) (Fin R) F) i j
    rcases lt_trichotomy i j with h | h | h
    · simp only [altOf, dif_pos h]
    · subst h
      simp [altOf, hA.1 i]
    · have h' : ¬ i < j := not_lt.2 h.le
      simp only [altOf, dif_pos h, dif_neg h']
      rw [hA.2 j i]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, hij⟩ := p
    show altOf f i j = f ⟨(i, j), hij⟩
    simp only [altOf, dif_pos hij]

lemma card_TPairs (R : ℕ) : Fintype.card (TPairs R) = R.choose 2 := by
  have h1 : Fintype.card (TPairs R) =
      ∑ j : Fin R, ∑ i : Fin R, if i < j then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ∀ j : Fin R, (∑ i : Fin R, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have h3 : ∑ j : Fin R, (j : ℕ) = ∑ i ∈ Finset.range R, i :=
    Fin.sum_univ_eq_sum_range (fun i => i) R
  rw [h1, Finset.sum_congr rfl (fun j _ => h2 j), h3, Nat.choose_two_right,
    ← Finset.sum_range_id_mul_two, Nat.mul_div_cancel _ (by norm_num)]

variable (F R) in
/-- D.Alt : `dim Alt(X) = C(R, 2)`. -/
theorem finrank_altSub : finrank F (altSub F R) = R.choose 2 := by
  rw [(altEquiv F R).finrank_eq, Module.finrank_fintype_fun_eq_card, card_TPairs]

variable (F R) in
theorem card_altSub : Nat.card (altSub F R) = Nat.card F ^ R.choose 2 := by
  rw [Nat.card_congr (altEquiv F R).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := TPairs R),
    card_TPairs]

/-- The bilinear form `A(x, y) = x ⬝ A y`, as a linear function of the matrix `A`. -/
def bfL (x y : Fin R → F) : Matrix (Fin R) (Fin R) F →ₗ[F] F where
  toFun A := x ⬝ᵥ (A *ᵥ y)
  map_add' A B := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by rw [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

lemma bfL_apply (x y : Fin R → F) (A : Matrix (Fin R) (Fin R) F) :
    bfL x y A = x ⬝ᵥ (A *ᵥ y) := rfl

lemma bfL_single (A : Matrix (Fin R) (Fin R) F) (i j : Fin R) :
    bfL (Pi.single i 1) (Pi.single j 1) A = A i j := by
  simp [bfL, dotProduct, Matrix.mulVec, Pi.single_apply]

lemma bfL_sum (β : Fin M → Matrix (Fin R) (Fin R) F) (c : Fin M → F) (x y : Fin R → F) :
    bfL x y (∑ k, c k • β k) = ∑ k, c k * bfL x y (β k) := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- An alternating form vanishes on the diagonal: `A(x, x) = 0`. -/
lemma bfL_self_eq_zero {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A) (x : Fin R → F) :
    bfL x x A = 0 := by
  rw [bfL_apply, Matrix.dot_mulVec_eq_sum_sum]
  have e : ∑ j, ∑ i, x i * A i j * x j = ∑ p : Fin R × Fin R, x p.2 * A p.2 p.1 * x p.1 :=
    (Fintype.sum_prod_type' (fun j i => x i * A i j * x j)).symm
  rw [e]
  apply Finset.sum_ninvolution (fun p => (p.2, p.1))
  · rintro ⟨j, i⟩
    show x i * A i j * x j + x j * A j i * x i = 0
    rw [hA.2 i j]
    ring
  · rintro ⟨j, i⟩ hne heq
    have hij : i = j := congrArg Prod.fst heq
    apply hne
    show x i * A i j * x j = 0
    rw [hij, hA.1 j]
    ring
  · intro p
    exact Finset.mem_univ _
  · intro p
    rfl

/-- `A|_{U×U} = 0`: `U` is totally isotropic for `A`. -/
def Isotropic (A : Matrix (Fin R) (Fin R) F) (U : Submodule F (Fin R → F)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, bfL x y A = 0

/-- `𝒜` is faithful on `U`: the restriction map `res_U : 𝒜 → Alt(U)` is injective. -/
def FaithfulOn (𝒜 : Submodule F (Matrix (Fin R) (Fin R) F)) (U : Submodule F (Fin R → F)) :
    Prop :=
  ∀ A ∈ 𝒜, Isotropic A U → A = 0

/-- `𝒜` is `d`-faithful: faithful on some `d`-dimensional subspace. -/
def IsFaithfulDim (𝒜 : Submodule F (Matrix (Fin R) (Fin R) F)) (d : ℕ) : Prop :=
  ∃ U : Submodule F (Fin R → F), finrank F U = d ∧ FaithfulOn 𝒜 U

/-- `𝒜` is `h`-hollowing: every `h`-space is totally isotropic for some nonzero `A ∈ 𝒜`. -/
def IsHollowing (𝒜 : Submodule F (Matrix (Fin R) (Fin R) F)) (h : ℕ) : Prop :=
  ∀ H : Submodule F (Fin R → F), finrank F H = h → ∃ A ∈ 𝒜, A ≠ 0 ∧ Isotropic A H

/-- `𝒜` is minimally `h`-hollowing. -/
def IsMinHollowing (𝒜 : Submodule F (Matrix (Fin R) (Fin R) F)) (h : ℕ) : Prop :=
  IsHollowing 𝒜 h ∧ ∀ 𝒝 : Submodule F (Matrix (Fin R) (Fin R) F), 𝒝 < 𝒜 → ¬ IsHollowing 𝒝 h

lemma isotropic_top_iff (A : Matrix (Fin R) (Fin R) F) : Isotropic A ⊤ ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := h (Pi.single i 1) Submodule.mem_top (Pi.single j 1) Submodule.mem_top
    rw [bfL_single] at this
    simpa using this
  · rintro rfl x _ y _
    exact map_zero _

/-- The values `β(x, y)`, `x, y ∈ U`, of the tuple `β` (i.e. `β(∧²U)` as a set). -/
def vals (β : Fin M → Matrix (Fin R) (Fin R) F) (U : Submodule F (Fin R → F)) :
    Set (Fin M → F) :=
  {w | ∃ x ∈ U, ∃ y ∈ U, w = fun k => bfL x y (β k)}

/-- `β(∧²U) = W`. -/
def GensOn (β : Fin M → Matrix (Fin R) (Fin R) F) (U : Submodule F (Fin R → F)) : Prop :=
  Submodule.span F (vals β U) = ⊤

/-- The Sims rank (91): `s(β) = min {dim U : β(∧²U) = W}`. -/
noncomputable def simsRk (β : Fin M → Matrix (Fin R) (Fin R) F) : ℕ :=
  sInf {d | ∃ U : Submodule F (Fin R → F), finrank F U = d ∧ GensOn β U}

/-- `A_β = β*(W*)`, the span of the coordinate forms. -/
def dualSpan (β : Fin M → Matrix (Fin R) (Fin R) F) : Submodule F (Matrix (Fin R) (Fin R) F) :=
  Submodule.span F (Set.range β)

/-- `rad A = {x : A(x, y) = 0 for all y}`. -/
def rad (A : Matrix (Fin R) (Fin R) F) : Submodule F (Fin R → F) :=
  LinearMap.ker (Matrix.toBilin' A)

/-- The isotropic locus `Z_h(A)`. -/
def isoLocus (A : Matrix (Fin R) (Fin R) F) (h : ℕ) : Set (Submodule F (Fin R → F)) :=
  {H | finrank F H = h ∧ Isotropic A H}

/-- `I_h(A) = |Z_h(A)|`. -/
noncomputable def isoCount (A : Matrix (Fin R) (Fin R) F) (h : ℕ) : ℕ :=
  (isoLocus A h).ncard

end Defs

section Duality

variable {F : Type*} [Field F] {R M : ℕ}

/-- Duality: a family of vectors of `F^M` spans iff no nonzero functional kills all of them. -/
theorem span_range_eq_top_iff {ι : Type*} (g : ι → (Fin M → F)) :
    Submodule.span F (Set.range g) = ⊤ ↔
      ∀ c : Fin M → F, (∀ i, ∑ k, c k * g i k = 0) → c = 0 := by
  constructor
  · intro hg c hc
    let φ : (Fin M → F) →ₗ[F] F :=
      { toFun := fun v => ∑ k, c k * v k
        map_add' := by
          intro v w
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro a v
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring) }
    have hle : Submodule.span F (Set.range g) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    funext j
    have hmem : (Pi.single j (1 : F) : Fin M → F) ∈ Submodule.span F (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    have hj := LinearMap.mem_ker.1 (hle hmem)
    change ∑ k, c k * (Pi.single j (1 : F) : Fin M → F) k = 0 at hj
    simpa [Pi.single_apply] using hj
  · intro hc
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨c, key⟩ : ∃ c : Fin M → F, ∀ v, φ v = ∑ k, c k * v k :=
      ⟨fun k => φ (fun j => if k = j then 1 else 0), fun v => by
        rw [LinearMap.pi_apply_eq_sum_univ φ v]
        exact Finset.sum_congr rfl (fun k _ => by rw [smul_eq_mul, mul_comm])⟩
    have h0 : c = 0 := hc c (fun i => by
      rw [← key]
      exact LinearMap.mem_ker.1 (hφ (Submodule.subset_span ⟨i, rfl⟩)))
    apply hφ0
    exact LinearMap.ext fun v => by rw [key v, h0]; simp

/-- Prop 7.2, dual form: `β(∧²U) = W` iff no nonzero `λ ∈ W*` has `λ ∘ β` vanishing on `U`. -/
theorem gensOn_iff (β : Fin M → Matrix (Fin R) (Fin R) F) (U : Submodule F (Fin R → F)) :
    GensOn β U ↔ ∀ c : Fin M → F, Isotropic (∑ k, c k • β k) U → c = 0 := by
  have hv : vals β U = Set.range
      (fun p : {p : (Fin R → F) × (Fin R → F) // p.1 ∈ U ∧ p.2 ∈ U} =>
        fun k => bfL p.1.1 p.1.2 (β k)) := by
    ext w
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨⟨(x, y), hx, hy⟩, rfl⟩
    · rintro ⟨⟨⟨x, y⟩, hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  unfold GensOn
  rw [hv, span_range_eq_top_iff]
  constructor
  · intro h c hc
    apply h c
    rintro ⟨⟨x, y⟩, hx, hy⟩
    show ∑ k, c k * bfL x y (β k) = 0
    rw [← bfL_sum]
    exact hc x hx y hy
  · intro h c hc
    apply h c
    intro x hx y hy
    rw [bfL_sum]
    exact hc ⟨(x, y), hx, hy⟩

/-- `β : ∧²X → W` is surjective iff its coordinate forms are linearly independent. -/
theorem gensOn_top_iff (β : Fin M → Matrix (Fin R) (Fin R) F) :
    GensOn β ⊤ ↔ LinearIndependent F β := by
  rw [gensOn_iff, Fintype.linearIndependent_iff]
  simp only [isotropic_top_iff]
  constructor
  · intro h c hc
    exact congrFun (h c hc)
  · intro h c hc
    funext k
    exact h c hc k

/-- Prop 7.2 (i): `β(∧²U) = W` iff `A_β` is faithful on `U`. -/
theorem prop72_i (β : Fin M → Matrix (Fin R) (Fin R) F) (hβ : LinearIndependent F β)
    (U : Submodule F (Fin R → F)) : GensOn β U ↔ FaithfulOn (dualSpan β) U := by
  rw [gensOn_iff]
  constructor
  · intro h A hA hiso
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hA
    rw [h c hiso]
    simp
  · intro h c hc
    have h0 := h _ ((Submodule.mem_span_range_iff_exists_fun F).2 ⟨c, rfl⟩) hc
    funext k
    exact Fintype.linearIndependent_iff.1 hβ c h0 k

lemma gensOn_mono (β : Fin M → Matrix (Fin R) (Fin R) F) {U U' : Submodule F (Fin R → F)}
    (hUU : U ≤ U') (h : GensOn β U) : GensOn β U' := by
  unfold GensOn at *
  apply top_unique
  rw [← h]
  apply Submodule.span_mono
  rintro w ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, hUU hx, y, hUU hy, rfl⟩

/-- Every subspace extends to a subspace of any larger dimension `≤ R`. -/
lemma exists_le_finrank_eq (k : ℕ) :
    ∀ U : Submodule F (Fin R → F), finrank F U + k ≤ R →
      ∃ H : Submodule F (Fin R → F), U ≤ H ∧ finrank F H = finrank F U + k := by
  induction k with
  | zero => intro U _; exact ⟨U, le_rfl, rfl⟩
  | succ k ih =>
    intro U hU
    have hlt : U < ⊤ := by
      apply lt_top_iff_ne_top.2
      intro htop
      have : finrank F U = R := by rw [htop, finrank_top, Module.finrank_fin_fun]
      omega
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact U.zero_mem)
    obtain ⟨U', hUU', hU'⟩ : ∃ U' : Submodule F (Fin R → F),
        U < U' ∧ finrank F U' ≤ finrank F U + 1 := by
      refine ⟨U ⊔ Submodule.span F {v}, ?_, ?_⟩
      · refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hv
        rw [heq]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
      · have := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span F {v})
        rwa [finrank_span_singleton hv0] at this
    have h1 : finrank F U < finrank F U' := Submodule.finrank_lt_finrank_of_lt hUU'
    obtain ⟨H, hH, hHf⟩ := ih U' (by omega)
    exact ⟨H, hUU'.le.trans hH, by omega⟩

lemma simsRk_le_of (β : Fin M → Matrix (Fin R) (Fin R) F) {U : Submodule F (Fin R → F)} {d : ℕ}
    (hU : finrank F U = d) (hg : GensOn β U) : simsRk β ≤ d :=
  Nat.sInf_le ⟨U, hU, hg⟩

lemma simsRk_le_R (β : Fin M → Matrix (Fin R) (Fin R) F) (hg : GensOn β ⊤) : simsRk β ≤ R :=
  simsRk_le_of β (by rw [finrank_top, Module.finrank_fin_fun]) hg

lemma exists_gens_of_simsRk (β : Fin M → Matrix (Fin R) (Fin R) F) (hg : GensOn β ⊤) :
    ∃ U : Submodule F (Fin R → F), finrank F U = simsRk β ∧ GensOn β U :=
  Nat.sInf_mem (s := {d | ∃ U : Submodule F (Fin R → F), finrank F U = d ∧ GensOn β U})
    ⟨R, ⊤, by rw [finrank_top, Module.finrank_fin_fun], hg⟩

/-- (92): `d < s(β)` iff no `d`-space generates `W`. -/
theorem lt_simsRk_iff (β : Fin M → Matrix (Fin R) (Fin R) F) (hg : GensOn β ⊤) {d : ℕ}
    (hd : d ≤ R) :
    d < simsRk β ↔ ∀ H : Submodule F (Fin R → F), finrank F H = d → ¬ GensOn β H := by
  constructor
  · intro hlt H hH hgH
    have := simsRk_le_of β hH hgH
    omega
  · intro hall
    by_contra hle
    push_neg at hle
    obtain ⟨U, hU, hgU⟩ := exists_gens_of_simsRk β hg
    obtain ⟨H, hUH, hH⟩ := exists_le_finrank_eq (d - finrank F U) U (by omega)
    exact hall H (by rw [hH]; omega) (gensOn_mono β hUH hgU)

/-- Prop 7.2 (ii): for `h ≤ dim X`, `A_β` is `h`-hollowing iff `s(β) > h`. -/
theorem prop72_ii (β : Fin M → Matrix (Fin R) (Fin R) F) (hβ : LinearIndependent F β) (h : ℕ)
    (hh : h ≤ R) : IsHollowing (dualSpan β) h ↔ h < simsRk β := by
  have hg := (gensOn_top_iff β).2 hβ
  rw [lt_simsRk_iff β hg hh]
  unfold IsHollowing
  refine forall_congr' fun H => forall_congr' fun _ => ?_
  rw [prop72_i β hβ H]
  unfold FaithfulOn
  push_neg
  constructor
  · rintro ⟨A, hA, h1, h2⟩
    exact ⟨A, hA, h2, h1⟩
  · rintro ⟨A, hA, h1, h2⟩
    exact ⟨A, hA, h2, h1⟩

/-- `s(β) ≤ d` iff `A_β` is `d`-faithful (for `d ≤ dim X`). -/
theorem faithfulDim_iff (β : Fin M → Matrix (Fin R) (Fin R) F) (hβ : LinearIndependent F β)
    (d : ℕ) (hd : d ≤ R) : IsFaithfulDim (dualSpan β) d ↔ simsRk β ≤ d := by
  have hg := (gensOn_top_iff β).2 hβ
  constructor
  · rintro ⟨U, hU, hf⟩
    exact simsRk_le_of β hU ((prop72_i β hβ U).2 hf)
  · intro hle
    obtain ⟨U, hU, hgU⟩ := exists_gens_of_simsRk β hg
    obtain ⟨H, hUH, hH⟩ := exists_le_finrank_eq (d - finrank F U) U (by omega)
    exact ⟨H, by rw [hH]; omega, (prop72_i β hβ H).1 (gensOn_mono β hUH hgU)⟩

/-- Prop 7.2 (iii): for `1 ≤ s ≤ dim X`, `s(β) = s` iff `A_β` is `(s-1)`-hollowing and
`s`-faithful. -/
theorem prop72_iii (β : Fin M → Matrix (Fin R) (Fin R) F) (hβ : LinearIndependent F β) (s : ℕ)
    (hs1 : 1 ≤ s) (hsR : s ≤ R) :
    simsRk β = s ↔ IsHollowing (dualSpan β) (s - 1) ∧ IsFaithfulDim (dualSpan β) s := by
  rw [prop72_ii β hβ (s - 1) (by omega), faithfulDim_iff β hβ s hsR]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- For an alternating surjective `β` onto a nonzero `W`, `s(β) ≥ 2`. -/
theorem two_le_simsRk (β : Fin M → Matrix (Fin R) (Fin R) F) (hA : ∀ k, IsAltMat (β k))
    (hg : GensOn β ⊤) (hM : 1 ≤ M) : 2 ≤ simsRk β := by
  obtain ⟨U, hU, hgU⟩ := exists_gens_of_simsRk β hg
  by_contra hlt
  have h1 : finrank F U ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
  have hsub : vals β U ⊆ {0} := by
    rintro w ⟨x, hx, y, hy, rfl⟩
    rw [Set.mem_singleton_iff]
    obtain ⟨a, ha⟩ := hv ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hv ⟨y, hy⟩
    have hx' : x = a • (v : Fin R → F) := (congrArg Subtype.val ha).symm
    have hy' : y = b • (v : Fin R → F) := (congrArg Subtype.val hb).symm
    funext k
    rw [hx', hy', bfL_apply, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    have := bfL_self_eq_zero (hA k) (v : Fin R → F)
    rw [bfL_apply] at this
    simp only [this, smul_zero, Pi.zero_apply]
  have hle : Submodule.span F (vals β U) ≤ ⊥ :=
    Submodule.span_le.2 (fun w hw => by
      rw [Set.mem_singleton_iff.1 (hsub hw)]
      exact Submodule.zero_mem _)
  unfold GensOn at hgU
  rw [hgU] at hle
  have hmem : (Pi.single (⟨0, hM⟩ : Fin M) (1 : F) : Fin M → F) ∈ (⊥ : Submodule F (Fin M → F)) :=
    hle Submodule.mem_top
  rw [Submodule.mem_bot] at hmem
  have := congrFun hmem ⟨0, hM⟩
  simp at this

/-- `dim W ≤ dim Alt(X) = C(R, 2)` for a surjective alternating `β`. -/
theorem card_le_choose (β : Fin M → Matrix (Fin R) (Fin R) F) (hA : ∀ k, IsAltMat (β k))
    (hβ : LinearIndependent F β) : M ≤ R.choose 2 := by
  have h1 := finrank_span_eq_card hβ
  have h2 : Submodule.span F (Set.range β) ≤ altSub F R :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hA k)
  have h3 := Submodule.finrank_mono h2
  rw [h1, Fintype.card_fin, finrank_altSub] at h3
  exact h3

end Duality

section N2

open Classical in
/-- `N_2(r1, r2, s)` as a count (not its `log_2`): the number of `r2`-tuples of alternating
`ZMod 2` matrices on `F_2^r1` whose values span `F_2^r2` and of Sims rank `s` (eq. (21)). -/
noncomputable def N2 (r1 r2 s : ℕ) : ℕ :=
  (Finset.univ.filter (fun β : Fin r2 → Matrix (Fin r1) (Fin r1) (ZMod 2) =>
    (∀ k, IsAltMat (β k)) ∧ GensOn β ⊤ ∧ simsRk β = s)).card

/-- Support of `N_2`: nonzero only if `s ≤ r1`, `r2 ≤ C(r1, 2)` and (`r2 ≥ 1 → s ≥ 2`). -/
theorem N2_support {r1 r2 s : ℕ} (h : 0 < N2 r1 r2 s) :
    s ≤ r1 ∧ r2 ≤ r1.choose 2 ∧ (1 ≤ r2 → 2 ≤ s) := by
  classical
  unfold N2 at h
  obtain ⟨β, hβ⟩ := Finset.card_pos.1 h
  obtain ⟨-, hA, hg, hs⟩ := Finset.mem_filter.1 hβ
  refine ⟨?_, ?_, ?_⟩
  · rw [← hs]
    exact simsRk_le_R β hg
  · exact card_le_choose β hA ((gensOn_top_iff β).1 hg)
  · intro h2
    rw [← hs]
    exact two_le_simsRk β hA hg h2

/-- Trivial bound `N_2(r1, r2, s) ≤ |Alt(F_2^r1)|^r2 = 2^(r2 C(r1,2))`. -/
theorem N2_le (r1 r2 s : ℕ) : N2 r1 r2 s ≤ 2 ^ (r2 * r1.choose 2) := by
  classical
  unfold N2
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine (Nat.card_le_card_of_injective
    (fun β => fun k => (⟨β.1 k, β.2.1 k⟩ : altSub (ZMod 2) r1)) ?_).trans (le_of_eq ?_)
  · intro β γ h
    apply Subtype.ext
    funext k
    exact congrArg Subtype.val (congrFun h k)
  · rw [Nat.card_fun, Nat.card_fin, card_altSub, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
      ← pow_mul, mul_comm]

end N2

section Lemma27

variable {F : Type*} [Field F]

/-- Lemma 2.7 (iii), first part: `|GL_d(q)| ≤ q^(d^2)`. -/
theorem card_GL_le [Fintype F] (d : ℕ) :
    Nat.card (GL (Fin d) F) ≤ Fintype.card F ^ (d ^ 2) := by
  calc Nat.card (GL (Fin d) F) ≤ Nat.card (Matrix (Fin d) (Fin d) F) :=
        Nat.card_le_card_of_injective (fun g => (g : Matrix (Fin d) (Fin d) F))
          (fun g h hgh => Units.ext hgh)
    _ = Fintype.card F ^ (d ^ 2) := by
        show Nat.card (Fin d → Fin d → F) = _
        rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ← pow_mul, sq]

/-- Every `k`-dimensional subspace of `F^n` is spanned by a `k`-tuple. -/
lemma grass_subset_range (n k : ℕ) :
    {U : Submodule F (Fin n → F) | finrank F U = k} ⊆
      Set.range (fun v : Fin k → (Fin n → F) => Submodule.span F (Set.range v)) := by
  intro U hU
  let B := Module.finBasisOfFinrankEq F U hU
  refine ⟨fun i => (B i : Fin n → F), ?_⟩
  have h := congrArg (Submodule.map U.subtype) B.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
  exact h

lemma grass_finite [Finite F] (n k : ℕ) :
    {U : Submodule F (Fin n → F) | finrank F U = k}.Finite :=
  (Set.finite_range _).subset (grass_subset_range n k)

/-- Crude Lemma 2.7 (i)/(iii): `F^n` has at most `q^(n k)` subspaces of dimension `k`. -/
theorem ncard_grass_le [Finite F] (n k : ℕ) :
    {U : Submodule F (Fin n → F) | finrank F U = k}.ncard ≤ Nat.card F ^ (n * k) := by
  calc {U : Submodule F (Fin n → F) | finrank F U = k}.ncard
      ≤ (Set.range (fun v : Fin k → (Fin n → F) => Submodule.span F (Set.range v))).ncard :=
        Set.ncard_le_ncard (grass_subset_range n k) (Set.finite_range _)
    _ ≤ (Set.univ : Set (Fin k → (Fin n → F))).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card F ^ (n * k) := by
        rw [Set.ncard_univ, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul]

end Lemma27

section Grass

variable {F : Type*} [Field F] {n : ℕ}

/-- Pivot coordinates: every subspace `U ≤ F^n` has a coordinate set `S` with `|S| = dim U` such
that the coordinate projection `U → F^S` is bijective. -/
theorem exists_pivots (U : Submodule F (Fin n → F)) :
    ∃ S : Finset (Fin n), S.card = finrank F U ∧
      (∀ v ∈ U, (∀ i ∈ S, v i = 0) → v = 0) ∧
      (∀ w : S → F, ∃ v ∈ U, ∀ i : S, v i = w i) := by
  classical
  let P : Finset (Fin n) → Prop := fun S => ∀ v ∈ U, (∀ i ∈ S, v i = 0) → v = 0
  have hne : (Finset.univ.filter P).Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun v _ hv => funext fun i => hv i (Finset.mem_univ i)⟩⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card hne
  have hPS : P S := (Finset.mem_filter.1 hS).2
  let L : U →ₗ[F] (S → F) := (LinearMap.funLeft F F (fun i : S => (i : Fin n))).comp U.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    exact hPS v v.2 (fun i hi => congrFun hv ⟨i, hi⟩)
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne'
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne')
    obtain ⟨c, key⟩ : ∃ c : S → F, ∀ w, φ w = ∑ i, c i * w i :=
      ⟨fun i => φ (fun j => if i = j then 1 else 0), fun w => by
        rw [LinearMap.pi_apply_eq_sum_univ φ w]
        exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul, mul_comm])⟩
    have hc : c ≠ 0 := by
      intro h0
      apply hφ0
      exact LinearMap.ext fun w => by rw [key w, h0]; simp
    obtain ⟨i0, hi0⟩ : ∃ i0, c i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc (funext h)
    have hrel : ∀ v ∈ U, ∑ i : S, c i * v i = 0 := by
      intro v hv
      have := LinearMap.mem_ker.1 (hφ (LinearMap.mem_range_self L ⟨v, hv⟩))
      rw [key] at this
      exact this
    have hP' : P (S.erase (i0 : Fin n)) := by
      intro v hv hz
      apply hPS v hv
      have hv0 : v i0 = 0 := by
        have h1 := hrel v hv
        rw [Finset.sum_eq_single i0] at h1
        · exact (mul_eq_zero.1 h1).resolve_left hi0
        · intro b _ hb
          rw [hz b (Finset.mem_erase.2 ⟨fun h => hb (Subtype.ext h), b.2⟩), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      intro i hi
      by_cases h : i = (i0 : Fin n)
      · rw [h]
        exact hv0
      · exact hz i (Finset.mem_erase.2 ⟨h, hi⟩)
    have h1 := hmin (S.erase (i0 : Fin n)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP'⟩)
    have h2 := Finset.card_erase_lt_of_mem i0.2
    omega
  refine ⟨S, ?_, hPS, fun w => ?_⟩
  · have e := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at e
    exact e.symm
  · obtain ⟨v, hv⟩ := hsurj w
    exact ⟨v, v.2, fun i => congrFun hv i⟩

/-- Lemma 2.7 (i), upper bound in crude form: `F^n` has at most `2^n q^(k(n-k))` subspaces of
dimension `k` (each is the graph over its pivot coordinates of a map `F^k → F^(n-k)`). -/
theorem ncard_grass_le_pivot [Finite F] (k : ℕ) :
    {U : Submodule F (Fin n → F) | finrank F U = k}.ncard ≤
      2 ^ n * Nat.card F ^ (k * (n - k)) := by
  classical
  have hdata : ∀ U : {U : Submodule F (Fin n → F) // finrank F U = k},
      ∃ S : Finset (Fin n), ∃ _ : S.card = k, ∃ u : Fin n → (Fin n → F),
        (∀ i, u i ∈ U.1) ∧ (∀ i ∈ S, ∀ j ∈ S, u i j = if j = i then 1 else 0) ∧
        (∀ v ∈ U.1, (∀ i ∈ S, v i = 0) → v = 0) := by
    intro U
    obtain ⟨S, hS, hinj, hsurj⟩ := exists_pivots U.1
    choose u' hu'U hu' using fun i : S => hsurj (Pi.single i 1)
    refine ⟨S, hS.trans U.2, fun i => if h : i ∈ S then u' ⟨i, h⟩ else 0, ?_, ?_, hinj⟩
    · intro i
      by_cases h : i ∈ S
      · dsimp only
        rw [dif_pos h]
        exact hu'U _
      · dsimp only
        rw [dif_neg h]
        exact U.1.zero_mem
    · intro i hi j hj
      dsimp only
      rw [dif_pos hi, hu' ⟨i, hi⟩ ⟨j, hj⟩]
      simp [Pi.single_apply]
  choose S hS u hu hpiv hinj using hdata
  have hc : ∀ U, ((S U)ᶜ).card = n - k := fun U => by
    rw [Finset.card_compl, Fintype.card_fin, hS U]
  let code : {U : Submodule F (Fin n → F) // finrank F U = k} →
      Finset (Fin n) × (Fin k → Fin (n - k) → F) := fun U =>
    (S U, fun a b => u U ((S U).orderEmbOfFin (hS U) a) (((S U)ᶜ).orderEmbOfFin (hc U) b))
  have hemb : ∀ (T T' : Finset (Fin n)) {m : ℕ} (h : T.card = m) (h' : T'.card = m), T = T' →
      ∀ a, T.orderEmbOfFin h a = T'.orderEmbOfFin h' a := by
    rintro T _ m h h' rfl a
    rfl
  have hle : ∀ U U', code U = code U' → U.1 ≤ U'.1 := by
    intro U U' h
    have hSS : S U = S U' := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have huu : ∀ i ∈ S U, u U i = u U' i := by
      intro i hi
      funext j
      by_cases hj : j ∈ S U
      · rw [hpiv U i hi j hj, hpiv U' i (hSS ▸ hi) j (hSS ▸ hj)]
      · have hjc : j ∈ (S U)ᶜ := Finset.mem_compl.2 hj
        obtain ⟨b, hb⟩ : j ∈ Set.range ((S U)ᶜ.orderEmbOfFin (hc U)) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjc
        obtain ⟨a, ha⟩ : i ∈ Set.range ((S U).orderEmbOfFin (hS U)) := by
          rw [Finset.range_orderEmbOfFin]
          exact hi
        have h3 := congrFun (congrFun h2 a) b
        simp only [code] at h3
        rw [← hemb _ _ (hS U) (hS U') hSS a, ← hemb _ _ (hc U) (hc U') (by rw [hSS]) b, ha,
          hb] at h3
        exact h3
    intro v hv
    have hw : v - ∑ i ∈ S U, v i • u U i = 0 := by
      apply hinj U _ (sub_mem hv (sum_mem (fun i _ => Submodule.smul_mem _ _ (hu U i))))
      intro j hj
      have hsum : ∑ i ∈ S U, v i * u U i j = ∑ i ∈ S U, if j = i then v i else 0 :=
        Finset.sum_congr rfl (fun i hi => by rw [hpiv U i hi j hj]; split_ifs <;> simp)
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum, Finset.sum_ite_eq, if_pos hj, sub_self]
    have hv' : v = ∑ i ∈ S U, v i • u U i := sub_eq_zero.1 hw
    rw [hv']
    exact sum_mem (fun i hi => by rw [huu i hi]; exact Submodule.smul_mem _ _ (hu U' i))
  have hinjc : Function.Injective code := by
    intro U U' h
    exact Subtype.ext (le_antisymm (hle U U' h) (hle U' U h.symm))
  rw [← Nat.card_coe_set_eq]
  calc Nat.card {U : Submodule F (Fin n → F) | finrank F U = k}
      = Nat.card {U : Submodule F (Fin n → F) // finrank F U = k} := rfl
    _ ≤ Nat.card (Finset (Fin n) × (Fin k → Fin (n - k) → F)) :=
        Nat.card_le_card_of_injective code hinjc
    _ = 2 ^ n * Nat.card F ^ (k * (n - k)) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin,
          Nat.card_eq_fintype_card (α := Finset (Fin n)), Fintype.card_finset, Fintype.card_fin,
          ← pow_mul, mul_comm (n - k) k]

end Grass

section Lemma27ii

variable {F : Type*} [Field F] {R : ℕ}

/-- Alternating forms are skew: `A(x, y) = - A(y, x)`. -/
lemma bfL_swap {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A) (x y : Fin R → F) :
    bfL x y A = -bfL y x A := by
  have h := bfL_self_eq_zero hA (x + y)
  have hx := bfL_self_eq_zero hA x
  have hy := bfL_self_eq_zero hA y
  rw [bfL_apply, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct] at h
  rw [bfL_apply] at hx hy
  rw [bfL_apply, bfL_apply]
  linear_combination h - hx - hy

lemma bfL_rad_left {A : Matrix (Fin R) (Fin R) F} {x : Fin R → F} (hx : x ∈ rad A)
    (y : Fin R → F) : bfL x y A = 0 := by
  have h := LinearMap.congr_fun (LinearMap.mem_ker.1 hx) y
  rw [Matrix.toBilin'_apply', LinearMap.zero_apply] at h
  exact h

lemma bfL_rad_right {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A) {x : Fin R → F}
    (hx : x ∈ rad A) (y : Fin R → F) : bfL y x A = 0 := by
  rw [bfL_swap hA, bfL_rad_left hx, neg_zero]

/-- A subspace `U ≤ W` extends inside `W` to any dimension `≤ dim W`. -/
lemma exists_le_le_finrank_eq (W : Submodule F (Fin R → F)) (k : ℕ) :
    ∀ U : Submodule F (Fin R → F), U ≤ W → finrank F U + k ≤ finrank F W →
      ∃ H : Submodule F (Fin R → F), U ≤ H ∧ H ≤ W ∧ finrank F H = finrank F U + k := by
  induction k with
  | zero => intro U hU _; exact ⟨U, le_rfl, hU, rfl⟩
  | succ k ih =>
    intro U hUW hk
    have hlt : U < W := lt_of_le_of_ne hUW (fun h => by rw [h] at hk; omega)
    obtain ⟨v, hvW, hv⟩ := SetLike.exists_of_lt hlt
    have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact U.zero_mem)
    obtain ⟨U', hUU', hU'W, hU'⟩ : ∃ U' : Submodule F (Fin R → F),
        U < U' ∧ U' ≤ W ∧ finrank F U' ≤ finrank F U + 1 := by
      refine ⟨U ⊔ Submodule.span F {v}, ?_,
        sup_le hUW (Submodule.span_le.2 (Set.singleton_subset_iff.2 hvW)), ?_⟩
      · refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hv
        rw [heq]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
      · have := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span F {v})
        rwa [finrank_span_singleton hv0] at this
    have h1 : finrank F U < finrank F U' := Submodule.finrank_lt_finrank_of_lt hUU'
    obtain ⟨H, hH, hHW, hHf⟩ := ih U' hU'W (by omega)
    exact ⟨H, hUU'.le.trans hH, hHW, by omega⟩

/-- Two forms agreeing on the coordinates outside `P` agree on vectors vanishing on `P`. -/
lemma bfL_eq_of_agree {A A' : Matrix (Fin R) (Fin R) F} (P : Finset (Fin R))
    (hAA : ∀ p ∉ P, ∀ q ∉ P, A p q = A' p q) {c d : Fin R → F} (hc : ∀ i ∈ P, c i = 0)
    (hd : ∀ i ∈ P, d i = 0) : bfL c d A = bfL c d A' := by
  rw [bfL_apply, bfL_apply, Matrix.dot_mulVec_eq_sum_sum, Matrix.dot_mulVec_eq_sum_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  by_cases hj : j ∈ P
  · rw [hd j hj, mul_zero, mul_zero]
  · by_cases hi : i ∈ P
    · rw [hc i hi, zero_mul, zero_mul, zero_mul, zero_mul]
    · rw [hAA i hi j hj]

/-- Lemma 2.7 (ii), crude form: the alternating `R × R` forms of rank at most `ρ`
(`dim rad A ≥ R - ρ`) number at most `2^R q^((R-ρ)ρ + C(ρ,2))`; for `ρ = 2a` the exponent is
`a(2R - 2a - 1)`. -/
theorem ncard_alt_rank_le [Finite F] (ρ : ℕ) (hρ : ρ ≤ R) :
    {A : Matrix (Fin R) (Fin R) F | IsAltMat A ∧ R - ρ ≤ finrank F (rad A)}.ncard ≤
      2 ^ R * Nat.card F ^ ((R - ρ) * ρ + ρ.choose 2) := by
  classical
  have hK : ∀ A : {A : Matrix (Fin R) (Fin R) F // IsAltMat A ∧ R - ρ ≤ finrank F (rad A)},
      ∃ K : Submodule F (Fin R → F), K ≤ rad A.1 ∧ finrank F K = R - ρ := by
    intro A
    have h2 := A.2.2
    obtain ⟨H, -, hH, hf⟩ := exists_le_le_finrank_eq (rad A.1) (R - ρ) ⊥ bot_le
      (by rw [finrank_bot]; omega)
    exact ⟨H, hH, by rw [hf, finrank_bot, zero_add]⟩
  choose K hKrad hKdim using hK
  have hP : ∀ K : Submodule F (Fin R → F), ∃ P : Finset (Fin R), P.card = finrank F K ∧
      (∀ w : P → F, ∃ v ∈ K, ∀ i : P, v i = w i) := fun K => by
    obtain ⟨P, h1, -, h3⟩ := exists_pivots K
    exact ⟨P, h1, h3⟩
  choose P hPcard hPsurj using hP
  have hPc : ∀ A, ((P (K A))ᶜ).card = ρ := fun A => by
    rw [Finset.card_compl, Fintype.card_fin, hPcard, hKdim]
    omega
  let code : {A : Matrix (Fin R) (Fin R) F // IsAltMat A ∧ R - ρ ≤ finrank F (rad A)} →
      {U : Submodule F (Fin R → F) // finrank F U = R - ρ} × (TPairs ρ → F) := fun A =>
    (⟨K A, hKdim A⟩, fun p => A.1 (((P (K A))ᶜ).orderEmbOfFin (hPc A) p.1.1)
      (((P (K A))ᶜ).orderEmbOfFin (hPc A) p.1.2))
  have hemb : ∀ (T T' : Finset (Fin R)) {m : ℕ} (h : T.card = m) (h' : T'.card = m), T = T' →
      ∀ a, T.orderEmbOfFin h a = T'.orderEmbOfFin h' a := by
    rintro T _ m h h' rfl a
    rfl
  have hinjc : Function.Injective code := by
    intro A A' h
    have hKK : K A = K A' := congrArg Subtype.val (congrArg Prod.fst h)
    have h2 := congrArg Prod.snd h
    have hPP : (P (K A))ᶜ = (P (K A'))ᶜ := by rw [hKK]
    set τ := ((P (K A))ᶜ).orderEmbOfFin (hPc A) with hτ
    have hτ' : ∀ a, ((P (K A'))ᶜ).orderEmbOfFin (hPc A') a = τ a := fun a =>
      (hemb _ _ (hPc A) (hPc A') hPP a).symm
    have hent : ∀ p : TPairs ρ, A.1 (τ p.1.1) (τ p.1.2) = A'.1 (τ p.1.1) (τ p.1.2) := by
      intro p
      have h3 := congrFun h2 p
      simp only [code] at h3
      rw [hτ', hτ'] at h3
      exact h3
    have hagree : ∀ p ∉ P (K A), ∀ q ∉ P (K A), A.1 p q = A'.1 p q := by
      intro p hp q hq
      obtain ⟨a, rfl⟩ : p ∈ Set.range τ := by
        rw [hτ, Finset.range_orderEmbOfFin]
        exact Finset.mem_compl.2 hp
      obtain ⟨b, rfl⟩ : q ∈ Set.range τ := by
        rw [hτ, Finset.range_orderEmbOfFin]
        exact Finset.mem_compl.2 hq
      rcases lt_trichotomy a b with hab | hab | hab
      · exact hent ⟨(a, b), hab⟩
      · rw [hab, A.2.1.1, A'.2.1.1]
      · rw [A.2.1.2 (τ b) (τ a), A'.2.1.2 (τ b) (τ a)]
        congr 1
        exact hent ⟨(b, a), hab⟩
    apply Subtype.ext
    ext i j
    have hdec : ∀ i : Fin R, ∃ k ∈ K A, ∀ l ∈ P (K A), (Pi.single i (1 : F) - k) l = 0 := by
      intro i
      obtain ⟨k, hk, hkP⟩ := hPsurj (K A) (fun l => (Pi.single i (1 : F) : Fin R → F) l)
      refine ⟨k, hk, fun l hl => ?_⟩
      show (Pi.single i (1 : F) : Fin R → F) l - k l = 0
      rw [hkP ⟨l, hl⟩]
      exact sub_self _
    obtain ⟨ki, hki, hci⟩ := hdec i
    obtain ⟨kj, hkj, hcj⟩ := hdec j
    have hki' : ki ∈ K A' := hKK ▸ hki
    have hkj' : kj ∈ K A' := hKK ▸ hkj
    have expand : ∀ B : Matrix (Fin R) (Fin R) F, IsAltMat B → ki ∈ rad B → kj ∈ rad B →
        B i j = bfL (Pi.single i 1 - ki) (Pi.single j 1 - kj) B := by
      intro B hB hri hrj
      have e1 : bfL (Pi.single i 1 - ki) (Pi.single j 1 - kj) B =
          bfL (Pi.single i 1) (Pi.single j 1) B - bfL (Pi.single i 1) kj B -
            (bfL ki (Pi.single j 1) B - bfL ki kj B) := by
        simp only [bfL_apply, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
        ring
      rw [e1, bfL_single, bfL_rad_right hB hrj, bfL_rad_left hri, bfL_rad_left hri]
      ring
    rw [expand A.1 A.2.1 (hKrad A hki) (hKrad A hkj),
      expand A'.1 A'.2.1 (hKrad A' hki') (hKrad A' hkj')]
    exact bfL_eq_of_agree (P (K A)) hagree hci hcj
  rw [← Nat.card_coe_set_eq]
  have hG := ncard_grass_le_pivot (F := F) (n := R) (R - ρ)
  have hRR : R - (R - ρ) = ρ := by omega
  rw [hRR] at hG
  calc Nat.card {A : Matrix (Fin R) (Fin R) F | IsAltMat A ∧ R - ρ ≤ finrank F (rad A)}
      = Nat.card {A : Matrix (Fin R) (Fin R) F // IsAltMat A ∧ R - ρ ≤ finrank F (rad A)} := rfl
    _ ≤ Nat.card ({U : Submodule F (Fin R → F) // finrank F U = R - ρ} × (TPairs ρ → F)) :=
        Nat.card_le_card_of_injective code hinjc
    _ = {U : Submodule F (Fin R → F) | finrank F U = R - ρ}.ncard * Nat.card F ^ ρ.choose 2 := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := TPairs ρ), card_TPairs]
        try rfl
    _ ≤ 2 ^ R * Nat.card F ^ ((R - ρ) * ρ) * Nat.card F ^ ρ.choose 2 :=
        Nat.mul_le_mul_right _ hG
    _ = 2 ^ R * Nat.card F ^ ((R - ρ) * ρ + ρ.choose 2) := by
        rw [pow_add, mul_assoc]

end Lemma27ii

section Lemma81

variable {F : Type*} [Field F] {R : ℕ}

/-- Every subspace of the radical is totally isotropic. -/
theorem isotropic_of_le_rad {A : Matrix (Fin R) (Fin R) F} {U : Submodule F (Fin R → F)}
    (hU : U ≤ rad A) : Isotropic A U := by
  intro x hx y _
  have h := LinearMap.congr_fun (LinearMap.mem_ker.1 (hU hx)) y
  rw [Matrix.toBilin'_apply', LinearMap.zero_apply] at h
  exact h

/-- `Z_h(cA) = Z_h(A)` for `c ≠ 0`. -/
theorem isoLocus_smul (A : Matrix (Fin R) (Fin R) F) {c : F} (hc : c ≠ 0) (h : ℕ) :
    isoLocus (c • A) h = isoLocus A h := by
  ext H
  simp only [isoLocus, Set.mem_setOf_eq]
  apply and_congr_right
  intro _
  unfold Isotropic
  simp only [map_smul, smul_eq_mul, mul_eq_zero, hc, false_or]

/-- `I_h(A) ≤ |Gr(h, X)|`. -/
theorem isoCount_le_grass [Finite F] (A : Matrix (Fin R) (Fin R) F) (h : ℕ) :
    isoCount A h ≤ {H : Submodule F (Fin R → F) | finrank F H = h}.ncard :=
  Set.ncard_le_ncard (fun _ hH => hH.1) (grass_finite R h)

/-- `I_h(0) = |Gr(h, X)|`. -/
theorem isoLocus_zero (h : ℕ) :
    isoLocus (0 : Matrix (Fin R) (Fin R) F) h = {H : Submodule F (Fin R → F) | finrank F H = h} := by
  ext H
  simp only [isoLocus, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro _ x _ y _
  exact map_zero _

/-- Dimension bound behind Lemma 8.1: a totally isotropic `H` satisfies
`2 dim H ≤ dim X + dim rad A`. With `rank A = 2a` (`dim rad A = R - 2a`) this says
`h ≤ R - a`, i.e. `Z_h(A) = ∅` for `h > r_0 + a`. -/
theorem two_mul_finrank_le_of_isotropic {A : Matrix (Fin R) (Fin R) F}
    {H : Submodule F (Fin R → F)} (hiso : Isotropic A H) :
    2 * finrank F H ≤ R + finrank F (rad A) := by
  have key : finrank F H + finrank F ((Matrix.toBilin' A).orthogonal H) =
      R + finrank F (H ⊓ LinearMap.ker (Matrix.toBilin' A) : Submodule F (Fin R → F)) := by
    have := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Matrix.toBilin' A) H
    rwa [Module.finrank_fin_fun] at this
  have h1 : H ≤ (Matrix.toBilin' A).orthogonal H := by
    intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [Matrix.toBilin'_apply']
    exact hiso n hn m hm
  have h2 := Submodule.finrank_mono h1
  have h3 : finrank F (H ⊓ LinearMap.ker (Matrix.toBilin' A) : Submodule F (Fin R → F)) ≤
      finrank F (rad A) := Submodule.finrank_mono inf_le_right
  omega

theorem isoLocus_eq_empty {A : Matrix (Fin R) (Fin R) F} {h : ℕ}
    (hh : R + finrank F (rad A) < 2 * h) : isoLocus A h = ∅ := by
  ext H
  simp only [isoLocus, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hH hiso
  have := two_mul_finrank_le_of_isotropic hiso
  omega

end Lemma81

#print axioms prop72_iii
#print axioms ncard_grass_le_pivot
#print axioms ncard_alt_rank_le
#print axioms N2_support
#print axioms two_mul_finrank_le_of_isotropic

end OMA.SimsLite.Alt2
