import H2Dev.Alt2

/-! # N2B: Li-Qiao Sec. 10, minimally hollowing subspaces (start of the chain for Prop 10.4)

Li-Qiao (arXiv:2610.14509v3), Part II, Sec. 10 (pp. 53-66), pure linear algebra.  The target field
is `F_2 = ZMod 2`; the links proved here hold over an arbitrary field `F` (Remark 10.6), with
`X = Fin R → F`, alternating forms `R × R` matrices (`IsAltMat`), `A(x, y) = bfL x y A` and the
definitions `Isotropic`, `IsHollowing`, `IsMinHollowing`, `rad`, `valL` of `H2Dev.Alt2`.

* `minHollowSet R M h` : `𝔄^min_M`, the `M`-dimensional minimally `h`-hollowing subspaces of
  `Alt(F_2^R)`; `aStar R h = min {⌊κ h^2 / 2⌋, ⌊R / 2⌋}` with `κ = 4/5`.
* `N2BStmt` : Prop 10.4 (hypothesis N2B of the plan), stated exactly, with the absolute constants
  `h0` and the `O(hR + h^4)` constant existentially quantified.  Not proved here.
* `Prop103Stmt` : Prop 10.3 (rank bound for unique hollowing forms), stated with its `O(h)`
  constant existentially quantified.  Not proved here.
* `isoSub H = {A : A|_{H×H} = 0}`, `hollowKer B H = B_H = B ⊓ isoSub H`.
* `prop102` (Prop 10.2): for minimally `h`-hollowing `B`, the `B_H` with `dim B_H = 1` span `B`.
* `perpA A H = H^{⊥_A}`; `mem_rad_iff`, `rank_add_finrank_rad` (`rank A + dim rad A = R`).
* `prop105` (Prop 10.5): for `H = H1 ⊕ (H ∩ rad A)` and `H^{⊥_A} = rad A ⊕ H1 ⊕ X0`:
  `codim H^{⊥_A} = d`, `A|_{X0×X0}` is nondegenerate, `X0 ∩ H = 0`, and (108)
  `rank A = 2d + dim X0 ≤ 2 dim H + dim X0`.  `exists_prop105_data`: such `H1`, `X0` exist when
  `A|_{H×H} = 0`.
* `V0 i0 = {c : c_{i0} = 0}`, `rowFam β z x y` (the evaluation rows `r(z_i, z_j)` (`i < j`),
  `r(z_i, x)`, `r(z_i, y)`), `hBasis z x y` (the ordered basis `z_1, ..., z_{h-2}, x, y`).
* `lemma107` (Lemma 10.7): if `B = span β` (a basis `β` with `β i0 = A`), `dim B = C(h, 2)` and
  `B_H = span {A}`, then `H` has an ordered basis `z, x, y` whose `C(h,2) - 1` rows form a basis
  of `V0`.  (Minimality of `B` is not needed for this lemma.)
* `lemma108` (Lemma 10.8): the perturbed spaces `H_{u,v} = K + ⟨x + u⟩ + ⟨y + v⟩` are
  `h`-dimensional, their first `M - 1` rows lie in `V0`, and the last has first coordinate
  `b(u, v) = A(u, v)`.
* `lemma109` (Lemma 10.9): the coefficient maps `w_j`, `P`, `Q` (linear in `u ∈ X0`) with unique
  expansion `r(z_j, u) = w_j(u) + Σ_i P(u)_{ij} r(z_i, x) + Σ_i Q(u)_{ij} r(z_i, y)`.
-/

namespace OMA.SimsLite.N2B

open Module Matrix OMA.SimsLite.Alt2

/-! ### Statements (Prop 10.3, Prop 10.4) -/

section Stmt

/-- `𝔄^min_M`: the `M`-dimensional minimally `h`-hollowing subspaces of `Alt(F_2^R)`. -/
def minHollowSet (R M h : ℕ) : Set (Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2))) :=
  {B | B ≤ altSub (ZMod 2) R ∧ finrank (ZMod 2) B = M ∧ IsMinHollowing B h}

/-- `a_* = min {⌊κ h^2 / 2⌋, ⌊R / 2⌋}` with `κ = 4/5`, i.e. `min {⌊2 h^2 / 5⌋, ⌊R / 2⌋}`. -/
def aStar (R h : ℕ) : ℕ := min (2 * h ^ 2 / 5) (R / 2)

lemma two_mul_aStar_le (R h : ℕ) : 2 * aStar R h ≤ R := by
  unfold aStar
  have := min_le_right (2 * h ^ 2 / 5) (R / 2)
  omega

/-- Prop 10.4 (minimal endpoint spaces), the hypothesis N2B: there are absolute constants `h0`
and `C` such that for `h0 ≤ h < R`, `M = C(h, 2)`,
`log_2 |𝔄^min_M| ≤ (M - h) C(R, 2) + h a_* (2R - 2a_* - 1) + C (hR + h^4)` (107). -/
def N2BStmt : Prop :=
  ∃ h0 : ℕ, ∃ C : ℝ, ∀ R h : ℕ, h0 ≤ h → h < R →
    Real.logb 2 ((minHollowSet R (h.choose 2) h).ncard : ℝ) ≤
      ((h.choose 2 : ℝ) - h) * (R.choose 2 : ℝ) +
        (h : ℝ) * (aStar R h : ℝ) * (2 * (R : ℝ) - 2 * (aStar R h : ℝ) - 1) +
        C * ((h : ℝ) * R + (h : ℝ) ^ 4)

end Stmt

section Defs

variable {F : Type*} [Field F] {R M : ℕ}

/-- `{A : A|_{H×H} = 0}` as a subspace of matrices. -/
def isoSub (H : Submodule F (Fin R → F)) : Submodule F (Matrix (Fin R) (Fin R) F) where
  carrier := {A | Isotropic A H}
  add_mem' := by
    intro A B hA hB
    have hA' : Isotropic A H := hA
    have hB' : Isotropic B H := hB
    show Isotropic (A + B) H
    intro x hx y hy
    rw [map_add, hA' x hx y hy, hB' x hx y hy, add_zero]
  zero_mem' := by
    show Isotropic 0 H
    intro x _ y _
    exact map_zero _
  smul_mem' := by
    intro c A hA
    have hA' : Isotropic A H := hA
    show Isotropic (c • A) H
    intro x hx y hy
    rw [map_smul, hA' x hx y hy, smul_zero]

lemma mem_isoSub {H : Submodule F (Fin R → F)} {A : Matrix (Fin R) (Fin R) F} :
    A ∈ isoSub H ↔ Isotropic A H := Iff.rfl

/-- `B_H = {A ∈ B : A|_{H×H} = 0}`. -/
def hollowKer (B : Submodule F (Matrix (Fin R) (Fin R) F)) (H : Submodule F (Fin R → F)) :
    Submodule F (Matrix (Fin R) (Fin R) F) :=
  B ⊓ isoSub H

lemma mem_hollowKer {B : Submodule F (Matrix (Fin R) (Fin R) F)} {H : Submodule F (Fin R → F)}
    {A : Matrix (Fin R) (Fin R) F} : A ∈ hollowKer B H ↔ A ∈ B ∧ Isotropic A H := Iff.rfl

/-- `H^{⊥_A} = {x : A(h, x) = 0 for all h ∈ H}` (for alternating `A` either side may be used). -/
def perpA (A : Matrix (Fin R) (Fin R) F) (H : Submodule F (Fin R → F)) :
    Submodule F (Fin R → F) :=
  (Matrix.toBilin' A).orthogonal H

lemma mem_perpA {A : Matrix (Fin R) (Fin R) F} {H : Submodule F (Fin R → F)} {u : Fin R → F} :
    u ∈ perpA A H ↔ ∀ n ∈ H, bfL n u A = 0 := by
  rw [perpA, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [Matrix.toBilin'_apply', bfL_apply]

lemma mem_rad_iff {A : Matrix (Fin R) (Fin R) F} {x : Fin R → F} :
    x ∈ rad A ↔ ∀ y, bfL x y A = 0 := by
  rw [rad, LinearMap.mem_ker]
  constructor
  · intro h y
    have := LinearMap.congr_fun h y
    rw [Matrix.toBilin'_apply', LinearMap.zero_apply] at this
    exact this
  · intro h
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toBilin'_apply', LinearMap.zero_apply]
    exact h y

lemma bfL_add_left (A : Matrix (Fin R) (Fin R) F) (x x' y : Fin R → F) :
    bfL (x + x') y A = bfL x y A + bfL x' y A := by
  simp only [bfL_apply, add_dotProduct]

lemma bfL_add_right (A : Matrix (Fin R) (Fin R) F) (x y y' : Fin R → F) :
    bfL x (y + y') A = bfL x y A + bfL x y' A := by
  simp only [bfL_apply, Matrix.mulVec_add, dotProduct_add]

lemma bfL_eq_transpose (A : Matrix (Fin R) (Fin R) F) (x y : Fin R → F) :
    bfL x y A = (Aᵀ *ᵥ x) ⬝ᵥ y := by
  rw [bfL_apply, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

lemma rad_eq_ker (A : Matrix (Fin R) (Fin R) F) : rad A = LinearMap.ker Aᵀ.mulVecLin := by
  ext x
  rw [mem_rad_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  simp only [bfL_eq_transpose]
  exact dotProduct_eq_zero_iff

/-- `rank A = R - dim rad A`. -/
theorem rank_add_finrank_rad (A : Matrix (Fin R) (Fin R) F) : A.rank + finrank F (rad A) = R := by
  rw [← Matrix.rank_transpose A, rad_eq_ker]
  have := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at this
  exact this

end Defs

section Stmt103

/-- Prop 10.3 (rank bound for unique hollowing forms), with the `O(h)` constant existentially
quantified: if `B ≤ Alt(F_2^R)` is minimally `h`-hollowing with `dim B = C(h, 2)` and
`B_H = span {A}` for some `H ∈ Gr(h, X)` and nonzero `A`, then
`rank A ≤ ((10 - √10) / 9) h^2 + C h`.  Not proved here. -/
def Prop103Stmt : Prop :=
  ∃ C : ℝ, ∀ (R h : ℕ) (B : Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2)))
    (H : Submodule (ZMod 2) (Fin R → ZMod 2)) (A : Matrix (Fin R) (Fin R) (ZMod 2)),
    B ≤ altSub (ZMod 2) R → finrank (ZMod 2) B = h.choose 2 → IsMinHollowing B h →
    finrank (ZMod 2) H = h → A ≠ 0 →
    hollowKer B H = Submodule.span (ZMod 2) {A} →
    (A.rank : ℝ) ≤ (10 - Real.sqrt 10) / 9 * (h : ℝ) ^ 2 + C * h

end Stmt103

/-! ### Prop 10.2 -/

section Prop102

variable {F : Type*} [Field F] {R : ℕ}

/-- Prop 10.2 (unique hollowing forms span): if `B` is minimally `h`-hollowing, the spaces `B_H`
(`H ∈ Gr(h, X)`) with `dim B_H = 1` span `B`. -/
theorem prop102 {B : Submodule F (Matrix (Fin R) (Fin R) F)} {h : ℕ} (hB : IsMinHollowing B h) :
    (⨆ (H : Submodule F (Fin R → F)) (_ : finrank F H = h ∧ finrank F (hollowKer B H) = 1),
      hollowKer B H) = B := by
  have hle : (⨆ (H : Submodule F (Fin R → F)) (_ : finrank F H = h ∧
      finrank F (hollowKer B H) = 1), hollowKer B H) ≤ B :=
    iSup₂_le fun H _ => inf_le_left
  by_contra hne
  have hlt := lt_of_le_of_ne hle hne
  obtain ⟨A0, hA0B, hA0⟩ := SetLike.exists_of_lt hlt
  obtain ⟨f, hfA0, hf⟩ := Submodule.exists_le_ker_of_notMem hA0
  apply hB.2 (B ⊓ LinearMap.ker f)
  · refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have h1 : A0 ∈ B ⊓ LinearMap.ker f := by rw [heq]; exact hA0B
    exact hfA0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h1).2)
  · intro H hH
    obtain ⟨A1, hA1B, hA10, hA1iso⟩ := hB.1 H hH
    by_cases hf1 : f A1 = 0
    · exact ⟨A1, Submodule.mem_inf.2 ⟨hA1B, LinearMap.mem_ker.2 hf1⟩, hA10, hA1iso⟩
    · have hA1K : A1 ∈ hollowKer B H := mem_hollowKer.2 ⟨hA1B, hA1iso⟩
      have hne1 : finrank F (hollowKer B H) ≠ 1 := by
        intro h1
        have hsub : hollowKer B H ≤ ⨆ (H : Submodule F (Fin R → F)) (_ : finrank F H = h ∧
            finrank F (hollowKer B H) = 1), hollowKer B H :=
          le_iSup₂_of_le H ⟨hH, h1⟩ le_rfl
        exact hf1 (LinearMap.mem_ker.1 (hf (hsub hA1K)))
      have hspan : Submodule.span F {A1} ≠ hollowKer B H := by
        intro heq
        apply hne1
        rw [← heq, finrank_span_singleton hA10]
      have hsl : Submodule.span F {A1} < hollowKer B H :=
        lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hA1K) hspan
      obtain ⟨A2, hA2K, hA2⟩ := SetLike.exists_of_lt hsl
      obtain ⟨hA2B, hA2iso⟩ := mem_hollowKer.1 hA2K
      refine ⟨A2 - (f A2 / f A1) • A1, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
      · exact B.sub_mem hA2B (B.smul_mem _ hA1B)
      · rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hf1, sub_self]
      · intro h0
        apply hA2
        rw [sub_eq_zero] at h0
        rw [h0]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self A1)
      · exact mem_isoSub.1 ((isoSub H).sub_mem (mem_isoSub.2 hA2iso)
          ((isoSub H).smul_mem _ (mem_isoSub.2 hA1iso)))

end Prop102

/-! ### Prop 10.5 -/

section Prop105

variable {F : Type*} [Field F] {R : ℕ}

/-- Prop 10.5 (block structure of a hollowing form).  Let `A` be alternating, `J = H ∩ rad A`,
`H = H1 ⊕ J`, `d = dim H - dim J` and `H^{⊥_A} = rad A ⊕ H1 ⊕ X0`.  Then `codim H^{⊥_A} = d`, the
restriction of `A` to `X0` is nondegenerate, `X0 ∩ H = 0`, and (108)
`rank A = 2d + dim X0 ≤ 2 dim H + dim X0`. -/
theorem prop105 {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A)
    {H H1 X0 : Submodule F (Fin R → F)}
    (hH1H : H1 ≤ H) (hH1J : H1 ⊓ (H ⊓ rad A) = ⊥) (hH1J' : H1 ⊔ (H ⊓ rad A) = H)
    (hX0c : (rad A ⊔ H1) ⊓ X0 = ⊥) (hX0s : rad A ⊔ H1 ⊔ X0 = perpA A H) :
    finrank F (perpA A H) + (finrank F H - finrank F (H ⊓ rad A)) = R ∧
    (∀ u ∈ X0, (∀ v ∈ X0, bfL u v A = 0) → u = 0) ∧
    X0 ⊓ H = ⊥ ∧
    A.rank = 2 * (finrank F H - finrank F (H ⊓ rad A)) + finrank F X0 ∧
    A.rank ≤ 2 * finrank F H + finrank F X0 := by
  have hJH : finrank F ↥(H ⊓ rad A) ≤ finrank F H := Submodule.finrank_mono inf_le_left
  have ha : finrank F H + finrank F (perpA A H) = R + finrank F ↥(H ⊓ rad A) := by
    have := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Matrix.toBilin' A) H
    rw [Module.finrank_fin_fun] at this
    exact this
  have hradP : rad A ≤ perpA A H := by
    rw [← hX0s]
    exact le_sup_left.trans le_sup_left
  have hradH1 : rad A ⊓ H1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx' : x ∈ H1 ⊓ (H ⊓ rad A) :=
      Submodule.mem_inf.2 ⟨hx2, Submodule.mem_inf.2 ⟨hH1H hx2, hx1⟩⟩
    rw [hH1J] at hx'
    exact hx'
  have hd1 := Submodule.finrank_sup_add_finrank_inf_eq (rad A) H1
  rw [hradH1, finrank_bot] at hd1
  have hd2 := Submodule.finrank_sup_add_finrank_inf_eq (rad A ⊔ H1) X0
  rw [hX0c, finrank_bot, hX0s] at hd2
  have hd3 := Submodule.finrank_sup_add_finrank_inf_eq H1 (H ⊓ rad A)
  rw [hH1J, hH1J', finrank_bot] at hd3
  have hr := rank_add_finrank_rad A
  have hHle : H ≤ rad A ⊔ H1 := by
    rw [← hH1J']
    exact sup_le le_sup_right (inf_le_right.trans le_sup_left)
  refine ⟨by omega, ?_, ?_, by omega, by omega⟩
  · intro u hu hperp
    have huP : u ∈ perpA A H := by
      rw [← hX0s]
      exact Submodule.mem_sup_right hu
    -- `u` is orthogonal to all of `H^{⊥_A}`
    have huO : u ∈ (Matrix.toBilin' A).orthogonal (perpA A H) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [Matrix.toBilin'_apply']
      show bfL n u A = 0
      rw [← hX0s] at hn
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hn
      obtain ⟨r, hr, h1, hh1, rfl⟩ := Submodule.mem_sup.1 hy
      rw [bfL_add_left, bfL_add_left, bfL_rad_left hr, mem_perpA.1 huP h1 (hH1H hh1),
        bfL_swap hA w u, hperp w hw]
      simp
    -- `(H^{⊥_A})^{⊥_A} = rad A + H`
    have hle1 : rad A ⊔ H ≤ (Matrix.toBilin' A).orthogonal (perpA A H) := by
      refine sup_le (fun r hr => ?_) (fun x hx => ?_)
      · rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n _
        rw [Matrix.toBilin'_apply']
        exact bfL_rad_right hA hr n
      · rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        rw [Matrix.toBilin'_apply']
        show bfL n x A = 0
        rw [bfL_swap hA, mem_perpA.1 hn x hx, neg_zero]
    have hO := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Matrix.toBilin' A)
      (perpA A H)
    rw [Module.finrank_fin_fun] at hO
    have hPr : perpA A H ⊓ LinearMap.ker (Matrix.toBilin' A) = rad A := inf_eq_right.2 hradP
    rw [hPr] at hO
    have hd4 := Submodule.finrank_sup_add_finrank_inf_eq (rad A) H
    rw [inf_comm] at hd4
    have heq : rad A ⊔ H = (Matrix.toBilin' A).orthogonal (perpA A H) :=
      Submodule.eq_of_le_of_finrank_le hle1 (by omega)
    have hu1 : u ∈ rad A ⊔ H1 := by
      rw [← heq] at huO
      exact (sup_le le_sup_left hHle) huO
    have hu2 : u ∈ (rad A ⊔ H1) ⊓ X0 := Submodule.mem_inf.2 ⟨hu1, hu⟩
    rw [hX0c] at hu2
    exact (Submodule.mem_bot F).1 hu2
  · have hsub : X0 ⊓ H ≤ (rad A ⊔ H1) ⊓ X0 := fun x hx =>
      Submodule.mem_inf.2 ⟨hHle (Submodule.mem_inf.1 hx).2, (Submodule.mem_inf.1 hx).1⟩
    rw [hX0c] at hsub
    exact eq_bot_iff.2 hsub

/-- The data of Prop 10.5 exist whenever `A|_{H×H} = 0` (`A ∈ B_H`). -/
theorem exists_prop105_data {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A)
    {H : Submodule F (Fin R → F)} (hiso : Isotropic A H) :
    ∃ H1 X0 : Submodule F (Fin R → F), H1 ≤ H ∧ H1 ⊓ (H ⊓ rad A) = ⊥ ∧
      H1 ⊔ (H ⊓ rad A) = H ∧ X0 ≤ perpA A H ∧ (rad A ⊔ H1) ⊓ X0 = ⊥ ∧
      rad A ⊔ H1 ⊔ X0 = perpA A H := by
  obtain ⟨K1, hK1⟩ := Submodule.exists_isCompl (H ⊓ rad A)
  have hH1H : K1 ⊓ H ≤ H := inf_le_right
  have hH1J : K1 ⊓ H ⊓ (H ⊓ rad A) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (H ⊓ rad A) ⊓ K1 :=
      Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hx).2,
        (Submodule.mem_inf.1 (Submodule.mem_inf.1 hx).1).1⟩
    rw [hK1.inf_eq_bot] at hx'
    exact hx'
  have hH1J' : K1 ⊓ H ⊔ (H ⊓ rad A) = H := by
    rw [sup_comm, ← sup_inf_assoc_of_le K1 (inf_le_left : H ⊓ rad A ≤ H), hK1.sup_eq_top,
      top_inf_eq]
  have hS : rad A ⊔ K1 ⊓ H ≤ perpA A H := by
    refine sup_le (fun r hr => ?_) (fun x hx => ?_)
    · exact mem_perpA.2 fun n _ => bfL_rad_right hA hr n
    · exact mem_perpA.2 fun n hn => hiso n hn x (Submodule.mem_inf.1 hx).2
  obtain ⟨K2, hK2⟩ := Submodule.exists_isCompl (rad A ⊔ K1 ⊓ H)
  refine ⟨K1 ⊓ H, K2 ⊓ perpA A H, hH1H, hH1J, hH1J', inf_le_right, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (rad A ⊔ K1 ⊓ H) ⊓ K2 :=
      Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hx).1,
        (Submodule.mem_inf.1 (Submodule.mem_inf.1 hx).2).1⟩
    rw [hK2.inf_eq_bot] at hx'
    exact hx'
  · rw [← sup_inf_assoc_of_le K2 hS, hK2.sup_eq_top, top_inf_eq]

end Prop105

/-! ### Evaluation rows, Lemmas 10.7-10.9 -/

section Rows

variable {F : Type*} [Field F] {R M : ℕ}

/-- `V0 = {c ∈ F^M : c_{i0} = 0}`. -/
def V0 (i0 : Fin M) : Submodule F (Fin M → F) :=
  LinearMap.ker (LinearMap.proj i0 : (Fin M → F) →ₗ[F] F)

lemma mem_V0 {i0 : Fin M} {c : Fin M → F} : c ∈ V0 i0 ↔ c i0 = 0 := by
  rw [V0, LinearMap.mem_ker, LinearMap.proj_apply]

lemma finrank_V0 (i0 : Fin M) : finrank F (V0 (F := F) i0) + 1 = M := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj i0 : (Fin M → F) →ₗ[F] F)
  have hr : LinearMap.range (LinearMap.proj i0 : (Fin M → F) →ₗ[F] F) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨Pi.single i0 a, by simp⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  have e : finrank F (V0 (F := F) i0) =
      finrank F (LinearMap.ker (LinearMap.proj i0 : (Fin M → F) →ₗ[F] F)) := rfl
  omega

/-- The evaluation rows `r(z_i, z_j)` (`i < j`), `r(z_i, x)`, `r(z_i, y)` of Lemma 10.7. -/
def rowFam (β : Fin M → Matrix (Fin R) (Fin R) F) {k : ℕ} (z : Fin k → (Fin R → F))
    (x y : Fin R → F) : TPairs k ⊕ (Fin k ⊕ Fin k) → (Fin M → F) :=
  Sum.elim (fun p => valL β (z p.1.1) (z p.1.2))
    (Sum.elim (fun i => valL β (z i) x) (fun i => valL β (z i) y))

/-- The ordered family `z_1, ..., z_k, x, y` (`k = h - 2`). -/
def hBasis {k : ℕ} (z : Fin k → (Fin R → F)) (x y : Fin R → F) : Fin k ⊕ Fin 2 → (Fin R → F) :=
  Sum.elim z ![x, y]

/-- `W = span {r(z_i, z_j) : i < j ≤ h - 2}`. -/
def Wsp (β : Fin M → Matrix (Fin R) (Fin R) F) {k : ℕ} (z : Fin k → (Fin R → F)) :
    Submodule F (Fin M → F) :=
  Submodule.span F (Set.range (fun p : TPairs k => valL β (z p.1.1) (z p.1.2)))

lemma choose_two_add_two (k : ℕ) : (k + 2).choose 2 = k.choose 2 + 2 * k + 1 := by
  have h1 : (k + 2).choose 2 = (k + 1).choose 1 + (k + 1).choose 2 := Nat.choose_succ_succ (k + 1) 1
  have h2 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
  rw [h1, h2, Nat.choose_one_right, Nat.choose_one_right]
  ring

/-- Lemma 10.7 (row basis at a unique hollowing matrix).  Let `β` be a basis of `B`
(`dim B = M = C(h, 2)`, `h = k + 2`) with `β i0 = A`, and let `B_H = span {A}` with
`dim H = h`.  Then `H` has an ordered basis `z_1, ..., z_k, x, y` such that the `M - 1` rows
`r(z_i, z_j)` (`i < j`), `r(z_i, x)`, `r(z_i, y)` form a basis of `V0 = {c : c_{i0} = 0}`. -/
theorem lemma107 {k : ℕ} (β : Fin M → Matrix (Fin R) (Fin R) F) (hA : ∀ r, IsAltMat (β r))
    (hβ : LinearIndependent F β) (hM : M = (k + 2).choose 2) (i0 : Fin M)
    (H : Submodule F (Fin R → F)) (hH : finrank F H = k + 2)
    (hBH : hollowKer (Submodule.span F (Set.range β)) H = Submodule.span F {β i0}) :
    ∃ (z : Fin k → (Fin R → F)) (x y : Fin R → F),
      LinearIndependent F (hBasis z x y) ∧ Submodule.span F (Set.range (hBasis z x y)) = H ∧
      LinearIndependent F (rowFam β z x y) ∧
      Submodule.span F (Set.range (rowFam β z x y)) = V0 i0 := by
  classical
  -- Step 1: the forms vanishing on `H` are the multiples of `β i0`
  have hcoord : ∀ c : Fin M → F, Isotropic (∑ r, c r • β r) H → ∀ r, r ≠ i0 → c r = 0 := by
    intro c hc r hr
    have hmem : ∑ r, c r • β r ∈ hollowKer (Submodule.span F (Set.range β)) H :=
      mem_hollowKer.2 ⟨Submodule.sum_mem _ (fun r _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)), hc⟩
    rw [hBH, Submodule.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    have e : ∑ r, (Pi.single i0 t : Fin M → F) r • β r = t • β i0 := by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]
    have h0 : ∑ r, (c r - (Pi.single i0 t : Fin M → F) r) • β r = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e, ht, sub_self]
    have := Fintype.linearIndependent_iff.1 hβ _ h0 r
    rw [Pi.single_eq_of_ne hr, sub_zero] at this
    exact this
  -- Step 2: a basis `y` of `H`
  obtain ⟨y, hy⟩ := grass_subset_range (F := F) R (k + 2)
    (show H ∈ {U : Submodule F (Fin R → F) | finrank F U = k + 2} from hH)
  have hy' : Submodule.span F (Set.range y) = H := hy
  have hyli : LinearIndependent F y := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    show k + 2 = finrank F ↥(Submodule.span F (Set.range y))
    rw [hy', hH]
  have hyH : ∀ j, y j ∈ H := fun j => by
    rw [← hy']
    exact Submodule.subset_span ⟨j, rfl⟩
  have hβ0mem : β i0 ∈ hollowKer (Submodule.span F (Set.range β)) H := by
    rw [hBH]
    exact Submodule.mem_span_singleton_self _
  have hβ0 : Isotropic (β i0) H := (mem_hollowKer.1 hβ0mem).2
  -- Step 3: the rows of `y` span `V0`
  let ρ : TPairs (k + 2) → (Fin M → F) := fun p => valL β (y p.1.1) (y p.1.2)
  have hS_le : Submodule.span F (Set.range ρ) ≤ V0 i0 := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact mem_V0.2 (hβ0 (y p.1.1) (hyH _) (y p.1.2) (hyH _))
  have hsup : Submodule.span F (Set.range ρ) ⊔
      Submodule.span F {(Pi.single i0 1 : Fin M → F)} = ⊤ := by
    let g : Option (TPairs (k + 2)) → (Fin M → F) := fun o => Option.elim o (Pi.single i0 1) ρ
    have hg : Submodule.span F (Set.range g) = ⊤ := by
      rw [span_range_eq_top_iff]
      intro c hc
      have hc0 : c i0 = 0 := by
        have e : ∑ j, c j * (Pi.single i0 (1 : F) : Fin M → F) j = c i0 := by
          rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
            (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_one]
        rw [← e]
        exact hc none
      have hiso : Isotropic (∑ r, c r • β r) H := by
        intro a ha b hb
        rw [bfL_sum]
        have hsub := vals_subset_span_pairs β hA y
        rw [hy'] at hsub
        have hmem : valL β a b ∈ Submodule.span F (Set.range ρ) := hsub ⟨a, ha, b, hb, rfl⟩
        let φ : (Fin M → F) →ₗ[F] F :=
          { toFun := fun v => ∑ j, c j * v j
            map_add' := fun v w => by
              simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
            map_smul' := fun t v => by
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring) }
        have hle : Submodule.span F (Set.range ρ) ≤ LinearMap.ker φ := by
          rw [Submodule.span_le]
          rintro _ ⟨p, rfl⟩
          exact LinearMap.mem_ker.2 (hc (some p))
        exact LinearMap.mem_ker.1 (hle hmem)
      funext r
      by_cases hr : r = i0
      · rw [Pi.zero_apply, hr]
        exact hc0
      · exact hcoord c hiso r hr
    apply top_unique
    rw [← hg, Submodule.span_le]
    rintro _ ⟨o, rfl⟩
    cases o with
    | none => exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    | some p => exact Submodule.mem_sup_left (Submodule.subset_span ⟨p, rfl⟩)
  have hS_eq : Submodule.span F (Set.range ρ) = V0 i0 := by
    refine le_antisymm hS_le (fun w hw => ?_)
    have hw' : w ∈ Submodule.span F (Set.range ρ) ⊔
        Submodule.span F {(Pi.single i0 1 : Fin M → F)} := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨s, hs, e, he, rfl⟩ := Submodule.mem_sup.1 hw'
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 he
    have h1 : s i0 = 0 := mem_V0.1 (hS_le hs)
    have h2 : (s + t • (Pi.single i0 1 : Fin M → F)) i0 = 0 := mem_V0.1 hw
    have ht : t = 0 := by simpa [h1] using h2
    rw [ht, zero_smul, add_zero]
    exact hs
  -- Step 4: one row is redundant
  have hfr := finrank_V0 (F := F) i0
  have hnotli : ¬ LinearIndependent F ρ := by
    rw [linearIndependent_iff_card_eq_finrank_span, card_TPairs]
    show ¬ ((k + 2).choose 2 = finrank F ↥(Submodule.span F (Set.range ρ)))
    rw [hS_eq]
    omega
  rw [linearIndependent_iff_notMem_span] at hnotli
  push_neg at hnotli
  obtain ⟨p0, hp0⟩ := hnotli
  have hS' : Submodule.span F (ρ '' (Set.univ \ {p0})) = V0 i0 := by
    rw [← hS_eq]
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    by_cases hp : p = p0
    · subst hp
      exact hp0
    · exact Submodule.subset_span ⟨p, Set.mem_diff_of_mem (Set.mem_univ _) hp, rfl⟩
  -- Step 5: reorder so that the redundant pair is the last one
  obtain ⟨⟨a, b⟩, hab⟩ := p0
  have hab' : a < b := hab
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin (k + 2)), s = Finset.univ \ {a, b} := ⟨_, rfl⟩
  have hscard : s.card = k := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({a, b} : Finset (Fin (k + 2))))
    rw [Finset.card_pair_eq_two_iff.2 (ne_of_lt hab'), Finset.card_univ, Fintype.card_fin] at h1
    rw [hs]
    omega
  obtain ⟨emb, hemb_mem, hemb_range⟩ : ∃ emb : Fin k ↪o Fin (k + 2),
      (∀ i, emb i ∈ s) ∧ Set.range emb = ↑s :=
    ⟨_, s.orderEmbOfFin_mem hscard, s.range_orderEmbOfFin hscard⟩
  have hsmem : ∀ j, j ∈ s → j ≠ a ∧ j ≠ b := by
    intro j hj
    rw [hs, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hj
    push_neg at hj
    exact ⟨hj.2.1, hj.2.2⟩
  have hembs : ∀ i, emb i ≠ a ∧ emb i ≠ b := fun i => hsmem _ (hemb_mem i)
  let ι : Fin k ⊕ Fin 2 → Fin (k + 2) := Sum.elim (fun i => emb i) ![a, b]
  have hinj : Function.Injective ι := by
    rintro (i | t) (j | t') h
    · exact congrArg Sum.inl (emb.injective h)
    · fin_cases t'
      · exact absurd h (hembs i).1
      · exact absurd h (hembs i).2
    · fin_cases t
      · exact absurd h.symm (hembs j).1
      · exact absurd h.symm (hembs j).2
    · fin_cases t <;> fin_cases t'
      · rfl
      · exact absurd h (ne_of_lt hab')
      · exact absurd h.symm (ne_of_lt hab')
      · rfl
  have hsurj : Function.Surjective ι := by
    intro j
    by_cases hja : j = a
    · exact ⟨Sum.inr 0, hja.symm⟩
    by_cases hjb : j = b
    · exact ⟨Sum.inr 1, hjb.symm⟩
    have hjs : j ∈ s := by
      rw [hs, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Finset.mem_univ _, by push_neg; exact ⟨hja, hjb⟩⟩
    have : j ∈ Set.range emb := by
      rw [hemb_range]
      exact hjs
    obtain ⟨i, hi⟩ := this
    exact ⟨Sum.inl i, hi⟩
  let z : Fin k → (Fin R → F) := fun i => y (emb i)
  have hu : hBasis z (y a) (y b) = y ∘ ι := by
    funext c
    rcases c with i | t
    · rfl
    · fin_cases t <;> rfl
  -- the rows of the new basis
  obtain ⟨T, hT⟩ : ∃ T : Submodule F (Fin M → F),
      T = Submodule.span F (Set.range (rowFam β z (y a) (y b))) := ⟨_, rfl⟩
  have hfam_le : T ≤ V0 i0 := by
    rw [hT, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    rcases q with p | i | i
    · exact mem_V0.2 (hβ0 (y (emb p.1.1)) (hyH _) (y (emb p.1.2)) (hyH _))
    · exact mem_V0.2 (hβ0 (y (emb i)) (hyH _) (y a) (hyH _))
    · exact mem_V0.2 (hβ0 (y (emb i)) (hyH _) (y b) (hyH _))
  have hmemT : ∀ q, rowFam β z (y a) (y b) q ∈ T := fun q => by
    rw [hT]
    exact Submodule.subset_span ⟨q, rfl⟩
  have hcontain : ∀ c d : Fin k ⊕ Fin 2, ¬ (c = Sum.inr 0 ∧ d = Sum.inr 1) →
      ¬ (c = Sum.inr 1 ∧ d = Sum.inr 0) → valL β (y (ι c)) (y (ι d)) ∈ T := by
    intro c d h1 h2
    rcases c with i | t <;> rcases d with j | t'
    · rcases lt_trichotomy i j with h | h | h
      · exact hmemT (Sum.inl ⟨(i, j), h⟩)
      · subst h
        rw [valL_self β hA]
        exact T.zero_mem
      · rw [valL_swap β hA]
        exact T.neg_mem (hmemT (Sum.inl ⟨(j, i), h⟩))
    · fin_cases t'
      · exact hmemT (Sum.inr (Sum.inl i))
      · exact hmemT (Sum.inr (Sum.inr i))
    · rw [valL_swap β hA]
      fin_cases t
      · exact T.neg_mem (hmemT (Sum.inr (Sum.inl j)))
      · exact T.neg_mem (hmemT (Sum.inr (Sum.inr j)))
    · fin_cases t <;> fin_cases t'
      · rw [valL_self β hA]
        exact T.zero_mem
      · exact (h1 ⟨rfl, rfl⟩).elim
      · exact (h2 ⟨rfl, rfl⟩).elim
      · rw [valL_self β hA]
        exact T.zero_mem
  have hρT : ∀ q : TPairs (k + 2), q ≠ ⟨(a, b), hab⟩ → ρ q ∈ T := by
    intro q hq
    obtain ⟨c, hc⟩ := hsurj q.1.1
    obtain ⟨d, hd⟩ := hsurj q.1.2
    have key := hcontain c d ?_ ?_
    · show valL β (y q.1.1) (y q.1.2) ∈ T
      rw [← hc, ← hd]
      exact key
    · rintro ⟨rfl, rfl⟩
      apply hq
      apply Subtype.ext
      exact Prod.ext hc.symm hd.symm
    · rintro ⟨rfl, rfl⟩
      have hq2 := q.2
      rw [← hc, ← hd] at hq2
      exact lt_asymm hab' hq2
  have hTeq : T = V0 i0 := by
    apply le_antisymm hfam_le
    rw [← hS', Submodule.span_le]
    rintro _ ⟨q, hq, rfl⟩
    exact hρT q hq.2
  refine ⟨z, y a, y b, ?_, ?_, ?_, ?_⟩
  · rw [hu]
    exact hyli.comp ι hinj
  · rw [hu, hsurj.range_comp, hy']
  · rw [linearIndependent_iff_card_eq_finrank_span]
    show _ = finrank F ↥(Submodule.span F (Set.range (rowFam β z (y a) (y b))))
    rw [← hT, hTeq, Fintype.card_sum, Fintype.card_sum, card_TPairs, Fintype.card_fin]
    have := choose_two_add_two k
    omega
  · rw [← hT, hTeq]

/-- Lemma 10.8 (perturbed `h`-spaces).  With `A = β i0` vanishing on `H = span (z, x, y)` and
`X0 ≤ H^{⊥_A}` with `X0 ∩ H = 0`: for `u, v ∈ X0` the family `z, x + u, y + v` is linearly
independent (so `dim H_{u,v} = h`), the first `M - 1` rows of `R_{B, H_{u,v}}` lie in `V0`, and the
last row has first coordinate `b(u, v) = A(u, v)`. -/
theorem lemma108 {k : ℕ} (β : Fin M → Matrix (Fin R) (Fin R) F) (i0 : Fin M)
    (hA0 : IsAltMat (β i0)) {H X0 : Submodule F (Fin R → F)} (hiso : Isotropic (β i0) H)
    {z : Fin k → (Fin R → F)} {x y : Fin R → F}
    (hli : LinearIndependent F (hBasis z x y))
    (hsp : Submodule.span F (Set.range (hBasis z x y)) = H)
    (hX0 : X0 ≤ perpA (β i0) H) (hX0H : X0 ⊓ H = ⊥) {u v : Fin R → F} (hu : u ∈ X0)
    (hv : v ∈ X0) :
    LinearIndependent F (hBasis z (x + u) (y + v)) ∧
    finrank F ↥(Submodule.span F (Set.range (hBasis z (x + u) (y + v)))) = k + 2 ∧
    (∀ q, rowFam β z (x + u) (y + v) q i0 = 0) ∧
    valL β (x + u) (y + v) i0 = bfL u v (β i0) := by
  have hmemH : ∀ c, hBasis z x y c ∈ H := fun c => by
    rw [← hsp]
    exact Submodule.subset_span ⟨c, rfl⟩
  have hzH : ∀ i, z i ∈ H := fun i => hmemH (Sum.inl i)
  have hxH : x ∈ H := hmemH (Sum.inr 0)
  have hyH : y ∈ H := hmemH (Sum.inr 1)
  have huP := mem_perpA.1 (hX0 hu)
  have hvP := mem_perpA.1 (hX0 hv)
  have hLI : LinearIndependent F (hBasis z (x + u) (y + v)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsplit : ∑ c, g c • hBasis z (x + u) (y + v) c =
        ∑ c, g c • hBasis z x y c + (g (Sum.inr 0) • u + g (Sum.inr 1) • v) := by
      simp only [hBasis, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_add]
      abel
    rw [hsplit] at hg
    have htH : ∑ c, g c • hBasis z x y c ∈ H :=
      Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (hmemH c))
    have hsX : g (Sum.inr 0) • u + g (Sum.inr 1) • v ∈ X0 :=
      X0.add_mem (X0.smul_mem _ hu) (X0.smul_mem _ hv)
    have ht : ∑ c, g c • hBasis z x y c = -(g (Sum.inr 0) • u + g (Sum.inr 1) • v) :=
      eq_neg_of_add_eq_zero_left hg
    have htX : ∑ c, g c • hBasis z x y c ∈ X0 := by
      rw [ht]
      exact X0.neg_mem hsX
    have hmem : ∑ c, g c • hBasis z x y c ∈ X0 ⊓ H := Submodule.mem_inf.2 ⟨htX, htH⟩
    rw [hX0H] at hmem
    exact Fintype.linearIndependent_iff.1 hli g ((Submodule.mem_bot F).1 hmem)
  refine ⟨hLI, ?_, ?_, ?_⟩
  · rw [finrank_span_eq_card hLI]
    simp
  · intro q
    rcases q with p | i | i
    · show bfL (z p.1.1) (z p.1.2) (β i0) = 0
      exact hiso _ (hzH _) _ (hzH _)
    · show bfL (z i) (x + u) (β i0) = 0
      rw [bfL_add_right, hiso _ (hzH i) _ hxH, huP _ (hzH i), add_zero]
    · show bfL (z i) (y + v) (β i0) = 0
      rw [bfL_add_right, hiso _ (hzH i) _ hyH, hvP _ (hzH i), add_zero]
  · show bfL (x + u) (y + v) (β i0) = bfL u v (β i0)
    rw [bfL_add_left, bfL_add_right, bfL_add_right, hiso x hxH y hyH, hvP x hxH,
      bfL_swap hA0 u y, huP y hyH]
    simp

/-- Lemma 10.9 (coefficient maps).  If the rows `rowFam β z x y` form a basis of `V0` and
`A = β i0` vanishes on `H ∋ z_j`, then for `u ∈ X0 ≤ H^{⊥_A}` there are maps `w_j : X0 → W`,
`P, Q : X0 → F^{k×k}`, all linear, with
`r(z_j, u) = w_j(u) + Σ_i P(u)_{ij} r(z_i, x) + Σ_i Q(u)_{ij} r(z_i, y)`, and this expansion is
unique. -/
theorem lemma109 {k : ℕ} (β : Fin M → Matrix (Fin R) (Fin R) F) (i0 : Fin M)
    {H X0 : Submodule F (Fin R → F)} {z : Fin k → (Fin R → F)} {x y : Fin R → F}
    (hzH : ∀ i, z i ∈ H) (hrli : LinearIndependent F (rowFam β z x y))
    (hrsp : Submodule.span F (Set.range (rowFam β z x y)) = V0 i0)
    (hX0 : X0 ≤ perpA (β i0) H) :
    ∃ (w : Fin k → (X0 →ₗ[F] (Fin M → F))) (P Q : X0 →ₗ[F] Matrix (Fin k) (Fin k) F),
      (∀ j u, w j u ∈ Wsp β z) ∧
      (∀ j (u : X0), valL β (z j) u =
        w j u + ∑ i, P u i j • valL β (z i) x + ∑ i, Q u i j • valL β (z i) y) ∧
      (∀ j (u : X0) (w' : Fin M → F) (p q : Fin k → F), w' ∈ Wsp β z →
        valL β (z j) u = w' + ∑ i, p i • valL β (z i) x + ∑ i, q i • valL β (z i) y →
        w' = w j u ∧ p = (fun i => P u i j) ∧ q = (fun i => Q u i j)) := by
  classical
  set fam := rowFam β z x y with hfam
  have hmemS : ∀ j (u : X0), valL β (z j) u ∈ Submodule.span F (Set.range fam) := by
    intro j u
    rw [hrsp, mem_V0]
    exact mem_perpA.1 (hX0 u.2) _ (hzH j)
  -- the linear maps `u ↦ r(z_j, u)` into the span of the rows, and their coordinates
  let L : Fin k → (X0 →ₗ[F] Submodule.span F (Set.range fam)) := fun j =>
    LinearMap.codRestrict _ ((valL β (z j)).comp X0.subtype) (fun u => hmemS j u)
  let C : Fin k → (X0 →ₗ[F] (TPairs k ⊕ (Fin k ⊕ Fin k) →₀ F)) := fun j =>
    (Basis.span hrli).repr.toLinearMap ∘ₗ L j
  have hexp : ∀ j (u : X0), valL β (z j) u = ∑ c, C j u c • fam c := by
    intro j u
    have h := (Basis.span hrli).sum_repr (L j u)
    have h' := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply] at h'
    exact h'.symm
  let w : Fin k → (X0 →ₗ[F] (Fin M → F)) := fun j =>
    { toFun := fun u => ∑ p : TPairs k, C j u (Sum.inl p) • fam (Sum.inl p)
      map_add' := fun u u' => by
        simp only [map_add, Finsupp.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t u => by
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply, Finset.smul_sum] }
  let P : X0 →ₗ[F] Matrix (Fin k) (Fin k) F :=
    { toFun := fun u => Matrix.of fun i j => C j u (Sum.inr (Sum.inl i))
      map_add' := fun u u' => by
        ext i j
        simp only [map_add, Finsupp.coe_add, Pi.add_apply, Matrix.of_apply, Matrix.add_apply]
      map_smul' := fun t u => by
        ext i j
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.smul_apply, RingHom.id_apply] }
  let Q : X0 →ₗ[F] Matrix (Fin k) (Fin k) F :=
    { toFun := fun u => Matrix.of fun i j => C j u (Sum.inr (Sum.inr i))
      map_add' := fun u u' => by
        ext i j
        simp only [map_add, Finsupp.coe_add, Pi.add_apply, Matrix.of_apply, Matrix.add_apply]
      map_smul' := fun t u => by
        ext i j
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.smul_apply, RingHom.id_apply] }
  have hsplit : ∀ j (u : X0), ∑ c, C j u c • fam c =
      w j u + ∑ i, P u i j • valL β (z i) x + ∑ i, Q u i j • valL β (z i) y := by
    intro j u
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
    rfl
  refine ⟨w, P, Q, ?_, ?_, ?_⟩
  · intro j u
    show (∑ p : TPairs k, C j u (Sum.inl p) • fam (Sum.inl p)) ∈ Wsp β z
    unfold Wsp
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨p, rfl⟩))
  · intro j u
    rw [hexp, hsplit]
  · intro j u w' p q hw' hrep
    unfold Wsp at hw'
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hw'
    let d : TPairs k ⊕ (Fin k ⊕ Fin k) → F := Sum.elim a (Sum.elim p q)
    have hd : ∑ c, d c • fam c = ∑ c, C j u c • fam c := by
      rw [← hexp, hrep, ← ha, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
      rfl
    have hdiff : ∑ c, (d c - C j u c) • fam c = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [hd, sub_self]
    have hcoef : ∀ c, d c = C j u c := fun c =>
      sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hrli _ hdiff c)
    refine ⟨?_, ?_, ?_⟩
    · rw [← ha]
      show _ = ∑ p : TPairs k, C j u (Sum.inl p) • fam (Sum.inl p)
      exact Finset.sum_congr rfl (fun p _ => by rw [← hcoef (Sum.inl p)]; rfl)
    · funext i
      exact hcoef (Sum.inr (Sum.inl i))
    · funext i
      exact hcoef (Sum.inr (Sum.inr i))

end Rows

end OMA.SimsLite.N2B
