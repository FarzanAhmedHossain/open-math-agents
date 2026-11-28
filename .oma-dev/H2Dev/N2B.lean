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
* `prop1010` (Prop 10.10, determinant constraint): if moreover `B` is `h`-hollowing and
  `b(u, v) = 1`, then `det [[I + P(u), P(v)], [Q(u), I + Q(v)]] = 0` (109).  Proof as in the
  paper: hollowing makes the `M` rows of `R_{B, H_{u,v}}` dependent, the last row drops out by
  its first coordinate, and the coordinates along `r(z_i, x)`, `r(z_i, y)` (via the basis `bF` of
  `F^M` extending the rows) give the block system.
* Lemma 10.11 (Reed-Muller support): `HasDeg f d` (`f : F_2^n → F_2` is a polynomial function of
  total degree `≤ d`), `suppCard f = |supp f|`; `rm_support` (`f ≠ 0 → 2^(n-d) ≤ |supp f|`, the
  minimum distance of `RM(d, n)`, by induction on `n` via `finSuccEquiv`) and `rm_span`
  (`f 0 = 1 → codim span (supp f) ≤ d`, by restricting `f` to a complement of `span (supp f)`,
  where it becomes the delta function at `0`; `totalDegree_bind₁_le_of`: linear substitutions do
  not raise the degree).
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
    finrank F (perpA A H) + (finrank F H - finrank F ↥(H ⊓ rad A)) = R ∧
    (∀ u ∈ X0, (∀ v ∈ X0, bfL u v A = 0) → u = 0) ∧
    X0 ⊓ H = ⊥ ∧
    A.rank = 2 * (finrank F H - finrank F ↥(H ⊓ rad A)) + finrank F X0 ∧
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
  push Not at hnotli
  obtain ⟨p0, hp0⟩ := hnotli
  have hS' : Submodule.span F (ρ '' (Set.univ \ {p0})) = V0 i0 := by
    rw [← hS_eq]
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    by_cases hp : p = p0
    · subst hp
      exact hp0
    · exact Submodule.subset_span ⟨p, Set.mem_sdiff_of_mem (Set.mem_univ _) hp, rfl⟩
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
    push Not at hj
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
      exact ⟨Finset.mem_univ _, by push Not; exact ⟨hja, hjb⟩⟩
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

/-! ### Prop 10.10 (determinant constraint) -/

section Prop1010

variable {F : Type*} [Field F] {R M : ℕ}

/-- Prop 10.10 (determinant constraint).  Keep the data of Lemmas 10.7-10.9 (`B = span β`
`h`-hollowing with `h = k + 2`, `A = β i0` vanishing on `H = span (z, x, y)`, the rows
`rowFam β z x y` a basis of `V0`, `X0 ≤ H^{⊥_A}` with `X0 ∩ H = 0`, and coefficient maps
`w, P, Q` as in Lemma 10.9).  If `u, v ∈ X0` satisfy `b(u, v) = A(u, v) = 1`, then
`F(u, v) = det [[I + P(u), P(v)], [Q(u), I + Q(v)]] = 0` (109). -/
theorem prop1010 {k : ℕ} (β : Fin M → Matrix (Fin R) (Fin R) F) (hA : ∀ r, IsAltMat (β r))
    (hhol : IsHollowing (Submodule.span F (Set.range β)) (k + 2)) (i0 : Fin M)
    {H X0 : Submodule F (Fin R → F)} (hiso : Isotropic (β i0) H)
    {z : Fin k → (Fin R → F)} {x y : Fin R → F}
    (hli : LinearIndependent F (hBasis z x y))
    (hsp : Submodule.span F (Set.range (hBasis z x y)) = H)
    (hrli : LinearIndependent F (rowFam β z x y))
    (hrsp : Submodule.span F (Set.range (rowFam β z x y)) = V0 i0)
    (hX0 : X0 ≤ perpA (β i0) H) (hX0H : X0 ⊓ H = ⊥)
    (w : Fin k → (X0 →ₗ[F] (Fin M → F))) (P Q : X0 →ₗ[F] Matrix (Fin k) (Fin k) F)
    (hw : ∀ j u, w j u ∈ Wsp β z)
    (hrep : ∀ j (u : X0), valL β (z j) u =
      w j u + ∑ i, P u i j • valL β (z i) x + ∑ i, Q u i j • valL β (z i) y)
    (u v : X0) (huv : bfL (u : Fin R → F) v (β i0) = 1) :
    (Matrix.fromBlocks (1 + P u) (P v) (Q u) (1 + Q v)).det = 0 := by
  classical
  obtain ⟨-, hfr', hrow0, hlast⟩ :=
    lemma108 β i0 (hA i0) hiso hli hsp hX0 hX0H u.2 v.2
  -- a nonzero form of `B` vanishing on `H_{u,v}`
  obtain ⟨A', hA'B, hA'0, hA'iso⟩ := hhol _ hfr'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hA'B
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hA'0
    rw [← hc]
    simp
  have hperp : ∀ a b, a ∈ Submodule.span F (Set.range (hBasis z (x + u) (y + v))) →
      b ∈ Submodule.span F (Set.range (hBasis z (x + u) (y + v))) →
      ∑ r, c r * valL β a b r = 0 := by
    intro a b ha hb
    have h := hA'iso a ha b hb
    rw [← hc, bfL_sum] at h
    exact h
  have hmem : ∀ e, hBasis z (x + u) (y + v) e ∈
      Submodule.span F (Set.range (hBasis z (x + u) (y + v))) :=
    fun e => Submodule.subset_span ⟨e, rfl⟩
  -- the `M` rows of `R_{B, H_{u,v}}`
  let G : Option (TPairs k ⊕ (Fin k ⊕ Fin k)) → (Fin M → F) := fun o =>
    Option.elim o (valL β (x + u) (y + v)) (rowFam β z (x + u) (y + v))
  have hGperp : ∀ o, ∑ r, c r * G o r = 0 := by
    intro o
    rcases o with _ | p | i | i
    · exact hperp _ _ (hmem (Sum.inr 0)) (hmem (Sum.inr 1))
    · exact hperp _ _ (hmem (Sum.inl p.1.1)) (hmem (Sum.inl p.1.2))
    · exact hperp _ _ (hmem (Sum.inl i)) (hmem (Sum.inr 0))
    · exact hperp _ _ (hmem (Sum.inl i)) (hmem (Sum.inr 1))
  have hcardι : Fintype.card (TPairs k ⊕ (Fin k ⊕ Fin k)) + 1 = M := by
    have h1 := finrank_span_eq_card hrli
    rw [hrsp] at h1
    have h2 := finrank_V0 (F := F) i0
    omega
  have hGnot : ¬ LinearIndependent F G := by
    intro hG
    have htop : Submodule.span F (Set.range G) = ⊤ := by
      apply Submodule.eq_of_le_of_finrank_le le_top
      rw [finrank_span_eq_card hG, finrank_top, Module.finrank_fin_fun, Fintype.card_option]
      omega
    exact hc0 ((span_range_eq_top_iff G).1 htop c hGperp)
  rw [Fintype.linearIndependent_iff] at hGnot
  push Not at hGnot
  obtain ⟨g, hg, o0, ho0⟩ := hGnot
  rw [Fintype.sum_option] at hg
  have hG0 : G none i0 = 1 := by
    show valL β (x + u) (y + v) i0 = 1
    rw [hlast, huv]
  have hnone : g none = 0 := by
    have h := congrFun hg i0
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hG0, mul_one] at h
    have hs : ∑ q, g (some q) * G (some q) i0 = 0 :=
      Finset.sum_eq_zero (fun q _ => by rw [show G (some q) i0 = 0 from hrow0 q, mul_zero])
    rw [hs, add_zero] at h
    exact h
  rw [hnone, zero_smul, zero_add] at hg
  have hg2 : ∑ q, g (some q) • rowFam β z (x + u) (y + v) q = 0 := hg
  -- `hg : ∑ q, g (some q) • rowFam β z (x + u) (y + v) q = 0`
  -- a basis of `F^M` extending the rows
  let K : Option (TPairs k ⊕ (Fin k ⊕ Fin k)) → (Fin M → F) := fun o =>
    Option.elim o (Pi.single i0 1) (rowFam β z x y)
  have hKsp : ⊤ ≤ Submodule.span F (Set.range K) := by
    intro c' _
    have h1 : c' - c' i0 • (Pi.single i0 1 : Fin M → F) ∈ V0 i0 := by
      rw [mem_V0]
      simp
    rw [← hrsp] at h1
    have h2 : Submodule.span F (Set.range (rowFam β z x y)) ≤ Submodule.span F (Set.range K) := by
      apply Submodule.span_mono
      rintro _ ⟨q, rfl⟩
      exact ⟨some q, rfl⟩
    have h3 : (Pi.single i0 1 : Fin M → F) ∈ Submodule.span F (Set.range K) :=
      Submodule.subset_span ⟨none, rfl⟩
    have := Submodule.add_mem _ (h2 h1) (Submodule.smul_mem _ (c' i0) h3)
    rwa [sub_add_cancel] at this
  have hKli : LinearIndependent F K :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hKsp
      (by rw [Fintype.card_option, Module.finrank_fin_fun]; omega)
  let bF := Basis.mk hKli hKsp
  have hκ : ∀ o q, bF.coord o (rowFam β z x y q) = if some q = o then 1 else 0 := by
    intro o q
    have e : rowFam β z x y q = bF (some q) := (Basis.mk_apply hKli hKsp (some q)).symm
    rw [e, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hκW : ∀ t : Fin k ⊕ Fin k, ∀ w' ∈ Wsp β z, bF.coord (some (Sum.inr t)) w' = 0 := by
    intro t w' hw'
    have hle : Wsp β z ≤ LinearMap.ker (bF.coord (some (Sum.inr t))) := by
      unfold Wsp
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have := hκ (some (Sum.inr t)) (Sum.inl p)
      rw [if_neg (by simp)] at this
      exact this
    exact LinearMap.mem_ker.1 (hle hw')
  have ex : ∀ l, valL β (z l) x = rowFam β z x y (Sum.inr (Sum.inl l)) := fun l => rfl
  have ey : ∀ l, valL β (z l) y = rowFam β z x y (Sum.inr (Sum.inr l)) := fun l => rfl
  -- coordinates of `r(z_i, u')`
  have hκv : ∀ i (u' : X0) j,
      bF.coord (some (Sum.inr (Sum.inl j))) (valL β (z i) u') = P u' j i ∧
      bF.coord (some (Sum.inr (Sum.inr j))) (valL β (z i) u') = Q u' j i := by
    intro i u' j
    rw [hrep i u']
    constructor
    all_goals simp only [ex, ey, map_add, map_sum, map_smul, smul_eq_mul, hκ,
      hκW (Sum.inl j) _ (hw i u'), hκW (Sum.inr j) _ (hw i u'),
      Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte, mul_zero,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_const_zero,
      zero_add, add_zero]
  -- coordinates of the perturbed rows
  have hrx : ∀ j q, bF.coord (some (Sum.inr (Sum.inl j))) (rowFam β z (x + u) (y + v) q) =
      Sum.elim (fun _ => 0) (Sum.elim (fun i => (1 + P u) j i) (fun i => P v j i)) q := by
    intro j q
    rcases q with p | i | i
    · show bF.coord _ (rowFam β z x y (Sum.inl p)) = 0
      rw [hκ, if_neg (by simp)]
    · show bF.coord _ (valL β (z i) (x + u)) = (1 + P u) j i
      rw [map_add, map_add, ex, hκ, (hκv i u j).1, Matrix.add_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    · show bF.coord _ (valL β (z i) (y + v)) = P v j i
      rw [map_add, map_add, ey, hκ, (hκv i v j).1, if_neg (by simp), zero_add]
  have hry : ∀ j q, bF.coord (some (Sum.inr (Sum.inr j))) (rowFam β z (x + u) (y + v) q) =
      Sum.elim (fun _ => 0) (Sum.elim (fun i => Q u j i) (fun i => (1 + Q v) j i)) q := by
    intro j q
    rcases q with p | i | i
    · show bF.coord _ (rowFam β z x y (Sum.inl p)) = 0
      rw [hκ, if_neg (by simp)]
    · show bF.coord _ (valL β (z i) (x + u)) = Q u j i
      rw [map_add, map_add, ex, hκ, (hκv i u j).2, if_neg (by simp), zero_add]
    · show bF.coord _ (valL β (z i) (y + v)) = (1 + Q v) j i
      rw [map_add, map_add, ey, hκ, (hκv i v j).2, Matrix.add_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
  -- the kernel vector `(β, γ)`
  let bv : Fin k → F := fun i => g (some (Sum.inr (Sum.inl i)))
  let gv : Fin k → F := fun i => g (some (Sum.inr (Sum.inr i)))
  have hx_eq : ∀ j, ((1 + P u) *ᵥ bv + P v *ᵥ gv) j = 0 := by
    intro j
    have h := congrArg (bF.coord (some (Sum.inr (Sum.inl j)))) hg2
    rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul, hrx, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      mul_zero, Finset.sum_const_zero, zero_add] at h
    show (∑ i, (1 + P u) j i * bv i) + (∑ i, P v j i * gv i) = 0
    refine Eq.trans ?_ h
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hy_eq : ∀ j, (Q u *ᵥ bv + (1 + Q v) *ᵥ gv) j = 0 := by
    intro j
    have h := congrArg (bF.coord (some (Sum.inr (Sum.inr j)))) hg2
    rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul, hry, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      mul_zero, Finset.sum_const_zero, zero_add] at h
    show (∑ i, Q u j i * bv i) + (∑ i, (1 + Q v) j i * gv i) = 0
    refine Eq.trans ?_ h
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  -- `(β, γ) ≠ 0`
  have hne : (Sum.elim bv gv : Fin k ⊕ Fin k → F) ≠ 0 := by
    intro h0
    have hbv : ∀ i, bv i = 0 := fun i => congrFun h0 (Sum.inl i)
    have hgv : ∀ i, gv i = 0 := fun i => congrFun h0 (Sum.inr i)
    -- then the relation only involves the rows `r(z_i, z_j)`
    have hrel : ∑ p : TPairs k, g (some (Sum.inl p)) • rowFam β z x y (Sum.inl p) = 0 := by
      have hg3 := hg2
      simp only [Fintype.sum_sum_type] at hg3
      have e1 : ∑ i, g (some (Sum.inr (Sum.inl i))) •
          rowFam β z (x + u) (y + v) (Sum.inr (Sum.inl i)) = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [show g (some (Sum.inr (Sum.inl i))) = 0 from hbv i,
          zero_smul])
      have e2 : ∑ i, g (some (Sum.inr (Sum.inr i))) •
          rowFam β z (x + u) (y + v) (Sum.inr (Sum.inr i)) = 0 :=
        Finset.sum_eq_zero (fun i _ => by rw [show g (some (Sum.inr (Sum.inr i))) = 0 from hgv i,
          zero_smul])
      rw [e1, e2, add_zero, add_zero] at hg3
      exact hg3
    let g' : TPairs k ⊕ (Fin k ⊕ Fin k) → F := Sum.elim (fun p => g (some (Sum.inl p))) 0
    have hg' : ∑ q, g' q • rowFam β z x y q = 0 := by
      simp only [Fintype.sum_sum_type, g', Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero]
      exact hrel
    have hall := Fintype.linearIndependent_iff.1 hrli g' hg'
    apply ho0
    rcases o0 with _ | p | i | i
    · exact hnone
    · exact hall (Sum.inl p)
    · exact hbv i
    · exact hgv i
  apply Matrix.exists_mulVec_eq_zero_iff.1
  refine ⟨Sum.elim bv gv, hne, ?_⟩
  rw [Matrix.fromBlocks_mulVec]
  funext t
  rcases t with j | j
  · exact hx_eq j
  · exact hy_eq j

end Prop1010

/-! ### Lemma 10.11 (Reed-Muller support) -/

section ReedMuller

open MvPolynomial

/-- `f : F_2^n → F_2` has (algebraic) degree at most `d`: it is the evaluation of a polynomial
of total degree at most `d`. -/
def HasDeg {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) (ZMod 2), p.totalDegree ≤ d ∧ ∀ x, eval x p = f x

/-- `|supp f|`. -/
def suppCard {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) : ℕ :=
  (Finset.univ.filter fun x => f x ≠ 0).card

/-- `(t, x') ↦ (t, x'_1, ..., x'_n)`. -/
def cons2 {n : ℕ} (t : ZMod 2) (x' : Fin n → ZMod 2) : Fin (n + 1) → ZMod 2 := Fin.cons t x'

lemma suppCard_of_const {n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2} {c : ZMod 2} (hc : c ≠ 0)
    (hf : ∀ x, f x = c) : suppCard f = 2 ^ n := by
  unfold suppCard
  rw [Finset.filter_true_of_mem (fun x _ => by rw [hf x]; exact hc), Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma suppCard_congr {n : ℕ} {f g : (Fin n → ZMod 2) → ZMod 2} (h : ∀ x, f x ≠ 0 ↔ g x ≠ 0) :
    suppCard f = suppCard g := by
  unfold suppCard
  rw [Finset.filter_congr (fun x _ => h x)]

lemma suppCard_cons_ge {n : ℕ} (f : (Fin (n + 1) → ZMod 2) → ZMod 2) :
    suppCard (fun x' => f (cons2 0 x')) + suppCard (fun x' => f (cons2 1 x')) ≤ suppCard f := by
  classical
  unfold suppCard
  let e0 : (Fin n → ZMod 2) ↪ (Fin (n + 1) → ZMod 2) :=
    ⟨cons2 0, Fin.cons_right_injective (α := fun _ => ZMod 2) 0⟩
  let e1 : (Fin n → ZMod 2) ↪ (Fin (n + 1) → ZMod 2) :=
    ⟨cons2 1, Fin.cons_right_injective (α := fun _ => ZMod 2) 1⟩
  have hdisj : Disjoint ((Finset.univ.filter fun x' => f (cons2 0 x') ≠ 0).map e0)
      ((Finset.univ.filter fun x' => f (cons2 1 x') ≠ 0).map e1) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx0
    obtain ⟨b, _, hb⟩ := Finset.mem_map.1 hx1
    have h := congrFun hb 0
    have h' : (1 : ZMod 2) = 0 := h
    exact absurd h' (by decide)
  rw [← Finset.card_map e0, ← Finset.card_map e1, ← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, ha.2⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, ha.2⟩

/-- Lemma 10.11, first assertion (minimum distance of `RM(d, n)`): a nonzero `f : F_2^n → F_2` of
degree at most `d` has `|supp f| ≥ 2^(n-d)`. -/
theorem rm_support : ∀ (n d : ℕ) (f : (Fin n → ZMod 2) → ZMod 2), HasDeg f d →
    (∃ x, f x ≠ 0) → 2 ^ (n - d) ≤ suppCard f := by
  intro n
  induction n with
  | zero =>
    intro d f _ ⟨x, hx⟩
    rw [Nat.zero_sub, pow_zero]
    unfold suppCard
    exact Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
  | succ n ih =>
    intro d f ⟨p, hpd, hpf⟩ ⟨x, hx⟩
    by_cases hd : d = 0
    · subst hd
      have h0 : p.totalDegree = 0 := Nat.le_zero.1 hpd
      have hC := totalDegree_eq_zero_iff_eq_C.1 h0
      have hconst : ∀ y, f y = p.coeff 0 := fun y => by
        have := congrArg (eval y) hC
        rw [eval_C] at this
        rw [← hpf y]
        exact this
      exact le_of_eq (by rw [suppCard_of_const (c := p.coeff 0) (by rw [← hconst x]; exact hx)
        hconst, Nat.sub_zero])
    · set q := finSuccEquiv (ZMod 2) n p with hq
      have heval : ∀ t x', f (cons2 t x') =
          ∑ i ∈ Finset.range (q.natDegree + 1), eval x' (q.coeff i) * t ^ i := by
        intro t x'
        rw [← hpf, cons2, eval_eq_eval_mv_eval', ← hq,
          Polynomial.eval_eq_sum_range' (n := q.natDegree + 1)
            (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _))]
        simp only [Polynomial.coeff_map]
      have hcd : ∀ i, (q.coeff i).totalDegree ≤ d - i := fun i => by
        by_cases h : q.coeff i = 0
        · rw [h, totalDegree_zero]
          exact Nat.zero_le _
        · have := totalDegree_coeff_finSuccEquiv_add_le p i h
          rw [← hq] at this
          omega
      have hf0 : ∀ x', f (cons2 0 x') = eval x' (q.coeff 0) := by
        intro x'
        rw [heval, Finset.sum_range_succ']
        simp
      have hf1 : ∀ x', f (cons2 1 x') = eval x' (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) := by
        intro x'
        rw [heval, map_sum]
        simp only [one_pow, mul_one]
      have hfd : ∀ x', f (cons2 1 x') - f (cons2 0 x') =
          eval x' (∑ i ∈ Finset.range q.natDegree, q.coeff (i + 1)) := by
        intro x'
        rw [hf1, hf0, Finset.sum_range_succ', map_add, add_sub_cancel_right]
      have hD0 : HasDeg (fun x' => f (cons2 0 x')) d :=
        ⟨q.coeff 0, (hcd 0).trans (Nat.sub_le _ _), fun x' => (hf0 x').symm⟩
      have hD1 : HasDeg (fun x' => f (cons2 1 x')) d :=
        ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i,
          totalDegree_finsetSum_le (fun i _ => (hcd i).trans (Nat.sub_le _ _)),
          fun x' => (hf1 x').symm⟩
      have hDd : HasDeg (fun x' => f (cons2 1 x') - f (cons2 0 x')) (d - 1) :=
        ⟨∑ i ∈ Finset.range q.natDegree, q.coeff (i + 1),
          totalDegree_finsetSum_le (fun i _ => (hcd (i + 1)).trans (by omega)),
          fun x' => (hfd x').symm⟩
      have hsplit := suppCard_cons_ge f
      have hx' : f (cons2 (x 0) (Fin.tail x)) ≠ 0 := by
        rw [cons2, Fin.cons_self_tail]
        exact hx
      by_cases h0 : ∃ y, f (cons2 0 y) ≠ 0 <;> by_cases h1 : ∃ y, f (cons2 1 y) ≠ 0
      · have a0 := ih d _ hD0 h0
        have a1 := ih d _ hD1 h1
        have : 2 ^ (n + 1 - d) ≤ 2 ^ (n - d) * 2 := by
          rw [← pow_succ]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · push Not at h1
        obtain ⟨y, hy⟩ := h0
        have hne : ∃ y, f (cons2 1 y) - f (cons2 0 y) ≠ 0 :=
          ⟨y, by rw [h1 y, zero_sub, neg_ne_zero]; exact hy⟩
        have a := ih (d - 1) _ hDd hne
        have heq : suppCard (fun x' => f (cons2 1 x') - f (cons2 0 x')) =
            suppCard (fun x' => f (cons2 0 x')) :=
          suppCard_congr (fun z => by simp only [h1 z, zero_sub, neg_ne_zero])
        have : 2 ^ (n + 1 - d) ≤ 2 ^ (n - (d - 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · push Not at h0
        obtain ⟨y, hy⟩ := h1
        have hne : ∃ y, f (cons2 1 y) - f (cons2 0 y) ≠ 0 :=
          ⟨y, by rw [h0 y, sub_zero]; exact hy⟩
        have a := ih (d - 1) _ hDd hne
        have heq : suppCard (fun x' => f (cons2 1 x') - f (cons2 0 x')) =
            suppCard (fun x' => f (cons2 1 x')) :=
          suppCard_congr (fun z => by simp only [h0 z, sub_zero])
        have : 2 ^ (n + 1 - d) ≤ 2 ^ (n - (d - 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · push Not at h0 h1
        exfalso
        apply hx'
        have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
        rcases h01 (x 0) with ht | ht
        · rw [ht]
          exact h0 _
        · rw [ht]
          exact h1 _

/-- Substituting linear forms does not raise the total degree. -/
theorem totalDegree_bind₁_le_of {σ τ : Type*} {S : Type*} [CommSemiring S]
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ S) :
    (bind₁ g p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum]
  apply Finset.sum_le_sum
  intro i _
  calc (g i ^ m i).totalDegree ≤ m i * (g i).totalDegree := totalDegree_pow _ _
    _ ≤ m i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = m i := mul_one _

/-- Lemma 10.11, second assertion: if `f` has degree at most `d` and `f 0 = 1`, then
`codim span (supp f) ≤ d`. -/
theorem rm_span (n d : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) (hf : HasDeg f d) (h0 : f 0 = 1) :
    n ≤ finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {x | f x ≠ 0}) + d := by
  classical
  obtain ⟨p, hpd, hpf⟩ := hf
  set S := Submodule.span (ZMod 2) {x : Fin n → ZMod 2 | f x ≠ 0} with hS
  obtain ⟨T, hT⟩ := S.exists_isCompl
  have hST : finrank (ZMod 2) S + finrank (ZMod 2) T = n := by
    have := Submodule.finrank_add_eq_of_isCompl hT
    rwa [Module.finrank_fin_fun] at this
  set c := finrank (ZMod 2) T with hc
  let bT := Module.finBasis (ZMod 2) T
  let v : Fin c → (Fin n → ZMod 2) := fun i => (bT i : Fin n → ZMod 2)
  have hvli : LinearIndependent (ZMod 2) v :=
    bT.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hvT : ∀ t : Fin c → ZMod 2, ∑ i, t i • v i ∈ T := fun t =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (bT i).2)
  let g : (Fin c → ZMod 2) → ZMod 2 := fun t => f (∑ i, t i • v i)
  let φ : Fin n → MvPolynomial (Fin c) (ZMod 2) := fun j => ∑ i, C (v i j) * X i
  have hφ : ∀ j, (φ j).totalDegree ≤ 1 := fun j =>
    totalDegree_finsetSum_le (fun i _ => (totalDegree_mul _ _).trans (by
      simp [totalDegree_C, totalDegree_X]))
  have hg : HasDeg g d := by
    refine ⟨bind₁ φ p, (totalDegree_bind₁_le_of φ hφ p).trans hpd, fun t => ?_⟩
    have hb : eval t (bind₁ φ p) = eval (fun i => eval t (φ i)) p := aeval_bind₁ t φ p
    rw [hb, hpf]
    show f _ = f _
    congr 1
    funext j
    simp only [φ, map_sum, map_mul, eval_C, eval_X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hg0 : g 0 = 1 := by
    show f (∑ i, (0 : Fin c → ZMod 2) i • v i) = 1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact h0
  have hgsupp : ∀ t, g t ≠ 0 → t = 0 := by
    intro t ht
    have hmemS : ∑ i, t i • v i ∈ S := Submodule.subset_span ht
    have hmem : ∑ i, t i • v i ∈ S ⊓ T := Submodule.mem_inf.2 ⟨hmemS, hvT t⟩
    rw [hT.inf_eq_bot] at hmem
    funext i
    exact Fintype.linearIndependent_iff.1 hvli t ((Submodule.mem_bot _).1 hmem) i
  have hcard : suppCard g ≤ 1 := by
    unfold suppCard
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [hgsupp a (Finset.mem_filter.1 ha).2, hgsupp b (Finset.mem_filter.1 hb).2]
  have hrm := rm_support c d g hg ⟨0, by rw [hg0]; exact one_ne_zero⟩
  have hcd : c - d = 0 := by
    by_contra hne
    have : 2 ≤ 2 ^ (c - d) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (c - d) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

end ReedMuller


#print axioms prop102
#print axioms prop105
#print axioms exists_prop105_data
#print axioms lemma107
#print axioms lemma108
#print axioms lemma109
#print axioms prop1010
#print axioms rm_support
#print axioms rm_span

end OMA.SimsLite.N2B
