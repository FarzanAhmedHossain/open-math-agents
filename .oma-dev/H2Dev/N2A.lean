import H2Dev.Isotropic
import H2Dev.Alt2

/-! # N2A: Li-Qiao Lemma 9.1, Prop 9.2, Prop 10.1 and Thm 7.1 (i) at `p = 2`

Li-Qiao (arXiv:2610.14509v3), Part II, Sec. 9-11 (pp. 51-53, 66-67), pure linear algebra over
`F_2 = ZMod 2` (Lemma 9.1 over any field).  `X = Fin R → F`, `Alt(X) = altSub F R`, and a space
of alternating forms is a submodule `𝒜 ≤ altSub`.  Hypothesis N2A of the plan.

* `lemma91` (Lemma 9.1, minimum dimension): an `h`-hollowing `𝒜` (with `h ≤ dim X`) has
  `dim 𝒜 ≥ h`.  Proof as in the paper: a basis of `𝒜` is a surjective alternating tuple `β` with
  `A_β = 𝒜`; Prop 7.2 (ii) (`prop72_ii`) gives `h < s(β)` and BNV 5.2 (`simsRk_le_succ`) gives
  `s(β) ≤ dim 𝒜 + 1`.
* `hollowSet R M h` : the set `H_2(R, M, h)` of `M`-dimensional `h`-hollowing subspaces of
  `Alt(F_2^R)`.
* `hollow_lowrank_dim` (the covering step (104)-(105) of the proof of Prop 9.2): with the cutoff
  `a` satisfying either `M + 6 ≤ κ_h(a+1)` or (`h = a + 2` and `M + 1 ≤ C(h,2)`), the forms of
  rank `≤ 2a` in an `h`-hollowing `M`-space span a space of dimension `k_a ≥ h - 10`.  This uses
  Lemma 8.2 (95) (`isoCount_uniform_of_le`, constant `32`) for all forms and (96)
  (`isoCount_saturated_two_of_le`, `γ_2 ≤ 15/8`) for the forms of rank `≥ 2h - 2` at the
  endpoint cutoff `a = h - 2`.
* `exists_cutoff` : the choice of `a` (least `a` with `κ_h(a+1) ≥ M + 6`, else `a = h - 2`),
  with `a h ≤ 2M + 12` (the paper's `h a = O(M)`).
* `prop92` (Prop 9.2 at `q = 2` with explicit constant): for `h ≤ R` and `M ≤ C(h,2) - 1`,
  `|H_2(R, M, h)| ≤ 2^((M - h) C(R,2) + 40 (R^2 + M^2))`.  The counting is the paper's: every
  space is spanned by `h - 10` forms of rank `≤ 2a` (Lemma 2.7 (ii), `ncard_alt_rank_le`) and
  `M - (h - 10)` arbitrary alternating forms (`n2a_exists_tuple`, a greedy extension).
* `nonminSet`, `prop101` (Prop 10.1, nonminimal endpoint spaces, `M = C(h,2)`):
  `|A^nonmin_M| ≤ 2^((M - h) C(R,2) + 40 (R^2 + M^2))`.  A nonminimal `h`-hollowing `M`-space
  contains an `h`-hollowing hyperplane (hollowing is inherited upwards), counted by `prop92`, and
  is that hyperplane plus one form (`2^C(R,2)` choices).  This replaces the paper's Gaussian
  binomial count of overspaces of the minimal `B` by the one-step version.
* `N2_le_hollow` (the inequality of (123)): `N_2(r1, r2, s) ≤ |H_2(r1, r2, s-1)| · 2^(r2^2)`
  (`|GL_r2(2)| ≤ 2^(r2^2)` replaced by the count of coordinate tuples in a fixed basis).
* `thm71_i` (Thm 7.1 (i) at `p = 2`, explicit constant `41`): for `2 ≤ s ≤ r1`,
  `s - 1 ≤ r2 < C(s-1, 2)`,
  `logN2 r1 r2 s ≤ (r2 - s + 1) C(r1, 2) + 41 (r1^2 + r2^2)`; `thm71_i_exists` is the
  `O(r1^2 + r2^2)` form.

Auxiliary: `n2a_finrank_span_sup`, `n2a_exists_tuple`, `n2a_ncard_le_of_subset_range`,
`n2a_ncard_biUnion_le`, `n2a_card_filter_mem`, `n2a_two_le_rank`, `n2a_isHollowing_mono`,
`lowAlt`, `n2a_exp_le`, `nonmin_decomp`, `n2a_logb_le`, `n2a_finite_submodule`.
-/

namespace OMA.SimsLite.Alt2

open Module

/-! ### Generic linear algebra and counting helpers -/

section Helpers

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

lemma n2a_finrank_span_sup [FiniteDimensional F V] {P : Submodule F V} {y : V} (hy : y ∉ P) :
    finrank F ↥(Submodule.span F {y} ⊔ P) = finrank F P + 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ P.zero_mem)
  have hinf : Submodule.span F {y} ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz1
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply hy
      have := P.smul_mem c⁻¹ hz2
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {y}) P
  rw [hinf, finrank_bot, finrank_span_singleton hy0] at this
  omega

/-- Greedy extension: if `U ⊔ span S` has dimension at least `dim U + k`, then `k` vectors of `S`
extend `U` by exactly `k` dimensions. -/
theorem n2a_exists_tuple [FiniteDimensional F V] (S : Set V) : ∀ (k : ℕ) (U : Submodule F V),
    finrank F U + k ≤ finrank F ↥(U ⊔ Submodule.span F S) →
      ∃ w : Fin k → V, (∀ i, w i ∈ S) ∧
        finrank F ↥(U ⊔ Submodule.span F (Set.range w)) = finrank F U + k := by
  intro k
  induction k with
  | zero =>
    intro U _
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    rw [Set.range_eq_empty, Submodule.span_empty, sup_bot_eq, add_zero]
  | succ k ih =>
    intro U hU
    obtain ⟨x, hxS, hxU⟩ : ∃ x ∈ S, x ∉ U := by
      by_contra hcon
      push_neg at hcon
      have hle : Submodule.span F S ≤ U := Submodule.span_le.2 hcon
      rw [sup_eq_left.2 hle] at hU
      omega
    have hU' := n2a_finrank_span_sup (F := F) hxU
    have hsup : (Submodule.span F {x} ⊔ U) ⊔ Submodule.span F S = U ⊔ Submodule.span F S := by
      have hx : Submodule.span F {x} ≤ Submodule.span F S :=
        Submodule.span_mono (Set.singleton_subset_iff.2 hxS)
      apply le_antisymm
      · exact sup_le (sup_le (hx.trans le_sup_right) le_sup_left) le_sup_right
      · exact sup_le (le_sup_left.trans le_sup_right) le_sup_right
    obtain ⟨w, hwS, hw⟩ := ih (Submodule.span F {x} ⊔ U) (by rw [hsup, hU']; omega)
    refine ⟨Fin.cons x w, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hxS
      | succ j => simpa using hwS j
    · have he : U ⊔ Submodule.span F (Set.range (Fin.cons x w : Fin (k + 1) → V)) =
          (Submodule.span F {x} ⊔ U) ⊔ Submodule.span F (Set.range w) := by
        rw [Fin.range_cons, Submodule.span_insert, ← sup_assoc, sup_comm U]
      rw [he, hw, hU']
      omega

/-- A set covered by the range of a map from a finite type has at most that many elements. -/
lemma n2a_ncard_le_of_subset_range {α β : Type*} [Finite α] (g : α → β) {S : Set β}
    (h : S ⊆ Set.range g) : S.ncard ≤ Nat.card α := by
  calc S.ncard ≤ (Set.range g).ncard := Set.ncard_le_ncard h (Set.finite_range g)
    _ ≤ (Set.univ : Set α).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le (Set.toFinite _)
    _ = Nat.card α := by rw [Set.ncard_univ]

/-- Union bound. -/
lemma n2a_ncard_biUnion_le {ι α : Type*} [DecidableEq ι] (I : Finset ι) (T : ι → Set α) :
    (⋃ i ∈ I, T i).ncard ≤ ∑ i ∈ I, (T i).ncard := by
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro a J ha ih
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- Submodules of a finite module form a finite type. -/
lemma n2a_finite_submodule [Finite V] : Finite (Submodule F V) :=
  Finite.of_injective (fun p : Submodule F V => fun x : V => x ∈ p)
    (fun p q hpq => SetLike.ext fun x => Iff.of_eq (congrFun hpq x))

/-- `n ≤ 2 ^ k` gives `log_2 n ≤ k` in the reals. -/
theorem n2a_logb_le {n k : ℕ} (h : n ≤ 2 ^ k) : Real.logb 2 (n : ℝ) ≤ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (n : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast h
    have h2 : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (k : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn) h1
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h2

end Helpers

/-! ### Lemma 9.1 -/

section Lemma91

variable {F : Type*} [Field F] {R : ℕ}

lemma n2a_isHollowing_mono {𝒝 𝒜 : Submodule F (Matrix (Fin R) (Fin R) F)} {h : ℕ}
    (hle : 𝒝 ≤ 𝒜) (hB : IsHollowing 𝒝 h) : IsHollowing 𝒜 h := by
  intro H hH
  obtain ⟨A, hA, h0, hi⟩ := hB H hH
  exact ⟨A, hle hA, h0, hi⟩

/-- **Lemma 9.1** (minimum dimension): if `𝒜 ≤ Alt(X)` is `h`-hollowing with `h ≤ dim X`, then
`dim 𝒜 ≥ h`. -/
theorem lemma91 (𝒜 : Submodule F (Matrix (Fin R) (Fin R) F)) {h : ℕ} (hh : h ≤ R)
    (hA : IsHollowing 𝒜 h) : h ≤ finrank F 𝒜 := by
  obtain ⟨M, hM⟩ : ∃ M, finrank F 𝒜 = M := ⟨_, rfl⟩
  rw [hM]
  let b : Basis (Fin M) F 𝒜 := Module.finBasisOfFinrankEq F 𝒜 hM
  let β : Fin M → Matrix (Fin R) (Fin R) F := fun k => (b k : Matrix (Fin R) (Fin R) F)
  have hβ : LinearIndependent F β := b.linearIndependent.map' 𝒜.subtype (by simp)
  have hspan : dualSpan β = 𝒜 := by
    have h1 := congrArg (Submodule.map 𝒜.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    exact h1
  have h2 := (prop72_ii β hβ h hh).1 (by rw [hspan]; exact hA)
  have h3 := simsRk_le_succ β ((gensOn_top_iff β).2 hβ)
  omega

end Lemma91

/-! ### Prop 9.2 over `F_2` -/

section Prop92

open Classical

variable {R : ℕ}

/-- `H_2(R, M, h)`: the `M`-dimensional `h`-hollowing subspaces of `Alt(F_2^R)`. -/
def hollowSet (R M h : ℕ) : Set (Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2))) :=
  {𝒜 | 𝒜 ≤ altSub (ZMod 2) R ∧ finrank (ZMod 2) 𝒜 = M ∧ IsHollowing 𝒜 h}

lemma mem_hollowSet {M h : ℕ} {𝒜 : Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2))} :
    𝒜 ∈ hollowSet R M h ↔
      𝒜 ≤ altSub (ZMod 2) R ∧ finrank (ZMod 2) 𝒜 = M ∧ IsHollowing 𝒜 h := Iff.rfl

/-- The alternating forms of rank at most `ρ` (`dim rad ≥ R - ρ`), as in `ncard_alt_rank_le`. -/
def lowAlt (R ρ : ℕ) : Set (Matrix (Fin R) (Fin R) (ZMod 2)) :=
  {A | IsAltMat A ∧ R - ρ ≤ finrank (ZMod 2) (rad A)}

lemma n2a_card_filter_mem {F : Type*} [Field F] [Fintype F]
    (P : Submodule F (Matrix (Fin R) (Fin R) F)) :
    (Finset.univ.filter (fun y => y ∈ P)).card = Fintype.card F ^ finrank F P := by
  rw [← Fintype.card_subtype]
  convert Module.card_eq_pow_finrank (K := F) (V := P)

/-- A nonzero alternating form has rank at least `2`. -/
lemma n2a_two_le_rank {F : Type*} [Field F] [Fintype F] {A : Matrix (Fin R) (Fin R) F}
    (hA : IsAltMat A) (h0 : A ≠ 0) : 2 * 1 ≤ R - finrank F (rad A) := by
  have hle : finrank F (rad A) ≤ R := by
    have := Submodule.finrank_le (rad A)
    rwa [Module.finrank_fin_fun] at this
  have hlt : finrank F (rad A) < R := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply h0
      have htop : rad A = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h, Module.finrank_fin_fun])
      apply (isotropic_top_iff A).1
      intro x _ y _
      exact bfL_rad_left (by rw [htop]; exact Submodule.mem_top) y
  obtain ⟨a, ha⟩ := exists_finrank_rad_add_two_mul hA
  omega

/-- The covering step of Prop 9.2, (104)-(105): at a cutoff `a` with either
`M + 6 ≤ κ_h(a+1)`, or `h = a + 2` and `M + 1 ≤ C(h,2)`, the forms of rank `≤ 2a` in an
`h`-hollowing `M`-space `𝒜 ≤ Alt(F_2^R)` span a subspace of dimension `≥ h - 10`. -/
theorem hollow_lowrank_dim {M h a : ℕ}
    {𝒜 : Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2))}
    (hAlt : 𝒜 ≤ altSub (ZMod 2) R) (hM : finrank (ZMod 2) 𝒜 = M) (hH : IsHollowing 𝒜 h)
    (hhR : h ≤ R) (h1 : 1 ≤ h)
    (hcase : M + 6 ≤ kappaH h (a + 1) ∨ (h = a + 2 ∧ M + 1 ≤ h.choose 2)) :
    h ≤ finrank (ZMod 2) (Submodule.span (ZMod 2)
      {A | A ∈ 𝒜 ∧ R - finrank (ZMod 2) (rad A) ≤ 2 * a}) + 10 := by
  obtain ⟨k, hk⟩ : ∃ k, finrank (ZMod 2) (Submodule.span (ZMod 2)
      {A | A ∈ 𝒜 ∧ R - finrank (ZMod 2) (rad A) ≤ 2 * a}) = k := ⟨_, rfl⟩
  rw [hk]
  obtain ⟨G, hG⟩ : ∃ G : ℝ,
      G = ({H : Submodule (ZMod 2) (Fin R → ZMod 2) | finrank (ZMod 2) H = h}.ncard : ℝ) :=
    ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    have h0 : 0 < Nat.card (ZMod 2) ^ (h * (R - h)) := pow_pos Nat.card_pos _
    have := h0.trans_le (pow_le_ncard_grass (F := ZMod 2) hhR)
    exact_mod_cast this
  let T1 := Finset.univ.filter (fun A : Matrix (Fin R) (Fin R) (ZMod 2) =>
    A ∈ 𝒜 ∧ A ≠ 0 ∧ R - finrank (ZMod 2) (rad A) ≤ 2 * a)
  let T2 := Finset.univ.filter (fun A : Matrix (Fin R) (Fin R) (ZMod 2) =>
    A ∈ 𝒜 ∧ A ≠ 0 ∧ ¬ (R - finrank (ZMod 2) (rad A) ≤ 2 * a))
  -- the covering (104)
  have hcovN : {H : Submodule (ZMod 2) (Fin R → ZMod 2) | finrank (ZMod 2) H = h}.ncard ≤
      ∑ A ∈ T1, isoCount A h + ∑ A ∈ T2, isoCount A h := by
    have hsub : {H : Submodule (ZMod 2) (Fin R → ZMod 2) | finrank (ZMod 2) H = h} ⊆
        (⋃ A ∈ T1, isoLocus A h) ∪ (⋃ A ∈ T2, isoLocus A h) := by
      intro H hHd
      obtain ⟨A, hA, h0, hiso⟩ := hH H hHd
      by_cases hlow : R - finrank (ZMod 2) (rad A) ≤ 2 * a
      · left
        exact Set.mem_iUnion₂.2 ⟨A, Finset.mem_filter.2 ⟨Finset.mem_univ _, hA, h0, hlow⟩,
          show H ∈ isoLocus A h from ⟨hHd, hiso⟩⟩
      · right
        exact Set.mem_iUnion₂.2 ⟨A, Finset.mem_filter.2 ⟨Finset.mem_univ _, hA, h0, hlow⟩,
          show H ∈ isoLocus A h from ⟨hHd, hiso⟩⟩
    have hfin : ((⋃ A ∈ T1, isoLocus A h) ∪ (⋃ A ∈ T2, isoLocus A h)).Finite := by
      refine (grass_finite (F := ZMod 2) R h).subset ?_
      intro H hH
      rcases hH with hH | hH
      · obtain ⟨A, -, hA⟩ := Set.mem_iUnion₂.1 hH
        exact hA.1
      · obtain ⟨A, -, hA⟩ := Set.mem_iUnion₂.1 hH
        exact hA.1
    calc _ ≤ ((⋃ A ∈ T1, isoLocus A h) ∪ (⋃ A ∈ T2, isoLocus A h)).ncard :=
          Set.ncard_le_ncard hsub hfin
      _ ≤ (⋃ A ∈ T1, isoLocus A h).ncard + (⋃ A ∈ T2, isoLocus A h).ncard :=
          Set.ncard_union_le _ _
      _ ≤ _ := Nat.add_le_add (n2a_ncard_biUnion_le T1 _) (n2a_ncard_biUnion_le T2 _)
  have hcov : G ≤ (∑ A ∈ T1, (isoCount A h : ℝ)) + ∑ A ∈ T2, (isoCount A h : ℝ) := by
    rw [hG]
    exact_mod_cast hcovN
  -- the low-rank forms: each covers at most `32 · 2^(1-h)` of the Grassmannian
  have hT1 : ∀ A ∈ T1, (isoCount A h : ℝ) * 2 ^ (h - 1) ≤ 32 * G := by
    intro A hA
    obtain ⟨-, hA𝒜, h0, -⟩ := Finset.mem_filter.1 hA
    have hAlt' : IsAltMat A := mem_altSub.1 (hAlt hA𝒜)
    have := isoCount_uniform_of_le hAlt' (n2a_two_le_rank hAlt' h0) h
    rwa [ZMod.card, Nat.cast_ofNat, kappaH_one, ← hG] at this
  have hT1card : (T1.card : ℝ) ≤ 2 ^ k := by
    have : T1.card ≤ 2 ^ k := by
      calc T1.card ≤ (Finset.univ.filter (fun y => y ∈ Submodule.span (ZMod 2)
              {A | A ∈ 𝒜 ∧ R - finrank (ZMod 2) (rad A) ≤ 2 * a})).card :=
            Finset.card_le_card (fun A hA => by
              obtain ⟨-, hA𝒜, -, hlow⟩ := Finset.mem_filter.1 hA
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
                Submodule.subset_span (show A ∈ {A | A ∈ 𝒜 ∧
                  R - finrank (ZMod 2) (rad A) ≤ 2 * a} from ⟨hA𝒜, hlow⟩)⟩)
        _ = 2 ^ k := by rw [n2a_card_filter_mem, ZMod.card, hk]
    exact_mod_cast this
  -- the high-rank forms
  have hT2rank : ∀ A ∈ T2, IsAltMat A ∧ 2 * (a + 1) ≤ R - finrank (ZMod 2) (rad A) := by
    intro A hA
    obtain ⟨-, hA𝒜, -, hhi⟩ := Finset.mem_filter.1 hA
    have hAlt' : IsAltMat A := mem_altSub.1 (hAlt hA𝒜)
    obtain ⟨b, hb⟩ := exists_finrank_rad_add_two_mul hAlt'
    exact ⟨hAlt', by omega⟩
  have hT2card : (T2.card : ℝ) ≤ 2 ^ M := by
    have : T2.card ≤ 2 ^ M := by
      calc T2.card ≤ (Finset.univ.filter (fun y => y ∈ 𝒜)).card :=
            Finset.card_le_card (fun A hA =>
              Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hA).2.1⟩)
        _ = 2 ^ M := by rw [n2a_card_filter_mem, ZMod.card, hM]
    exact_mod_cast this
  have hS2 : ∑ A ∈ T2, (isoCount A h : ℝ) ≤ 15 / 16 * G := by
    rcases hcase with hbig | ⟨hha, hMh⟩
    · have hterm : ∀ A ∈ T2, (isoCount A h : ℝ) * 2 ^ kappaH h (a + 1) ≤ 32 * G := by
        intro A hA'
        obtain ⟨hAlt', hr⟩ := hT2rank A hA'
        have := isoCount_uniform_of_le hAlt' hr h
        rwa [ZMod.card, Nat.cast_ofNat, ← hG] at this
      have hsum : (∑ A ∈ T2, (isoCount A h : ℝ)) * 2 ^ kappaH h (a + 1) ≤
          T2.card * (32 * G) := by
        rw [Finset.sum_mul]
        calc _ ≤ ∑ A ∈ T2, 32 * G := Finset.sum_le_sum hterm
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hpow : (2 : ℝ) ^ M * 64 ≤ 2 ^ kappaH h (a + 1) := by
        have h' : 2 ^ (M + 6) ≤ 2 ^ kappaH h (a + 1) := Nat.pow_le_pow_right (by norm_num) hbig
        have h'' : (2 : ℝ) ^ (M + 6) ≤ (2 : ℝ) ^ kappaH h (a + 1) := by exact_mod_cast h'
        have h64 : (2 : ℝ) ^ 6 = 64 := by norm_num
        rw [pow_add, h64] at h''
        exact h''
      have hZ : (0 : ℝ) < 2 ^ kappaH h (a + 1) := by positivity
      have h3 : (T2.card : ℝ) * (32 * G) ≤ 2 ^ M * (32 * G) :=
        mul_le_mul_of_nonneg_right hT2card (by linarith)
      have h4 : (2 : ℝ) ^ M * 64 * G ≤ 2 ^ kappaH h (a + 1) * G :=
        mul_le_mul_of_nonneg_right hpow hGpos.le
      have key : (∑ A ∈ T2, (isoCount A h : ℝ)) * 2 ^ kappaH h (a + 1) ≤
          (G / 2) * 2 ^ kappaH h (a + 1) := by
        linarith
      have := le_of_mul_le_mul_right key hZ
      linarith
    · have hterm : ∀ A ∈ T2, (isoCount A h : ℝ) * 2 ^ h.choose 2 ≤ 15 / 8 * G := by
        intro A hA'
        obtain ⟨hAlt', hr⟩ := hT2rank A hA'
        have := isoCount_saturated_two_of_le hAlt' (h := h) (by omega)
        rwa [← hG] at this
      have hsum : (∑ A ∈ T2, (isoCount A h : ℝ)) * 2 ^ h.choose 2 ≤
          T2.card * (15 / 8 * G) := by
        rw [Finset.sum_mul]
        calc _ ≤ ∑ A ∈ T2, 15 / 8 * G := Finset.sum_le_sum hterm
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hpow : (2 : ℝ) ^ M * 2 ≤ 2 ^ h.choose 2 := by
        have h' : 2 ^ (M + 1) ≤ 2 ^ h.choose 2 := Nat.pow_le_pow_right (by norm_num) hMh
        have h'' : (2 : ℝ) ^ (M + 1) ≤ (2 : ℝ) ^ h.choose 2 := by exact_mod_cast h'
        rwa [pow_succ] at h''
      have hZ : (0 : ℝ) < 2 ^ h.choose 2 := by positivity
      have h3 : (T2.card : ℝ) * (15 / 8 * G) ≤ 2 ^ M * (15 / 8 * G) :=
        mul_le_mul_of_nonneg_right hT2card (by linarith)
      have h4 : (2 : ℝ) ^ M * 2 * G ≤ 2 ^ h.choose 2 * G :=
        mul_le_mul_of_nonneg_right hpow hGpos.le
      have key : (∑ A ∈ T2, (isoCount A h : ℝ)) * 2 ^ h.choose 2 ≤
          (15 / 16 * G) * 2 ^ h.choose 2 := by
        linarith
      exact le_of_mul_le_mul_right key hZ
  -- conclusion of (105)
  have hS1 : (∑ A ∈ T1, (isoCount A h : ℝ)) * 2 ^ (h - 1) ≤ T1.card * (32 * G) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ A ∈ T1, 32 * G := Finset.sum_le_sum hT1
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hX0 : (0 : ℝ) < 2 ^ (h - 1) := by positivity
  have hS1' : G / 16 ≤ ∑ A ∈ T1, (isoCount A h : ℝ) := by linarith
  have h5 : G / 16 * 2 ^ (h - 1) ≤ (∑ A ∈ T1, (isoCount A h : ℝ)) * 2 ^ (h - 1) :=
    mul_le_mul_of_nonneg_right hS1' hX0.le
  have h6 : (T1.card : ℝ) * (32 * G) ≤ 2 ^ k * (32 * G) :=
    mul_le_mul_of_nonneg_right hT1card (by linarith)
  have h7 : G * 2 ^ (h - 1) ≤ G * (512 * 2 ^ k) := by linarith
  have h8 : (2 : ℝ) ^ (h - 1) ≤ 512 * 2 ^ k := le_of_mul_le_mul_left h7 hGpos
  have h9 : (2 : ℝ) ^ h ≤ 2 ^ (k + 10) := by
    have e1 : (2 : ℝ) ^ h = 2 * 2 ^ (h - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel h1]
    have h1024 : (2 : ℝ) ^ 10 = 1024 := by norm_num
    rw [e1, pow_add, h1024]
    linarith
  have h10 : 2 ^ h ≤ 2 ^ (k + 10) := by exact_mod_cast h9
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h10

lemma n2a_cutoff_bound {h M a : ℕ} (ha : a ≤ h - 2) (hmin : 1 ≤ a → kappaH h a < M + 6) :
    a * h ≤ 2 * M + 12 := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0, zero_mul]
    omega
  · have hk := hmin hpos
    have h2k := two_mul_kappaH h a
    rw [min_eq_left (by omega : a ≤ h - 1)] at h2k
    have hmul : a * (h + 1) ≤ a * (2 * h - a - 1) := Nat.mul_le_mul_left _ (by omega)
    have he : a * (h + 1) = a * h + a := by ring
    omega

/-- The cutoff of the proof of Prop 9.2: the least `a` with `κ_h(a+1) ≥ M + 6` if
`C(h,2) ≥ M + 6`, else `a = h - 2`; in both cases `a h ≤ 2M + 12`. -/
theorem exists_cutoff {h M : ℕ} (h2 : 2 ≤ h) (hM : M + 1 ≤ h.choose 2) :
    ∃ a : ℕ, (M + 6 ≤ kappaH h (a + 1) ∨ (h = a + 2 ∧ M + 1 ≤ h.choose 2)) ∧
      a * h ≤ 2 * M + 12 := by
  by_cases hbig : M + 6 ≤ h.choose 2
  · have hw : M + 6 ≤ kappaH h (h - 2 + 1) := by
      rw [kappaH_of_le (by omega)]
      exact hbig
    have hex : ∃ a, M + 6 ≤ kappaH h (a + 1) := ⟨h - 2, hw⟩
    refine ⟨Nat.find hex, Or.inl (Nat.find_spec hex), ?_⟩
    have hle : Nat.find hex ≤ h - 2 := Nat.find_min' hex hw
    apply n2a_cutoff_bound hle
    intro hpos
    have hmin : ¬ (M + 6 ≤ kappaH h (Nat.find hex - 1 + 1)) := Nat.find_min hex (by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    omega
  · refine ⟨h - 2, Or.inr ⟨by omega, hM⟩, ?_⟩
    have t1 := two_mul_choose_two_add h
    have t2 : (h - 2) * h + 2 * h = h * h := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h2]
    omega

lemma n2a_exp_le {M h a ρ : ℕ} (hρ : ρ ≤ 2 * a) (hρR : ρ ≤ R) (hah : a * h ≤ 2 * M + 12)
    (hhR : h ≤ R) (hhM : h ≤ M) :
    (R + ((R - ρ) * ρ + ρ.choose 2)) * (h - 10) + R.choose 2 * (M - (h - 10)) ≤
      (M - h) * R.choose 2 + 40 * (R ^ 2 + M ^ 2) := by
  have e1 : (R - ρ) * ρ + ρ.choose 2 ≤ R * ρ := by
    have t1 := two_mul_choose_two_add ρ
    have t2 : (R - ρ) * ρ + ρ * ρ = R * ρ := by rw [← Nat.add_mul, Nat.sub_add_cancel hρR]
    omega
  have e2 : (R + ((R - ρ) * ρ + ρ.choose 2)) * (h - 10) ≤ (R + R * ρ) * h :=
    Nat.mul_le_mul (Nat.add_le_add_left e1 R) (Nat.sub_le h 10)
  have e3 : (R + R * ρ) * h ≤ R * R + 2 * R * (2 * M + 12) := by
    have t1 : R * h ≤ R * R := Nat.mul_le_mul_left R hhR
    have t2 : R * ρ * h ≤ R * (2 * a) * h := Nat.mul_le_mul_right h (Nat.mul_le_mul_left R hρ)
    have t3 : R * (2 * a) * h = 2 * R * (a * h) := by ring
    have t4 : 2 * R * (a * h) ≤ 2 * R * (2 * M + 12) := Nat.mul_le_mul_left _ hah
    have t5 : (R + R * ρ) * h = R * h + R * ρ * h := by ring
    omega
  have e4 : R.choose 2 * (M - (h - 10)) ≤ (M - h) * R.choose 2 + 10 * (R * R) := by
    have hs : M - (h - 10) = (M - h) + (h - (h - 10)) := by omega
    have t1 : R.choose 2 * (M - (h - 10)) =
        (M - h) * R.choose 2 + (h - (h - 10)) * R.choose 2 := by
      rw [hs, Nat.mul_add, mul_comm (R.choose 2) (M - h), mul_comm (R.choose 2) (h - (h - 10))]
    have t2 : (h - (h - 10)) * R.choose 2 ≤ 10 * (R * R) := by
      have := two_mul_choose_two_add R
      exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have e5 : 2 * R * M ≤ R ^ 2 + M ^ 2 := by
    have : ((2 * R * M : ℕ) : ℤ) ≤ ((R ^ 2 + M ^ 2 : ℕ) : ℤ) := by
      push_cast
      nlinarith [sq_nonneg ((R : ℤ) - M)]
    exact_mod_cast this
  have e6 : R ≤ R * R := Nat.le_mul_self R
  have e7 : R ^ 2 = R * R := sq R
  have e8 : 2 * R * (2 * M + 12) = 2 * (2 * R * M) + 24 * R := by ring
  omega

/-- **Prop 9.2** at `q = 2` (explicit constant): for `h ≤ R` and `M ≤ C(h,2) - 1`,
`|H_2(R, M, h)| ≤ 2^((M - h) C(R,2) + 40 (R^2 + M^2))`, i.e.
`log_2 |H_2(R, M, h)| ≤ (M - h) C(R, 2) + O(R^2 + M^2)` (103). -/
theorem prop92 {M h : ℕ} (hhR : h ≤ R) (hM : M + 1 ≤ h.choose 2) :
    (hollowSet R M h).ncard ≤ 2 ^ ((M - h) * R.choose 2 + 40 * (R ^ 2 + M ^ 2)) := by
  have h2 : 2 ≤ h := by
    by_contra hlt
    push_neg at hlt
    rw [Nat.choose_eq_zero_of_lt hlt] at hM
    omega
  by_cases hhM : h ≤ M
  swap
  · have he : hollowSet R M h = ∅ := by
      ext 𝒜
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h𝒜
      obtain ⟨-, hdim, hH⟩ := mem_hollowSet.1 h𝒜
      have := lemma91 𝒜 hhR hH
      omega
    rw [he, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨a, hcase, hah⟩ := exists_cutoff h2 hM
  let g : (Fin (h - 10) → ↥(lowAlt R (min (2 * a) R))) ×
      (Fin (M - (h - 10)) → ↥(altSub (ZMod 2) R)) →
        Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2)) := fun p =>
    Submodule.span (ZMod 2) (Set.range (fun i => (p.1 i : Matrix (Fin R) (Fin R) (ZMod 2)))) ⊔
      Submodule.span (ZMod 2) (Set.range (fun i => (p.2 i : Matrix (Fin R) (Fin R) (ZMod 2))))
  have hsub : hollowSet R M h ⊆ Set.range g := by
    intro 𝒜 h𝒜
    obtain ⟨hAlt, hdim, hH⟩ := mem_hollowSet.1 h𝒜
    have hk := hollow_lowrank_dim hAlt hdim hH hhR (by omega) hcase
    obtain ⟨v, hvS, hv⟩ := n2a_exists_tuple
      {A | A ∈ 𝒜 ∧ R - finrank (ZMod 2) (rad A) ≤ 2 * a} (h - 10) ⊥
      (by rw [bot_sup_eq, finrank_bot]; omega)
    rw [bot_sup_eq, finrank_bot, zero_add] at hv
    have hUle : Submodule.span (ZMod 2) (Set.range v) ≤ 𝒜 :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (hvS i).1)
    obtain ⟨w, hwS, hw⟩ := n2a_exists_tuple (𝒜 : Set (Matrix (Fin R) (Fin R) (ZMod 2)))
      (M - (h - 10)) (Submodule.span (ZMod 2) (Set.range v))
      (by rw [Submodule.span_eq, sup_eq_right.2 hUle, hv, hdim]; omega)
    have heq : Submodule.span (ZMod 2) (Set.range v) ⊔ Submodule.span (ZMod 2) (Set.range w) =
        𝒜 :=
      Submodule.eq_of_le_of_finrank_eq
        (sup_le hUle (Submodule.span_le.2 (Set.range_subset_iff.2 hwS)))
        (by rw [hw, hv, hdim]; omega)
    have hlow : ∀ i, v i ∈ lowAlt R (min (2 * a) R) := by
      intro i
      have hA : IsAltMat (v i) := mem_altSub.1 (hAlt (hvS i).1)
      have hr := Submodule.finrank_le (rad (v i))
      rw [Module.finrank_fin_fun] at hr
      have h3 := (hvS i).2
      exact ⟨hA, by omega⟩
    exact ⟨(fun i => ⟨v i, hlow i⟩, fun i => ⟨w i, hAlt (hwS i)⟩), heq⟩
  have hLow : (lowAlt R (min (2 * a) R)).ncard ≤
      2 ^ R * 2 ^ ((R - min (2 * a) R) * min (2 * a) R + (min (2 * a) R).choose 2) := by
    have := ncard_alt_rank_le (F := ZMod 2) (R := R) (min (2 * a) R) (min_le_right _ _)
    rw [Nat.card_zmod] at this
    exact this
  calc (hollowSet R M h).ncard
      ≤ Nat.card ((Fin (h - 10) → ↥(lowAlt R (min (2 * a) R))) ×
          (Fin (M - (h - 10)) → ↥(altSub (ZMod 2) R))) := n2a_ncard_le_of_subset_range g hsub
    _ = (lowAlt R (min (2 * a) R)).ncard ^ (h - 10) * (2 ^ R.choose 2) ^ (M - (h - 10)) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin,
          Nat.card_coe_set_eq, card_altSub, Nat.card_zmod]
    _ ≤ (2 ^ R * 2 ^ ((R - min (2 * a) R) * min (2 * a) R + (min (2 * a) R).choose 2)) ^
          (h - 10) * (2 ^ R.choose 2) ^ (M - (h - 10)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hLow _)
    _ = 2 ^ ((R + ((R - min (2 * a) R) * min (2 * a) R + (min (2 * a) R).choose 2)) *
          (h - 10) + R.choose 2 * (M - (h - 10))) := by
        rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num)
        (n2a_exp_le (min_le_left _ _) (min_le_right _ _) hah hhR hhM)

end Prop92

/-! ### Prop 10.1 -/

section Prop101

variable {R : ℕ}

/-- `A^nonmin_M`: the `M`-dimensional `h`-hollowing subspaces of `Alt(F_2^R)` that are not
minimally `h`-hollowing. -/
def nonminSet (R M h : ℕ) : Set (Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2))) :=
  {𝒜 | 𝒜 ∈ hollowSet R M h ∧ ¬ IsMinHollowing 𝒜 h}

/-- A nonminimal `h`-hollowing `M`-space is an `h`-hollowing hyperplane plus one form. -/
theorem nonmin_decomp {M h : ℕ} {𝒜 : Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2))}
    (h𝒜 : 𝒜 ∈ nonminSet R M h) :
    1 ≤ M ∧ ∃ 𝒞 ∈ hollowSet R (M - 1) h, ∃ w : Fin 1 → ↥(altSub (ZMod 2) R),
      𝒞 ⊔ Submodule.span (ZMod 2)
        (Set.range (fun i => (w i : Matrix (Fin R) (Fin R) (ZMod 2)))) = 𝒜 := by
  obtain ⟨h𝒜1, hnm⟩ := h𝒜
  obtain ⟨hAlt, hdim, hH⟩ := mem_hollowSet.1 h𝒜1
  have hex : ∃ 𝒝, 𝒝 < 𝒜 ∧ IsHollowing 𝒝 h := by
    by_contra hcon
    push_neg at hcon
    unfold IsMinHollowing at hnm
    exact hnm ⟨hH, fun 𝒝 hlt hB => hcon 𝒝 hlt hB⟩
  obtain ⟨𝒝, hlt, hB⟩ := hex
  have hfl : finrank (ZMod 2) 𝒝 < M := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [hdim] at this
  obtain ⟨w, hwS, hw⟩ := n2a_exists_tuple (𝒜 : Set (Matrix (Fin R) (Fin R) (ZMod 2)))
    (M - 1 - finrank (ZMod 2) 𝒝) 𝒝
    (by rw [Submodule.span_eq, sup_eq_right.2 hlt.le, hdim]; omega)
  obtain ⟨𝒞, h𝒞⟩ : ∃ 𝒞, 𝒞 = 𝒝 ⊔ Submodule.span (ZMod 2) (Set.range w) := ⟨_, rfl⟩
  rw [← h𝒞] at hw
  have h𝒞le : 𝒞 ≤ 𝒜 := by
    rw [h𝒞]
    exact sup_le hlt.le (Submodule.span_le.2 (Set.range_subset_iff.2 hwS))
  have hB𝒞 : 𝒝 ≤ 𝒞 := by
    rw [h𝒞]
    exact le_sup_left
  have h𝒞dim : finrank (ZMod 2) 𝒞 = M - 1 := by
    rw [hw]
    omega
  have h𝒞mem : 𝒞 ∈ hollowSet R (M - 1) h :=
    mem_hollowSet.2 ⟨h𝒞le.trans hAlt, h𝒞dim, n2a_isHollowing_mono hB𝒞 hB⟩
  obtain ⟨x, hxS, hx⟩ := n2a_exists_tuple (𝒜 : Set (Matrix (Fin R) (Fin R) (ZMod 2))) 1 𝒞
    (by rw [Submodule.span_eq, sup_eq_right.2 h𝒞le, h𝒞dim, hdim]; omega)
  have heq : 𝒞 ⊔ Submodule.span (ZMod 2) (Set.range x) = 𝒜 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le h𝒞le (Submodule.span_le.2 (Set.range_subset_iff.2 hxS)))
      (by rw [hx, h𝒞dim, hdim]; omega)
  exact ⟨by omega, 𝒞, h𝒞mem, fun i => ⟨x i, hAlt (hxS i)⟩, heq⟩

/-- **Prop 10.1** (nonminimal endpoint spaces), `M = C(h, 2)`:
`|A^nonmin_M| ≤ 2^((M - h) C(R,2) + 40 (R^2 + M^2))`. -/
theorem prop101 {h : ℕ} (hhR : h ≤ R) :
    (nonminSet R (h.choose 2) h).ncard ≤
      2 ^ ((h.choose 2 - h) * R.choose 2 + 40 * (R ^ 2 + (h.choose 2) ^ 2)) := by
  haveI := n2a_finite_submodule (F := ZMod 2) (V := Matrix (Fin R) (Fin R) (ZMod 2))
  by_cases hc : 1 ≤ h.choose 2 ∧ h ≤ h.choose 2 - 1
  · obtain ⟨hM1, hhM⟩ := hc
    let g : ↥(hollowSet R (h.choose 2 - 1) h) × (Fin 1 → ↥(altSub (ZMod 2) R)) →
        Submodule (ZMod 2) (Matrix (Fin R) (Fin R) (ZMod 2)) := fun p =>
      p.1.1 ⊔ Submodule.span (ZMod 2)
        (Set.range (fun i => (p.2 i : Matrix (Fin R) (Fin R) (ZMod 2))))
    have hsub : nonminSet R (h.choose 2) h ⊆ Set.range g := by
      intro 𝒜 h𝒜
      obtain ⟨-, 𝒞, h𝒞, w, hw⟩ := nonmin_decomp h𝒜
      exact ⟨(⟨𝒞, h𝒞⟩, w), hw⟩
    have h92 := prop92 (R := R) (M := h.choose 2 - 1) (h := h) hhR (by omega)
    calc (nonminSet R (h.choose 2) h).ncard
        ≤ Nat.card (↥(hollowSet R (h.choose 2 - 1) h) × (Fin 1 → ↥(altSub (ZMod 2) R))) :=
          n2a_ncard_le_of_subset_range g hsub
      _ = (hollowSet R (h.choose 2 - 1) h).ncard * (2 ^ R.choose 2) ^ 1 := by
          rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun, Nat.card_fin, card_altSub,
            Nat.card_zmod]
      _ ≤ 2 ^ ((h.choose 2 - 1 - h) * R.choose 2 + 40 * (R ^ 2 + (h.choose 2 - 1) ^ 2)) *
            (2 ^ R.choose 2) ^ 1 := Nat.mul_le_mul_right _ h92
      _ = 2 ^ ((h.choose 2 - 1 - h) * R.choose 2 + 40 * (R ^ 2 + (h.choose 2 - 1) ^ 2) +
            R.choose 2) := by rw [pow_one, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by
          have e1 : h.choose 2 - h = (h.choose 2 - 1 - h) + 1 := by omega
          have e2 : (h.choose 2 - 1) ^ 2 ≤ (h.choose 2) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
          rw [e1, Nat.add_mul, one_mul]
          omega)
  · have he : nonminSet R (h.choose 2) h = ∅ := by
      ext 𝒜
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h𝒜
      obtain ⟨hM1, 𝒞, h𝒞, -⟩ := nonmin_decomp h𝒜
      obtain ⟨-, h𝒞dim, h𝒞H⟩ := mem_hollowSet.1 h𝒞
      have := lemma91 𝒞 hhR h𝒞H
      exact hc ⟨hM1, by omega⟩
    rw [he, Set.ncard_empty]
    exact Nat.zero_le _

end Prop101

/-! ### Eq. (123) and Thm 7.1 (i) at `p = 2` -/

section Thm71

/-- The inequality of (123): `N_2(r1, r2, s) ≤ |H_2(r1, r2, s - 1)| · 2^(r2^2)`. -/
theorem N2_le_hollow (r1 r2 s : ℕ) (hs : s - 1 ≤ r1) (hs1 : 1 ≤ s) :
    N2 r1 r2 s ≤ (hollowSet r1 r2 (s - 1)).ncard * 2 ^ (r2 * r2) := by
  haveI := n2a_finite_submodule (F := ZMod 2) (V := Matrix (Fin r1) (Fin r1) (ZMod 2))
  let g3 : ↥(hollowSet r1 r2 (s - 1)) × (Fin r2 → Fin r2 → ZMod 2) →
      (Fin r2 → Matrix (Fin r1) (Fin r1) (ZMod 2)) := fun p k =>
    ∑ j, p.2 k j • ((Module.finBasisOfFinrankEq (ZMod 2) p.1.1
      (mem_hollowSet.1 p.1.2).2.1 j : ↥p.1.1) : Matrix (Fin r1) (Fin r1) (ZMod 2))
  have hsub : {β : Fin r2 → Matrix (Fin r1) (Fin r1) (ZMod 2) |
      (∀ k, IsAltMat (β k)) ∧ GensOn β ⊤ ∧ simsRk β = s} ⊆ Set.range g3 := by
    rintro β ⟨hA, hg, hsr⟩
    have hβ : LinearIndependent (ZMod 2) β := (gensOn_top_iff β).1 hg
    have hdim : finrank (ZMod 2) (dualSpan β) = r2 := by
      rw [dualSpan, finrank_span_eq_card hβ, Fintype.card_fin]
    have hmem : dualSpan β ∈ hollowSet r1 r2 (s - 1) := by
      refine mem_hollowSet.2 ⟨Submodule.span_le.2 ?_, hdim, ?_⟩
      · rintro _ ⟨k, rfl⟩
        exact hA k
      · exact (prop72_ii β hβ (s - 1) hs).2 (by omega)
    let b := Module.finBasisOfFinrankEq (ZMod 2) (dualSpan β) (mem_hollowSet.1 hmem).2.1
    have hk : ∀ k, β k ∈ dualSpan β := fun k => Submodule.subset_span ⟨k, rfl⟩
    refine ⟨(⟨dualSpan β, hmem⟩, fun k j => b.repr ⟨β k, hk k⟩ j), ?_⟩
    funext k
    have h1 := congrArg Subtype.val (b.sum_repr ⟨β k, hk k⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1
  rw [N2_eq_ncard]
  refine (n2a_ncard_le_of_subset_range g3 hsub).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod, ← pow_mul]

/-- **Theorem 7.1 (i)** at `p = 2` (explicit constant `41`): for `2 ≤ s ≤ r1` and
`s - 1 ≤ r2 < C(s-1, 2)`, `N_2(r1, r2, s) ≤ (r2 - s + 1) C(r1, 2) + 41 (r1^2 + r2^2)`. -/
theorem thm71_i {r1 r2 s : ℕ} (hs : 2 ≤ s) (hsr : s ≤ r1) (hr2 : s - 1 ≤ r2)
    (hlt : r2 < (s - 1).choose 2) :
    logN2 r1 r2 s ≤
      ((r2 : ℝ) - s + 1) * (r1.choose 2 : ℝ) + 41 * ((r1 : ℝ) ^ 2 + (r2 : ℝ) ^ 2) := by
  have hN := N2_le_hollow r1 r2 s (by omega) (by omega)
  have h92 := prop92 (R := r1) (M := r2) (h := s - 1) (by omega) (by omega)
  obtain ⟨t, ht⟩ : ∃ t, r2 - (s - 1) = t := ⟨_, rfl⟩
  rw [ht] at h92
  have hN' : N2 r1 r2 s ≤ 2 ^ (t * r1.choose 2 + 40 * (r1 ^ 2 + r2 ^ 2) + r2 * r2) := by
    calc N2 r1 r2 s ≤ (hollowSet r1 r2 (s - 1)).ncard * 2 ^ (r2 * r2) := hN
      _ ≤ 2 ^ (t * r1.choose 2 + 40 * (r1 ^ 2 + r2 ^ 2)) * 2 ^ (r2 * r2) :=
          Nat.mul_le_mul_right _ h92
      _ = _ := by rw [← pow_add]
  have htR : (t : ℝ) = (r2 : ℝ) - s + 1 := by
    have e' : t + s = r2 + 1 := by omega
    have e'' : (t : ℝ) + s = r2 + 1 := by exact_mod_cast e'
    linarith
  have hlog := n2a_logb_le hN'
  unfold logN2
  refine hlog.trans ?_
  push_cast
  rw [htR]
  nlinarith [sq_nonneg (r1 : ℝ)]

/-- Thm 7.1 (i) at `p = 2` in the paper's `O(r1^2 + r2^2)` form. -/
theorem thm71_i_exists : ∃ C : ℝ, ∀ r1 r2 s : ℕ, 2 ≤ s → s ≤ r1 → s - 1 ≤ r2 →
    r2 < (s - 1).choose 2 →
      logN2 r1 r2 s ≤ ((r2 : ℝ) - s + 1) * (r1.choose 2 : ℝ) + C * ((r1 : ℝ) ^ 2 + (r2 : ℝ) ^ 2) :=
  ⟨41, fun _ _ _ hs hsr hr2 hlt => thm71_i hs hsr hr2 hlt⟩

end Thm71

#print axioms OMA.SimsLite.Alt2.thm71_i
#print axioms OMA.SimsLite.Alt2.prop101

end OMA.SimsLite.Alt2
