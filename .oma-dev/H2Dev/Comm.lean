import H2Dev.NF

/-! Commutator calculus for the Sims-lite bound (C1 to C5 of the blueprint).
Convention: Mathlib's `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`; `lcs D n` is the lower central series with
`lcs D 0 = ⊤`, so `lcs D n` is `γ_{n+1}`. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section Comm

variable {D : Type u} [Group D]

/-- The lower central series, 0-indexed. -/
abbrev lcs (D : Type u) [Group D] (n : ℕ) : Subgroup D := (⊤ : Subgroup D).lowerCentralSeries n

lemma lcs_zero : lcs D 0 = ⊤ := rfl

lemma lcs_succ (n : ℕ) : lcs D (n + 1) = ⁅lcs D n, ⊤⁆ := rfl

lemma lcs_succ' (n : ℕ) : lcs D (n + 1) = ⁅(⊤ : Subgroup D), lcs D n⁆ := by
  rw [lcs_succ, Subgroup.commutator_comm]

lemma lcs_antitone {a b : ℕ} (h : a ≤ b) : lcs D b ≤ lcs D a :=
  Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup D) h

lemma commElem_mem_lcs_succ {n : ℕ} {x : D} (hx : x ∈ lcs D n) (g : D) :
    ⁅x, g⁆ ∈ lcs D (n + 1) := by
  rw [lcs_succ]
  exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)

lemma commElem_mem_lcs_succ' {n : ℕ} (g : D) {x : D} (hx : x ∈ lcs D n) :
    ⁅g, x⁆ ∈ lcs D (n + 1) := by
  rw [lcs_succ']
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hx

/-- C1: for normal `N`, the elements `g` with `⁅x, g⁆ ∈ N` form a subgroup. -/
def zn (N : Subgroup D) [N.Normal] (x : D) : Subgroup D where
  carrier := {g | ⁅x, g⁆ ∈ N}
  one_mem' := by
    show ⁅x, (1 : D)⁆ ∈ N
    rw [commutatorElement_one_right]
    exact N.one_mem
  mul_mem' := by
    intro g h hg hh
    show ⁅x, g * h⁆ ∈ N
    have e : ⁅x, g * h⁆ = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hg (‹N.Normal›.conj_mem _ hh g)
  inv_mem' := by
    intro g hg
    show ⁅x, g⁻¹⁆ ∈ N
    have e : ⁅x, g⁻¹⁆ = g⁻¹ * ⁅x, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ‹N.Normal›.conj_mem _ (N.inv_mem hg) g⁻¹

lemma mem_zn {N : Subgroup D} [N.Normal] {x g : D} : g ∈ zn N x ↔ ⁅x, g⁆ ∈ N := Iff.rfl

lemma commElem_mem_symm {N : Subgroup D} {x g : D} (h : ⁅x, g⁆ ∈ N) : ⁅g, x⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact N.inv_mem h

/-- C1': commutators of generators control the commutator of the generated subgroups. -/
lemma commutator_closure_le {N : Subgroup D} [N.Normal] {A B : Set D}
    (h : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) :
    ⁅Subgroup.closure A, Subgroup.closure B⁆ ≤ N := by
  have hB : ∀ a ∈ A, Subgroup.closure B ≤ zn N a := fun a ha =>
    (Subgroup.closure_le (zn N a)).mpr fun b hb => h a ha b hb
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hA : Subgroup.closure A ≤ zn N y :=
    (Subgroup.closure_le (zn N y)).mpr fun a ha => commElem_mem_symm (hB a ha hy)
  exact commElem_mem_symm (hA hx)

/-- Elementwise form of C1'. -/
lemma commElem_mem_of_closure {N : Subgroup D} [N.Normal] {A B : Set D}
    (h : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) {x y : D}
    (hx : x ∈ Subgroup.closure A) (hy : y ∈ Subgroup.closure B) : ⁅x, y⁆ ∈ N :=
  commutator_closure_le h (Subgroup.commutator_mem_commutator hx hy)

/-- C2: a subgroup sandwiched between consecutive terms of the lower central series is normal. -/
lemma normal_of_sandwich {K : Subgroup D} {n : ℕ} (h1 : lcs D (n + 1) ≤ K) (h2 : K ≤ lcs D n) :
    K.Normal := by
  constructor
  intro k hk g
  have e : g * k * g⁻¹ = ⁅g, k⁆ * k := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact K.mul_mem (h1 (commElem_mem_lcs_succ' g (h2 hk))) hk

/-- C2: a subgroup containing the commutator subgroup is normal. -/
lemma normal_of_lcs_one_le {K : Subgroup D} (h1 : lcs D 1 ≤ K) : K.Normal :=
  normal_of_sandwich (n := 0) h1 le_top

/-- C3: the three subgroup lemma modulo a normal subgroup. -/
lemma three_subgroup_mod (N : Subgroup D) [N.Normal] {A B C : Subgroup D}
    (h1 : ⁅⁅B, C⁆, A⁆ ≤ N) (h2 : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  have key : ∀ X Y Z : Subgroup D, ⁅⁅X, Y⁆, Z⁆ ≤ N ↔
      ⁅⁅X.map (QuotientGroup.mk' N), Y.map (QuotientGroup.mk' N)⁆,
        Z.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    intro X Y Z
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

/-- C4: `⁅γ_{a+1}, γ_{b+1}⁆ ≤ γ_{a+b+2}`. -/
lemma lcs_comm_le : ∀ (b a : ℕ), ⁅lcs D a, lcs D b⁆ ≤ lcs D (a + b + 1)
  | 0, a => by rw [lcs_zero, ← lcs_succ]
  | b + 1, a => by
    rw [lcs_succ b, Subgroup.commutator_comm]
    have h1 : ⁅⁅(⊤ : Subgroup D), lcs D a⁆, lcs D b⁆ ≤ lcs D (a + (b + 1) + 1) := by
      rw [← lcs_succ']
      have := lcs_comm_le b (a + 1)
      rwa [show a + 1 + b + 1 = a + (b + 1) + 1 by omega] at this
    have h2 : ⁅⁅lcs D a, lcs D b⁆, (⊤ : Subgroup D)⁆ ≤ lcs D (a + (b + 1) + 1) := by
      rw [show a + (b + 1) + 1 = a + b + 1 + 1 by omega, lcs_succ]
      exact Subgroup.commutator_mono (lcs_comm_le b a) le_rfl
    exact three_subgroup_mod _ h1 h2

lemma commElem_mem_lcs_add {a b : ℕ} {x y : D} (hx : x ∈ lcs D a) (hy : y ∈ lcs D b) :
    ⁅x, y⁆ ∈ lcs D (a + b + 1) :=
  lcs_comm_le b a (Subgroup.commutator_mem_commutator hx hy)

/-- C5 (I1). -/
lemma commElem_mul_right (x y z : D) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅y, ⁅x, z⁆⁆ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

/-- C5 (I2). -/
lemma commElem_mul_left (x y z : D) : ⁅y * z, x⁆ = ⁅y, ⁅z, x⁆⁆ * ⁅z, x⁆ * ⁅y, x⁆ := by
  simp only [commutatorElement_def]
  group

/-- C5 consequence: modulo a subgroup `W ≥ γ_3`, `⁅x, y z⁆ ∈ W ↔ ⁅x, z⁆ ∈ W` when `⁅x, y⁆ ∈ W`. -/
lemma comm_mul_right_mem_iff {W : Subgroup D} (hW : lcs D 2 ≤ W) {x y z : D} (hxy : ⁅x, y⁆ ∈ W) :
    ⁅x, y * z⁆ ∈ W ↔ ⁅x, z⁆ ∈ W := by
  have h3 : ⁅y, ⁅x, z⁆⁆ ∈ W :=
    hW (commElem_mem_lcs_succ' y (commElem_mem_lcs_succ' (n := 0) x (Subgroup.mem_top z)))
  rw [commElem_mul_right, mul_assoc, Subgroup.mul_mem_cancel_left W hxy,
    Subgroup.mul_mem_cancel_left W h3]

/-- C5 consequence: modulo `W ≥ γ_3`, `⁅x, y z⁆ ∈ W ↔ ⁅x, y⁆ ∈ W` when `⁅x, z⁆ ∈ W`. -/
lemma comm_mul_right_mem_iff' {W : Subgroup D} (hW : lcs D 2 ≤ W) {x y z : D} (hxz : ⁅x, z⁆ ∈ W) :
    ⁅x, y * z⁆ ∈ W ↔ ⁅x, y⁆ ∈ W := by
  have h3 : ⁅y, ⁅x, z⁆⁆ ∈ W :=
    hW (commElem_mem_lcs_succ' y (commElem_mem_lcs_succ' (n := 0) x (Subgroup.mem_top z)))
  rw [commElem_mul_right, Subgroup.mul_mem_cancel_right W hxz,
    Subgroup.mul_mem_cancel_right W h3]

/-- C5 consequence: modulo `W ≥ γ_3`, `⁅y z, x⁆ ∈ W ↔ ⁅z, x⁆ ∈ W` when `⁅y, x⁆ ∈ W`. -/
lemma comm_mul_left_mem_iff {W : Subgroup D} (hW : lcs D 2 ≤ W) {x y z : D} (hyx : ⁅y, x⁆ ∈ W) :
    ⁅y * z, x⁆ ∈ W ↔ ⁅z, x⁆ ∈ W := by
  have h3 : ⁅y, ⁅z, x⁆⁆ ∈ W :=
    hW (commElem_mem_lcs_succ' y (commElem_mem_lcs_succ' (n := 0) z (Subgroup.mem_top x)))
  rw [commElem_mul_left, Subgroup.mul_mem_cancel_right W hyx,
    Subgroup.mul_mem_cancel_left W h3]

end Comm

end OMA.SimsLite
