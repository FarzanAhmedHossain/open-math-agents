import H2Dev.Comm
import Mathlib.GroupTheory.Commutator.Basic

/-! INF-3: the commutator form modulo the p-Frattini subgroups.
`pPhi p G = G^p γ_2` and `pN p G = γ_3 γ_2^p`. Modulo these subgroups the commutator map is
well defined, biadditive, alternating, and its values generate `γ_2`. No finiteness or primality
is needed for these facts. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section CommForm

variable {G : Type u} [Group G]

/-- The p-Frattini subgroup `G^p γ_2`. -/
abbrev pPhi (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  Subgroup.closure (Set.range (fun g : G => g ^ p)) ⊔ commutator G

/-- The subgroup `γ_3 γ_2^p`. -/
abbrev pN (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p))

lemma commutator_eq_lcs_one : commutator G = lcs G 1 := by
  rw [commutator_def]
  rfl

lemma commElem_mem_lcs_one (x y : G) : ⁅x, y⁆ ∈ lcs G 1 :=
  commElem_mem_lcs_succ (n := 0) (Subgroup.mem_top x) y

lemma lcs_two_le_pN (p : ℕ) : lcs G 2 ≤ pN p G := le_sup_left

lemma pN_le_lcs_one (p : ℕ) : pN p G ≤ lcs G 1 := by
  refine sup_le (lcs_antitone (by norm_num)) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  exact Subgroup.pow_mem _ g.2 p

lemma pN_normal (p : ℕ) : (pN p G).Normal :=
  normal_of_sandwich (n := 1) (lcs_two_le_pN p) (pN_le_lcs_one p)

/-- Modulo `γ_3`, `⁅g ^ n, y⁆ = ⁅g, y⁆ ^ n`. -/
lemma commElem_pow_left_mem (g y : G) (n : ℕ) : ⁅g ^ n, y⁆ * (⁅g, y⁆ ^ n)⁻¹ ∈ lcs G 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ⁅g, ⁅g ^ n, y⁆⁆ ∈ lcs G 2 :=
      commElem_mem_lcs_succ' (n := 1) g (commElem_mem_lcs_one _ _)
    have e : ⁅g ^ (n + 1), y⁆ * (⁅g, y⁆ ^ (n + 1))⁻¹ =
        ⁅g, ⁅g ^ n, y⁆⁆ * (⁅g ^ n, y⁆ * (⁅g, y⁆ ^ n)⁻¹) := by
      rw [pow_succ' g n, commElem_mul_left, pow_succ]
      group
    rw [e]
    exact Subgroup.mul_mem _ hc ih

lemma commElem_pow_left_mem_pN (p : ℕ) (g y : G) : ⁅g ^ p, y⁆ ∈ pN p G := by
  have h1 := lcs_two_le_pN p (commElem_pow_left_mem g y p)
  have h2 : ⁅g, y⁆ ^ p ∈ pN p G := by
    refine (le_sup_right : _ ≤ pN p G) (Subgroup.subset_closure ?_)
    exact ⟨⟨⁅g, y⁆, commElem_mem_lcs_one g y⟩, rfl⟩
  have e : ⁅g ^ p, y⁆ = ⁅g ^ p, y⁆ * (⁅g, y⁆ ^ p)⁻¹ * ⁅g, y⁆ ^ p := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

/-- Elements of the p-Frattini subgroup commute with everything modulo `pN`. -/
lemma commElem_pPhi_mem (p : ℕ) {φ : G} (hφ : φ ∈ pPhi p G) (y : G) : ⁅φ, y⁆ ∈ pN p G := by
  haveI := pN_normal (G := G) p
  suffices h : pPhi p G ≤ zn (pN p G) y from commElem_mem_symm (h hφ)
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact commElem_mem_symm (commElem_pow_left_mem_pN p g y)
  · intro c hc
    rw [commutator_eq_lcs_one] at hc
    exact lcs_two_le_pN p (commElem_mem_lcs_succ' (n := 1) y hc)

theorem commForm_wd_left (p : ℕ) (x x' y : G)
    (h : x' * x⁻¹ ∈ Subgroup.closure (Set.range (fun g : G => g ^ p)) ⊔ commutator G) :
    ⁅x', y⁆ * ⁅x, y⁆⁻¹ ∈
      lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p)) := by
  haveI := pN_normal (G := G) p
  obtain ⟨φ, hφ, rfl⟩ : ∃ φ ∈ pPhi p G, x' = φ * x := ⟨x' * x⁻¹, h, by group⟩
  have h1 : ⁅φ, ⁅x, y⁆⁆ ∈ pN p G :=
    lcs_two_le_pN p (commElem_mem_lcs_succ' (n := 1) φ (commElem_mem_lcs_one _ _))
  have h2 : ⁅x, y⁆ * ⁅φ, y⁆ * ⁅x, y⁆⁻¹ ∈ pN p G :=
    (pN_normal (G := G) p).conj_mem _ (commElem_pPhi_mem p hφ y) _
  have e : ⁅φ * x, y⁆ * ⁅x, y⁆⁻¹ = ⁅φ, ⁅x, y⁆⁆ * (⁅x, y⁆ * ⁅φ, y⁆ * ⁅x, y⁆⁻¹) := by
    rw [commElem_mul_left]
    group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

theorem commForm_wd_right (p : ℕ) (x y y' : G)
    (h : y' * y⁻¹ ∈ Subgroup.closure (Set.range (fun g : G => g ^ p)) ⊔ commutator G) :
    ⁅x, y'⁆ * ⁅x, y⁆⁻¹ ∈
      lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p)) := by
  have hu := commForm_wd_left p y y' x h
  have e : ⁅x, y'⁆ * ⁅x, y⁆⁻¹ = ⁅y', x⁆⁻¹ * (⁅y', x⁆ * ⁅y, x⁆⁻¹)⁻¹ * ⁅y', x⁆⁻¹⁻¹ := by
    rw [← commutatorElement_inv y' x, ← commutatorElement_inv y x]
    group
  rw [e]
  exact (pN_normal (G := G) p).conj_mem _ (Subgroup.inv_mem _ hu) _

theorem commForm_add_left (p : ℕ) (x x' y : G) :
    ⁅x * x', y⁆ * (⁅x, y⁆ * ⁅x', y⁆)⁻¹ ∈
      lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p)) := by
  have h1 : ⁅x, ⁅x', y⁆⁆ ∈ lcs G 2 :=
    commElem_mem_lcs_succ' (n := 1) x (commElem_mem_lcs_one _ _)
  have h2 : ⁅⁅x', y⁆, ⁅x, y⁆⁆ ∈ lcs G 2 :=
    commElem_mem_lcs_succ (n := 1) (commElem_mem_lcs_one _ _) _
  have e : ⁅x * x', y⁆ * (⁅x, y⁆ * ⁅x', y⁆)⁻¹ = ⁅x, ⁅x', y⁆⁆ * ⁅⁅x', y⁆, ⁅x, y⁆⁆ := by
    rw [commElem_mul_left]
    simp only [commutatorElement_def]
    group
  rw [e]
  exact lcs_two_le_pN p (Subgroup.mul_mem _ h1 h2)

theorem commForm_add_right (p : ℕ) (x y y' : G) :
    ⁅x, y * y'⁆ * (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ ∈
      lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p)) := by
  have h1 : ⁅y, ⁅x, y'⁆⁆ ∈ lcs G 2 :=
    commElem_mem_lcs_succ' (n := 1) y (commElem_mem_lcs_one _ _)
  have e : ⁅x, y * y'⁆ * (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ =
      ⁅x, y⁆ * ⁅y, ⁅x, y'⁆⁆ * ⁅x, y⁆⁻¹ := by
    rw [commElem_mul_right]
    group
  rw [e]
  exact (pN_normal (G := G) p).conj_mem _ (lcs_two_le_pN p h1) _

theorem commForm_comm_mod (p : ℕ) (x y z w : G) :
    ⁅x, y⁆ * ⁅z, w⁆ * (⁅z, w⁆ * ⁅x, y⁆)⁻¹ ∈
      lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p)) := by
  have h : ⁅⁅x, y⁆, ⁅z, w⁆⁆ ∈ lcs G 2 :=
    commElem_mem_lcs_succ (n := 1) (commElem_mem_lcs_one _ _) _
  have e : ⁅x, y⁆ * ⁅z, w⁆ * (⁅z, w⁆ * ⁅x, y⁆)⁻¹ = ⁅⁅x, y⁆, ⁅z, w⁆⁆ := by
    rw [commutatorElement_def ⁅x, y⁆ ⁅z, w⁆]
    group
  rw [e]
  exact lcs_two_le_pN p h

theorem commForm_alt (x y : G) : ⁅x, x⁆ = 1 ∧ ⁅x, y⁆ * ⁅y, x⁆ = 1 := by
  refine ⟨commutatorElement_self x, ?_⟩
  rw [← commutatorElement_inv x y]
  exact mul_inv_cancel _

theorem commForm_span (p : ℕ) :
    lcs G 1 ≤ Subgroup.closure (Set.range (fun xy : G × G => ⁅xy.1, xy.2⁆)) ⊔
      (lcs G 2 ⊔ Subgroup.closure (Set.range (fun g : lcs G 1 => (g : G) ^ p))) := by
  show ⁅lcs G 0, ⊤⁆ ≤ _
  rw [Subgroup.commutator_le]
  intro a _ b _
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(a, b), rfl⟩)

end CommForm

end OMA.SimsLite
