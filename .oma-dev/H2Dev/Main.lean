import H2Dev.Count
import H2Dev.Rigidity
import H2Dev.ExistStmt
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Data.Set.Card

/-! Assembly: isomorphism classes inject into codes (existence + rigidity), the code count
bounds them, and the arithmetic gives the step with `B = 84`. -/

namespace OMA.SimsLite

open scoped commutatorElement

section Main

/-- A verbatim local copy of the upstream `Erdos1160.g`, used only in the development build. -/
noncomputable def gg (n : ℕ) : ℕ :=
  (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}).ncard

theorem gg_le_card_code (p : ℕ) (hp : p.Prime) (m : ℕ) : gg (p ^ m) ≤ Nat.card (Code p m) := by
  classical
  unfold gg
  set S := (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) ''
    {G : FiniteGrp.{0} | Nat.card G = p ^ m} with hS
  let Pr : Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) → Code p m → Prop :=
    fun s c => ∃ G : FiniteGrp.{0}, Quotient.mk _ G = s ∧ ∃ X : Fin m → G, Realizes X c
  have key : ∀ s ∈ S, ∃ c, Pr s c := by
    rintro s ⟨G, hG, rfl⟩
    obtain ⟨X, c, hc⟩ := existence hp m G hG
    exact ⟨c, G, rfl, X, hc⟩
  rcases S.eq_empty_or_nonempty with hE | ⟨s₀, hs₀⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨c₀, -⟩ := key s₀ hs₀
  let F : Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) → Code p m :=
    fun s => if h : ∃ c, Pr s c then h.choose else c₀
  have hF : ∀ s ∈ S, Pr s (F s) := by
    intro s hs
    have h := key s hs
    simp only [F, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn F S := by
    intro s₁ h₁ s₂ h₂ heq
    obtain ⟨G₁, rfl, X₁, hX₁⟩ := hF s₁ h₁
    obtain ⟨G₂, rfl, X₂, hX₂⟩ := hF s₂ h₂
    rw [heq] at hX₁
    obtain ⟨e⟩ := rigidity hp X₁ X₂ _ hX₁ hX₂
    apply Quotient.sound
    exact ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩
  have h := Set.ncard_le_ncard_of_injOn F (fun s _ => Set.mem_univ (F s)) hinj Set.finite_univ
  rwa [Set.ncard_univ] at h

lemma add_two_le_three_pow (a : ℕ) : a + 2 ≤ 3 ^ (a + 1) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ]
    omega

theorem gg_three_pow (a : ℕ) : gg (3 ^ a) ^ 12 ≤ 3 ^ (a ^ 3 + 84 * (a + 1) ^ 2) := by
  have h1 : gg (3 ^ a) ≤ (a + 2) ^ (5 * a) * 3 ^ ((2 * a ^ 3 + 50 * a ^ 2) / 25) :=
    (gg_le_card_code 3 Nat.prime_three a).trans (card_code_le 3 a (by norm_num))
  set q := (2 * a ^ 3 + 50 * a ^ 2) / 25 with hq
  have hq25 : 25 * (12 * q) ≤ 25 * (a ^ 3 + 24 * a ^ 2) := by
    have := Nat.div_mul_le_self (2 * a ^ 3 + 50 * a ^ 2) 25
    rw [← hq] at this
    nlinarith [Nat.zero_le (a ^ 3)]
  have h12q : 12 * q ≤ a ^ 3 + 24 * a ^ 2 := Nat.le_of_mul_le_mul_left hq25 (by norm_num)
  have h2 : (a + 2) ^ (60 * a) ≤ 3 ^ ((a + 1) * (60 * a)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (add_two_le_three_pow a) _
  calc gg (3 ^ a) ^ 12 ≤ ((a + 2) ^ (5 * a) * 3 ^ q) ^ 12 := Nat.pow_le_pow_left h1 12
    _ = (a + 2) ^ (60 * a) * 3 ^ (12 * q) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        ring_nf
    _ ≤ 3 ^ ((a + 1) * (60 * a)) * 3 ^ (a ^ 3 + 24 * a ^ 2) :=
        Nat.mul_le_mul h2 (Nat.pow_le_pow_right (by norm_num) h12q)
    _ = 3 ^ ((a + 1) * (60 * a) + (a ^ 3 + 24 * a ^ 2)) := (pow_add _ _ _).symm
    _ ≤ 3 ^ (a ^ 3 + 84 * (a + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith [Nat.zero_le a]

/-- The step, for the local copy `gg`. -/
theorem step_H2 : ∃ B : ℕ, ∀ a : ℕ, gg (3 ^ a) ^ 12 ≤ 3 ^ (a ^ 3 + B * (a + 1) ^ 2) :=
  ⟨84, gg_three_pow⟩

end Main

end OMA.SimsLite
