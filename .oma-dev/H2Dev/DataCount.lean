import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! INF-1 (conditional counting of isomorphism classes) and Li-Qiao Proposition 2.5
(counting recorded Sims presentation data).

INF-1. Isomorphism classes of finite groups are encoded as in `Main.lean`: elements of
`Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})`, and a set of classes is the image
of a set of groups under `Quotient.mk`. The counting lemmas are stated for an arbitrary type of
objects, then specialised to classes of groups:
* (a) data in a finite set `D` that determines the object gives `S.ncard ≤ D.card`
  (`ncard_le_card_of_rel`, `ncard_le_card_of_injOn`, `ncard_le_card_of_surjOn`,
  `ncard_classes_le_of_data`, `ncard_classes_le_fintype_card`);
* (b) union bounds (`ncard_biUnion_le`, `ncard_le_sum_of_rel`);
* (c) the logarithmic form in naturals (`ncard_le_pow_of_rel`, `log_le_of_le_pow`).

Proposition 2.5. The recorded Sims presentation data of a nonabelian group of order `p ^ m`
are the integers `c`, `s`, `(r i)`, `(d k)`, the auxiliary function `f`, the index pairs of the
generators of weight `≥ 3`, and the relative order array `(a i j)`. They are modelled here by
the finite type `RecData m`:
* `c, s : Fin (m + 1)` (the paper has `2 ≤ c ≤ m`, `2 ≤ s ≤ m`);
* `r : RankVec m c`, the ranks, positive with sum at most `m`;
* the increments `d 2 - d 1, ..., d s - d (s - 1)`, which determine `(d k)` since `d 1 = 0`:
  a composition of `r 2` into `s - 1` parts, `PosVec (s - 1) r.r2`;
* `AuxData m s r.r2 r.r3`: the function `f : [r 2] → [s - 1]` and, for each of the `r.r3`
  generators of weight `≥ 3`, its defining index pair, of which there are at most `m * m`;
* the relative order array, flattened along the `r.tot = Σ r i` generators: positive entries
  with sum `m`, `PosVec r.tot m`.
The bullets of Proposition 2.5 are `card_intData_le`, `card_auxData_le` and
`card_relOrder_le`; their product is `card_recData_le`, and the `p ^ O(m log m)` form is
`card_recData_le_pow` and `card_recData_le_prime_pow`. -/

namespace OMA.SimsLite

section DataCount

/-! ### INF-1 (a): data determining the object -/

theorem ncard_le_card_of_injOn {α β : Type*} {S : Set α} (D : Finset β) (F : α → β)
    (hF : ∀ s ∈ S, F s ∈ D) (hinj : Set.InjOn F S) : S.ncard ≤ D.card := by
  have h := Set.ncard_le_ncard_of_injOn (t := (D : Set β)) F
    (fun s hs => Finset.mem_coe.2 (hF s hs)) hinj D.finite_toSet
  rwa [Set.ncard_coe_finset] at h

/-- If every object of `S` has some datum in `D`, and a datum is shared by at most one object of
`S`, then `S.ncard ≤ D.card`. -/
theorem ncard_le_card_of_rel {α β : Type*} {S : Set α} (D : Finset β) (P : α → β → Prop)
    (hex : ∀ s ∈ S, ∃ d ∈ D, P s d)
    (huniq : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ d, P s₁ d → P s₂ d → s₁ = s₂) : S.ncard ≤ D.card := by
  classical
  rcases D.eq_empty_or_nonempty with hD | ⟨d₀, -⟩
  · have hS : S = ∅ := by
      ext s
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hs
      obtain ⟨d, hd, -⟩ := hex s hs
      simp [hD] at hd
    simp [hS]
  · let F : α → β := fun s => if h : ∃ d ∈ D, P s d then h.choose else d₀
    have hF : ∀ s ∈ S, F s ∈ D ∧ P s (F s) := by
      intro s hs
      have h := hex s hs
      simp only [F, dif_pos h]
      exact h.choose_spec
    refine ncard_le_card_of_injOn D F (fun s hs => (hF s hs).1) ?_
    intro s₁ h₁ s₂ h₂ heq
    have h₂' : P s₂ (F s₁) := by
      rw [heq]
      exact (hF s₂ h₂).2
    exact huniq s₁ h₁ s₂ h₂ (F s₁) (hF s₁ h₁).2 h₂'

/-- Surjective form: every object of `S` is the image of a datum in `D`. -/
theorem ncard_le_card_of_surjOn {α β : Type*} {S : Set α} (D : Finset β) (g : β → α)
    (hg : ∀ s ∈ S, ∃ d ∈ D, g d = s) : S.ncard ≤ D.card :=
  ncard_le_card_of_rel D (fun s d => g d = s) hg
    (fun _ _ _ _ _ h₁ h₂ => h₁.symm.trans h₂)

/-- INF-1 (a) for isomorphism classes of finite groups: if every group of `T` has data in `D`
satisfying `R`, and two groups of `T` with the same data are isomorphic (rigidity, taken as a
hypothesis), then the number of isomorphism classes of groups of `T` is at most `D.card`. -/
theorem ncard_classes_le_of_data {β : Type*} (T : Set FiniteGrp.{0}) (D : Finset β)
    (R : FiniteGrp.{0} → β → Prop) (hex : ∀ G ∈ T, ∃ d ∈ D, R G d)
    (hrig : ∀ G ∈ T, ∀ H ∈ T, ∀ d, R G d → R H d → Nonempty (G ≃* H)) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard ≤ D.card := by
  refine ncard_le_card_of_rel D
    (fun s d => ∃ G ∈ T,
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) G = s ∧ R G d) ?_ ?_
  · rintro s ⟨G, hG, rfl⟩
    obtain ⟨d, hd, hR⟩ := hex G hG
    exact ⟨d, hd, G, hG, rfl, hR⟩
  · rintro s₁ - s₂ - d ⟨G₁, hG₁, rfl, hR₁⟩ ⟨G₂, hG₂, rfl, hR₂⟩
    obtain ⟨e⟩ := hrig G₁ hG₁ G₂ hG₂ d hR₁ hR₂
    apply Quotient.sound
    exact ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩

/-- The same with the data ranging over a whole finite type. -/
theorem ncard_classes_le_fintype_card {β : Type*} [Fintype β] (T : Set FiniteGrp.{0})
    (R : FiniteGrp.{0} → β → Prop) (hex : ∀ G ∈ T, ∃ d, R G d)
    (hrig : ∀ G ∈ T, ∀ H ∈ T, ∀ d, R G d → R H d → Nonempty (G ≃* H)) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard
      ≤ Fintype.card β := by
  refine (ncard_classes_le_of_data T Finset.univ R ?_ hrig).trans_eq Finset.card_univ
  intro G hG
  obtain ⟨d, hd⟩ := hex G hG
  exact ⟨d, Finset.mem_univ d, hd⟩

/-! ### INF-1 (b): union bounds -/

theorem ncard_biUnion_le {ι α : Type*} [DecidableEq ι] (I : Finset ι) (T : ι → Set α) :
    (⋃ i ∈ I, T i).ncard ≤ ∑ i ∈ I, (T i).ncard := by
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro a J ha ih
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- Data with a finite parameter: if every object of `S` has, for some parameter `i ∈ I`, a
datum in `D i`, and the pair (parameter, datum) determines the object, then
`S.ncard ≤ Σ i ∈ I, (D i).card`. -/
theorem ncard_le_sum_of_rel {ι α : Type*} {β : ι → Type*} {S : Set α} (I : Finset ι)
    (D : ∀ i, Finset (β i)) (P : ∀ i, α → β i → Prop)
    (hex : ∀ s ∈ S, ∃ i ∈ I, ∃ d ∈ D i, P i s d)
    (huniq : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ i d, P i s₁ d → P i s₂ d → s₁ = s₂) :
    S.ncard ≤ ∑ i ∈ I, (D i).card := by
  rw [← Finset.card_sigma]
  refine ncard_le_card_of_rel (I.sigma D) (fun s x => P x.1 s x.2) ?_ ?_
  · intro s hs
    obtain ⟨i, hi, d, hd, h⟩ := hex s hs
    exact ⟨⟨i, d⟩, Finset.mem_sigma.2 ⟨hi, hd⟩, h⟩
  · rintro s₁ h₁ s₂ h₂ ⟨i, d⟩ hP₁ hP₂
    exact huniq s₁ h₁ s₂ h₂ i d hP₁ hP₂

/-! ### INF-1 (c): the logarithmic form -/

theorem ncard_le_pow_of_rel {α β : Type*} {S : Set α} (D : Finset β) (P : α → β → Prop)
    (hex : ∀ s ∈ S, ∃ d ∈ D, P s d)
    (huniq : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ d, P s₁ d → P s₂ d → s₁ = s₂) {p k : ℕ}
    (hD : D.card ≤ p ^ k) : S.ncard ≤ p ^ k :=
  (ncard_le_card_of_rel D P hex huniq).trans hD

theorem log_le_of_le_pow {p n k : ℕ} (hp : 1 < p) (h : n ≤ p ^ k) : Nat.log p n ≤ k :=
  (Nat.log_mono_right h).trans_eq (Nat.log_pow hp k)

theorem ncard_classes_log_le {β : Type*} [Fintype β] (T : Set FiniteGrp.{0})
    (R : FiniteGrp.{0} → β → Prop) (hex : ∀ G ∈ T, ∃ d, R G d)
    (hrig : ∀ G ∈ T, ∀ H ∈ T, ∀ d, R G d → R H d → Nonempty (G ≃* H)) {p k : ℕ} (hp : 1 < p)
    (hβ : Fintype.card β ≤ p ^ k) :
    Nat.log p (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard ≤ k :=
  log_le_of_le_pow hp ((ncard_classes_le_fintype_card T R hex hrig).trans hβ)

/-! ### Proposition 2.5: compositions -/

/-- Positive integer vectors of length `k` with entry sum `n` (compositions of `n` into `k`
parts). -/
abbrev PosVec (k n : ℕ) : Type :=
  {a : Fin k → Fin (n + 1) // (∀ i, 0 < (a i).val) ∧ ∑ i, (a i).val = n}

/-- A positive vector as a composition. -/
def PosVec.toComp {k n : ℕ} (a : PosVec k n) : Composition n where
  blocks := List.ofFn (fun i => (a.1 i).val)
  blocks_pos := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact a.2.1 i
  blocks_sum := by
    rw [List.sum_ofFn]
    exact a.2.2

theorem PosVec.toComp_injective (k n : ℕ) : Function.Injective (@PosVec.toComp k n) := by
  intro a b h
  have h2 : List.ofFn (fun i => (a.1 i).val) = List.ofFn (fun i => (b.1 i).val) :=
    congrArg Composition.blocks h
  have h3 := List.ofFn_injective h2
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun h3 i)

theorem card_posVec_le (k n : ℕ) : Fintype.card (PosVec k n) ≤ 2 ^ (n - 1) :=
  (Fintype.card_le_of_injective _ (PosVec.toComp_injective k n)).trans_eq (composition_card n)

/-- Rank vectors: `c` positive integers with sum at most `m`. -/
abbrev RankVec (m c : ℕ) : Type :=
  {r : Fin c → Fin (m + 1) // (∀ i, 0 < (r i).val) ∧ ∑ i, (r i).val ≤ m}

/-- A rank vector as a composition of `m + 1`, by appending the positive slack. -/
def RankVec.toComp {m c : ℕ} (r : RankVec m c) : Composition (m + 1) where
  blocks := List.ofFn (fun i => (r.1 i).val) ++ [m + 1 - ∑ i, (r.1 i).val]
  blocks_pos := by
    intro x hx
    rw [List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
    rcases hx with ⟨i, rfl⟩ | rfl
    · exact r.2.1 i
    · have := r.2.2
      omega
  blocks_sum := by
    rw [List.sum_append, List.sum_ofFn, List.sum_singleton]
    have := r.2.2
    omega

theorem RankVec.toComp_injective (m c : ℕ) : Function.Injective (@RankVec.toComp m c) := by
  intro a b h
  have h2 : List.ofFn (fun i => (a.1 i).val) ++ [m + 1 - ∑ i, (a.1 i).val]
      = List.ofFn (fun i => (b.1 i).val) ++ [m + 1 - ∑ i, (b.1 i).val] :=
    congrArg Composition.blocks h
  have h3 : List.ofFn (fun i => (a.1 i).val) = List.ofFn (fun i => (b.1 i).val) :=
    List.append_inj_left' h2 (by simp)
  have h4 := List.ofFn_injective h3
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun h4 i)

theorem card_rankVec_le (m c : ℕ) : Fintype.card (RankVec m c) ≤ 2 ^ m := by
  have h := Fintype.card_le_of_injective _ (RankVec.toComp_injective m c)
  rw [composition_card, Nat.add_sub_cancel] at h
  exact h

/-- The total rank `Σ r i`. -/
def RankVec.tot {m c : ℕ} (r : RankVec m c) : ℕ := ∑ i, (r.1 i).val

/-- The rank `r 2` of weight `2` (index `1` in `Fin c`; `0` if `c < 2`). -/
def RankVec.r2 {m c : ℕ} (r : RankVec m c) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin c => i.val = 1), (r.1 i).val

/-- The number `Σ_{i ≥ 3} r i` of generators of weight at least `3`. -/
def RankVec.r3 {m c : ℕ} (r : RankVec m c) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin c => 2 ≤ i.val), (r.1 i).val

theorem RankVec.tot_le {m c : ℕ} (r : RankVec m c) : r.tot ≤ m := r.2.2

theorem RankVec.r2_add_r3_le {m c : ℕ} (r : RankVec m c) : r.r2 + r.r3 ≤ m := by
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin c => i.val = 1))
      (Finset.univ.filter (fun i : Fin c => 2 ≤ i.val)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    omega
  unfold RankVec.r2 RankVec.r3
  rw [← Finset.sum_union hdisj]
  exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans r.2.2

theorem sum_le_card_mul {ι : Type*} [Fintype ι] (f : ι → ℕ) (A B : ℕ)
    (hA : Fintype.card ι ≤ A) (hB : ∀ i, f i ≤ B) : ∑ i, f i ≤ A * B := by
  calc ∑ i, f i ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = Fintype.card ι * B := by simp
    _ ≤ A * B := Nat.mul_le_mul hA le_rfl

/-! ### Proposition 2.5, first bullet: the integers -/

/-- The integers `c`, `s`, `(r i)` and the increments of `(d k)`. -/
abbrev IntData (m : ℕ) : Type :=
  Σ c : Fin (m + 1), Σ s : Fin (m + 1), Σ r : RankVec m c.val, PosVec (s.val - 1) r.r2

theorem card_intData_le (m : ℕ) :
    Fintype.card (IntData m) ≤ (m + 1) * ((m + 1) * (2 ^ m * 2 ^ (m - 1))) := by
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ (by simp) (fun c => ?_)
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ (by simp) (fun s => ?_)
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ (card_rankVec_le m c.val) (fun r => ?_)
  have hr := r.r2_add_r3_le
  exact (card_posVec_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ### Proposition 2.5, first bullet: the auxiliary function and index pairs -/

/-- The auxiliary function `f : [r₂] → [s - 1]` and the defining index pairs of the `R₃`
generators of weight at least `3` (each pair has at most `s * r (i - 1) ≤ m * m` values). -/
abbrev AuxData (m s r₂ R₃ : ℕ) : Type := (Fin r₂ → Fin (s - 1)) × (Fin R₃ → Fin m × Fin m)

theorem card_auxData (m s r₂ R₃ : ℕ) :
    Fintype.card (AuxData m s r₂ R₃) = (s - 1) ^ r₂ * (m * m) ^ R₃ := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

theorem card_auxData_le (m s r₂ R₃ : ℕ) (hs : s ≤ m + 1) (hr : r₂ + R₃ ≤ m) :
    Fintype.card (AuxData m s r₂ R₃) ≤ m ^ (2 * m) := by
  rw [card_auxData]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : r₂ = 0 := by omega
    have h2 : R₃ = 0 := by omega
    subst h1
    subst h2
    simp
  · calc (s - 1) ^ r₂ * (m * m) ^ R₃ ≤ m ^ r₂ * (m * m) ^ R₃ :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) le_rfl
      _ = m ^ (r₂ + 2 * R₃) := by ring
      _ ≤ m ^ (2 * m) := Nat.pow_le_pow_right hm (by omega)

/-! ### Proposition 2.5, second bullet: relative order arrays -/

/-- Relative order arrays for `R` generators of a group of order `p ^ m`: positive entries with
sum `m`. There are at most `2 ^ (m - 1)` of them. -/
theorem card_relOrder_le (R m : ℕ) : Fintype.card (PosVec R m) ≤ 2 ^ (m - 1) :=
  card_posVec_le R m

/-! ### Proposition 2.5: the recorded Sims presentation data -/

/-- Recorded Sims presentation data for groups of order `p ^ m`. -/
abbrev RecData (m : ℕ) : Type :=
  Σ c : Fin (m + 1), Σ s : Fin (m + 1), Σ r : RankVec m c.val,
    PosVec (s.val - 1) r.r2 × AuxData m s.val r.r2 r.r3 × PosVec r.tot m

theorem card_recData_le (m : ℕ) :
    Fintype.card (RecData m) ≤
      (m + 1) * ((m + 1) * (2 ^ m * (2 ^ (m - 1) * (m ^ (2 * m) * 2 ^ (m - 1))))) := by
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ (by simp) (fun c => ?_)
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ (by simp) (fun s => ?_)
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ (card_rankVec_le m c.val) (fun r => ?_)
  have hr := r.r2_add_r3_le
  rw [Fintype.card_prod, Fintype.card_prod]
  refine Nat.mul_le_mul ?_ (Nat.mul_le_mul ?_ ?_)
  · exact (card_posVec_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · exact card_auxData_le m s.val r.r2 r.r3 (by omega) hr
  · exact card_relOrder_le r.tot m

/-- Proposition 2.5 in the closed form `(m + 1) ^ (5 m + 2)`. -/
theorem card_recData_le_pow (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (RecData m) ≤ (m + 1) ^ (5 * m + 2) := by
  refine (card_recData_le m).trans ?_
  have h1 : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m 1)
  have h2 : m ^ (2 * m) ≤ (m + 1) ^ (2 * m) := Nat.pow_le_pow_left (Nat.le_succ m) _
  have h8 : (8 : ℕ) ≤ (m + 1) ^ 3 := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ (m + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : 2 ^ m * 2 ^ m * 2 ^ m ≤ (m + 1) ^ (3 * m) := by
    calc 2 ^ m * 2 ^ m * 2 ^ m = (2 * 2 * 2) ^ m := by rw [mul_pow, mul_pow]
      _ = 8 ^ m := by norm_num
      _ ≤ ((m + 1) ^ 3) ^ m := Nat.pow_le_pow_left h8 m
      _ = (m + 1) ^ (3 * m) := by rw [← pow_mul]
  calc (m + 1) * ((m + 1) * (2 ^ m * (2 ^ (m - 1) * (m ^ (2 * m) * 2 ^ (m - 1)))))
      ≤ (m + 1) * ((m + 1) * (2 ^ m * (2 ^ m * ((m + 1) ^ (2 * m) * 2 ^ m)))) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl
          (Nat.mul_le_mul le_rfl (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h1))))
    _ = (m + 1) ^ 2 * (2 ^ m * 2 ^ m * 2 ^ m) * (m + 1) ^ (2 * m) := by ring
    _ ≤ (m + 1) ^ 2 * (m + 1) ^ (3 * m) * (m + 1) ^ (2 * m) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl h3) le_rfl
    _ = (m + 1) ^ (5 * m + 2) := by ring

/-- Proposition 2.5, the `p ^ O(m log m)` form: at most
`p ^ ((log_p (m + 1) + 1) (5 m + 2))` choices. -/
theorem card_recData_le_prime_pow (p m : ℕ) (hp : 1 < p) (hm : 1 ≤ m) :
    Fintype.card (RecData m) ≤ p ^ ((Nat.log p (m + 1) + 1) * (5 * m + 2)) := by
  refine (card_recData_le_pow m hm).trans ?_
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self hp (m + 1)).le _

end DataCount

end OMA.SimsLite
