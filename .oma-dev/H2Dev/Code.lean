import H2Dev.Comm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! The interface of the Sims-lite count: shapes, validity, index sets, codes, and what it means
for a generating tuple `X : Fin m → G` to realise a code.

Levels are 0-based: a position of level `ℓ` lies in `lcs G ℓ` (`γ_{ℓ+1}`).
* `df i = none`: `X i` is free (level 0);
* `df i = some none`: `X i = X (i-1) ^ p` (same level as `i-1`);
* `df i = some (some (a, b))`: `X i = ⁅X a, X b⁆` with `b` a core position and level `lv a + 1`.
Core positions carry a core index `cidx`; level-1 positions carry a step `st`.
Recorded relations: all `p`-th powers; commutators of level-0 pairs; commutators of a level-1
position `i` with core positions of core index `≤ st i`; commutators of a position of level `≥ 2`
with every core position. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section Code

/-- A shape on `m` positions: level, definition, core index, step. -/
abbrev Shape (m : ℕ) : Type :=
  (Fin m → Fin (m + 1)) × (Fin m → Option (Option (Fin m × Fin m))) ×
    (Fin m → Option (Fin m)) × (Fin m → Fin m)

variable {m : ℕ}

/-- Level (0-based weight). -/
def Shape.lv (s : Shape m) (i : Fin m) : ℕ := s.1 i

/-- Definition of a position. -/
def Shape.df (s : Shape m) (i : Fin m) : Option (Option (Fin m × Fin m)) := s.2.1 i

/-- Core index (`none` off the core). -/
def Shape.cidx (s : Shape m) (i : Fin m) : Option (Fin m) := s.2.2.1 i

/-- Step of a level-1 position. -/
def Shape.st (s : Shape m) (i : Fin m) : ℕ := s.2.2.2 i

/-- Number of core positions. -/
def Shape.ncore (s : Shape m) : ℕ := Nat.card {i : Fin m // (s.cidx i).isSome}

/-- Number of positions of level `< w`; by monotonicity the positions of level `≥ w` are the
suffix starting here. -/
def Shape.start (s : Shape m) (w : ℕ) : ℕ := Nat.card {i : Fin m // s.lv i < w}

/-- Validity conditions V1 to V6. -/
structure Shape.Valid (s : Shape m) : Prop where
  mono : ∀ i j : Fin m, i ≤ j → s.lv i ≤ s.lv j
  free : ∀ i, s.df i = none → s.lv i = 0
  pow : ∀ i, s.df i = some none → ∃ h : 0 < i.val,
    s.lv ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ = s.lv i ∧ (s.lv i = 1 → s.st i = s.st ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)
  comm : ∀ i a b, s.df i = some (some (a, b)) →
    a < i ∧ b < i ∧ (s.cidx b).isSome ∧ s.lv i = s.lv a + 1 ∧
      (s.lv i = 1 → ∃ ka kb : Fin m, s.cidx a = some ka ∧ s.cidx b = some kb ∧ ka < kb ∧
        kb.val = s.st i)
  core : ∀ i (k : Fin m), s.cidx i = some k → s.df i = none ∧ k.val < s.ncore
  core_inj : ∀ i j (k : Fin m), s.cidx i = some k → s.cidx j = some k → i = j
  steps : ∀ β, 1 ≤ β → β < s.ncore → ∃ i, s.lv i = 1 ∧ s.st i = β
  st_range : ∀ i, s.lv i = 1 → 1 ≤ s.st i ∧ s.st i < s.ncore

/-- Index predicate. Kind `0`: power relations; `1`: level-0 pairs; `2`: level 1 against core;
`3`: level `≥ 2` against core. The last coordinate is the column (position of the exponent). -/
def Shape.IdxP (s : Shape m) : Fin 4 × Fin m × Fin m × Fin m → Prop
  | (κ, i, k, j) =>
    (κ.val = 0 ∧ k = i ∧ i < j) ∨
    (κ.val = 1 ∧ s.lv i = 0 ∧ s.lv k = 0 ∧ i < k ∧ 1 ≤ s.lv j) ∨
    (κ.val = 2 ∧ s.lv i = 1 ∧ (∃ c : Fin m, s.cidx k = some c ∧ c.val ≤ s.st i) ∧ 2 ≤ s.lv j) ∨
    (κ.val = 3 ∧ 2 ≤ s.lv i ∧ (s.cidx k).isSome ∧ s.lv i + 1 ≤ s.lv j)

/-- The index set of a shape. -/
def Shape.Idx (s : Shape m) : Type := {q : Fin 4 × Fin m × Fin m × Fin m // s.IdxP q}

instance (s : Shape m) : Finite s.Idx := Subtype.finite

/-- Codes: a valid shape and an exponent below `p` for every index. -/
def Code (p m : ℕ) : Type := Σ s : {s : Shape m // s.Valid}, (s.1.Idx → Fin p)

instance (p m : ℕ) : Finite (Code p m) := by
  unfold Code
  infer_instance

open Classical in
/-- Exponent of column `j` in the relation of kind `κ` for the pair `(i, k)`; `0` off the index set. -/
noncomputable def Code.ex {p m : ℕ} (c : Code p m) (κ : Fin 4) (i k : Fin m) (j : ℕ) : ℕ :=
  if h : ∃ hj : j < m, c.1.1.IdxP (κ, i, k, ⟨j, hj⟩) then
    (c.2 ⟨(κ, i, k, ⟨j, h.1⟩), h.2⟩ : ℕ)
  else 0

/-- `(G, X)` realises the code `c`. -/
def Realizes {p m : ℕ} {G : Type u} [Group G] (X : Fin m → G) (c : Code p m) : Prop :=
  Nat.card G = p ^ m ∧
  Subgroup.closure (Set.range X) = ⊤ ∧
  (∀ i, c.1.1.df i = some none → ∀ h : 0 < i.val, X i = X ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ ^ p) ∧
  (∀ i a b, c.1.1.df i = some (some (a, b)) → X i = ⁅X a, X b⁆) ∧
  (∀ i, X i ^ p = nf ((List.ofFn X).drop (i.val + 1)) (fun j => c.ex 0 i i (i.val + 1 + j))) ∧
  (∀ i k, c.1.1.lv i = 0 → c.1.1.lv k = 0 → i < k →
    ⁅X i, X k⁆ = nf ((List.ofFn X).drop (c.1.1.start 1)) (fun j => c.ex 1 i k (c.1.1.start 1 + j))) ∧
  (∀ i k (κ : Fin m), c.1.1.lv i = 1 → c.1.1.cidx k = some κ → κ.val ≤ c.1.1.st i →
    ⁅X i, X k⁆ = nf ((List.ofFn X).drop (c.1.1.start 2)) (fun j => c.ex 2 i k (c.1.1.start 2 + j))) ∧
  (∀ i k, 2 ≤ c.1.1.lv i → (c.1.1.cidx k).isSome →
    ⁅X i, X k⁆ = nf ((List.ofFn X).drop (c.1.1.start (c.1.1.lv i + 1)))
      (fun j => c.ex 3 i k (c.1.1.start (c.1.1.lv i + 1) + j)))

end Code

end OMA.SimsLite
