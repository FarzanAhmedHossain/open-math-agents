import H2Dev.Code
import H2Dev.Stmt

/-! Theorem E (existence): every group of order `p ^ m` realises some code.

Construction (0-based levels). Layer `w` is the greedy fold `layer` of a candidate list
`cands w` relative to `lcs G (w + 1)`: each candidate `c` contributes the chain
`c, c ^ p, c ^ (p ^ 2), ...` of length `log_p [K ⊔ ⟨c⟩ : K]`, where `K` is the closure of the
later candidates together with `lcs G (w + 1)`. The final list is `full m`, the concatenation of
the layers `0, ..., m - 1`; entries carry their level, definition, core index and step.
* `cands 0`: all elements of `G` (free), then the core `u (t - 1), ..., u 0`;
* `cands 1`: blocks `β = t - 1, ..., 1`, block `β` being `⁅u a, u β⁆` for `a < β`;
* `cands (w + 2)`: `⁅y, u b⁆` for every entry `y` of layer `w + 1` and every `b < t`.
The list invariants are collected in `LGood`; `realizes_of_good` turns them into a code. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

/-! ## Tagged positions -/

section Ent

/-- A tagged position: element, level, definition, core index and step. -/
structure Ent (G : Type u) where
  g : G
  lv : ℕ
  df : Option (Option (ℕ × ℕ))
  ci : Option ℕ
  st : ℕ

variable {G : Type u} [Group G]

/-- The default entry, used by the total accessor `ent`. -/
def Ent.dft : Ent G := ⟨1, 0, none, none, 0⟩

/-- Total accessor for lists of entries. -/
def ent (L : List (Ent G)) (i : ℕ) : Ent G := L.getD i Ent.dft

lemma ent_eq (L : List (Ent G)) {i : ℕ} (h : i < L.length) : ent L i = L[i] :=
  List.getD_eq_getElem L Ent.dft h

lemma ent_append_left (L M : List (Ent G)) {i : ℕ} (h : i < L.length) :
    ent (L ++ M) i = ent L i :=
  List.getD_append L M Ent.dft i h

lemma ent_append_right (L M : List (Ent G)) {i : ℕ} (h : L.length ≤ i) :
    ent (L ++ M) i = ent M (i - L.length) :=
  List.getD_append_right L M Ent.dft i h

lemma ent_mem (L : List (Ent G)) {i : ℕ} (h : i < L.length) : ent L i ∈ L := by
  rw [ent_eq L h]
  exact List.getElem_mem h

lemma exists_ent_of_mem {L : List (Ent G)} {e : Ent G} (h : e ∈ L) :
    ∃ i < L.length, ent L i = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, ent_eq L hi⟩

lemma cl_append (l l' : List G) : cl (l ++ l') = cl l ⊔ cl l' := by
  simp only [cl_def]
  rw [← Subgroup.closure_union]
  congr 1
  ext x
  simp

lemma cl_cons (x : G) (l : List G) : cl (x :: l) = Subgroup.zpowers x ⊔ cl l := by
  simp only [cl_def]
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext y
  simp

end Ent

/-! ## Greedy chains and layers (Lemma G) -/

section Greedy

variable {G : Type u} [Group G]

/-- Chain length of `x` over `K`: `log_p [K ⊔ ⟨x⟩ : K]`. -/
noncomputable def clen (p : ℕ) (K : Subgroup G) (x : G) : ℕ :=
  Nat.log p (K.relIndex (K ⊔ Subgroup.zpowers x))

/-- The chain `c, c ^ p, ..., c ^ (p ^ (n - 1))`; non-initial entries are powers. -/
def chainE (p n : ℕ) (c : Ent G) : List (Ent G) :=
  (List.range n).map fun e => if e = 0 then c else ⟨c.g ^ (p ^ e), c.lv, some none, none, c.st⟩

/-- The greedy layer: the chain of each candidate is taken over the closure of the later
candidates together with `N`. -/
noncomputable def layer (p : ℕ) (N : Subgroup G) : List (Ent G) → List (Ent G)
  | [] => []
  | c :: C => chainE p (clen p (cl (C.map Ent.g) ⊔ N) c.g) c ++ layer p N C

@[simp] lemma layer_nil (p : ℕ) (N : Subgroup G) : layer p N ([] : List (Ent G)) = [] := rfl

lemma layer_cons (p : ℕ) (N : Subgroup G) (c : Ent G) (C : List (Ent G)) :
    layer p N (c :: C) = chainE p (clen p (cl (C.map Ent.g) ⊔ N) c.g) c ++ layer p N C := rfl

lemma length_chainE (p n : ℕ) (c : Ent G) : (chainE p n c).length = n := by
  simp [chainE]

lemma ent_chainE (p n : ℕ) (c : Ent G) {e : ℕ} (he : e < n) :
    ent (chainE p n c) e = if e = 0 then c else ⟨c.g ^ (p ^ e), c.lv, some none, none, c.st⟩ := by
  rw [ent_eq (chainE p n c) (by rw [length_chainE]; exact he)]
  simp [chainE]

lemma g_ent_chainE (p n : ℕ) (c : Ent G) {e : ℕ} (he : e < n) :
    (ent (chainE p n c) e).g = c.g ^ (p ^ e) := by
  rw [ent_chainE p n c he]
  by_cases h : e = 0
  · rw [if_pos h, h, pow_zero, pow_one]
  · rw [if_neg h]

/-- `layer p N C` is a suffix of `layer p N (A ++ C)`. -/
lemma layer_append (p : ℕ) (N : Subgroup G) (A C : List (Ent G)) :
    ∃ P, layer p N (A ++ C) = P ++ layer p N C := by
  induction A with
  | nil => exact ⟨[], rfl⟩
  | cons a A ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨chainE p (clen p (cl ((A ++ C).map Ent.g) ⊔ N) a.g) a ++ P, ?_⟩
    rw [List.cons_append, layer_cons, hP, List.append_assoc]

/-- Every entry of a layer is a candidate or a power entry derived from one. -/
lemma layer_src (p : ℕ) (N : Subgroup G) (C : List (Ent G)) :
    ∀ e ∈ layer p N C, ∃ c ∈ C, ∃ k : ℕ, e.g = c.g ^ k ∧ e.lv = c.lv ∧ e.st = c.st ∧
      (e = c ∨ (e.df = some none ∧ e.ci = none)) := by
  induction C with
  | nil => intro e he; simp at he
  | cons c C ih =>
    intro e he
    rw [layer_cons, List.mem_append] at he
    rcases he with he | he
    · simp only [chainE, List.mem_map, List.mem_range] at he
      obtain ⟨j, -, rfl⟩ := he
      refine ⟨c, List.mem_cons_self .., ?_⟩
      by_cases hj : j = 0
      · rw [if_pos hj]
        exact ⟨1, (pow_one _).symm, rfl, rfl, Or.inl rfl⟩
      · rw [if_neg hj]
        exact ⟨p ^ j, rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · obtain ⟨c', hc', k, h1, h2, h3, h4⟩ := ih e he
      exact ⟨c', List.mem_cons_of_mem _ hc', k, h1, h2, h3, h4⟩

/-- Power entries of a layer follow the previous entry of the same chain. -/
lemma layer_pow (p : ℕ) (N : Subgroup G) (C : List (Ent G)) (hC : ∀ c ∈ C, c.df ≠ some none) :
    ∀ r < (layer p N C).length, (ent (layer p N C) r).df = some none →
      0 < r ∧ (ent (layer p N C) (r - 1)).lv = (ent (layer p N C) r).lv ∧
      (ent (layer p N C) (r - 1)).st = (ent (layer p N C) r).st ∧
      (ent (layer p N C) r).g = (ent (layer p N C) (r - 1)).g ^ p := by
  sorry

variable [Finite G] {p m : ℕ}

/-- G1: chain lengths are exact `p`-power indices. -/
lemma clen_spec (hp : p.Prime) (hG : Nat.card G = p ^ m) (K : Subgroup G) [K.Normal] (x : G) :
    p ^ clen p K x = K.relIndex (K ⊔ Subgroup.zpowers x) ∧ x ^ (p ^ clen p K x) ∈ K ∧
      (clen p K x = 0 → x ∈ K) := by
  sorry

/-- Y3: a layer generates the same subgroup as its candidates, modulo `lcs G (w + 1)`. -/
lemma layer_sup (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (C : List (Ent G))
    (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    cl ((layer p (lcs G (w + 1)) C).map Ent.g) ⊔ lcs G (w + 1) =
      cl (C.map Ent.g) ⊔ lcs G (w + 1) := by
  sorry

/-- Y4: the length of a layer is the `p`-logarithm of the index it covers. -/
lemma layer_card (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (C : List (Ent G))
    (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    p ^ (layer p (lcs G (w + 1)) C).length =
      (lcs G (w + 1)).relIndex (cl (C.map Ent.g) ⊔ lcs G (w + 1)) := by
  sorry

/-- Y2: `p`-th powers of layer entries lie in the later entries modulo `lcs G (w + 1)`. -/
lemma layer_powrel (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (C : List (Ent G))
    (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    ∀ r < (layer p (lcs G (w + 1)) C).length,
      (ent (layer p (lcs G (w + 1)) C) r).g ^ p ∈
        cl (((layer p (lcs G (w + 1)) C).map Ent.g).drop (r + 1)) ⊔ lcs G (w + 1) := by
  sorry

/-- Y5 (head form): a candidate outside the closure of the later ones keeps its head. -/
lemma layer_mem_head (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (A C : List (Ent G))
    (c : Ent G) (hC : ∀ x ∈ A ++ c :: C, x.g ∈ lcs G w)
    (hc : c.g ∉ cl (C.map Ent.g) ⊔ lcs G (w + 1)) :
    c ∈ layer p (lcs G (w + 1)) (A ++ c :: C) := by
  sorry

/-- Y5 (block form): if a block enlarges the closure, one of its heads survives. -/
lemma layer_head_of_ne (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (B C : List (Ent G))
    (hC : ∀ x ∈ B ++ C, x.g ∈ lcs G w)
    (hne : cl ((B ++ C).map Ent.g) ⊔ lcs G (w + 1) ≠ cl (C.map Ent.g) ⊔ lcs G (w + 1)) :
    ∃ c ∈ B, c ∈ layer p (lcs G (w + 1)) (B ++ C) := by
  sorry

/-- Lemma K: a group of order `p ^ m` has `lcs G m = ⊥`. -/
lemma lcs_eq_bot_of_card (hp : p.Prime) (hG : Nat.card G = p ^ m) : lcs G m = ⊥ := by
  sorry

end Greedy

/-! ## Shapes: suffix cuts -/

section ShapeCut

lemma Shape.start_le {m : ℕ} (s : Shape m) (w : ℕ) : s.start w ≤ m := by
  sorry

/-- For a monotone shape, the positions of level `< w` are exactly those below `start w`. -/
lemma Shape.lt_start_iff {m : ℕ} (s : Shape m) (hmono : ∀ i j : Fin m, i ≤ j → s.lv i ≤ s.lv j)
    (w : ℕ) (i : Fin m) : i.val < s.start w ↔ s.lv i < w := by
  sorry

end ShapeCut

/-! ## From a layout to a code (exponents, R2 to R5) -/

section Layout

variable {G : Type u} [Group G]

/-- A tuple with a valid shape whose levels are compatible with the lower central series
realises a code; the exponents are read off from `nf_surj`. -/
theorem realizes_of_layout {p m : ℕ} (hp : 0 < p) (hG : Nat.card G = p ^ m) (X : Fin m → G)
    (s : Shape m) (hs : s.Valid)
    (hpowdef : ∀ i, s.df i = some none → ∀ h : 0 < i.val,
      X i = X ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ ^ p)
    (hcommdef : ∀ i a b, s.df i = some (some (a, b)) → X i = ⁅X a, X b⁆)
    (hmem : ∀ i, X i ∈ lcs G (s.lv i))
    (hspan : ∀ w, lcs G w ≤ cl ((List.ofFn X).drop (s.start w)))
    (hpow : ∀ i : Fin m, X i ^ p ∈ cl ((List.ofFn X).drop (i.val + 1))) :
    ∃ c : Code p m, Realizes X c := by
  sorry

end Layout

/-! ## From good lists of entries to layouts -/

section Good

variable {G : Type u} [Group G]

/-- List-level form of V1 to V6, R1 and the generation facts, for a list of entries. -/
structure LGood (p t : ℕ) (pos : ℕ → ℕ) (L : List (Ent G)) : Prop where
  lv_lt : ∀ i < L.length, (ent L i).lv < L.length
  mono : ∀ i j, i ≤ j → j < L.length → (ent L i).lv ≤ (ent L j).lv
  free : ∀ i < L.length, (ent L i).df = none → (ent L i).lv = 0
  pow : ∀ i < L.length, (ent L i).df = some none → 0 < i ∧
    (ent L (i - 1)).lv = (ent L i).lv ∧ (ent L (i - 1)).st = (ent L i).st ∧
    (ent L i).g = (ent L (i - 1)).g ^ p
  comm : ∀ i < L.length, ∀ a b, (ent L i).df = some (some (a, b)) → a < i ∧ b < i ∧
    (∃ κ < t, b = pos κ) ∧ (ent L i).lv = (ent L a).lv + 1 ∧
    ((ent L i).lv = 1 → ∃ ka kb, ka < kb ∧ kb < t ∧ a = pos ka ∧ b = pos kb ∧
      kb = (ent L i).st) ∧
    (ent L i).g = ⁅(ent L a).g, (ent L b).g⁆
  core : ∀ κ < t, pos κ < L.length ∧ (ent L (pos κ)).ci = some κ
  ci : ∀ i < L.length, ∀ κ, (ent L i).ci = some κ → κ < t ∧ (ent L i).df = none
  steps : ∀ β, 1 ≤ β → β < t → ∃ i < L.length, (ent L i).lv = 1 ∧ (ent L i).st = β
  st_range : ∀ i < L.length, (ent L i).lv = 1 → 1 ≤ (ent L i).st ∧ (ent L i).st < t
  mem : ∀ i < L.length, (ent L i).g ∈ lcs G (ent L i).lv
  span : ∀ w k, k ≤ L.length → (∀ i < L.length, i < k ↔ (ent L i).lv < w) →
    lcs G w ≤ cl ((L.map Ent.g).drop k)
  powrel : ∀ i < L.length, (ent L i).g ^ p ∈ cl ((L.map Ent.g).drop (i + 1))

/-- The shape read off from a list of entries (values are clamped into range; the clamps are
inactive for good lists of length `m`). -/
def shapeOf (m : ℕ) (pos : ℕ → ℕ) (L : List (Ent G)) : Shape m :=
  (fun i => ⟨min (ent L i.val).lv m, by omega⟩,
   fun i => (ent L i.val).df.map (Option.map fun ab =>
     (⟨min ab.1 (m - 1), by have := i.isLt; omega⟩, ⟨min ab.2 (m - 1), by have := i.isLt; omega⟩)),
   fun i => (ent L i.val).ci.bind fun κ =>
     if pos κ = i.val then some ⟨min κ (m - 1), by have := i.isLt; omega⟩ else none,
   fun i => ⟨min (ent L i.val).st (m - 1), by have := i.isLt; omega⟩)

/-- The tuple read off from a list of entries. -/
def Xof (m : ℕ) (L : List (Ent G)) : Fin m → G := fun i => (ent L i.val).g

variable {p t m : ℕ} {pos : ℕ → ℕ} {L : List (Ent G)}

lemma ofFn_Xof (hlen : L.length = m) : List.ofFn (Xof m L) = L.map Ent.g := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, Xof]
    rw [ent_eq L (by simpa using h2)]

lemma shapeOf_lv (hL : LGood p t pos L) (hlen : L.length = m) (i : Fin m) :
    (shapeOf m pos L).lv i = (ent L i.val).lv := by
  have h := hL.lv_lt i.val (by omega)
  show min (ent L i.val).lv m = (ent L i.val).lv
  omega

/-- V1 to V6 for the shape of a good list. -/
lemma shapeOf_valid (hL : LGood p t pos L) (hlen : L.length = m) : (shapeOf m pos L).Valid := by
  sorry

lemma Xof_pow (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ i, (shapeOf m pos L).df i = some none → ∀ h : 0 < i.val,
      Xof m L i = Xof m L ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ ^ p := by
  sorry

lemma Xof_comm (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ i a b, (shapeOf m pos L).df i = some (some (a, b)) → Xof m L i = ⁅Xof m L a, Xof m L b⁆ := by
  sorry

lemma Xof_mem (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ i, Xof m L i ∈ lcs G ((shapeOf m pos L).lv i) := by
  intro i
  rw [shapeOf_lv hL hlen]
  exact hL.mem i.val (by omega)

lemma Xof_span (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ w, lcs G w ≤ cl ((List.ofFn (Xof m L)).drop ((shapeOf m pos L).start w)) := by
  intro w
  rw [ofFn_Xof hlen]
  refine hL.span w _ (by rw [hlen]; exact Shape.start_le _ w) fun i hi => ?_
  have h := Shape.lt_start_iff _ (shapeOf_valid hL hlen).mono w ⟨i, by omega⟩
  rw [shapeOf_lv hL hlen] at h
  exact h

lemma Xof_powrel (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ i : Fin m, Xof m L i ^ p ∈ cl ((List.ofFn (Xof m L)).drop (i.val + 1)) := by
  intro i
  rw [ofFn_Xof hlen]
  exact hL.powrel i.val (by omega)

/-- A good list of length `m` in a group of order `p ^ m` yields a realised code. -/
theorem realizes_of_good (hp : 0 < p) (hG : Nat.card G = p ^ m) (hL : LGood p t pos L)
    (hlen : L.length = m) : ∃ (X : Fin m → G) (c : Code p m), Realizes X c := by
  obtain ⟨c, hc⟩ := realizes_of_layout hp hG (Xof m L) (shapeOf m pos L) (shapeOf_valid hL hlen)
    (Xof_pow hL hlen) (Xof_comm hL hlen) (Xof_mem hL hlen) (Xof_span hL hlen) (Xof_powrel hL hlen)
  exact ⟨Xof m L, c, hc⟩

end Good

/-! ## The construction -/

/-- Data of the construction: the prime, the core length and core, and an enumeration of `G`. -/
structure Dat (G : Type u) where
  p : ℕ
  t : ℕ
  u : ℕ → G
  en : List G

namespace Dat

variable {G : Type u} [Group G]

/-- The entry of the core element `u κ`. -/
def coreE (d : Dat G) (κ : ℕ) : Ent G := ⟨d.u κ, 0, none, some κ, 0⟩

/-- Layer-0 candidates: all elements (free), then the core `u (t - 1), ..., u 0`. -/
def cand0 (d : Dat G) : List (Ent G) :=
  d.en.map (fun x => (⟨x, 0, none, none, 0⟩ : Ent G)) ++ (List.range d.t).reverse.map d.coreE

/-- Layer 0. -/
noncomputable def Y0 (d : Dat G) : List (Ent G) := layer d.p (lcs G 1) d.cand0

/-- Position of the core element `u κ` in layer 0. -/
noncomputable def pos (d : Dat G) (κ : ℕ) : ℕ := d.Y0.findIdx fun e => decide (e.ci = some κ)

/-- Block `β` of layer-1 candidates: `⁅u a, u β⁆` for `a < β`, with step `β`. -/
noncomputable def block (d : Dat G) (β : ℕ) : List (Ent G) :=
  (List.range β).map fun a =>
    (⟨⁅d.u a, d.u β⁆, 1, some (some (d.pos a, d.pos β)), none, β⟩ : Ent G)

/-- Layer-1 candidates: blocks `t - 1, ..., 0` (block `0` is empty). -/
noncomputable def cand1 (d : Dat G) : List (Ent G) := (List.range d.t).reverse.flatMap d.block

/-- Candidates of level `w ≥ 2`: `⁅y, u b⁆` for the entries `y` of the previous layer, which
starts at position `o`. -/
noncomputable def commC (d : Dat G) (w : ℕ) : ℕ → List (Ent G) → List (Ent G)
  | _, [] => []
  | o, y :: Y => (List.range d.t).map (fun b =>
      (⟨⁅y.g, d.u b⁆, w, some (some (o, d.pos b)), none, 0⟩ : Ent G)) ++ commC d w (o + 1) Y

/-- Layer `w` together with its starting position. -/
noncomputable def lay (d : Dat G) : ℕ → List (Ent G) × ℕ
  | 0 => (d.Y0, 0)
  | 1 => (layer d.p (lcs G 2) d.cand1, d.Y0.length)
  | w + 2 => (layer d.p (lcs G (w + 3)) (d.commC (w + 2) (lay d (w + 1)).2 (lay d (w + 1)).1),
      (lay d (w + 1)).2 + (lay d (w + 1)).1.length)

/-- Layer `w`. -/
noncomputable def Y (d : Dat G) (w : ℕ) : List (Ent G) := (d.lay w).1

/-- Starting position of layer `w`. -/
noncomputable def off (d : Dat G) (w : ℕ) : ℕ := (d.lay w).2

/-- Candidates of layer `w`. -/
noncomputable def cands (d : Dat G) : ℕ → List (Ent G)
  | 0 => d.cand0
  | 1 => d.cand1
  | w + 2 => d.commC (w + 2) (d.off (w + 1)) (d.Y (w + 1))

/-- Layers `0, ..., n - 1`. -/
noncomputable def full (d : Dat G) : ℕ → List (Ent G)
  | 0 => []
  | n + 1 => full d n ++ d.Y n

lemma Y_eq (d : Dat G) (w : ℕ) : d.Y w = layer d.p (lcs G (w + 1)) (d.cands w) := by
  rcases w with _ | _ | w <;> rfl

lemma off_succ (d : Dat G) (w : ℕ) : d.off (w + 1) = d.off w + (d.Y w).length := by
  rcases w with _ | w
  · show d.Y0.length = 0 + d.Y0.length
    omega
  · rfl

lemma full_length (d : Dat G) (n : ℕ) : (d.full n).length = d.off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (d.full n ++ d.Y n).length = d.off (n + 1)
    rw [List.length_append, ih, off_succ]

/-- Hypotheses on the data. -/
structure Hyp (d : Dat G) (m : ℕ) : Prop where
  prime : d.p.Prime
  card : Nat.card G = d.p ^ m
  t_ne : d.t ≠ 1
  strict : StrictChain d.u d.t
  top : lcs G 1 ≤ Wk d.u d.t
  en : ∀ x, x ∈ d.en

/-! ### Candidates (no hypotheses needed) -/

lemma cands_lv (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, c.lv = w := by
  sorry

lemma cands_df (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, c.df ≠ some none ∧ (c.df = none → w = 0) := by
  sorry

lemma cands_ci (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, ∀ κ, c.ci = some κ →
    κ < d.t ∧ c.g = d.u κ ∧ c.df = none := by
  sorry

lemma cands_st (d : Dat G) : ∀ c ∈ d.cands 1, 1 ≤ c.st ∧ c.st < d.t := by
  sorry

lemma mem_commC (d : Dat G) (w o : ℕ) (Y : List (Ent G)) (c : Ent G) :
    c ∈ d.commC w o Y ↔ ∃ r < Y.length, ∃ b < d.t,
      c = ⟨⁅(ent Y r).g, d.u b⁆, w, some (some (o + r, d.pos b)), none, 0⟩ := by
  sorry

lemma mem_cand1 (d : Dat G) (c : Ent G) : c ∈ d.cand1 ↔ ∃ a b, a < b ∧ b < d.t ∧
    c = ⟨⁅d.u a, d.u b⁆, 1, some (some (d.pos a, d.pos b)), none, b⟩ := by
  sorry

/-! ### Layers and the full list (no hypotheses needed) -/

lemma Y_lv (d : Dat G) : ∀ w, ∀ e ∈ d.Y w, e.lv = w := by
  sorry

lemma Y_ci (d : Dat G) : ∀ w, ∀ e ∈ d.Y w, ∀ κ, e.ci = some κ →
    κ < d.t ∧ e.g = d.u κ ∧ e.df = none := by
  sorry

lemma off_mono (d : Dat G) {v w : ℕ} (h : v ≤ w) : d.off v ≤ d.off w := by
  sorry

lemma full_prefix (d : Dat G) {n n' : ℕ} (h : n ≤ n') {i : ℕ} (hi : i < d.off n) :
    ent (d.full n') i = ent (d.full n) i := by
  sorry

lemma ent_full (d : Dat G) {n w r : ℕ} (hw : w < n) (hr : r < (d.Y w).length) :
    ent (d.full n) (d.off w + r) = ent (d.Y w) r := by
  sorry

lemma locate (d : Dat G) {n i : ℕ} (hi : i < (d.full n).length) :
    ∃ w < n, ∃ r < (d.Y w).length, i = d.off w + r := by
  sorry

lemma full_cut (d : Dat G) (n : ℕ) {i : ℕ} (hi : i < (d.full n).length) {v : ℕ} (hv : v ≤ n) :
    i < d.off v ↔ (ent (d.full n) i).lv < v := by
  sorry

/-! ### Generic fields of `LGood` for `full n` -/

lemma good_mono (d : Dat G) (n : ℕ) :
    ∀ i j, i ≤ j → j < (d.full n).length → (ent (d.full n) i).lv ≤ (ent (d.full n) j).lv := by
  sorry

lemma good_free (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).df = none → (ent (d.full n) i).lv = 0 := by
  sorry

lemma good_pow (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).df = some none → 0 < i ∧
      (ent (d.full n) (i - 1)).lv = (ent (d.full n) i).lv ∧
      (ent (d.full n) (i - 1)).st = (ent (d.full n) i).st ∧
      (ent (d.full n) i).g = (ent (d.full n) (i - 1)).g ^ d.p := by
  sorry

lemma good_ci (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, ∀ κ, (ent (d.full n) i).ci = some κ → κ < d.t ∧
      (ent (d.full n) i).df = none := by
  sorry

lemma good_st (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).lv = 1 → 1 ≤ (ent (d.full n) i).st ∧
      (ent (d.full n) i).st < d.t := by
  sorry

/-! ### Facts needing the hypotheses -/

variable [Finite G] {m : ℕ}

lemma cands_mem {d : Dat G} (hd : d.Hyp m) : ∀ w, ∀ c ∈ d.cands w, c.g ∈ lcs G w := by
  sorry

lemma Y_mem {d : Dat G} (hd : d.Hyp m) : ∀ w, ∀ e ∈ d.Y w, e.g ∈ lcs G w := by
  sorry

lemma core_Y0 {d : Dat G} (hd : d.Hyp m) :
    ∀ κ < d.t, d.pos κ < d.Y0.length ∧ (ent d.Y0 (d.pos κ)).ci = some κ := by
  sorry

lemma Y_nil {d : Dat G} (hd : d.Hyp m) {w : ℕ} (hw : m ≤ w) : d.Y w = [] := by
  sorry

lemma steps_Y1 {d : Dat G} (hd : d.Hyp m) :
    ∀ β, 1 ≤ β → β < d.t → ∃ e ∈ d.Y 1, e.lv = 1 ∧ e.st = β := by
  sorry

/-- Theorem L applied in `G`: each layer generates `lcs G w` modulo `lcs G (w + 1)`. -/
lemma lie_app {d : Dat G} (hd : d.Hyp m) :
    ∀ w, lcs G w ≤ cl ((d.Y w).map Ent.g) ⊔ lcs G (w + 1) := by
  sorry

lemma span_drop {d : Dat G} (hd : d.Hyp m) :
    ∀ v ≤ m, lcs G v = cl (((d.full m).map Ent.g).drop (d.off v)) := by
  sorry

lemma card_drop {d : Dat G} (hd : d.Hyp m) :
    ∀ v ≤ m, Nat.card (lcs G v) = d.p ^ ((d.full m).length - d.off v) := by
  sorry

lemma full_length_eq {d : Dat G} (hd : d.Hyp m) : (d.full m).length = m := by
  sorry

/-! ### The fields of `LGood` for `full m` -/

lemma good_lv_lt {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, (ent (d.full m) i).lv < (d.full m).length := by
  sorry

lemma good_comm {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, ∀ a b, (ent (d.full m) i).df = some (some (a, b)) → a < i ∧ b < i ∧
      (∃ κ < d.t, b = d.pos κ) ∧ (ent (d.full m) i).lv = (ent (d.full m) a).lv + 1 ∧
      ((ent (d.full m) i).lv = 1 → ∃ ka kb, ka < kb ∧ kb < d.t ∧ a = d.pos ka ∧ b = d.pos kb ∧
        kb = (ent (d.full m) i).st) ∧
      (ent (d.full m) i).g = ⁅(ent (d.full m) a).g, (ent (d.full m) b).g⁆ := by
  sorry

lemma good_core {d : Dat G} (hd : d.Hyp m) :
    ∀ κ < d.t, d.pos κ < (d.full m).length ∧ (ent (d.full m) (d.pos κ)).ci = some κ := by
  sorry

lemma good_steps {d : Dat G} (hd : d.Hyp m) :
    ∀ β, 1 ≤ β → β < d.t → ∃ i < (d.full m).length, (ent (d.full m) i).lv = 1 ∧
      (ent (d.full m) i).st = β := by
  sorry

lemma good_mem {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, (ent (d.full m) i).g ∈ lcs G (ent (d.full m) i).lv := by
  sorry

lemma good_span {d : Dat G} (hd : d.Hyp m) :
    ∀ w k, k ≤ (d.full m).length → (∀ i < (d.full m).length, i < k ↔ (ent (d.full m) i).lv < w) →
      lcs G w ≤ cl (((d.full m).map Ent.g).drop k) := by
  sorry

lemma good_powrel {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, (ent (d.full m) i).g ^ d.p ∈
      cl (((d.full m).map Ent.g).drop (i + 1)) := by
  sorry

/-- All invariants of `full m`. -/
theorem good_full {d : Dat G} (hd : d.Hyp m) : LGood d.p d.t d.pos (d.full m) where
  lv_lt := good_lv_lt hd
  mono := good_mono d m
  free := good_free d m
  pow := good_pow d m
  comm := good_comm hd
  core := good_core hd
  ci := good_ci d m
  steps := good_steps hd
  st_range := good_st d m
  mem := good_mem hd
  span := good_span hd
  powrel := good_powrel hd

end Dat

/-! ## Theorem E -/

theorem existence {p : ℕ} (hp : p.Prime) (m : ℕ) (G : Type u) [Group G] [Finite G]
    (hG : Nat.card G = p ^ m) : ∃ (X : Fin m → G) (c : Code p m), Realizes X c := by
  obtain ⟨t, u, ht, hstr, htop⟩ := exists_strict_chain (G := G)
  haveI : Fintype G := Fintype.ofFinite G
  let d : Dat G := ⟨p, t, u, (Finset.univ : Finset G).toList⟩
  have hd : d.Hyp m := ⟨hp, hG, ht, hstr, htop, fun x => Finset.mem_toList.mpr (Finset.mem_univ x)⟩
  exact realizes_of_good hp.pos hG (Dat.good_full hd) (Dat.full_length_eq hd)

end OMA.SimsLite
