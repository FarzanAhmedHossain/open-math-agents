import H2Dev.Code
import H2Dev.Stmt
import Mathlib.Data.List.GetD

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

lemma cl_nil : cl ([] : List G) = ⊥ := by
  rw [cl_def, eq_bot_iff, Subgroup.closure_le]
  intro x hx
  simp at hx
lemma mem_sup_mid {A B N : Subgroup G} {x : G} (h : x ∈ B ⊔ N) : x ∈ A ⊔ B ⊔ N :=  (sup_le_sup_right (le_sup_right : B ≤ A ⊔ B) N) h

lemma cl_le_of_forall {l : List G} {H : Subgroup G} (h : ∀ x ∈ l, x ∈ H) : cl l ≤ H := by
  rw [cl_def, Subgroup.closure_le]
  exact fun x hx => h x hx

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

lemma chainE_zero (p : ℕ) (c : Ent G) : chainE p 0 c = [] := rfl

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

lemma head_mem_chainE (p : ℕ) {n : ℕ} (hn : 0 < n) (c : Ent G) : c ∈ chainE p n c := by
  have h := ent_mem (chainE p n c) (i := 0) (by rw [length_chainE]; exact hn)
  rwa [ent_chainE p n c hn, if_pos rfl] at h

lemma cl_chainE (p : ℕ) {n : ℕ} (hn : 0 < n) (c : Ent G) :
    cl ((chainE p n c).map Ent.g) = Subgroup.zpowers c.g := by
  apply le_antisymm
  · refine cl_le_of_forall fun y hy => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    obtain ⟨j, hj, rfl⟩ := exists_ent_of_mem he
    rw [length_chainE] at hj
    rw [g_ent_chainE p n c hj]
    exact pow_mem (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    exact mem_cl_of_mem (List.mem_map.mpr ⟨c, head_mem_chainE p hn c, rfl⟩)

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
      refine ⟨c, List.mem_cons_self, ?_⟩
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
  induction C with
  | nil => intro r hr; simp at hr
  | cons c C ih =>
    intro r hr hdf
    have hC' : ∀ c ∈ C, c.df ≠ some none := fun c' hc' => hC c' (List.mem_cons_of_mem _ hc')
    rw [layer_cons] at hr hdf ⊢
    set n := clen p (cl (C.map Ent.g) ⊔ N) c.g with hn
    have hlen : (chainE p n c).length = n := length_chainE p n c
    rw [List.length_append, hlen] at hr
    by_cases hrn : r < n
    · rw [ent_append_left (chainE p n c) (layer p N C) (by rw [hlen]; exact hrn),
        ent_chainE p n c hrn] at hdf
      have hr0 : r ≠ 0 := by
        intro h0
        rw [if_pos h0] at hdf
        exact hC c List.mem_cons_self hdf
      have hr1 : r - 1 < n := by omega
      rw [ent_append_left (chainE p n c) (layer p N C) (by rw [hlen]; exact hr1),
        ent_append_left (chainE p n c) (layer p N C) (by rw [hlen]; exact hrn),
        ent_chainE p n c hr1, ent_chainE p n c hrn, if_neg hr0]
      refine ⟨Nat.pos_of_ne_zero hr0, ?_, ?_, ?_⟩
      · split_ifs <;> rfl
      · split_ifs <;> rfl
      · split_ifs with h1
        · have h2 : r = 1 := by omega
          subst h2
          show c.g ^ p ^ 1 = c.g ^ p
          rw [pow_one]
        · show c.g ^ p ^ r = (c.g ^ p ^ (r - 1)) ^ p
          rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
    · push_neg at hrn
      rw [ent_append_right (chainE p n c) (layer p N C) (by rw [hlen]; exact hrn), hlen] at hdf
      have hr' : r - n < (layer p N C).length := by omega
      obtain ⟨h0, h1, h2, h3⟩ := ih hC' (r - n) hr' hdf
      have e1 : r - 1 - n = r - n - 1 := by omega
      rw [ent_append_right (chainE p n c) (layer p N C) (i := r) (by rw [hlen]; exact hrn),
        ent_append_right (chainE p n c) (layer p N C) (i := r - 1) (by rw [hlen]; omega), hlen, e1]
      exact ⟨by omega, h1, h2, h3⟩

/-- Subgroups between `lcs G (w + 1)` and `lcs G w` given by candidates are normal. -/
lemma normal_K (w : ℕ) (C : List (Ent G)) (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    (cl (C.map Ent.g) ⊔ lcs G (w + 1)).Normal := by
  refine normal_of_sandwich (n := w) le_sup_right
    (sup_le (cl_le_of_forall fun x hx => ?_) (lcs_antitone (Nat.le_succ w)))
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact hC c hc

variable [Finite G] {p m : ℕ}

/-- G1: chain lengths are exact `p`-power indices. -/
lemma clen_spec (hp : p.Prime) (hG : Nat.card G = p ^ m) (K : Subgroup G) [K.Normal] (x : G) :
    p ^ clen p K x = K.relIndex (K ⊔ Subgroup.zpowers x) ∧ x ^ (p ^ clen p K x) ∈ K ∧
      (clen p K x = 0 → x ∈ K) := by
  have hdvd : K.relIndex (K ⊔ Subgroup.zpowers x) ∣ p ^ m := by
    rw [← hG]
    exact (Subgroup.relIndex_dvd_card K _).trans (Subgroup.card_subgroup_dvd_card _)
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hclen : clen p K x = a := by
    rw [clen, ha, Nat.log_pow hp.one_lt]
  rw [hclen, ← ha]
  refine ⟨rfl, Subgroup.pow_relIndex_mem K (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)), ?_⟩
  intro h0
  rw [h0, pow_zero, Subgroup.relIndex_eq_one] at ha
  exact ha (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

/-- Y3: a layer generates the same subgroup as its candidates, modulo `lcs G (w + 1)`. -/
lemma layer_sup (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (C : List (Ent G))
    (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    cl ((layer p (lcs G (w + 1)) C).map Ent.g) ⊔ lcs G (w + 1) =
      cl (C.map Ent.g) ⊔ lcs G (w + 1) := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    have hC' : ∀ d ∈ C, d.g ∈ lcs G w := fun d hd => hC d (List.mem_cons_of_mem _ hd)
    haveI := normal_K w C hC'
    have e1 : cl ((layer p (lcs G (w + 1)) (c :: C)).map Ent.g) ⊔ lcs G (w + 1) =
        cl ((chainE p (clen p (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g) c).map Ent.g) ⊔
          (cl (C.map Ent.g) ⊔ lcs G (w + 1)) := by
      rw [layer_cons, List.map_append, cl_append, sup_assoc, ih hC']
    have e2 : cl ((c :: C).map Ent.g) ⊔ lcs G (w + 1) =
        Subgroup.zpowers c.g ⊔ (cl (C.map Ent.g) ⊔ lcs G (w + 1)) := by
      rw [List.map_cons, cl_cons, sup_assoc]
    rw [e1, e2]
    obtain ⟨-, -, h3⟩ := clen_spec hp hG (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g
    rcases Nat.eq_zero_or_pos (clen p (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g) with h0 | h0
    · rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr (h3 h0)), h0, chainE_zero, List.map_nil,
        cl_nil, bot_sup_eq]
    · rw [cl_chainE p h0 c]

/-- Y4: the length of a layer is the `p`-logarithm of the index it covers. -/
lemma layer_card (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (C : List (Ent G))
    (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    p ^ (layer p (lcs G (w + 1)) C).length =
      (lcs G (w + 1)).relIndex (cl (C.map Ent.g) ⊔ lcs G (w + 1)) := by
  induction C with
  | nil =>
    rw [layer_nil, List.length_nil, pow_zero, List.map_nil, cl_nil, bot_sup_eq,
      Subgroup.relIndex_self]
  | cons c C ih =>
    have hC' : ∀ d ∈ C, d.g ∈ lcs G w := fun d hd => hC d (List.mem_cons_of_mem _ hd)
    haveI := normal_K w C hC'
    obtain ⟨h1, -, -⟩ := clen_spec hp hG (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g
    rw [layer_cons, List.length_append, length_chainE, pow_add, h1, ih hC', mul_comm,
      Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right le_sup_left]
    congr 1
    rw [List.map_cons, cl_cons]
    ac_rfl

/-- Y2: `p`-th powers of layer entries lie in the later entries modulo `lcs G (w + 1)`. -/
lemma layer_powrel (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (C : List (Ent G))
    (hC : ∀ c ∈ C, c.g ∈ lcs G w) :
    ∀ r < (layer p (lcs G (w + 1)) C).length,
      (ent (layer p (lcs G (w + 1)) C) r).g ^ p ∈
        cl (((layer p (lcs G (w + 1)) C).map Ent.g).drop (r + 1)) ⊔ lcs G (w + 1) := by
  induction C with
  | nil => intro r hr; simp at hr
  | cons c C ih =>
    intro r hr
    have hC' : ∀ d ∈ C, d.g ∈ lcs G w := fun d hd => hC d (List.mem_cons_of_mem _ hd)
    haveI := normal_K w C hC'
    obtain ⟨-, h2, -⟩ := clen_spec hp hG (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g
    rw [layer_cons] at hr ⊢
    set n := clen p (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g with hn
    have hlen : (chainE p n c).length = n := length_chainE p n c
    rw [List.length_append, hlen] at hr
    have hdrop : cl (((chainE p n c ++ layer p (lcs G (w + 1)) C).map Ent.g).drop (r + 1)) =
        cl (((chainE p n c).map Ent.g).drop (r + 1)) ⊔
          cl (((layer p (lcs G (w + 1)) C).map Ent.g).drop (r + 1 - n)) := by
      rw [List.map_append, List.drop_append, cl_append, List.length_map, hlen]
    rw [hdrop]
    by_cases hrn : r < n
    · rw [ent_append_left (chainE p n c) _ (by rw [hlen]; exact hrn), g_ent_chainE p n c hrn,
        ← pow_mul, ← pow_succ]
      rcases Nat.lt_or_ge (r + 1) n with hr1 | hr1
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_cl_of_mem ?_))
        have hl : r + 1 < ((chainE p n c).map Ent.g).length := by
          rw [List.length_map, hlen]; exact hr1
        have hm := getElem_mem_drop ((chainE p n c).map Ent.g) (le_refl (r + 1)) hl
        rw [List.getElem_map, ← ent_eq (chainE p n c) (by rw [hlen]; exact hr1),
          g_ent_chainE p n c hr1] at hm
        exact hm
      · have hrn1 : r + 1 = n := by omega
        rw [hrn1, Nat.sub_self, List.drop_zero]
        have h' : c.g ^ p ^ n ∈ cl ((layer p (lcs G (w + 1)) C).map Ent.g) ⊔ lcs G (w + 1) := by
          rw [layer_sup hp hG w C hC']
          exact h2
        exact mem_sup_mid h'
    · push_neg at hrn
      have hr' : r - n < (layer p (lcs G (w + 1)) C).length := by omega
      rw [ent_append_right (chainE p n c) _ (by rw [hlen]; exact hrn), hlen]
      have h' := ih hC' (r - n) hr'
      rw [show r - n + 1 = r + 1 - n by omega] at h'
      exact mem_sup_mid h'

/-- Y5 (head form): a candidate outside the closure of the later ones keeps its head. -/
lemma layer_mem_head (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (A C : List (Ent G))
    (c : Ent G) (hC : ∀ x ∈ A ++ c :: C, x.g ∈ lcs G w)
    (hc : c.g ∉ cl (C.map Ent.g) ⊔ lcs G (w + 1)) :
    c ∈ layer p (lcs G (w + 1)) (A ++ c :: C) := by
  obtain ⟨P, hP⟩ := layer_append p (lcs G (w + 1)) A (c :: C)
  rw [hP, layer_cons]
  have hC' : ∀ x ∈ C, x.g ∈ lcs G w := fun x hx =>
    hC x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
  haveI := normal_K w C hC'
  obtain ⟨-, -, h3⟩ := clen_spec hp hG (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g
  have hpos : 0 < clen p (cl (C.map Ent.g) ⊔ lcs G (w + 1)) c.g :=
    Nat.pos_of_ne_zero fun h => hc (h3 h)
  exact List.mem_append_right _ (List.mem_append_left _ (head_mem_chainE p hpos c))

/-- Y5 (block form): if a block enlarges the closure, one of its heads survives. -/
lemma layer_head_of_ne (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ) (B C : List (Ent G))
    (hC : ∀ x ∈ B ++ C, x.g ∈ lcs G w)
    (hne : cl ((B ++ C).map Ent.g) ⊔ lcs G (w + 1) ≠ cl (C.map Ent.g) ⊔ lcs G (w + 1)) :
    ∃ c ∈ B, c ∈ layer p (lcs G (w + 1)) (B ++ C) := by
  induction B with
  | nil => exact (hne rfl).elim
  | cons b B ih =>
    have hC' : ∀ x ∈ B ++ C, x.g ∈ lcs G w := fun x hx => hC x (List.mem_cons_of_mem _ hx)
    haveI := normal_K w (B ++ C) hC'
    obtain ⟨-, -, h3⟩ := clen_spec hp hG (cl ((B ++ C).map Ent.g) ⊔ lcs G (w + 1)) b.g
    rw [List.cons_append, layer_cons]
    by_cases h0 : clen p (cl ((B ++ C).map Ent.g) ⊔ lcs G (w + 1)) b.g = 0
    · have e : cl ((b :: B ++ C).map Ent.g) ⊔ lcs G (w + 1) =
          cl ((B ++ C).map Ent.g) ⊔ lcs G (w + 1) := by
        rw [List.cons_append, List.map_cons, cl_cons, sup_assoc]
        exact sup_eq_right.mpr (Subgroup.zpowers_le.mpr (h3 h0))
      obtain ⟨c, hcB, hcl⟩ := ih hC' fun h => hne (e.trans h)
      exact ⟨c, List.mem_cons_of_mem _ hcB, List.mem_append_right _ hcl⟩
    · exact ⟨b, List.mem_cons_self,
        List.mem_append_left _ (head_mem_chainE p (Nat.pos_of_ne_zero h0) b)⟩

/-- Lemma K: a group of order `p ^ m` has `lcs G m = ⊥`. -/
lemma lcs_eq_bot_of_card (hp : p.Prime) (hG : Nat.card G = p ^ m) : lcs G m = ⊥ := by
  haveI := Fact.mk hp
  have hnil : Group.IsNilpotent G := (IsPGroup.of_card hG).isNilpotent
  obtain ⟨N, hN⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  have hN' : lcs G N = ⊥ := hN
  have key : ∀ w, lcs G w = ⊥ ∨ Nat.card (lcs G w) * p ^ w ≤ p ^ m := by
    intro w
    induction w with
    | zero =>
      right
      rw [lcs_zero, pow_zero, mul_one, Subgroup.card_top, hG]
    | succ w ih =>
      by_cases hb : lcs G (w + 1) = ⊥
      · exact Or.inl hb
      · right
        rcases ih with ih | ih
        · have h := lcs_antitone (D := G) (Nat.le_succ w)
          rw [ih] at h
          exact absurd (le_bot_iff.mp h) hb
        · have hlt : lcs G (w + 1) ≠ lcs G w := by
            intro heq
            have hconst : ∀ k, lcs G (w + k) = lcs G w := by
              intro k
              induction k with
              | zero => rfl
              | succ k ihk => rw [← Nat.add_assoc, lcs_succ, ihk, ← lcs_succ, heq]
            apply hb
            rw [heq, ← hconst N]
            have h := lcs_antitone (D := G) (Nat.le_add_left N w)
            rw [hN'] at h
            exact le_bot_iff.mp h
          have hdvd : (lcs G (w + 1)).relIndex (lcs G w) ∣ p ^ m := by
            rw [← hG]
            exact (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_subgroup_dvd_card _)
          obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp hdvd
          have ha1 : a ≠ 0 := by
            intro h0
            rw [h0, pow_zero, Subgroup.relIndex_eq_one] at ha
            exact hlt (le_antisymm (lcs_antitone (Nat.le_succ w)) ha)
          have hmul := Subgroup.relIndex_mul_relIndex ⊥ (lcs G (w + 1)) (lcs G w) bot_le
            (lcs_antitone (Nat.le_succ w))
          rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, ha] at hmul
          calc Nat.card (lcs G (w + 1)) * p ^ (w + 1)
              = Nat.card (lcs G (w + 1)) * p * p ^ w := by ring
            _ ≤ Nat.card (lcs G (w + 1)) * p ^ a * p ^ w := by
              gcongr
              exact Nat.le_self_pow ha1 p
            _ = Nat.card (lcs G w) * p ^ w := by rw [hmul]
            _ ≤ p ^ m := ih
  rcases key m with h | h
  · exact h
  · have hpos : 0 < p ^ m := pow_pos hp.pos m
    have h1 : Nat.card (lcs G m) ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by rw [one_mul]; exact h) hpos
    exact Subgroup.eq_bot_of_card_le _ h1

end Greedy

/-! ## Shapes: suffix cuts -/

section ShapeCut

lemma Shape.start_le {m : ℕ} (s : Shape m) (w : ℕ) : s.start w ≤ m := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {i : Fin m // s.lv i < w} → Fin m)
    Subtype.val_injective
  rw [Nat.card_fin] at h
  exact h

/-- For a monotone shape, the positions of level `< w` are exactly those below `start w`. -/
lemma Shape.lt_start_iff {m : ℕ} (s : Shape m) (hmono : ∀ i j : Fin m, i ≤ j → s.lv i ≤ s.lv j)
    (w : ℕ) (i : Fin m) : i.val < s.start w ↔ s.lv i < w := by
  constructor
  · intro hi
    by_contra hcon
    have hlt : ∀ j : {j : Fin m // s.lv j < w}, j.1.val < i.val := by
      intro j
      by_contra h
      have h1 := hmono i j.1 (Fin.le_def.mpr (by omega))
      have h2 := j.2
      omega
    have hle := Nat.card_le_card_of_injective
      (fun j : {j : Fin m // s.lv j < w} => (⟨j.1.val, hlt j⟩ : Fin i.val))
      (fun a b hab => Subtype.ext (Fin.ext (by simpa using hab)))
    rw [Nat.card_fin] at hle
    have h' : s.start w ≤ i.val := hle
    omega
  · intro hi
    have hle := Nat.card_le_card_of_injective
      (fun j : Fin (i.val + 1) => (⟨⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
        lt_of_le_of_lt (hmono _ i (Fin.le_def.mpr (by have := j.isLt; show j.val ≤ i.val; omega)))
          hi⟩ : {j : Fin m // s.lv j < w}))
      (fun a b hab => Fin.ext (by simpa using hab))
    rw [Nat.card_fin] at hle
    have h' : i.val + 1 ≤ s.start w := hle
    omega

end ShapeCut

/-! ## From a layout to a code (exponents, R2 to R5) -/

section Layout

variable {G : Type u} [Group G]

open Classical in
/-- Normal-form exponents of `x` over `l`, when they exist. -/
noncomputable def nfE (p : ℕ) (l : List G) (x : G) : ℕ → ℕ :=
  if h : ∃ e : ℕ → ℕ, (∀ k, e k < p) ∧ x = nf l e then Classical.choose h else fun _ => 0

lemma nfE_lt {p : ℕ} (hp : 0 < p) (l : List G) (x : G) (k : ℕ) : nfE p l x k < p := by
  unfold nfE
  by_cases h : ∃ e : ℕ → ℕ, (∀ k, e k < p) ∧ x = nf l e
  · rw [dif_pos h]
    exact (Classical.choose_spec h).1 k
  · rw [dif_neg h]
    exact hp

lemma nfE_spec {p : ℕ} {l : List G} {x : G} (h : ∃ e : ℕ → ℕ, (∀ k, e k < p) ∧ x = nf l e) :
    x = nf l (nfE p l x) := by
  unfold nfE
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

/-- Offset of the suffix used by the relation of kind `κ` at position `i`. -/
noncomputable def relOff {m : ℕ} (s : Shape m) (κ : Fin 4) (i : Fin m) : ℕ :=
  if κ.val = 0 then i.val + 1 else if κ.val = 1 then s.start 1 else if κ.val = 2 then s.start 2
  else s.start (s.lv i + 1)

/-- Left-hand side of the relation of kind `κ` for the pair `(i, k)`. -/
def relLhs {m : ℕ} (p : ℕ) (X : Fin m → G) (κ : Fin 4) (i k : Fin m) : G :=
  if κ.val = 0 then X i ^ p else ⁅X i, X k⁆

lemma relOff_zero {m : ℕ} (s : Shape m) (i : Fin m) : relOff s 0 i = i.val + 1 := rfl
lemma relOff_one {m : ℕ} (s : Shape m) (i : Fin m) : relOff s 1 i = s.start 1 := rfl
lemma relOff_two {m : ℕ} (s : Shape m) (i : Fin m) : relOff s 2 i = s.start 2 := rfl
lemma relOff_three {m : ℕ} (s : Shape m) (i : Fin m) : relOff s 3 i = s.start (s.lv i + 1) := rfl

lemma relLhs_zero {m : ℕ} (p : ℕ) (X : Fin m → G) (i k : Fin m) : relLhs p X 0 i k = X i ^ p :=
  rfl

lemma relLhs_pos {m : ℕ} (p : ℕ) (X : Fin m → G) (κ : Fin 4) (hκ : κ.val ≠ 0) (i k : Fin m) :
    relLhs p X κ i k = ⁅X i, X k⁆ :=
  if_neg hκ

/-- The code whose exponents are the chosen normal forms. -/
noncomputable def codeOf {p m : ℕ} (hp : 0 < p) (X : Fin m → G) (s : Shape m) (hs : s.Valid) :
    Code p m :=
  ⟨⟨s, hs⟩, fun q => ⟨nfE p ((List.ofFn X).drop (relOff s q.1.1 q.1.2.1))
    (relLhs p X q.1.1 q.1.2.1 q.1.2.2.1) (q.1.2.2.2.val - relOff s q.1.1 q.1.2.1),
    nfE_lt hp _ _ _⟩⟩

lemma codeOf_ex {p m : ℕ} (hp : 0 < p) (X : Fin m → G) (s : Shape m) (hs : s.Valid)
    (κ : Fin 4) (i k : Fin m) (j : ℕ) (hj : j < m) (hq : s.IdxP (κ, i, k, ⟨j, hj⟩)) :
    (codeOf hp X s hs).ex κ i k j =
      nfE p ((List.ofFn X).drop (relOff s κ i)) (relLhs p X κ i k) (j - relOff s κ i) := by
  have h : ∃ hj : j < m, (codeOf hp X s hs).1.1.IdxP (κ, i, k, ⟨j, hj⟩) := ⟨hj, hq⟩
  unfold Code.ex
  exact dif_pos h

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
  have hcut := Shape.lt_start_iff s hs.mono
  have h2 : ∀ i (hi : i < (List.ofFn X).length),
      (List.ofFn X)[i] ^ p ∈ cl ((List.ofFn X).drop (i + 1)) := by
    intro i hi
    rw [List.getElem_ofFn]
    exact hpow ⟨i, by simpa using hi⟩
  have h3 : ∀ (g : G) j (hj : j < (List.ofFn X).length),
      g * (List.ofFn X)[j] * g⁻¹ * ((List.ofFn X)[j])⁻¹ ∈ cl ((List.ofFn X).drop (j + 1)) := by
    intro g j hj
    have hjm : j < m := by simpa using hj
    rw [List.getElem_ofFn]
    have hc : ⁅g, X ⟨j, hjm⟩⁆ ∈ lcs G (s.lv ⟨j, hjm⟩ + 1) := commElem_mem_lcs_succ' g (hmem _)
    rw [commutatorElement_def] at hc
    have hle : j + 1 ≤ s.start (s.lv ⟨j, hjm⟩ + 1) :=
      (hcut _ ⟨j, hjm⟩).mpr (Nat.lt_succ_self _)
    exact cl_drop_mono _ hle (hspan _ hc)
  have key : ∀ o, ∀ x ∈ cl ((List.ofFn X).drop o),
      ∃ e : ℕ → ℕ, (∀ k, e k < p) ∧ x = nf ((List.ofFn X).drop o) e := by
    intro o
    obtain ⟨hA, hB⟩ := suffix_hyps p (List.ofFn X) h2 h3 o
    exact nf_surj p hp _ hA hB
  have hlvj : ∀ (w j : ℕ) (hj : s.start w + j < m), w ≤ s.lv ⟨s.start w + j, hj⟩ := by
    intro w j hj
    by_contra hcon
    have h' : s.start w + j < s.start w := (hcut w ⟨s.start w + j, hj⟩).mpr (by omega)
    omega
  have hdl : ∀ o j, j < ((List.ofFn X).drop o).length → o + j < m := by
    intro o j hj
    simp at hj
    omega
  refine ⟨codeOf hp X s hs, hG, ?_, hpowdef, hcommdef, ?_, ?_, ?_, ?_⟩
  · have h0 : s.start 0 = 0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun x => absurd x.2 (Nat.not_lt_zero _)⟩)
    have h := hspan 0
    rw [h0, List.drop_zero, lcs_zero, top_le_iff] at h
    rw [← h, cl_def]
    congr 1
    ext x
    simp
  · intro i
    have hx := key (i.val + 1) _ (hpow i)
    refine (nfE_spec hx).trans (nf_congr _ _ _ fun j hj => ?_)
    have hj' : i.val + 1 + j < m := hdl _ j hj
    refine Eq.trans ?_ (codeOf_ex hp X s hs 0 i i _ hj'
      (Or.inl ⟨rfl, rfl, by show i.val < i.val + 1 + j; omega⟩)).symm
    rw [relOff_zero, relLhs_zero, Nat.add_sub_cancel_left]
  · intro i k hi hk hik
    change s.lv i = 0 at hi
    have hc : ⁅X i, X k⁆ ∈ lcs G 1 := by
      have := commElem_mem_lcs_succ (hmem i) (X k)
      rwa [hi] at this
    have hx := key (s.start 1) _ (hspan 1 hc)
    refine (nfE_spec hx).trans (nf_congr _ _ _ fun j hj => ?_)
    have hj' : s.start 1 + j < m := hdl _ j hj
    refine Eq.trans ?_ (codeOf_ex hp X s hs 1 i k _ hj'
      (Or.inr (Or.inl ⟨rfl, hi, hk, hik, hlvj 1 j hj'⟩))).symm
    rw [relOff_one, relLhs_pos p X 1 (by decide), Nat.add_sub_cancel_left]
  · intro i k κ hi hk hκ
    change s.lv i = 1 at hi
    have hc : ⁅X i, X k⁆ ∈ lcs G 2 := by
      have := commElem_mem_lcs_succ (hmem i) (X k)
      rwa [hi] at this
    have hx := key (s.start 2) _ (hspan 2 hc)
    refine (nfE_spec hx).trans (nf_congr _ _ _ fun j hj => ?_)
    have hj' : s.start 2 + j < m := hdl _ j hj
    refine Eq.trans ?_ (codeOf_ex hp X s hs 2 i k _ hj'
      (Or.inr (Or.inr (Or.inl ⟨rfl, hi, ⟨κ, hk, hκ⟩, hlvj 2 j hj'⟩)))).symm
    rw [relOff_two, relLhs_pos p X 2 (by decide), Nat.add_sub_cancel_left]
  · intro i k hi hk
    change 2 ≤ s.lv i at hi
    have hc : ⁅X i, X k⁆ ∈ lcs G (s.lv i + 1) := commElem_mem_lcs_succ (hmem i) (X k)
    have hx := key (s.start (s.lv i + 1)) _ (hspan _ hc)
    refine (nfE_spec hx).trans (nf_congr _ _ _ fun j hj => ?_)
    have hj' : s.start (s.lv i + 1) + j < m := hdl _ j hj
    refine Eq.trans ?_ (codeOf_ex hp X s hs 3 i k _ hj'
      (Or.inr (Or.inr (Or.inr ⟨rfl, hi, hk, hlvj _ j hj'⟩)))).symm
    rw [relOff_three, relLhs_pos p X 3 (by decide), Nat.add_sub_cancel_left]

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

lemma LGood.t_le (hL : LGood p t pos L) : t ≤ L.length := by
  have h := Nat.card_le_card_of_injective
    (fun κ : Fin t => (⟨pos κ.val, (hL.core κ.val κ.isLt).1⟩ : Fin L.length)) (by
      intro a b hab
      have h1 := (hL.core a.val a.isLt).2
      have h2 := (hL.core b.val b.isLt).2
      have hab' : pos a.val = pos b.val := by simpa using hab
      rw [hab'] at h1
      rw [h1] at h2
      exact Fin.ext (Option.some.inj h2))
  rw [Nat.card_fin, Nat.card_fin] at h
  exact h

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

lemma shapeOf_df_none (i : Fin m) :
    (shapeOf m pos L).df i = none ↔ (ent L i.val).df = none := by
  show Option.map _ _ = none ↔ _
  exact Option.map_eq_none_iff

lemma shapeOf_df_pow (i : Fin m) :
    (shapeOf m pos L).df i = some none ↔ (ent L i.val).df = some none := by
  show Option.map _ _ = some none ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    rw [ha, Option.map_eq_none_iff.mp h]
  · intro h
    exact ⟨none, h, rfl⟩

lemma shapeOf_df_comm (hL : LGood p t pos L) (hlen : L.length = m) (i a b : Fin m)
    (h : (shapeOf m pos L).df i = some (some (a, b))) :
    (ent L i.val).df = some (some (a.val, b.val)) := by
  have hi : i.val < L.length := by omega
  have him := i.isLt
  change Option.map _ (ent L i.val).df = _ at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨a', b'⟩, rfl, h⟩ := h
  obtain ⟨ha, hb, -⟩ := hL.comm i.val hi a' b' hx
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [hx]
  simp only [Fin.val_mk, Option.some.injEq, Prod.mk.injEq]
  constructor <;> omega

lemma shapeOf_st (hL : LGood p t pos L) (hlen : L.length = m) (i : Fin m)
    (h1 : (ent L i.val).lv = 1) : (shapeOf m pos L).st i = (ent L i.val).st := by
  have h := (hL.st_range i.val (by omega) h1).2
  have htl := hL.t_le
  show min (ent L i.val).st (m - 1) = _
  omega

lemma shapeOf_cidx_pos (hL : LGood p t pos L) (hlen : L.length = m) {κ : ℕ} (hκ : κ < t)
    (i : Fin m) (hi : i.val = pos κ) :
    (shapeOf m pos L).cidx i = some ⟨κ, by have := hL.t_le; omega⟩ := by
  have hci : (ent L i.val).ci = some κ := by rw [hi]; exact (hL.core κ hκ).2
  have htl := hL.t_le
  show (ent L i.val).ci.bind _ = _
  rw [hci, Option.bind_some, if_pos hi.symm]
  congr 1
  apply Fin.ext
  show min κ (m - 1) = κ
  omega

lemma shapeOf_cidx_some (hL : LGood p t pos L) (hlen : L.length = m) {i k : Fin m}
    (h : (shapeOf m pos L).cidx i = some k) : (ent L i.val).ci = some k.val ∧ pos k.val = i.val := by
  have hi : i.val < L.length := by omega
  change (ent L i.val).ci.bind _ = _ at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨κ, hκ, h2⟩ := h
  have hκt := (hL.ci i.val hi κ hκ).1
  have htl := hL.t_le
  by_cases hp : pos κ = i.val
  · rw [if_pos hp, Option.some.injEq] at h2
    have hk : k.val = κ := by
      rw [← h2]
      show min κ (m - 1) = κ
      omega
    rw [hk]
    exact ⟨hκ, hp⟩
  · rw [if_neg hp] at h2
    exact absurd h2 (by simp)

lemma shapeOf_ncore (hL : LGood p t pos L) (hlen : L.length = m) : (shapeOf m pos L).ncore = t := by
  have hpos : ∀ κ : Fin t, pos κ.val < m := fun κ => by
    have := (hL.core κ.val κ.isLt).1
    omega
  let f : Fin t → {i : Fin m // ((shapeOf m pos L).cidx i).isSome} := fun κ =>
    ⟨⟨pos κ.val, hpos κ⟩,
      Option.isSome_iff_exists.mpr ⟨_, shapeOf_cidx_pos hL hlen κ.isLt ⟨pos κ.val, hpos κ⟩ rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 := (hL.core a.val a.isLt).2
      have h2 := (hL.core b.val b.isLt).2
      have hab' : pos a.val = pos b.val := congrArg (fun x => x.1.val) hab
      rw [hab'] at h1
      rw [h1] at h2
      exact Fin.ext (Option.some.inj h2)
    · rintro ⟨i, hi⟩
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hi
      obtain ⟨hci, hpk⟩ := shapeOf_cidx_some hL hlen hk
      have hkt := (hL.ci i.val (by omega) k.val hci).1
      exact ⟨⟨k.val, hkt⟩, Subtype.ext (Fin.ext hpk)⟩
  unfold Shape.ncore
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fin]

/-- V1 to V6 for the shape of a good list. -/
lemma shapeOf_valid (hL : LGood p t pos L) (hlen : L.length = m) : (shapeOf m pos L).Valid := by
  have hlv := shapeOf_lv hL hlen
  have hnc := shapeOf_ncore hL hlen
  have htl := hL.t_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hlv, hlv]
    exact hL.mono i.val j.val hij (by omega)
  · intro i h
    rw [hlv]
    exact hL.free i.val (by omega) ((shapeOf_df_none i).mp h)
  · intro i h
    obtain ⟨h0, h1, h2, -⟩ := hL.pow i.val (by omega) ((shapeOf_df_pow i).mp h)
    refine ⟨h0, ?_, fun _ => ?_⟩
    · rw [hlv, hlv]
      exact h1
    · show min (ent L i.val).st (m - 1) = min (ent L (i.val - 1)).st (m - 1)
      rw [h2]
  · intro i a b h
    have hdf := shapeOf_df_comm hL hlen i a b h
    obtain ⟨ha, hb, ⟨κ, hκ, hbκ⟩, hlva, h1, -⟩ := hL.comm i.val (by omega) a.val b.val hdf
    refine ⟨ha, hb, ?_, ?_, fun hl => ?_⟩
    · exact Option.isSome_iff_exists.mpr ⟨_, shapeOf_cidx_pos hL hlen hκ b hbκ⟩
    · rw [hlv, hlv]
      exact hlva
    · rw [hlv] at hl
      obtain ⟨ka, kb, hkab, hkb, hka', hkb', hst'⟩ := h1 hl
      refine ⟨⟨ka, by omega⟩, ⟨kb, by omega⟩, shapeOf_cidx_pos hL hlen (by omega) a hka',
        shapeOf_cidx_pos hL hlen hkb b hkb', hkab, ?_⟩
      show kb = (shapeOf m pos L).st i
      rw [shapeOf_st hL hlen i hl]
      exact hst'
  · intro i k h
    obtain ⟨hci, -⟩ := shapeOf_cidx_some hL hlen h
    obtain ⟨hkt, hdf⟩ := hL.ci i.val (by omega) k.val hci
    refine ⟨(shapeOf_df_none i).mpr hdf, ?_⟩
    rw [hnc]
    exact hkt
  · intro i j k hi hj
    obtain ⟨-, hpi⟩ := shapeOf_cidx_some hL hlen hi
    obtain ⟨-, hpj⟩ := shapeOf_cidx_some hL hlen hj
    exact Fin.ext (hpi.symm.trans hpj)
  · intro β h1 h2
    rw [hnc] at h2
    obtain ⟨i, hi, hlv1, hstβ⟩ := hL.steps β h1 h2
    refine ⟨⟨i, by omega⟩, ?_, ?_⟩
    · rw [hlv]
      exact hlv1
    · rw [shapeOf_st hL hlen ⟨i, by omega⟩ hlv1]
      exact hstβ
  · intro i h
    rw [hlv] at h
    rw [shapeOf_st hL hlen i h, hnc]
    exact hL.st_range i.val (by omega) h

lemma Xof_pow (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ i, (shapeOf m pos L).df i = some none → ∀ h : 0 < i.val,
      Xof m L i = Xof m L ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ ^ p := by
  intro i h _
  exact (hL.pow i.val (by omega) ((shapeOf_df_pow i).mp h)).2.2.2

lemma Xof_comm (hL : LGood p t pos L) (hlen : L.length = m) :
    ∀ i a b, (shapeOf m pos L).df i = some (some (a, b)) → Xof m L i = ⁅Xof m L a, Xof m L b⁆ := by
  intro i a b h
  exact (hL.comm i.val (by omega) a.val b.val (shapeOf_df_comm hL hlen i a b h)).2.2.2.2.2

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

lemma mem_commC (d : Dat G) (w o : ℕ) (Y : List (Ent G)) (c : Ent G) :
    c ∈ d.commC w o Y ↔ ∃ r < Y.length, ∃ b < d.t,
      c = ⟨⁅(ent Y r).g, d.u b⁆, w, some (some (o + r, d.pos b)), none, 0⟩ := by
  induction Y generalizing o with
  | nil => simp [commC]
  | cons y Y ih =>
    simp only [commC, List.mem_append]
    rw [ih]
    constructor
    · rintro (h | ⟨r, hr, b, hb, rfl⟩)
      · simp only [List.mem_map, List.mem_range] at h
        obtain ⟨b, hb, rfl⟩ := h
        exact ⟨0, by simp, b, hb, rfl⟩
      · refine ⟨r + 1, by simp; omega, b, hb, ?_⟩
        rw [show o + 1 + r = o + (r + 1) by omega]
        rfl
    · rintro ⟨r, hr, b, hb, rfl⟩
      rcases r with _ | r
      · left
        simp only [List.mem_map, List.mem_range]
        exact ⟨b, hb, rfl⟩
      · right
        refine ⟨r, by simpa using hr, b, hb, ?_⟩
        rw [show o + 1 + r = o + (r + 1) by omega]
        rfl

lemma mem_cand1 (d : Dat G) (c : Ent G) : c ∈ d.cand1 ↔ ∃ a b, a < b ∧ b < d.t ∧
    c = ⟨⁅d.u a, d.u b⁆, 1, some (some (d.pos a, d.pos b)), none, b⟩ := by
  simp only [cand1, block, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨b, hb, a, ha, rfl⟩

lemma cands_lv (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, c.lv = w := by
  intro w c hc
  rcases w with _ | _ | w
  · simp only [cands, cand0, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨x, -, rfl⟩ | ⟨κ, -, rfl⟩ <;> rfl
  · obtain ⟨a, b, -, -, rfl⟩ := (d.mem_cand1 c).mp hc
    rfl
  · obtain ⟨r, -, b, -, rfl⟩ := (d.mem_commC _ _ _ c).mp hc
    rfl

lemma cands_df (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, c.df ≠ some none ∧ (c.df = none ↔ w = 0) := by
  intro w c hc
  rcases w with _ | _ | w
  · simp only [cands, cand0, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨x, -, rfl⟩ | ⟨κ, -, rfl⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp [coreE], by simp [coreE]⟩
  · obtain ⟨a, b, -, -, rfl⟩ := (d.mem_cand1 c).mp hc
    exact ⟨by simp, by simp⟩
  · obtain ⟨r, -, b, -, rfl⟩ := (d.mem_commC _ _ _ c).mp hc
    exact ⟨by simp, by simp⟩

lemma cands_ci (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, ∀ κ, c.ci = some κ →
    κ < d.t ∧ c.g = d.u κ ∧ c.df = none := by
  intro w c hc κ hκ
  rcases w with _ | _ | w
  · simp only [cands, cand0, List.mem_append, List.mem_map, List.mem_reverse,
      List.mem_range] at hc
    rcases hc with ⟨x, -, rfl⟩ | ⟨κ', hκ', rfl⟩
    · exact absurd hκ (by simp)
    · simp only [coreE, Option.some.injEq] at hκ
      subst hκ
      exact ⟨hκ', rfl, rfl⟩
  · obtain ⟨a, b, -, -, rfl⟩ := (d.mem_cand1 c).mp hc
    exact absurd hκ (by simp)
  · obtain ⟨r, -, b, -, rfl⟩ := (d.mem_commC _ _ _ c).mp hc
    exact absurd hκ (by simp)

lemma cands_st (d : Dat G) : ∀ c ∈ d.cands 1, 1 ≤ c.st ∧ c.st < d.t := by
  intro c hc
  obtain ⟨a, b, hab, hb, rfl⟩ := (d.mem_cand1 c).mp hc
  exact ⟨by show 1 ≤ b; omega, hb⟩

/-- Closure of the blocks `k - 1, ..., 0`: the commutators `⁅u a, u b⁆` with `a < b < k`. -/
lemma cl_blocks (d : Dat G) (k : ℕ) : cl (((List.range k).reverse.flatMap d.block).map Ent.g) =
    Subgroup.closure {x | ∃ a b, a < b ∧ b < k ∧ x = ⁅d.u a, d.u b⁆} := by
  rw [cl_def]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map, List.mem_flatMap, List.mem_reverse, List.mem_range,
    block]
  constructor
  · rintro ⟨e, ⟨b, hb, a, ha, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨_, ⟨b, hb, a, ha, rfl⟩, rfl⟩

/-! ### Layers and the full list (no hypotheses needed) -/

lemma Y_src (d : Dat G) (w : ℕ) (e : Ent G) (he : e ∈ d.Y w) :
    ∃ c ∈ d.cands w, ∃ k : ℕ, e.g = c.g ^ k ∧ e.lv = c.lv ∧ e.st = c.st ∧
      (e = c ∨ (e.df = some none ∧ e.ci = none)) := by
  rw [Y_eq] at he
  exact layer_src _ _ _ e he

lemma Y_lv (d : Dat G) : ∀ w, ∀ e ∈ d.Y w, e.lv = w := by
  intro w e he
  obtain ⟨c, hc, -, -, h, -, -⟩ := d.Y_src w e he
  rw [h, d.cands_lv w c hc]

lemma Y_ci (d : Dat G) : ∀ w, ∀ e ∈ d.Y w, ∀ κ, e.ci = some κ →
    κ < d.t ∧ e.g = d.u κ ∧ e.df = none := by
  intro w e he κ hκ
  obtain ⟨c, hc, -, -, -, -, h | h⟩ := d.Y_src w e he
  · rw [h] at hκ ⊢
    exact d.cands_ci w c hc κ hκ
  · rw [h.2] at hκ
    exact absurd hκ (by simp)

lemma Y_mem_of (d : Dat G) (w : ℕ) (h : ∀ c ∈ d.cands w, c.g ∈ lcs G w) :
    ∀ e ∈ d.Y w, e.g ∈ lcs G w := by
  intro e he
  obtain ⟨c, hc, k, hk, -⟩ := d.Y_src w e he
  rw [hk]
  exact pow_mem (h c hc) k

lemma cands_mem (d : Dat G) : ∀ w, ∀ c ∈ d.cands w, c.g ∈ lcs G w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro c hc
    rcases w with _ | _ | w
    · exact Subgroup.mem_top _
    · obtain ⟨a, b, -, -, rfl⟩ := (d.mem_cand1 c).mp hc
      exact commElem_mem_lcs_succ (n := 0) (Subgroup.mem_top _) _
    · obtain ⟨r, hr, b, -, rfl⟩ := (d.mem_commC _ _ _ c).mp hc
      have hy := d.Y_mem_of (w + 1) (ih (w + 1) (by omega)) _ (ent_mem _ hr)
      exact commElem_mem_lcs_succ hy _

lemma Y_mem (d : Dat G) : ∀ w, ∀ e ∈ d.Y w, e.g ∈ lcs G w := fun w =>
  d.Y_mem_of w (d.cands_mem w)

lemma off_mono (d : Dat G) {v w : ℕ} (h : v ≤ w) : d.off v ≤ d.off w := by
  induction w, h using Nat.le_induction with
  | base => exact le_rfl
  | succ w _ ih =>
    rw [off_succ]
    omega

lemma full_append (d : Dat G) {n n' : ℕ} (h : n ≤ n') : ∃ R, d.full n' = d.full n ++ R := by
  induction n', h using Nat.le_induction with
  | base => exact ⟨[], (List.append_nil _).symm⟩
  | succ n' _ ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R ++ d.Y n', ?_⟩
    show d.full n' ++ d.Y n' = _
    rw [hR, List.append_assoc]

lemma full_prefix (d : Dat G) {n n' : ℕ} (h : n ≤ n') {i : ℕ} (hi : i < d.off n) :
    ent (d.full n') i = ent (d.full n) i := by
  obtain ⟨R, hR⟩ := d.full_append h
  rw [hR, ent_append_left (d.full n) R (by rw [full_length]; exact hi)]

lemma ent_full (d : Dat G) {n w r : ℕ} (hw : w < n) (hr : r < (d.Y w).length) :
    ent (d.full n) (d.off w + r) = ent (d.Y w) r := by
  have h1 : d.off w + r < d.off (w + 1) := by rw [off_succ]; omega
  rw [d.full_prefix (Nat.succ_le_of_lt hw) h1]
  show ent (d.full w ++ d.Y w) (d.off w + r) = _
  rw [ent_append_right (d.full w) (d.Y w) (i := d.off w + r) (by rw [full_length]; omega),
    full_length,
    Nat.add_sub_cancel_left]

lemma locate (d : Dat G) {n i : ℕ} (hi : i < (d.full n).length) :
    ∃ w < n, ∃ r < (d.Y w).length, i = d.off w + r := by
  induction n with
  | zero => simp [full] at hi
  | succ n ih =>
    rw [full_length, off_succ] at hi
    by_cases h : i < d.off n
    · obtain ⟨w, hw, r, hr, rfl⟩ := ih (by rw [full_length]; exact h)
      exact ⟨w, by omega, r, hr, rfl⟩
    · exact ⟨n, by omega, i - d.off n, by omega, by omega⟩

lemma full_cut (d : Dat G) (n : ℕ) {i : ℕ} (hi : i < (d.full n).length) (v : ℕ) :
    i < d.off v ↔ (ent (d.full n) i).lv < v := by
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr, d.Y_lv w _ (ent_mem _ hr)]
  have h1 : d.off w + r < d.off (w + 1) := by rw [off_succ]; omega
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have := d.off_mono hc
    omega
  · intro h
    have : d.off (w + 1) ≤ d.off v := d.off_mono h
    omega

/-! ### Generic fields of `LGood` for `full n` -/

lemma good_mono (d : Dat G) (n : ℕ) :
    ∀ i j, i ≤ j → j < (d.full n).length → (ent (d.full n) i).lv ≤ (ent (d.full n) j).lv := by
  intro i j hij hj
  by_contra h
  push_neg at h
  have h1 := (d.full_cut n hj ((ent (d.full n) i).lv)).mpr h
  have h2 := (d.full_cut n (lt_of_le_of_lt hij hj) ((ent (d.full n) i).lv)).mp
    (lt_of_le_of_lt hij h1)
  exact lt_irrefl _ h2

lemma good_free (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).df = none → (ent (d.full n) i).lv = 0 := by
  intro i hi hdf
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr] at hdf ⊢
  have hmem := ent_mem (d.Y w) hr
  rw [d.Y_lv w _ hmem]
  obtain ⟨c, hc, -, -, -, -, h | h⟩ := d.Y_src w _ hmem
  · rw [h] at hdf
    exact (d.cands_df w c hc).2.mp hdf
  · rw [h.1] at hdf
    exact absurd hdf (by simp)

lemma good_pow (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).df = some none → 0 < i ∧
      (ent (d.full n) (i - 1)).lv = (ent (d.full n) i).lv ∧
      (ent (d.full n) (i - 1)).st = (ent (d.full n) i).st ∧
      (ent (d.full n) i).g = (ent (d.full n) (i - 1)).g ^ d.p := by
  intro i hi hdf
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr] at hdf ⊢
  have hY : d.Y w = layer d.p (lcs G (w + 1)) (d.cands w) := Y_eq d w
  have hC : ∀ c ∈ d.cands w, c.df ≠ some none := fun c hc => (d.cands_df w c hc).1
  have hr' : r < (layer d.p (lcs G (w + 1)) (d.cands w)).length := by rw [← hY]; exact hr
  have hdf' : (ent (layer d.p (lcs G (w + 1)) (d.cands w)) r).df = some none := by
    rw [← hY]; exact hdf
  obtain ⟨h0, h1, h2, h3⟩ := layer_pow _ _ _ hC r hr' hdf'
  rw [← hY] at h1 h2 h3
  have e1 : d.off w + r - 1 = d.off w + (r - 1) := by omega
  rw [e1, d.ent_full (r := r - 1) hw (by omega)]
  exact ⟨by omega, h1, h2, h3⟩

lemma good_ci (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, ∀ κ, (ent (d.full n) i).ci = some κ → κ < d.t ∧
      (ent (d.full n) i).df = none := by
  intro i hi κ hκ
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr] at hκ ⊢
  obtain ⟨h1, -, h3⟩ := d.Y_ci w _ (ent_mem _ hr) κ hκ
  exact ⟨h1, h3⟩

lemma good_st (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).lv = 1 → 1 ≤ (ent (d.full n) i).st ∧
      (ent (d.full n) i).st < d.t := by
  intro i hi hlv
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr] at hlv ⊢
  have hmem := ent_mem (d.Y w) hr
  have hw1 : w = 1 := by rw [← d.Y_lv w _ hmem]; exact hlv
  subst hw1
  obtain ⟨c, hc, -, -, -, h, -⟩ := d.Y_src 1 _ hmem
  rw [h]
  exact d.cands_st c hc

lemma good_mem (d : Dat G) (n : ℕ) :
    ∀ i < (d.full n).length, (ent (d.full n) i).g ∈ lcs G (ent (d.full n) i).lv := by
  intro i hi
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr, d.Y_lv w _ (ent_mem _ hr)]
  exact d.Y_mem w _ (ent_mem _ hr)

/-! ### Facts needing the hypotheses -/

variable [Finite G] {m : ℕ}

lemma core_Y0 {d : Dat G} (hd : d.Hyp m) :
    ∀ κ < d.t, d.pos κ < d.Y0.length ∧ (ent d.Y0 (d.pos κ)).ci = some κ := by
  intro κ hκ
  have ht2 : 2 ≤ d.t := by have := hd.t_ne; omega
  have hind := strict_chain_indep d.u d.t hd.strict ht2 κ hκ
  have hsplit : (List.range d.t).reverse =
      ((List.range (d.t - (κ + 1))).map (κ + 1 + ·)).reverse ++ κ :: (List.range κ).reverse := by
    conv_lhs => rw [show d.t = κ + 1 + (d.t - (κ + 1)) by omega]
    rw [List.range_add, List.range_succ, List.reverse_append, List.reverse_append]
    simp
  have hcand : d.cand0 = (d.en.map (fun x => (⟨x, 0, none, none, 0⟩ : Ent G)) ++
      (((List.range (d.t - (κ + 1))).map (κ + 1 + ·)).reverse.map d.coreE)) ++
      d.coreE κ :: (List.range κ).reverse.map d.coreE := by
    rw [cand0, hsplit, List.map_append, List.map_cons, List.append_assoc]
  have hmem : d.coreE κ ∈ d.Y0 := by
    show d.coreE κ ∈ layer d.p (lcs G (0 + 1)) d.cand0
    rw [hcand]
    refine layer_mem_head hd.prime hd.card 0 _ _ _ (fun x _ => Subgroup.mem_top _) ?_
    have e : cl (((List.range κ).reverse.map d.coreE).map Ent.g) =
        Subgroup.closure (d.u '' Set.Iio κ) := by
      rw [cl_def]
      congr 1
      ext x
      simp [coreE]
    rw [e]
    exact hind
  have hex : ∃ e ∈ d.Y0, decide (e.ci = some κ) = true := ⟨_, hmem, by simp [coreE]⟩
  have hlt : d.pos κ < d.Y0.length := List.findIdx_lt_length_of_exists hex
  refine ⟨hlt, ?_⟩
  rw [ent_eq d.Y0 hlt]
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

lemma Y_nil {d : Dat G} (hd : d.Hyp m) {w : ℕ} (hw : m ≤ w) : d.Y w = [] := by
  have hbot : ∀ v, m ≤ v → lcs G v = ⊥ := fun v hv => by
    have h := lcs_antitone (D := G) hv
    rw [lcs_eq_bot_of_card hd.prime hd.card] at h
    exact le_bot_iff.mp h
  have hcard := layer_card hd.prime hd.card w (d.cands w) (d.cands_mem w)
  rw [← Y_eq] at hcard
  have hcl : cl ((d.cands w).map Ent.g) ⊔ lcs G (w + 1) = lcs G (w + 1) := by
    rw [hbot (w + 1) (by omega), sup_bot_eq, eq_bot_iff]
    refine cl_le_of_forall fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rw [← hbot w hw]
    exact d.cands_mem w c hc
  rw [hcl, Subgroup.relIndex_self] at hcard
  have h1 : d.p ^ (d.Y w).length = d.p ^ 0 := by rw [hcard, pow_zero]
  exact List.eq_nil_of_length_eq_zero (Nat.pow_right_injective hd.prime.two_le h1)

lemma steps_Y1 {d : Dat G} (hd : d.Hyp m) :
    ∀ β, 1 ≤ β → β < d.t → ∃ e ∈ d.Y 1, e.lv = 1 ∧ e.st = β := by
  intro β hβ1 hβ
  have hsplit : (List.range d.t).reverse =
      ((List.range (d.t - (β + 1))).map (β + 1 + ·)).reverse ++ β :: (List.range β).reverse := by
    conv_lhs => rw [show d.t = β + 1 + (d.t - (β + 1)) by omega]
    rw [List.range_add, List.range_succ, List.reverse_append, List.reverse_append]
    simp
  have hcand : d.cand1 =
      ((List.range (d.t - (β + 1))).map (β + 1 + ·)).reverse.flatMap d.block ++
        (d.block β ++ (List.range β).reverse.flatMap d.block) := by
    rw [cand1, hsplit, List.flatMap_append, List.flatMap_cons]
  have hb1 : (List.range (β + 1)).reverse.flatMap d.block =
      d.block β ++ (List.range β).reverse.flatMap d.block := by
    simp [List.range_succ]
  have hsub : ∀ x ∈ d.block β ++ (List.range β).reverse.flatMap d.block, x.g ∈ lcs G 1 :=
    fun x hx => d.cands_mem 1 x (show x ∈ d.cand1 by
      rw [hcand]; exact List.mem_append_right _ hx)
  have e1 : cl ((d.block β ++ (List.range β).reverse.flatMap d.block).map Ent.g) ⊔ lcs G 2 =
      Wk d.u (β + 1) := by
    rw [← hb1, cl_blocks]
    rfl
  have e2 : cl (((List.range β).reverse.flatMap d.block).map Ent.g) ⊔ lcs G 2 = Wk d.u β := by
    rw [cl_blocks]
    rfl
  have hs := hd.strict (β + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at hs
  have hne : cl ((d.block β ++ (List.range β).reverse.flatMap d.block).map Ent.g) ⊔ lcs G 2 ≠
      cl (((List.range β).reverse.flatMap d.block).map Ent.g) ⊔ lcs G 2 :=
    fun h => hs (e2.symm.trans (h.symm.trans e1))
  obtain ⟨c, hcB, hcl⟩ := layer_head_of_ne hd.prime hd.card 1 (d.block β)
    ((List.range β).reverse.flatMap d.block) hsub hne
  obtain ⟨P, hP⟩ := layer_append d.p (lcs G 2)
    (((List.range (d.t - (β + 1))).map (β + 1 + ·)).reverse.flatMap d.block)
    (d.block β ++ (List.range β).reverse.flatMap d.block)
  refine ⟨c, ?_, ?_⟩
  · show c ∈ layer d.p (lcs G 2) d.cand1
    rw [hcand, hP]
    exact List.mem_append_right _ hcl
  · simp only [block, List.mem_map, List.mem_range] at hcB
    obtain ⟨a, -, rfl⟩ := hcB
    exact ⟨rfl, rfl⟩

/-- Theorem L applied in `G`: each layer generates `lcs G w` modulo `lcs G (w + 1)`. -/
lemma lie_app {d : Dat G} (hd : d.Hyp m) :
    ∀ w, lcs G w ≤ cl ((d.Y w).map Ent.g) ⊔ lcs G (w + 1) := by
  have hsup : ∀ w, cl ((d.Y w).map Ent.g) ⊔ lcs G (w + 1) =
      cl ((d.cands w).map Ent.g) ⊔ lcs G (w + 1) := by
    intro w
    rw [Y_eq]
    exact layer_sup hd.prime hd.card w _ (d.cands_mem w)
  intro w
  rw [hsup w]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [lcs_zero]
    intro x _
    apply Subgroup.mem_sup_left
    apply mem_cl_of_mem
    show x ∈ d.cand0.map Ent.g
    simp only [cand0, List.map_append, List.mem_append, List.map_map]
    left
    exact List.mem_map.mpr ⟨x, hd.en x, rfl⟩
  · let E : ℕ → Set G := fun v => {x | x ∈ (d.cands v).map Ent.g}
    have hE : ∀ v, Subgroup.closure (E v) = cl ((d.cands v).map Ent.g) := fun v => rfl
    have hE1 : E 1 = (fun ab : ℕ × ℕ => ⁅d.u ab.1, d.u ab.2⁆) ''
        {ab : ℕ × ℕ | ab.1 < ab.2 ∧ ab.2 < d.t} := by
      ext x
      simp only [E, Set.mem_setOf_eq, Set.mem_image, List.mem_map]
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨a, b, hab, hb, rfl⟩ := (d.mem_cand1 c).mp hc
        exact ⟨(a, b), ⟨hab, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨hab, hb⟩, rfl⟩
        exact ⟨_, (d.mem_cand1 _).mpr ⟨a, b, hab, hb, rfl⟩, rfl⟩
    have hL2 : ∀ v, 1 ≤ v → ∀ x ∈ E (v + 1), ∃ y ∈ Subgroup.closure (E v), ∃ b < d.t,
        x = ⁅y, d.u b⁆ := by
      intro v hv x hx
      have hx' : x ∈ (d.cands (v + 1)).map Ent.g := hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx'
      obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
      obtain ⟨r, hr, b, hb, rfl⟩ := (d.mem_commC _ _ _ c).mp hc
      obtain ⟨c', hc', k, hk, -⟩ := d.Y_src (v' + 1) _ (ent_mem _ hr)
      refine ⟨(ent (d.Y (v' + 1)) r).g, ?_, b, hb, rfl⟩
      rw [hk]
      exact pow_mem (Subgroup.subset_closure
        (show c'.g ∈ E (v' + 1) from List.mem_map.mpr ⟨c', hc', rfl⟩)) k
    have hL0 : Subgroup.closure (Set.univ : Set G) ⊔ lcs G 1 = ⊤ := by
      rw [Subgroup.closure_univ, top_sup_eq]
    have hW : Wk d.u d.t = Subgroup.closure (E 1) ⊔ lcs G 2 := by
      rw [hE 1]
      show _ = cl (((List.range d.t).reverse.flatMap d.block).map Ent.g) ⊔ lcs G 2
      rw [cl_blocks]
      rfl
    have hH1 : ∀ x ∈ (Set.univ : Set G), ∀ y ∈ (Set.univ : Set G),
        ⁅x, y⁆ ∈ Subgroup.closure (E 1) ⊔ lcs G 2 := by
      intro x _ y _
      rw [← hW]
      exact hd.top (commElem_mem_lcs_succ (n := 0) (Subgroup.mem_top x) y)
    have hHgen : ∀ v, 1 ≤ v → ∀ x ∈ E v, ∀ k < d.t,
        ⁅x, d.u k⁆ ∈ Subgroup.closure (E (v + 1)) ⊔ lcs G (v + 2) := by
      intro v hv x hx k hk
      rw [hE]
      haveI : (cl ((d.cands (v + 1)).map Ent.g) ⊔ lcs G (v + 1 + 1)).Normal :=
        normal_K (v + 1) _ (d.cands_mem (v + 1))
      have hx1 : x ∈ cl ((d.Y v).map Ent.g) ⊔ lcs G (v + 1) := by
        rw [hsup v]
        exact Subgroup.mem_sup_left (mem_cl_of_mem (show x ∈ (d.cands v).map Ent.g from hx))
      have hle : cl ((d.Y v).map Ent.g) ⊔ lcs G (v + 1) ≤
          zn (cl ((d.cands (v + 1)).map Ent.g) ⊔ lcs G (v + 1 + 1)) (d.u k) := by
        refine sup_le (cl_le_of_forall fun y hy => ?_) (fun z hz => ?_)
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
          obtain ⟨r, hr, rfl⟩ := exists_ent_of_mem he
          rw [mem_zn]
          apply commElem_mem_symm
          apply Subgroup.mem_sup_left
          apply mem_cl_of_mem
          obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
          show _ ∈ (d.commC (v' + 2) (d.off (v' + 1)) (d.Y (v' + 1))).map Ent.g
          exact List.mem_map.mpr ⟨_, (d.mem_commC _ _ _ _).mpr ⟨r, hr, k, hk, rfl⟩, rfl⟩
        · rw [mem_zn]
          exact Subgroup.mem_sup_right (commElem_mem_lcs_succ' (d.u k) hz)
      exact commElem_mem_symm (mem_zn.mp (hle hx1))
    have hH2 : ∀ ab ∈ {ab : ℕ × ℕ | ab.1 < ab.2 ∧ ab.2 < d.t}, ∀ k ≤ ab.2,
        ⁅⁅d.u ab.1, d.u ab.2⁆, d.u k⁆ ∈ Subgroup.closure (E 2) ⊔ lcs G 3 := by
      intro ab hab k hk
      refine hHgen 1 le_rfl _ ?_ k (by have := hab.2; omega)
      rw [hE1]
      exact ⟨ab, hab, rfl⟩
    have hH3 : ∀ v, 2 ≤ v → ∀ x ∈ E v, ∀ k < d.t,
        ⁅x, d.u k⁆ ∈ Subgroup.closure (E (v + 1)) ⊔ lcs G (v + 2) :=
      fun v hv => hHgen v (by omega)
    have key := lie_lemma d.t d.u Set.univ {ab : ℕ × ℕ | ab.1 < ab.2 ∧ ab.2 < d.t} E
      (fun ab hab => hab) hE1 hL2 hL0 hH1 hH2 hH3 w hw
    rw [hE] at key
    exact key

lemma cands_sup {d : Dat G} (hd : d.Hyp m) (v : ℕ) :
    cl ((d.cands v).map Ent.g) ⊔ lcs G (v + 1) = lcs G v := by
  have h1 := layer_sup hd.prime hd.card v (d.cands v) (d.cands_mem v)
  rw [← Y_eq] at h1
  rw [← h1]
  apply le_antisymm
  · refine sup_le (cl_le_of_forall fun x hx => ?_) (lcs_antitone (Nat.le_succ v))
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact d.Y_mem v e he
  · exact lie_app hd v

lemma span_drop {d : Dat G} (hd : d.Hyp m) :
    ∀ v ≤ m, lcs G v = cl (((d.full m).map Ent.g).drop (d.off v)) := by
  have hlen := d.full_length m
  suffices h : ∀ k v, v + k = m → lcs G v = cl (((d.full m).map Ent.g).drop (d.off v)) by
    intro v hv
    exact h (m - v) v (by omega)
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [show v = m by omega, lcs_eq_bot_of_card hd.prime hd.card,
      List.drop_eq_nil_of_le (as := (d.full m).map Ent.g) (i := d.off m)
        (by rw [List.length_map, hlen]), cl_nil]
  | succ k ih =>
    intro v hv
    have hv1 := ih (v + 1) (by omega)
    obtain ⟨R, hR⟩ := d.full_append (show v + 1 ≤ m by omega)
    have hA : d.off v = ((d.full v).map Ent.g).length := by rw [List.length_map, full_length]
    have hB : d.off (v + 1) = ((d.full v).map Ent.g ++ (d.Y v).map Ent.g).length := by
      rw [List.length_append, List.length_map, List.length_map, full_length, off_succ]
    have hsplit : ((d.full m).map Ent.g).drop (d.off v) =
        (d.Y v).map Ent.g ++ ((d.full m).map Ent.g).drop (d.off (v + 1)) := by
      rw [hR]
      show ((d.full v ++ d.Y v ++ R).map Ent.g).drop (d.off v) =
        (d.Y v).map Ent.g ++ ((d.full v ++ d.Y v ++ R).map Ent.g).drop (d.off (v + 1))
      rw [List.map_append, List.map_append, hB, List.drop_append_length, hA, List.append_assoc,
        List.drop_append_length]
    rw [hsplit, cl_append, ← hv1]
    apply le_antisymm
    · exact lie_app hd v
    · refine sup_le (cl_le_of_forall fun x hx => ?_) (lcs_antitone (Nat.le_succ v))
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact d.Y_mem v e he

lemma card_drop {d : Dat G} (hd : d.Hyp m) :
    ∀ v ≤ m, Nat.card (lcs G v) = d.p ^ ((d.full m).length - d.off v) := by
  have hlen := d.full_length m
  suffices h : ∀ k v, v + k = m → Nat.card (lcs G v) = d.p ^ ((d.full m).length - d.off v) by
    intro v hv
    exact h (m - v) v (by omega)
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [show v = m by omega, lcs_eq_bot_of_card hd.prime hd.card, Subgroup.card_bot, hlen,
      Nat.sub_self, pow_zero]
  | succ k ih =>
    intro v hv
    have hv1 := ih (v + 1) (by omega)
    have hmul := Subgroup.relIndex_mul_relIndex ⊥ (lcs G (v + 1)) (lcs G v) bot_le
      (lcs_antitone (Nat.le_succ v))
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at hmul
    have hcard := layer_card hd.prime hd.card v (d.cands v) (d.cands_mem v)
    rw [← Y_eq, cands_sup hd v] at hcard
    rw [← hmul, hv1, ← hcard, ← pow_add]
    congr 1
    have h1 := d.off_mono (show v + 1 ≤ m by omega)
    rw [off_succ] at h1 ⊢
    omega

lemma full_length_eq {d : Dat G} (hd : d.Hyp m) : (d.full m).length = m := by
  have h := card_drop hd 0 (Nat.zero_le m)
  rw [lcs_zero, Subgroup.card_top, hd.card, show d.off 0 = 0 from rfl, Nat.sub_zero] at h
  exact (Nat.pow_right_injective hd.prime.two_le h).symm

/-! ### The fields of `LGood` for `full m` -/

lemma good_lv_lt {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, (ent (d.full m) i).lv < (d.full m).length := by
  intro i hi
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr, d.Y_lv w _ (ent_mem _ hr), full_length_eq hd]
  exact hw

lemma good_comm {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, ∀ a b, (ent (d.full m) i).df = some (some (a, b)) → a < i ∧ b < i ∧
      (∃ κ < d.t, b = d.pos κ) ∧ (ent (d.full m) i).lv = (ent (d.full m) a).lv + 1 ∧
      ((ent (d.full m) i).lv = 1 → ∃ ka kb, ka < kb ∧ kb < d.t ∧ a = d.pos ka ∧ b = d.pos kb ∧
        kb = (ent (d.full m) i).st) ∧
      (ent (d.full m) i).g = ⁅(ent (d.full m) a).g, (ent (d.full m) b).g⁆ := by
  intro i hi a b hdf
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr] at hdf ⊢
  have hm1 : 1 ≤ m := by omega
  have hcore := core_Y0 hd
  have hY0 : ∀ κ < d.t, ent (d.full m) (d.pos κ) = ent d.Y0 (d.pos κ) := fun κ hκ =>
    d.full_prefix hm1 (show d.pos κ < d.off 1 from (hcore κ hκ).1)
  have hgu : ∀ κ < d.t, (ent (d.full m) (d.pos κ)).g = d.u κ ∧
      (ent (d.full m) (d.pos κ)).lv = 0 := by
    intro κ hκ
    rw [hY0 κ hκ]
    have hmem : ent d.Y0 (d.pos κ) ∈ d.Y 0 := ent_mem _ (hcore κ hκ).1
    exact ⟨(d.Y_ci 0 _ hmem κ (hcore κ hκ).2).2.1, d.Y_lv 0 _ hmem⟩
  obtain ⟨c, hc, -, -, -, -, hec | hec⟩ := d.Y_src w _ (ent_mem _ hr)
  swap
  · rw [hec.1] at hdf
    exact absurd hdf (by simp)
  rw [hec] at hdf ⊢
  rcases w with _ | _ | w
  · rw [(d.cands_df 0 c hc).2.mpr rfl] at hdf
    exact absurd hdf (by simp)
  · obtain ⟨a', b', hab, hb, rfl⟩ := (d.mem_cand1 c).mp hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hdf
    obtain ⟨rfl, rfl⟩ := hdf
    have ha' : a' < d.t := by omega
    have hoff : d.off 1 ≤ d.off (0 + 1) + r := Nat.le_add_right _ _
    refine ⟨lt_of_lt_of_le (hcore a' ha').1 hoff, lt_of_lt_of_le (hcore b' hb).1 hoff,
      ⟨b', hb, rfl⟩, ?_, fun _ => ⟨a', b', hab, hb, rfl, rfl, rfl⟩, ?_⟩
    · show 1 = _
      simp [(hgu a' ha').2]
    · show ⁅d.u a', d.u b'⁆ = _
      rw [(hgu a' ha').1, (hgu b' hb).1]
  · obtain ⟨r', hr', b', hb, rfl⟩ := (d.mem_commC _ _ _ c).mp hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hdf
    obtain ⟨rfl, rfl⟩ := hdf
    have hw1 : w + 1 < m := by omega
    have hoff1 : d.off 1 ≤ d.off (w + 1 + 1) := d.off_mono (by omega)
    have hoffs : d.off (w + 1 + 1) = d.off (w + 1) + (d.Y (w + 1)).length := d.off_succ (w + 1)
    have hea : ent (d.full m) (d.off (w + 1) + r') = ent (d.Y (w + 1)) r' := d.ent_full hw1 hr'
    refine ⟨by omega, lt_of_lt_of_le (show d.pos b' < d.off 1 from (hcore b' hb).1) (by omega), ⟨b', hb, rfl⟩, ?_,
      fun h => by have h' : w + 2 = 1 := h; omega, ?_⟩
    · show w + 2 = _
      rw [hea, d.Y_lv (w + 1) _ (ent_mem _ hr')]
    · show ⁅(ent (d.Y (w + 1)) r').g, d.u b'⁆ = _
      rw [hea, (hgu b' hb).1]

lemma good_core {d : Dat G} (hd : d.Hyp m) :
    ∀ κ < d.t, d.pos κ < (d.full m).length ∧ (ent (d.full m) (d.pos κ)).ci = some κ := by
  intro κ hκ
  have hc := core_Y0 hd κ hκ
  have hm1 : 1 ≤ m := by
    by_contra h0
    push_neg at h0
    have h' := hc.1
    rw [show d.Y0 = d.Y 0 from rfl, Y_nil hd (w := 0) (by omega)] at h'
    simp at h'
  have hoff : d.pos κ < d.off 1 := hc.1
  refine ⟨?_, ?_⟩
  · rw [full_length]
    exact lt_of_lt_of_le hoff (d.off_mono hm1)
  · rw [d.full_prefix hm1 hoff]
    exact hc.2

lemma good_steps {d : Dat G} (hd : d.Hyp m) :
    ∀ β, 1 ≤ β → β < d.t → ∃ i < (d.full m).length, (ent (d.full m) i).lv = 1 ∧
      (ent (d.full m) i).st = β := by
  intro β hβ1 hβ
  obtain ⟨e, he, hlv, hst⟩ := steps_Y1 hd β hβ1 hβ
  obtain ⟨r, hr, rfl⟩ := exists_ent_of_mem he
  have hm2 : 1 < m := by
    by_contra h0
    push_neg at h0
    rw [Y_nil hd (w := 1) h0] at hr
    simp at hr
  refine ⟨d.off 1 + r, ?_, ?_⟩
  · rw [full_length]
    have h1 : d.off 2 ≤ d.off m := d.off_mono hm2
    have h2 : d.off 2 = d.off 1 + (d.Y 1).length := d.off_succ 1
    omega
  · rw [d.ent_full hm2 hr]
    exact ⟨hlv, hst⟩

lemma good_span {d : Dat G} (hd : d.Hyp m) :
    ∀ w k, k ≤ (d.full m).length → (∀ i < (d.full m).length, i < k ↔ (ent (d.full m) i).lv < w) →
      lcs G w ≤ cl (((d.full m).map Ent.g).drop k) := by
  intro w k hk hcut
  by_cases hw : w ≤ m
  · have hoff : d.off w ≤ (d.full m).length := by rw [full_length]; exact d.off_mono hw
    have hkw : k = d.off w := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have h1 := (d.full_cut m (show k < (d.full m).length by omega) w).mp h
        have h2 := (hcut k (by omega)).mpr h1
        omega
      · have h1 := (hcut (d.off w) (by omega)).mp h
        have h2 := (d.full_cut m (show d.off w < (d.full m).length by omega) w).mpr h1
        omega
    rw [hkw]
    exact le_of_eq (span_drop hd w hw)
  · have hbot : lcs G w = ⊥ := by
      have h := lcs_antitone (D := G) (le_of_lt (not_le.mp hw))
      rw [lcs_eq_bot_of_card hd.prime hd.card] at h
      exact le_bot_iff.mp h
    rw [hbot]
    exact bot_le

lemma good_powrel {d : Dat G} (hd : d.Hyp m) :
    ∀ i < (d.full m).length, (ent (d.full m) i).g ^ d.p ∈
      cl (((d.full m).map Ent.g).drop (i + 1)) := by
  intro i hi
  obtain ⟨w, hw, r, hr, rfl⟩ := d.locate hi
  rw [d.ent_full hw hr]
  have hY := Y_eq d w
  have h := layer_powrel hd.prime hd.card w (d.cands w) (d.cands_mem w) r
    (by rw [← hY]; exact hr)
  rw [← hY, span_drop hd (w + 1) (Nat.succ_le_of_lt hw)] at h
  obtain ⟨R, hR⟩ := d.full_append (Nat.succ_le_of_lt hw)
  have hA : d.off w + r + 1 = ((d.full w).map Ent.g).length + (r + 1) := by
    rw [List.length_map, full_length]
    omega
  have hle : r + 1 ≤ ((d.Y w).map Ent.g).length := by
    rw [List.length_map]
    omega
  have hsplit : ((d.full m).map Ent.g).drop (d.off w + r + 1) =
      ((d.Y w).map Ent.g).drop (r + 1) ++ R.map Ent.g := by
    rw [hR]
    show ((d.full w ++ d.Y w ++ R).map Ent.g).drop (d.off w + r + 1) = _
    rw [List.map_append, List.map_append, List.append_assoc, hA, List.drop_length_add_append,
      List.drop_append_of_le_length hle]
  have hdrop : ((d.full m).map Ent.g).drop (d.off (w + 1)) = R.map Ent.g := by
    rw [hR]
    show ((d.full w ++ d.Y w ++ R).map Ent.g).drop (d.off (w + 1)) = _
    rw [List.map_append, List.map_append, off_succ]
    have hB : d.off w + (d.Y w).length = ((d.full w).map Ent.g ++ (d.Y w).map Ent.g).length := by
      rw [List.length_append, List.length_map, List.length_map, full_length]
    rw [hB, List.drop_append_length]
  rw [hdrop] at h
  rw [hsplit, cl_append]
  exact h

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
  mem := good_mem d m
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
