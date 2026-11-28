import H2Dev.SimsGen
import H2Dev.PowerWords
import H2Dev.DataCount

/-! Bridges between the Sims generating set of `SimsGen.lean`, the power word count of
`PowerWords.lean` (Theorem 3.1) and the data count of `DataCount.lean` (Proposition 2.5).

Part 1 (`SimsGen.toSimsGenSet`, `exists_simsGenSet`, `sims_powerWords_counted`). The flattened
Sims generating set `X : Fin d.n → G` of `exists_sims_gen`, with layer lengths `r : ℕ → ℕ`, is
reindexed by `SimsIdx c (brR r c)` through the explicit equivalence `brEquiv`
(`⟨i, v⟩ ↦ fOff r i + v`), where `d.n = fOff r c` (`SimsGen.n_eq`). The relative orders, the
layer property, the minimality of the layer generating sets (from `layer_card`), the relative
order relation (25) (from the power relations and the support of the power word array) and the
Sims normal form (26) (from `nf_exists`, `nf_unique` and `nf_sub`) give a `SimsGenSet`, so the
power word array of the Sims generating set of every nonabelian finite p-group lies in the set
`realizedPW` counted by Theorem 3.1.

Part 2 (`ncard_classes_le_fullData`). See the section docstring below. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section ListProd

/-- The ordered product `sprod` as a list product. -/
lemma sprod_eq_prod_ofFn {D : Type u} [Group D] : ∀ (n : ℕ) (f : Fin n → D),
    sprod n f = (List.ofFn f).prod
  | 0, f => by
    show (1 : D) = (List.ofFn f).prod
    rw [List.ofFn_zero, List.prod_nil]
  | n + 1, f => by
    show f 0 * sprod n (fun i => f i.succ) = _
    rw [sprod_eq_prod_ofFn n, List.ofFn_succ, List.prod_cons]

lemma ofFn_val_congr {D : Type u} {n n' : ℕ} (h : n = n') (F : ℕ → D) :
    List.ofFn (fun t : Fin n => F t.val) = List.ofFn (fun t : Fin n' => F t.val) := by
  subst h
  rfl

/-- Splitting an ordered product over the flattened positions into the layer blocks. -/
lemma prod_ofFn_fOff {D : Type u} [Monoid D] (r : ℕ → ℕ) (F : ℕ → D) : ∀ c : ℕ,
    (List.ofFn fun t : Fin (fOff r c) => F t.val).prod =
      (List.ofFn fun i : Fin c =>
        (List.ofFn fun v : Fin (r i.val) => F (fOff r i.val + v.val)).prod).prod
  | 0 => by
    show (List.ofFn fun t : Fin 0 => F t.val).prod =
      (List.ofFn fun i : Fin 0 =>
        (List.ofFn fun v : Fin (r i.val) => F (fOff r i.val + v.val)).prod).prod
    rw [List.ofFn_zero, List.ofFn_zero]
  | c + 1 => by
    have hL : (List.ofFn fun t : Fin (fOff r c + r c) => F t.val) =
        (List.ofFn fun t : Fin (fOff r c) => F t.val) ++
          (List.ofFn fun v : Fin (r c) => F (fOff r c + v.val)) := by
      rw [List.ofFn_add] <;> rfl
    have hR : (List.ofFn fun i : Fin (c + 1) =>
        (List.ofFn fun v : Fin (r i.val) => F (fOff r i.val + v.val)).prod) =
        (List.ofFn fun i : Fin c =>
          (List.ofFn fun v : Fin (r i.val) => F (fOff r i.val + v.val)).prod) ++
          [(List.ofFn fun v : Fin (r c) => F (fOff r c + v.val)).prod] := by
      rw [List.ofFn_add] <;> rfl
    show (List.ofFn fun t : Fin (fOff r c + r c) => F t.val).prod = _
    rw [hL, hR, List.prod_append, List.prod_append, prod_ofFn_fOff r F c, List.prod_singleton]

/-- Extension of a function on `Fin n` by `1`. -/
def brExt {D : Type u} [One D] {n : ℕ} (f : Fin n → D) (k : ℕ) : D :=
  if h : k < n then f ⟨k, h⟩ else 1

lemma brExt_val {D : Type u} [One D] {n : ℕ} (f : Fin n → D) (t : Fin n) :
    brExt f t.val = f t := by
  unfold brExt
  exact dif_pos t.isLt

end ListProd

section LayerQuot

variable {G : Type u} [Group G]

/-- Generators of a layer modulo the next term generate the layer quotient. -/
theorem layerQ_closure_eq_top (i : ℕ) {N : ℕ} (x : Fin N → G) (hx : ∀ v, x v ∈ lcs G i)
    (h : lcs G i ≤ Subgroup.closure (Set.range x) ⊔ lcs G (i + 1)) :
    Subgroup.closure (Set.range fun v =>
      (QuotientGroup.mk (⟨x v, hx v⟩ : lcs G i) : LayerQ G i)) = ⊤ := by
  set Y := Subgroup.closure (Set.range fun v =>
      (QuotientGroup.mk (⟨x v, hx v⟩ : lcs G i) : LayerQ G i)) with hY
  have hK : lcs G i ≤ (Y.comap (QuotientGroup.mk' ((lcs G (i + 1)).subgroupOf (lcs G i)))).map
      (lcs G i).subtype := by
    refine h.trans (sup_le ?_ ?_)
    · rw [Subgroup.closure_le]
      rintro _ ⟨v, rfl⟩
      exact ⟨⟨x v, hx v⟩, Subgroup.subset_closure ⟨v, rfl⟩, rfl⟩
    · intro z hz
      have hz' : z ∈ lcs G i := lcs_antitone (Nat.le_succ i) hz
      refine ⟨⟨z, hz'⟩, ?_, rfl⟩
      show QuotientGroup.mk' ((lcs G (i + 1)).subgroupOf (lcs G i)) ⟨z, hz'⟩ ∈ Y
      have h1 : QuotientGroup.mk' ((lcs G (i + 1)).subgroupOf (lcs G i)) ⟨z, hz'⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hz)
      rw [h1]
      exact Y.one_mem
  rw [eq_top_iff]
  rintro q -
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨z', hz', hzz⟩ := hK z.2
  have hz2 : z' = z := Subtype.ext hzz
  rw [hz2] at hz'
  exact hz'

/-- Conversely, lifts of generators of the layer quotient generate the layer modulo the next
term. -/
theorem layer_le_of_closure_eq_top (i : ℕ) {N : ℕ} (x : Fin N → lcs G i)
    (h : Subgroup.closure (Set.range fun v => (QuotientGroup.mk (x v) : LayerQ G i)) = ⊤) :
    lcs G i ≤ Subgroup.closure (Set.range fun v => (x v : G)) ⊔ lcs G (i + 1) := by
  intro z hz
  set M := Subgroup.closure (Set.range fun v => (x v : G)) ⊔ lcs G (i + 1) with hM
  have hle : Subgroup.closure (Set.range fun v => (QuotientGroup.mk (x v) : LayerQ G i)) ≤
      (M.subgroupOf (lcs G i)).map
        (QuotientGroup.mk' ((lcs G (i + 1)).subgroupOf (lcs G i))) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨x v, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨v, rfl⟩)), rfl⟩
  rw [h] at hle
  obtain ⟨z', hz', hzz⟩ :=
    hle (Subgroup.mem_top (QuotientGroup.mk (⟨z, hz⟩ : lcs G i) : LayerQ G i))
  have hzz' : (QuotientGroup.mk z' : LayerQ G i) = QuotientGroup.mk ⟨z, hz⟩ := hzz
  have h2 : z'⁻¹ * ⟨z, hz⟩ ∈ (lcs G (i + 1)).subgroupOf (lcs G i) := QuotientGroup.eq.mp hzz'
  have h2' : ((z'⁻¹ * ⟨z, hz⟩ : lcs G i) : G) ∈ lcs G (i + 1) := Subgroup.mem_subgroupOf.mp h2
  have hz'' : (z' : G) ∈ M := Subgroup.mem_subgroupOf.mp hz'
  have h3 : z = (z' : G) * ((z'⁻¹ * ⟨z, hz⟩ : lcs G i) : G) := by simp
  rw [h3]
  exact M.mul_mem hz'' (Subgroup.mem_sup_right h2')

/-- A generating family of the layer quotient has at least `R` elements, where
`p ^ R |K| = |γ_{i+1}|` for the Frattini subgroup `K = layK p G i` of the layer. -/
theorem layer_rank_le [Finite G] {p : ℕ} (hp : p.Prime) (i R : ℕ)
    (hcard : p ^ R * Nat.card (layK p G i) = Nat.card (lcs G i))
    (N : ℕ) (y : Fin N → LayerQ G i) (hy : Subgroup.closure (Set.range y) = ⊤) : R ≤ N := by
  choose x hx using fun v => QuotientGroup.mk_surjective (y v)
  have hy' : Subgroup.closure (Set.range fun v => (QuotientGroup.mk (x v) : LayerQ G i)) = ⊤ := by
    have e : (fun v => (QuotientGroup.mk (x v) : LayerQ G i)) = y := funext hx
    rw [e]
    exact hy
  have h1 := layer_le_of_closure_eq_top i x hy'
  have hxN : ∀ j, brExt (fun v => (x v : G)) j ∈ lcs G i := by
    intro j
    unfold brExt
    split_ifs
    · exact (x _).2
    · exact one_mem _
  have hrange : Set.range (fun v => (x v : G)) ⊆ brExt (fun v => (x v : G)) '' Set.Iio N := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v.val, v.isLt, brExt_val _ v⟩
  have h2 : lcs G i ≤ Subgroup.closure (brExt (fun v => (x v : G)) '' Set.Iio N) ⊔ layK p G i :=
    h1.trans (sup_le_sup (Subgroup.closure_mono hrange) (lcs_succ_le_layK p i))
  have hN : ∀ j, (Subgroup.closure (brExt (fun v => (x v : G)) '' Set.Iio j) ⊔
      layK p G i).Normal := fun j =>
    layK_normal_sup p i _ (by rintro _ ⟨k, -, rfl⟩; exact hxN k)
  have h3 := card_closure_sup_le_of hp.pos (layK p G i) (brExt (fun v => (x v : G))) hN
    (fun j => pow_mem_layK p i _ (hxN j)) N
  have h4 : Nat.card (lcs G i) ≤ p ^ N * Nat.card (layK p G i) :=
    (Subgroup.card_le_of_le h2).trans h3
  have h5 : 0 < Nat.card (layK p G i) := Nat.card_pos
  rw [← hcard] at h4
  have h6 : p ^ R ≤ p ^ N := Nat.le_of_mul_le_mul_right h4 h5
  by_contra hRN
  have e3 : p ^ (N + 1) ≤ p ^ R := Nat.pow_le_pow_right hp.pos (by omega)
  have e1 : p ^ (N + 1) = p ^ N * p := pow_succ p N
  have e2 : p ^ N * 2 ≤ p ^ N * p := Nat.mul_le_mul_left _ hp.two_le
  have e4 : 0 < p ^ N := pow_pos hp.pos N
  rw [e1] at e3
  linarith

end LayerQuot

section Reindex

variable {G : Type u} [Group G] {p : ℕ} {u : ℕ → G} {d : SimsData} {X : Fin d.n → G}
  {r : ℕ → ℕ}

/-- The layer ranks as a function on `Fin c`. -/
abbrev brR (r : ℕ → ℕ) (c : ℕ) : Fin c → ℕ := fun i => r i.val

lemma brPos_lt {n : ℕ} (r : ℕ → ℕ) {c : ℕ} (hn : n = fOff r c) (i : Fin c)
    (v : Fin (r i.val)) : fOff r i.val + v.val < n := by
  have h1 := fOff_mono r (show i.val + 1 ≤ c from i.isLt)
  rw [fOff_succ] at h1
  have h2 := v.isLt
  omega

/-- The flattened position `fOff r i + v` of the index `⟨i, v⟩`. -/
def brPos {n : ℕ} (r : ℕ → ℕ) {c : ℕ} (hn : n = fOff r c) (k : SimsIdx c (brR r c)) : Fin n :=
  ⟨fOff r k.1.val + k.2.val, brPos_lt r hn k.1 k.2⟩

lemma SimsGen.lv_brPos (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k : SimsIdx c (brR r c)) : d.lv (brPos r hn k) = k.1.val :=
  (hS.layer_iff (brPos r hn k) k.1.val).mpr
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left k.2.isLt _⟩

lemma SimsGen.lv_lt (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c) (t : Fin d.n) :
    d.lv t < c := by
  by_contra h
  have h1 := fOff_mono r (not_lt.mp h)
  have h2 := ((hS.layer_iff t (d.lv t)).mp rfl).1
  have h3 := t.isLt
  omega

lemma SimsGen.brPos_inj (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c) :
    Function.Injective (brPos r hn) := by
  rintro ⟨i, v⟩ ⟨i', v'⟩ h
  have e1 : d.lv (brPos r hn ⟨i, v⟩) = i.val := hS.lv_brPos hn ⟨i, v⟩
  have e2 : d.lv (brPos r hn ⟨i', v'⟩) = i'.val := hS.lv_brPos hn ⟨i', v'⟩
  rw [h] at e1
  have h1 : i = i' := Fin.ext (e1.symm.trans e2)
  subst h1
  have h3 : fOff r i.val + v.val = fOff r i.val + v'.val := congrArg Fin.val h
  have h2 : v = v' := Fin.ext (by omega)
  subst h2
  rfl

lemma SimsGen.brPos_surj (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c) :
    Function.Surjective (brPos r hn) := by
  intro t
  obtain ⟨h1, h2⟩ := (hS.layer_iff t (d.lv t)).mp rfl
  refine ⟨⟨⟨d.lv t, hS.lv_lt hn t⟩, ⟨t.val - fOff r (d.lv t),
    show t.val - fOff r (d.lv t) < r (d.lv t) by omega⟩⟩, ?_⟩
  apply Fin.ext
  show fOff r (d.lv t) + (t.val - fOff r (d.lv t)) = t.val
  omega

/-- The explicit equivalence between `SimsIdx c (brR r c)` and the flattened positions. -/
noncomputable def SimsGen.brEquiv (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c) :
    SimsIdx c (brR r c) ≃ Fin d.n :=
  Equiv.ofBijective (brPos r hn) ⟨hS.brPos_inj hn, hS.brPos_surj hn⟩

lemma SimsGen.brEquiv_apply (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k : SimsIdx c (brR r c)) : hS.brEquiv hn k = brPos r hn k := rfl

lemma SimsGen.lv_brEquiv (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k : SimsIdx c (brR r c)) : d.lv (hS.brEquiv hn k) = k.1.val :=
  hS.lv_brPos hn k

lemma SimsGen.val_brEquiv (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k : SimsIdx c (brR r c)) : (hS.brEquiv hn k).val = fOff r k.1.val + k.2.val := rfl

lemma SimsGen.mem_lcs (hS : SimsGen p u d X r) (t : Fin d.n) : X t ∈ lcs G (d.lv t) :=
  lv_mem_lcs d hS.valid.toStruct X hS.realizes.dfeq t

lemma SimsGen.memE (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k : SimsIdx c (brR r c)) : X (hS.brEquiv hn k) ∈ lcs G k.1 := by
  have h := hS.mem_lcs (hS.brEquiv hn k)
  rwa [hS.lv_brEquiv hn k] at h

/-- The Sims normal form word of `X` is the blockwise product `fullProd` of `PowerWords`. -/
lemma SimsGen.nfw_eq_fullProd (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (e : SimsIdx c (brR r c) → ℕ) :
    fullProd (fun k => X (hS.brEquiv hn k)) e = nfw X (fun t => e ((hS.brEquiv hn).symm t)) := by
  have h1 : nfw X (fun t => e ((hS.brEquiv hn).symm t)) =
      (List.ofFn fun t : Fin d.n =>
        brExt (fun t => X t ^ e ((hS.brEquiv hn).symm t)) t.val).prod := by
    unfold nfw
    rw [sprod_eq_prod_ofFn]
    simp only [brExt_val]
  have key : ∀ (i : Fin c) (v : Fin (r i.val)),
      brExt (fun t => X t ^ e ((hS.brEquiv hn).symm t)) (fOff r i.val + v.val) =
        X (hS.brEquiv hn ⟨i, v⟩) ^ e ⟨i, v⟩ := by
    intro i v
    have h := brExt_val (fun t => X t ^ e ((hS.brEquiv hn).symm t)) (hS.brEquiv hn ⟨i, v⟩)
    refine h.trans ?_
    show X (hS.brEquiv hn ⟨i, v⟩) ^ e ((hS.brEquiv hn).symm (hS.brEquiv hn ⟨i, v⟩)) = _
    rw [Equiv.symm_apply_apply]
  rw [h1, ofFn_val_congr hn, prod_ofFn_fOff r _ c]
  unfold fullProd blockProd
  simp only [key]

/-- The generators of the tail subgroup `lset d i (fOff r i + j)` lie in the Sims series term
`relSub g i j`. -/
lemma SimsGen.closure_lset_le (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (i : Fin c) (j : ℕ) :
    Subgroup.closure (X '' lset d i.val (fOff r i.val + j)) ≤
      relSub (fun k => X (hS.brEquiv hn k)) i j := by
  rw [Subgroup.closure_le]
  rintro _ ⟨t, ht, rfl⟩
  rcases (mem_lset d).mp ht with h | ⟨h1, h2⟩
  · exact Subgroup.mem_sup_right
      (lcs_antitone (show i.val + 1 ≤ d.lv t by omega) (hS.mem_lcs t))
  · apply Subgroup.mem_sup_left
    apply Subgroup.subset_closure
    obtain ⟨⟨i', v'⟩, rfl⟩ := (hS.brEquiv hn).surjective t
    have hk : d.lv (hS.brEquiv hn ⟨i', v'⟩) = i'.val := hS.lv_brEquiv hn _
    have hii : i' = i := Fin.ext (by omega)
    subst hii
    have h3 : fOff r i'.val + v'.val < fOff r i'.val + j := h2
    exact ⟨v', by omega, rfl⟩

/-- The Sims series term `relSub g i j` is contained in the tail subgroup. -/
lemma SimsGen.relSub_le (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (i : Fin c) (j : ℕ) :
    relSub (fun k => X (hS.brEquiv hn k)) i j ≤
      Subgroup.closure (X '' lset d i.val (fOff r i.val + j)) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨hS.brEquiv hn ⟨i, v⟩, ?_, rfl⟩
    refine (mem_lset d).mpr (Or.inr ⟨(hS.lv_brEquiv hn ⟨i, v⟩).symm, ?_⟩)
    show fOff r i.val + v.val < fOff r i.val + j
    omega
  · refine (hS.deep (i.val + 1) (by omega)).trans (Subgroup.closure_mono ?_)
    rintro _ ⟨t, ht, rfl⟩
    have ht' : i.val + 1 ≤ d.lv t := ht
    exact ⟨t, (mem_lset d).mpr (Or.inl (by omega)), rfl⟩

/-- The Sims normal form (26) for the reindexed generating set. -/
noncomputable def SimsGen.toNF (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c) :
    SimsNormalForm p (fun k => d.a (hS.brEquiv hn k)) (fun k => X (hS.brEquiv hn k)) where
  coord x h := ⟨Classical.choose (hS.nf_exists x) (hS.brEquiv hn h),
    (Classical.choose_spec (hS.nf_exists x)).1 _⟩
  uniq e := by
    funext h
    apply Fin.ext
    obtain ⟨hb, hx⟩ := Classical.choose_spec
      (hS.nf_exists (fullProd (fun k => X (hS.brEquiv hn k)) fun h => (e h).val))
    have hb' : ∀ t, (e ((hS.brEquiv hn).symm t)).val < p ^ d.a t := by
      intro t
      have h0 := (e ((hS.brEquiv hn).symm t)).isLt
      simpa only [Equiv.apply_symm_apply] using h0
    have h2 := hS.nf_unique _ (fun t => (e ((hS.brEquiv hn).symm t)).val) hb hb'
      (hx.symm.trans (hS.nfw_eq_fullProd hn _))
    show Classical.choose (hS.nf_exists (fullProd (fun k => X (hS.brEquiv hn k))
      fun h => (e h).val)) (hS.brEquiv hn h) = (e h).val
    rw [h2]
    show (e ((hS.brEquiv hn).symm (hS.brEquiv hn h))).val = (e h).val
    rw [Equiv.symm_apply_apply]
  sub := by
    intro i j x hx
    obtain ⟨e0, hsupp, hbd, hx0⟩ :=
      hS.nf_sub i.val (fOff r i.val + j) x (hS.relSub_le hn i j hx)
    refine ⟨fun h => ⟨e0 (hS.brEquiv hn h), hbd (hS.brEquiv hn h)⟩, ?_, ?_⟩
    · rintro ⟨i', v'⟩ hh
      show e0 (hS.brEquiv hn ⟨i', v'⟩) = 0
      by_contra hne
      have hm := (mem_lset d).mp (hsupp _ hne)
      have hk : d.lv (hS.brEquiv hn ⟨i', v'⟩) = i'.val := hS.lv_brEquiv hn _
      have hv : (hS.brEquiv hn ⟨i', v'⟩).val = fOff r i'.val + v'.val := rfl
      rcases hh with h1 | ⟨h1, h2⟩
      · have h1' : i'.val < i.val := h1
        omega
      · have h1' : i' = i := h1
        subst h1'
        have h2' : j ≤ v'.val := h2
        omega
    · rw [hS.nfw_eq_fullProd hn, hx0]
      refine congrArg (nfw X) (funext fun t => ?_)
      show e0 (hS.brEquiv hn ((hS.brEquiv hn).symm t)) = e0 t
      rw [Equiv.apply_symm_apply]

/-- Bridge: the Sims generating set of `SimsGen` is a `SimsGenSet` in the sense of
`PowerWords` (Section 2.1, (25)-(26)), after the explicit reindexing `brEquiv`. -/
noncomputable def SimsGen.toSimsGenSet [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r)
    {c : ℕ} (hn : d.n = fOff r c) :
    SimsGenSet p (fun k => d.a (hS.brEquiv hn k)) (fun k => X (hS.brEquiv hn k)) where
  mem := hS.memE hn
  gen := by
    intro i
    refine layerQ_closure_eq_top i.val (fun v => X (hS.brEquiv hn ⟨i, v⟩))
      (fun v => hS.memE hn ⟨i, v⟩) ?_
    refine (hS.layer_gen i.val).trans (sup_le_sup_right (Subgroup.closure_mono ?_) _)
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨⟨i', v'⟩, rfl⟩ := (hS.brEquiv hn).surjective t
    have hk : d.lv (hS.brEquiv hn ⟨i', v'⟩) = i'.val := hS.lv_brEquiv hn _
    have ht' : d.lv (hS.brEquiv hn ⟨i', v'⟩) = i.val := ht
    have hii : i' = i := Fin.ext (by omega)
    subst hii
    exact ⟨v', rfl⟩
  minimum := fun i N y hy => layer_rank_le hp i.val (r i.val) (hS.layer_card i.val) N y hy
  pos := fun k => hS.a_pos _
  rel := by
    intro i j
    show X (hS.brEquiv hn ⟨i, j⟩) ^ p ^ d.a (hS.brEquiv hn ⟨i, j⟩) ∈ _
    rw [hS.realizes.pow (hS.brEquiv hn ⟨i, j⟩)]
    refine hS.closure_lset_le hn i j.val (nfw_mem X _ _ fun t ht => ?_)
    have hpr := hS.valid.b_supp _ t ht
    have hk : d.lv (hS.brEquiv hn ⟨i, j⟩) = i.val := hS.lv_brEquiv hn _
    have hv : (hS.brEquiv hn ⟨i, j⟩).val = fOff r i.val + j.val := rfl
    unfold SimsData.prec at hpr
    refine (mem_lset d).mpr ?_
    omega
  nf := hS.toNF hn

/-- Every nonabelian group of order `p ^ m` has a Sims generating set in the sense of
`PowerWords.SimsGenSet` (obtained from `exists_sims_gen` by `SimsGen.toSimsGenSet`). -/
theorem exists_simsGenSet {G : Type u} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ m) (hna : lcs G 1 ≠ ⊥) :
    ∃ (c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ) (g : SimsIdx c r → G),
      Nonempty (SimsGenSet p a g) := by
  obtain ⟨u, d, X, r, -, -, -, -, -, -, -, -, hS⟩ := exists_sims_gen hp hG hna
  obtain ⟨c, hn⟩ := hS.n_eq
  exact ⟨c, brR r c, _, _, ⟨hS.toSimsGenSet hp hn⟩⟩

/-- Theorem 3.1 applied to the Sims generating set: for every nonabelian group `G` of order
`p ^ m` there is a Sims generating set `S` (with `c` layers of ranks `r` and relative order array
`a ≥ 1`) whose power word array lies in the set `realizedPW p c r a` of Theorem 3.1, which has at
most `p ^ Σ_i [ r_i m_{i+1} + (r_i - 1)(s_i - r_i) ]` elements. -/
theorem sims_powerWords_counted {G : Type} [Group G] [Finite G] {p m : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p ^ m) (hna : lcs G 1 ≠ ⊥) :
    ∃ (c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ) (g : SimsIdx c r → G)
      (S : SimsGenSet p a g), (∀ k, 1 ≤ a k) ∧ S.powerWords ∈ realizedPW p c r a ∧
        (realizedPW p c r a).ncard ≤ p ^ pwBound2 a := by
  obtain ⟨c, r, a, g, ⟨S⟩⟩ := exists_simsGenSet hp.out hG hna
  exact ⟨c, r, a, g, S, S.pos, SimsGenSet.mem_realizedPW (IsPGroup.of_card hG) S,
    liqiao_thm_3_1 c r a S.pos⟩

end Reindex


section NatLemmas

lemma le_fOff (r : ℕ → ℕ) : ∀ c, (∀ w < c, 1 ≤ r w) → c ≤ fOff r c
  | 0, _ => Nat.zero_le _
  | c + 1, h => by
    have h1 := le_fOff r c (fun w hw => h w (by omega))
    have h2 := h c (by omega)
    rw [fOff_succ]
    omega

lemma fOff_congr {r r' : ℕ → ℕ} {c : ℕ} (h : ∀ w < c, r w = r' w) :
    ∀ w ≤ c, fOff r w = fOff r' w
  | 0, _ => rfl
  | w + 1, hw => by
    rw [fOff_succ, fOff_succ, fOff_congr h w (by omega), h w (by omega)]

lemma sum_fin_eq_fOff (r : ℕ → ℕ) : ∀ c, ∑ i : Fin c, r i.val = fOff r c
  | 0 => by
    rw [Fin.sum_univ_zero]
    rfl
  | c + 1 => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [sum_fin_eq_fOff r c, fOff_succ]

lemma sum_ite_ge_fOff (r : ℕ → ℕ) (k : ℕ) : ∀ c, k ≤ c →
    ∑ i : Fin c, (if k ≤ i.val then r i.val else 0) = fOff r c - fOff r k
  | 0, hk => by
    rw [Fin.sum_univ_zero]
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | c + 1, hk => by
    rcases Nat.lt_or_ge k (c + 1) with hlt | hge
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      rw [sum_ite_ge_fOff r k c (by omega), if_pos (show k ≤ c by omega), fOff_succ]
      have := fOff_mono r (show k ≤ c by omega)
      omega
    · have hk' : k = c + 1 := by omega
      subst hk'
      have hz : ∀ i : Fin (c + 1), (if c + 1 ≤ i.val then r i.val else 0) = 0 :=
        fun i => if_neg (by have := i.isLt; omega)
      rw [Finset.sum_eq_zero (fun i _ => hz i), Nat.sub_self]

/-- In a monotone sequence on `[0, R)`, the positions with value `< k` form an initial
segment. -/
lemma lt_iff_lt_card_filter (f : ℕ → ℕ) (R : ℕ) (hf : ∀ i j, i ≤ j → j < R → f i ≤ f j)
    (k j : ℕ) (hj : j < R) :
    f j < k ↔ j < ((Finset.range R).filter (fun i => f i < k)).card := by
  constructor
  · intro h
    have hsub : Finset.range (j + 1) ⊆ (Finset.range R).filter (fun i => f i < k) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, lt_of_le_of_lt (hf i j (by omega) hj) h⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    omega
  · intro h
    by_contra hk
    have hk' : k ≤ f j := not_lt.mp hk
    have hsub : (Finset.range R).filter (fun i => f i < k) ⊆ Finset.range j := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_range]
      by_contra hij
      have h2 := hf j i (by omega) hi.1
      omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    omega

lemma card_filter_lt_eq_sum (f : ℕ → ℕ) (R k : ℕ) :
    ((Finset.range R).filter (fun i => f i < k)).card =
      ∑ b ∈ Finset.range k, ((Finset.range R).filter (fun i => f i = b)).card := by
  have hmaps : ∀ i ∈ (Finset.range R).filter (fun i => f i < k), f i ∈ Finset.range k := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_range.mpr hi.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [Finset.mem_range] at hb
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by omega, h⟩

/-- Two monotone sequences on `[0, R)` with the same fibre cardinalities agree. -/
lemma eq_of_mono_fiber (f g : ℕ → ℕ) (R : ℕ) (hf : ∀ i j, i ≤ j → j < R → f i ≤ f j)
    (hg : ∀ i j, i ≤ j → j < R → g i ≤ g j)
    (hfib : ∀ k, ((Finset.range R).filter (fun i => f i = k)).card =
      ((Finset.range R).filter (fun i => g i = k)).card)
    (j : ℕ) (hj : j < R) : f j = g j := by
  have hA : ∀ k, ((Finset.range R).filter (fun i => f i < k)).card =
      ((Finset.range R).filter (fun i => g i < k)).card := by
    intro k
    rw [card_filter_lt_eq_sum, card_filter_lt_eq_sum]
    exact Finset.sum_congr rfl fun b _ => hfib b
  have h1 := (lt_iff_lt_card_filter f R hf (f j + 1) j hj).mp (Nat.lt_succ_self _)
  rw [hA] at h1
  have h1' := (lt_iff_lt_card_filter g R hg (f j + 1) j hj).mpr h1
  have h2 := (lt_iff_lt_card_filter g R hg (g j + 1) j hj).mp (Nat.lt_succ_self _)
  rw [← hA] at h2
  have h2' := (lt_iff_lt_card_filter f R hf (g j + 1) j hj).mpr h2
  omega

end NatLemmas

/-! ### Part 2: the class of `G` is determined by its Sims data, which lies in a finite set

`FullData p m` is the recorded Sims presentation data `RecData m` of Proposition 2.5
(`DataCount`) together with a power word array and a commutator coefficient array, flattened
along the `r.tot` generators, with entries `< p ^ m`. `SimsGen.enc` encodes the Sims generating
set of `SimsGen` with the exact conventions of `DataCount`:
* `c` is the number `nL` of layers (the least `c` with `fOff r c = n`; every layer below it is
  nonempty, `nL_pos`), `s = d.s`, and the `RankVec` is `i ↦ r i`;
* the increments of `(d_k)` are the block sizes `#{j < r_2 : co(j) = k + 1}` (`brFib`), where
  `co(j)` is the core index of the `j`-th weight-2 generator (0-based, so block `0` is empty
  and the blocks `1, ..., s - 1` are the paper's `d_{k+1} - d_k`);
* `f(j)` is the first index of the `j`-th weight-2 generator (`brPa`), and the index pair of the
  `j`-th generator of weight `≥ 3` is the pair of flattened positions of its two factors
  (`brPr`), both `< n ≤ m`;
* the relative order array, the power word array and the commutator coefficients on the index
  ranges `SimsData.Rec` of Proposition 2.4 (`0` outside) are read off the flattened arrays.
`SimsGen.normalize_eq_of_enc` shows that equal codes give equal normalised data
(`SimsData.normalize`: the junk definitions at weight 1 and the coefficients outside the recorded
ranges are reset), and Proposition 2.4 (`sims_rigidity`) then gives an isomorphism. With INF-1
(`ncard_classes_le_fintype_card`) the number of isomorphism classes of nonabelian groups of
order `p ^ m` is at most `Fintype.card (FullData p m)`, which is at most the Proposition 2.5
count `Fintype.card (RecData m)` times `(p ^ m) ^ (m m) (p ^ m) ^ (m m m)` (the trivial bound for
the arrays). The recorded data alone do not determine the class; the arrays are counted
trivially here, and the sharper counts of the paper (Theorem 3.1 for the power words) refine
this factor. -/

section DataBridge

instance instDecidableSimsDataRec (d : SimsData) (t k : Fin d.n) : Decidable (d.Rec t k) := by
  unfold SimsData.Rec
  infer_instance

/-- Normalised Sims data. -/
def SimsData.normalize (d : SimsData) : SimsData where
  n := d.n
  s := d.s
  lv := d.lv
  df := fun t => if 1 ≤ d.lv t then d.df t else (t, t)
  a := d.a
  b := d.b
  c := fun t k v => if d.Rec t k then d.c t k v else 0

lemma SimsData.normalize_c_supp {d : SimsData} (hd : d.Valid) (t k v : Fin d.n)
    (h : (if d.Rec t k then d.c t k v else 0) ≠ 0) : d.lv t < d.lv v := by
  split_ifs at h with hr
  · exact hd.c_supp t k v h
  · exact absurd rfl h

lemma SimsData.normalize_valid {d : SimsData} (hd : d.Valid) : d.normalize.Valid where
  mono := hd.mono
  s_le := hd.s_le
  core := hd.core
  df_lv := fun t ht => by
    have e : d.normalize.df t = d.df t := if_pos ht
    rw [e]
    exact hd.df_lv t ht
  df_core := fun t ht => by
    have e : d.normalize.df t = d.df t := if_pos ht
    rw [e]
    exact hd.df_core t ht
  df_one := fun t ht => by
    have ht' : d.lv t = 1 := ht
    have e : d.normalize.df t = d.df t := if_pos (show 1 ≤ d.lv t by omega)
    rw [e]
    exact hd.df_one t ht
  b_supp := hd.b_supp
  c_supp := fun t k v h => SimsData.normalize_c_supp hd t k v h

lemma SimsData.normalize_realizes {G : Type u} [Group G] {p : ℕ} {d : SimsData}
    {X : Fin d.n → G} (h : SimsRealizes p d X) : SimsRealizes p d.normalize X where
  card := h.card
  gen := h.gen
  dfeq := fun t ht => by
    have e : d.normalize.df t = d.df t := if_pos ht
    rw [e]
    exact h.dfeq t ht
  pow := h.pow
  comm0 := fun t k ht hk htk => by
    have hrec : d.Rec t k := Or.inl ⟨ht, hk, htk⟩
    have e2 : d.normalize.c t k = d.c t k := funext fun v => if_pos hrec
    rw [e2]
    exact h.comm0 t k ht hk htk
  comm1 := fun t k ht hk => by
    have ht' : d.lv t = 1 := ht
    have e : d.normalize.df t = d.df t := if_pos (show 1 ≤ d.lv t by omega)
    rw [e] at hk
    have hrec : d.Rec t k := Or.inr (Or.inl ⟨ht, hk⟩)
    have e2 : d.normalize.c t k = d.c t k := funext fun v => if_pos hrec
    rw [e2]
    exact h.comm1 t k ht hk
  comm2 := fun t k ht hk => by
    have hrec : d.Rec t k := Or.inr (Or.inr ⟨ht, hk⟩)
    have e2 : d.normalize.c t k = d.c t k := funext fun v => if_pos hrec
    rw [e2]
    exact h.comm2 t k ht hk

/-- Equal normalised data from the pointwise agreement of the flattened arrays. -/
theorem SimsData.normalize_eq {d1 d2 : SimsData} (hn : d1.n = d2.n) (hs : d1.s = d2.s)
    (hlv : ∀ i (h1 : i < d1.n) (h2 : i < d2.n), d1.lv ⟨i, h1⟩ = d2.lv ⟨i, h2⟩)
    (hdf : ∀ i (h1 : i < d1.n) (h2 : i < d2.n), 1 ≤ d1.lv ⟨i, h1⟩ →
      (d1.df ⟨i, h1⟩).1.val = (d2.df ⟨i, h2⟩).1.val ∧
        (d1.df ⟨i, h1⟩).2.val = (d2.df ⟨i, h2⟩).2.val)
    (ha : ∀ i (h1 : i < d1.n) (h2 : i < d2.n), d1.a ⟨i, h1⟩ = d2.a ⟨i, h2⟩)
    (hb : ∀ i j (h1 : i < d1.n) (h1' : j < d1.n) (h2 : i < d2.n) (h2' : j < d2.n),
      d1.b ⟨i, h1⟩ ⟨j, h1'⟩ = d2.b ⟨i, h2⟩ ⟨j, h2'⟩)
    (hc : ∀ i j k (h1 : i < d1.n) (h1' : j < d1.n) (h1'' : k < d1.n) (h2 : i < d2.n)
      (h2' : j < d2.n) (h2'' : k < d2.n),
      (if d1.Rec ⟨i, h1⟩ ⟨j, h1'⟩ then d1.c ⟨i, h1⟩ ⟨j, h1'⟩ ⟨k, h1''⟩ else 0) =
        (if d2.Rec ⟨i, h2⟩ ⟨j, h2'⟩ then d2.c ⟨i, h2⟩ ⟨j, h2'⟩ ⟨k, h2''⟩ else 0)) :
    d1.normalize = d2.normalize := by
  obtain ⟨n1, s1, lv1, df1, a1, b1, c1⟩ := d1
  obtain ⟨n2, s2, lv2, df2, a2, b2, c2⟩ := d2
  have hn' : n1 = n2 := hn
  subst hn'
  have hs' : s1 = s2 := hs
  subst hs'
  have elv : lv1 = lv2 := funext fun t => hlv t.val t.isLt t.isLt
  subst elv
  have ea : a1 = a2 := funext fun t => ha t.val t.isLt t.isLt
  subst ea
  have eb : b1 = b2 := funext fun t => funext fun k => hb t.val k.val t.isLt k.isLt t.isLt k.isLt
  subst eb
  have edf : (fun t => if 1 ≤ lv1 t then df1 t else (t, t)) =
      (fun t => if 1 ≤ lv1 t then df2 t else (t, t)) := by
    funext t
    by_cases h : 1 ≤ lv1 t
    · rw [if_pos h, if_pos h]
      have h' := hdf t.val t.isLt t.isLt h
      exact Prod.ext (Fin.ext h'.1) (Fin.ext h'.2)
    · rw [if_neg h, if_neg h]
  have ec : (fun t k v => if SimsData.Rec ⟨n1, s1, lv1, df1, a1, b1, c1⟩ t k then c1 t k v
      else 0) = (fun t k v => if SimsData.Rec ⟨n1, s1, lv1, df2, a1, b1, c2⟩ t k then c2 t k v
      else 0) := by
    funext t k v
    exact hc t.val k.val v.val t.isLt k.isLt v.isLt t.isLt k.isLt v.isLt
  show SimsData.mk n1 s1 lv1 (fun t => if 1 ≤ lv1 t then df1 t else (t, t)) a1 b1
      (fun t k v => if SimsData.Rec ⟨n1, s1, lv1, df1, a1, b1, c1⟩ t k then c1 t k v else 0) =
    SimsData.mk n1 s1 lv1 (fun t => if 1 ≤ lv1 t then df2 t else (t, t)) a1 b1
      (fun t k v => if SimsData.Rec ⟨n1, s1, lv1, df2, a1, b1, c2⟩ t k then c2 t k v else 0)
  rw [edf, ec]

lemma rigid_of_eq {G H : Type u} [Group G] [Group H] [Finite G] [Finite H] {p : ℕ}
    (hp : p.Prime) (D1 D2 : SimsData) (e : D1 = D2) (hv : D1.Valid) (Y1 : Fin D1.n → G)
    (Y2 : Fin D2.n → H) (k1 : SimsRealizes p D1 Y1) (k2 : SimsRealizes p D2 Y2) :
    Nonempty (G ≃* H) := by
  subst e
  exact sims_rigidity hp D1 hv Y1 Y2 k1 k2

/-- The core index of the `j`-th weight-2 generator. -/
def brCo (d : SimsData) (r : ℕ → ℕ) (j : ℕ) : ℕ :=
  if h : fOff r 1 + j < d.n then (d.df ⟨fOff r 1 + j, h⟩).2.val else 0

/-- The first index of the `j`-th weight-2 generator (the auxiliary function `f`). -/
def brPa (d : SimsData) (r : ℕ → ℕ) (j : ℕ) : ℕ :=
  if h : fOff r 1 + j < d.n then (d.df ⟨fOff r 1 + j, h⟩).1.val else 0

/-- The index pair of the `j`-th generator of weight at least `3`. -/
def brPr (d : SimsData) (r : ℕ → ℕ) (j : ℕ) : ℕ × ℕ :=
  if h : fOff r 2 + j < d.n then ((d.df ⟨fOff r 2 + j, h⟩).1.val, (d.df ⟨fOff r 2 + j, h⟩).2.val)
  else (0, 0)

/-- The flattened relative order array. -/
def brA (d : SimsData) (j : ℕ) : ℕ := if h : j < d.n then d.a ⟨j, h⟩ else 0

/-- The flattened power word array. -/
def brB (d : SimsData) (i j : ℕ) : ℕ :=
  if h : i < d.n ∧ j < d.n then d.b ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The flattened commutator coefficient array on the recorded index ranges. -/
def brCm (d : SimsData) (i j k : ℕ) : ℕ :=
  if h : i < d.n ∧ j < d.n ∧ k < d.n then
    (if d.Rec ⟨i, h.1⟩ ⟨j, h.2.1⟩ then d.c ⟨i, h.1⟩ ⟨j, h.2.1⟩ ⟨k, h.2.2⟩ else 0)
  else 0

/-- The size of the weight-2 block of core index `k + 1`: the increment `d_{k+2} - d_{k+1}`. -/
def brFib (d : SimsData) (r : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range (r 1)).filter (fun j => brCo d r j = k + 1)).card

lemma brCo_eq (d : SimsData) (r : ℕ → ℕ) (t : Fin d.n) (j : ℕ) (hj : fOff r 1 + j = t.val) :
    brCo d r j = (d.df t).2.val := by
  have h : fOff r 1 + j < d.n := by have := t.isLt; omega
  unfold brCo
  rw [dif_pos h]
  have e : (⟨fOff r 1 + j, h⟩ : Fin d.n) = t := Fin.ext hj
  rw [e]

lemma brPa_eq (d : SimsData) (r : ℕ → ℕ) (t : Fin d.n) (j : ℕ) (hj : fOff r 1 + j = t.val) :
    brPa d r j = (d.df t).1.val := by
  have h : fOff r 1 + j < d.n := by have := t.isLt; omega
  unfold brPa
  rw [dif_pos h]
  have e : (⟨fOff r 1 + j, h⟩ : Fin d.n) = t := Fin.ext hj
  rw [e]

lemma brPr_eq (d : SimsData) (r : ℕ → ℕ) (t : Fin d.n) (j : ℕ) (hj : fOff r 2 + j = t.val) :
    brPr d r j = ((d.df t).1.val, (d.df t).2.val) := by
  have h : fOff r 2 + j < d.n := by have := t.isLt; omega
  unfold brPr
  rw [dif_pos h]
  have e : (⟨fOff r 2 + j, h⟩ : Fin d.n) = t := Fin.ext hj
  rw [e]

lemma a_le_of_sum {d : SimsData} {m : ℕ} (hsum : ∑ t, d.a t = m) (t : Fin d.n) : d.a t ≤ m := by
  rw [← hsum]
  exact Finset.single_le_sum (f := d.a) (fun t _ => Nat.zero_le _) (Finset.mem_univ t)

lemma brA_le {d : SimsData} {m : ℕ} (hsum : ∑ t, d.a t = m) (j : ℕ) : brA d j ≤ m := by
  unfold brA
  split_ifs with h
  · exact a_le_of_sum hsum _
  · exact Nat.zero_le _

lemma brB_lt {d : SimsData} {p m : ℕ} (hp : 0 < p) (hb : d.Bounded p) (hsum : ∑ t, d.a t = m)
    (i j : ℕ) : brB d i j < p ^ m := by
  unfold brB
  split_ifs with h
  · exact lt_of_lt_of_le (hb.1 _ _) (Nat.pow_le_pow_right hp (a_le_of_sum hsum _))
  · exact pow_pos hp m

lemma brCm_lt {d : SimsData} {p m : ℕ} (hp : 0 < p) (hb : d.Bounded p) (hsum : ∑ t, d.a t = m)
    (i j k : ℕ) : brCm d i j k < p ^ m := by
  unfold brCm
  split_ifs
  · exact lt_of_lt_of_le (hb.2 _ _ _) (Nat.pow_le_pow_right hp (a_le_of_sum hsum _))
  · exact pow_pos hp m
  · exact pow_pos hp m

lemma brPr_lt (d : SimsData) (r : ℕ → ℕ) {m : ℕ} (hnm : d.n ≤ m) (hm : 0 < m) (j : ℕ) :
    (brPr d r j).1 < m ∧ (brPr d r j).2 < m := by
  unfold brPr
  split_ifs with h
  · exact ⟨lt_of_lt_of_le (d.df ⟨fOff r 2 + j, h⟩).1.isLt hnm,
      lt_of_lt_of_le (d.df ⟨fOff r 2 + j, h⟩).2.isLt hnm⟩
  · exact ⟨hm, hm⟩

/-- The full data: recorded Sims presentation data (Proposition 2.5) and the flattened power
word and commutator coefficient arrays. -/
abbrev FullData (p m : ℕ) : Type :=
  Σ D : RecData m, (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) ×
    (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m))

theorem card_fullData_le (p m : ℕ) (hp : 0 < p) :
    Fintype.card (FullData p m) ≤
      Fintype.card (RecData m) * ((p ^ m) ^ (m * m) * (p ^ m) ^ (m * m * m)) := by
  rw [Fintype.card_sigma]
  refine sum_le_card_mul _ _ _ le_rfl (fun D => ?_)
  rw [Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin]
  have ht := D.2.2.1.tot_le
  have hq : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp
  have e1 : ((p ^ m) ^ D.2.2.1.tot) ^ D.2.2.1.tot = (p ^ m) ^ (D.2.2.1.tot * D.2.2.1.tot) := by
    rw [pow_mul]
  have e2 : ((p ^ m) ^ (D.2.2.1.tot * D.2.2.1.tot)) ^ D.2.2.1.tot =
      (p ^ m) ^ (D.2.2.1.tot * D.2.2.1.tot * D.2.2.1.tot) := (pow_mul _ _ _).symm
  rw [e1, e2]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hq (Nat.mul_le_mul ht ht))
    (Nat.pow_le_pow_right hq (Nat.mul_le_mul (Nat.mul_le_mul ht ht) ht))

/-! Readback of the code as functions on `ℕ`. -/

def rdC {p m : ℕ} (D : FullData p m) : ℕ := D.1.1.val

def rdS {p m : ℕ} (D : FullData p m) : ℕ := D.1.2.1.val

def rdR {p m : ℕ} (D : FullData p m) (i : ℕ) : ℕ :=
  if h : i < D.1.1.val then (D.1.2.2.1.1 ⟨i, h⟩).val else 0

def rdInc {p m : ℕ} (D : FullData p m) (k : ℕ) : ℕ :=
  if h : k < D.1.2.1.val - 1 then (D.1.2.2.2.1.1 ⟨k, h⟩).val else 0

def rdF {p m : ℕ} (D : FullData p m) (j : ℕ) : ℕ :=
  if h : j < D.1.2.2.1.r2 then (D.1.2.2.2.2.1.1 ⟨j, h⟩).val else 0

def rdP {p m : ℕ} (D : FullData p m) (j : ℕ) : ℕ × ℕ :=
  if h : j < D.1.2.2.1.r3 then
    ((D.1.2.2.2.2.1.2 ⟨j, h⟩).1.val, (D.1.2.2.2.2.1.2 ⟨j, h⟩).2.val)
  else (0, 0)

def rdA {p m : ℕ} (D : FullData p m) (j : ℕ) : ℕ :=
  if h : j < D.1.2.2.1.tot then (D.1.2.2.2.2.2.1 ⟨j, h⟩).val else 0

def rdB {p m : ℕ} (D : FullData p m) (i j : ℕ) : ℕ :=
  if h : i < D.1.2.2.1.tot ∧ j < D.1.2.2.1.tot then (D.2.1 ⟨i, h.1⟩ ⟨j, h.2⟩).val else 0

def rdCm {p m : ℕ} (D : FullData p m) (i j k : ℕ) : ℕ :=
  if h : i < D.1.2.2.1.tot ∧ j < D.1.2.2.1.tot ∧ k < D.1.2.2.1.tot then
    (D.2.2 ⟨i, h.1⟩ ⟨j, h.2.1⟩ ⟨k, h.2.2⟩).val
  else 0

variable {G : Type u} [Group G] {p : ℕ} {u : ℕ → G} {d : SimsData} {X : Fin d.n → G}
  {r : ℕ → ℕ}

lemma SimsGen.n_eq' (hS : SimsGen p u d X r) : ∃ c, fOff r c = d.n := by
  obtain ⟨c, hc⟩ := hS.n_eq
  exact ⟨c, hc.symm⟩

/-- The number of layers `c`: the least `c` with `fOff r c = d.n`. -/
noncomputable def SimsGen.nL (hS : SimsGen p u d X r) : ℕ := Nat.find hS.n_eq'

lemma SimsGen.nL_spec (hS : SimsGen p u d X r) : fOff r hS.nL = d.n := Nat.find_spec hS.n_eq'

lemma SimsGen.nL_min (hS : SimsGen p u d X r) {w : ℕ} (hw : w < hS.nL) : fOff r w ≠ d.n :=
  Nat.find_min hS.n_eq' hw

/-- Every layer below `nL` is nonempty. -/
lemma SimsGen.nL_pos [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) :
    ∀ w < hS.nL, 0 < r w := by
  intro w hw
  by_contra h0
  have hr0 : r w = 0 := by omega
  have hlt : fOff r w < d.n := by
    have h1 := fOff_mono r hw.le
    have h2 := hS.nL_min hw
    rw [hS.nL_spec] at h1
    omega
  have h4 : (⟨fOff r w, hlt⟩ : Fin d.n).val = fOff r w := rfl
  have hw0 : w < d.lv ⟨fOff r w, hlt⟩ := by
    obtain ⟨h1, h2⟩ := (hS.layer_iff ⟨fOff r w, hlt⟩ (d.lv ⟨fOff r w, hlt⟩)).mp rfl
    by_contra hle
    have hle' : d.lv ⟨fOff r w, hlt⟩ ≤ w := not_lt.mp hle
    rcases lt_or_eq_of_le hle' with hl | he
    · have h3 := fOff_mono r (show d.lv ⟨fOff r w, hlt⟩ + 1 ≤ w by omega)
      rw [fOff_succ] at h3
      omega
    · rw [he, hr0] at h2
      omega
  have hsub : lcs G w ≤ lcs G (w + 1) := by
    refine (hS.layer_gen w).trans (sup_le ?_ le_rfl)
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exfalso
    have := (hS.layer_iff t w).mp ht
    omega
  have hstab : ∀ k, lcs G (w + k) = lcs G w := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show w + (k + 1) = (w + k) + 1 from rfl, lcs_succ, ih, ← lcs_succ]
      exact le_antisymm (lcs_antitone (Nat.le_succ w)) hsub
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card hS.realizes.card
  have : Group.IsNilpotent G := hpg.isNilpotent
  obtain ⟨N, hN⟩ : ∃ N, lcs G N = ⊥ :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
  have hbot : lcs G w = ⊥ := by
    rw [← hstab N]
    exact le_bot_iff.mp ((lcs_antitone (Nat.le_add_left N w)).trans (le_of_eq hN))
  have hX : X ⟨fOff r w, hlt⟩ = 1 := by
    have h := lcs_antitone hw0.le (hS.mem_lcs ⟨fOff r w, hlt⟩)
    rw [hbot] at h
    exact Subgroup.mem_bot.mp h
  apply hS.layer_indep ⟨fOff r w, hlt⟩
  rw [hX]
  exact one_mem _

lemma SimsGen.r_le_n (hS : SimsGen p u d X r) (w : ℕ) (hw : w < hS.nL) : r w ≤ d.n := by
  have h1 := fOff_mono r (show w + 1 ≤ hS.nL from hw)
  rw [fOff_succ, hS.nL_spec] at h1
  omega

lemma SimsGen.nL_le_n [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) : hS.nL ≤ d.n := by
  have h := le_fOff r hS.nL (fun w hw => hS.nL_pos hp w hw)
  rw [hS.nL_spec] at h
  exact h

lemma SimsGen.one_lt_nL (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) : 1 < hS.nL := by
  obtain ⟨t, ht, -⟩ := hS.block_ne 1 le_rfl (by omega)
  have := hS.lv_lt hS.nL_spec.symm t
  omega

lemma SimsGen.fOff_two_le (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) : fOff r 2 ≤ d.n := by
  have h := fOff_mono r (show 2 ≤ hS.nL from hS.one_lt_nL hs2)
  rw [hS.nL_spec] at h
  exact h

lemma SimsGen.pos_one (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) (j : ℕ) (hj : j < r 1) :
    ∃ h : fOff r 1 + j < d.n, d.lv ⟨fOff r 1 + j, h⟩ = 1 := by
  have h2 := hS.fOff_two_le hs2
  have e : fOff r 2 = fOff r 1 + r 1 := fOff_succ r 1
  exact ⟨by omega, (hS.layer_iff _ 1).mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩⟩

lemma SimsGen.brCo_bounds (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) (j : ℕ) (hj : j < r 1) :
    1 ≤ brCo d r j ∧ brCo d r j < d.s := by
  obtain ⟨h, hl⟩ := hS.pos_one hs2 j hj
  rw [brCo_eq d r ⟨fOff r 1 + j, h⟩ j rfl]
  have h1 : (d.df ⟨fOff r 1 + j, h⟩).1.val < (d.df ⟨fOff r 1 + j, h⟩).2.val :=
    hS.valid.df_one _ hl
  exact ⟨by omega, hS.valid.df_core _ (by omega)⟩

lemma SimsGen.brPa_lt (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) (j : ℕ) (hj : j < r 1) :
    brPa d r j < d.s - 1 := by
  obtain ⟨h, hl⟩ := hS.pos_one hs2 j hj
  rw [brPa_eq d r ⟨fOff r 1 + j, h⟩ j rfl]
  have h1 : (d.df ⟨fOff r 1 + j, h⟩).1.val < (d.df ⟨fOff r 1 + j, h⟩).2.val :=
    hS.valid.df_one _ hl
  have h2 := hS.valid.df_core ⟨fOff r 1 + j, h⟩ (by omega)
  omega

lemma SimsGen.brCo_mono (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) (i j : ℕ) (hij : i ≤ j)
    (hj : j < r 1) : brCo d r i ≤ brCo d r j := by
  obtain ⟨h1, hl1⟩ := hS.pos_one hs2 i (by omega)
  obtain ⟨h2, hl2⟩ := hS.pos_one hs2 j hj
  rw [brCo_eq d r ⟨fOff r 1 + i, h1⟩ i rfl, brCo_eq d r ⟨fOff r 1 + j, h2⟩ j rfl]
  exact hS.block_mono _ _ hl1 hl2 (show fOff r 1 + i ≤ fOff r 1 + j by omega)

lemma SimsGen.brFib_pos (hS : SimsGen p u d X r) (k : ℕ) (hk : k < d.s - 1) :
    0 < brFib d r k := by
  obtain ⟨t, ht, hco⟩ := hS.block_ne (k + 1) (by omega) (by omega)
  obtain ⟨a1, a2⟩ := (hS.layer_iff t 1).mp ht
  apply Finset.card_pos.mpr
  refine ⟨t.val - fOff r 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
  rw [brCo_eq d r t (t.val - fOff r 1) (by omega)]
  exact hco

lemma brFib_le (d : SimsData) (r : ℕ → ℕ) (k : ℕ) : brFib d r k ≤ r 1 :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

lemma SimsGen.sum_brFib (hS : SimsGen p u d X r) (hs2 : 2 ≤ d.s) :
    ∑ k ∈ Finset.range (d.s - 1), brFib d r k = r 1 := by
  have hmaps : ∀ j ∈ Finset.range (r 1), brCo d r j - 1 ∈ Finset.range (d.s - 1) := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    have := hS.brCo_bounds hs2 j hj
    omega
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_range] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold brFib
  congr 1
  apply Finset.filter_congr
  intro j hj
  have := hS.brCo_bounds hs2 j (Finset.mem_range.mp hj)
  constructor
  · intro e
    omega
  · intro e
    omega

/-- The rank vector `i ↦ r i` of `DataCount`. -/
noncomputable def SimsGen.rankVec [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) : RankVec m hS.nL :=
  ⟨fun i => ⟨r i.val, by have := hS.r_le_n i.val i.isLt; omega⟩,
    fun i => hS.nL_pos hp i.val i.isLt, by
      show ∑ i : Fin hS.nL, r i.val ≤ m
      rw [sum_fin_eq_fOff, hS.nL_spec]
      exact hnm⟩

lemma SimsGen.rankVec_tot [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) : (hS.rankVec hp hnm).tot = d.n := by
  unfold RankVec.tot
  show ∑ i : Fin hS.nL, r i.val = d.n
  rw [sum_fin_eq_fOff, hS.nL_spec]

lemma SimsGen.rankVec_r2 [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) : (hS.rankVec hp hnm).r2 = r 1 := by
  unfold RankVec.r2
  show ∑ i ∈ Finset.univ.filter (fun i : Fin hS.nL => i.val = 1), r i.val = r 1
  have hmem : (⟨1, hS.one_lt_nL hs2⟩ : Fin hS.nL) ∈
      Finset.univ.filter (fun i : Fin hS.nL => i.val = 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  exact Finset.sum_eq_single_of_mem _ hmem
    (fun b hb hne => absurd (Fin.ext (Finset.mem_filter.mp hb).2) hne)

lemma SimsGen.rankVec_r3 [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) : (hS.rankVec hp hnm).r3 = d.n - fOff r 2 := by
  unfold RankVec.r3
  show ∑ i ∈ Finset.univ.filter (fun i : Fin hS.nL => 2 ≤ i.val), r i.val = d.n - fOff r 2
  rw [Finset.sum_filter, sum_ite_ge_fOff r 2 hS.nL (hS.one_lt_nL hs2), hS.nL_spec]

/-- The increments of `(d_k)`. -/
noncomputable def SimsGen.incrVec [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) : PosVec (d.s - 1) (hS.rankVec hp hnm).r2 :=
  ⟨fun k => ⟨brFib d r k.val, by
      rw [hS.rankVec_r2 hp hnm hs2]
      exact Nat.lt_succ_of_le (brFib_le d r k.val)⟩,
    fun k => hS.brFib_pos k.val k.isLt, by
      show ∑ k : Fin (d.s - 1), brFib d r k.val = _
      rw [hS.rankVec_r2 hp hnm hs2, Fin.sum_univ_eq_sum_range (fun k => brFib d r k) (d.s - 1)]
      exact hS.sum_brFib hs2⟩

/-- The auxiliary function `f`. -/
noncomputable def SimsGen.fAux [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) : Fin (hS.rankVec hp hnm).r2 → Fin (d.s - 1) :=
  fun j => ⟨brPa d r j.val, hS.brPa_lt hs2 j.val
    (lt_of_lt_of_eq j.isLt (hS.rankVec_r2 hp hnm hs2))⟩

/-- The index pairs of the generators of weight at least `3`. -/
noncomputable def SimsGen.pAux [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) : Fin (hS.rankVec hp hnm).r3 → Fin m × Fin m :=
  fun j => (⟨(brPr d r j.val).1, (brPr_lt d r hnm (by have := hS.valid.s_le; omega) j.val).1⟩,
    ⟨(brPr d r j.val).2, (brPr_lt d r hnm (by have := hS.valid.s_le; omega) j.val).2⟩)

/-- The relative order array. -/
noncomputable def SimsGen.aVec [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ}
    (hnm : d.n ≤ m) (hsum : ∑ t, d.a t = m) : PosVec (hS.rankVec hp hnm).tot m :=
  ⟨fun j => ⟨brA d j.val, Nat.lt_succ_of_le (brA_le hsum j.val)⟩, fun j => by
      have hj : j.val < d.n := lt_of_lt_of_eq j.isLt (hS.rankVec_tot hp hnm)
      show 0 < brA d j.val
      unfold brA
      rw [dif_pos hj]
      exact hS.a_pos _, by
      show ∑ j : Fin (hS.rankVec hp hnm).tot, brA d j.val = m
      rw [Fin.sum_univ_eq_sum_range (fun j => brA d j), hS.rankVec_tot hp hnm,
        ← Fin.sum_univ_eq_sum_range (fun j => brA d j)]
      have e : ∀ t : Fin d.n, brA d t.val = d.a t := fun t => by
        unfold brA
        exact dif_pos t.isLt
      simp only [e]
      exact hsum⟩

/-- The code of a Sims generating set. -/
noncomputable def SimsGen.enc [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) (m : ℕ) (hnm : d.n ≤ m)
    (hs2 : 2 ≤ d.s) (hsum : ∑ t, d.a t = m) : FullData p m :=
  ⟨⟨⟨hS.nL, by have := hS.nL_le_n hp; omega⟩, ⟨d.s, by have := hS.valid.s_le; omega⟩,
      hS.rankVec hp hnm, hS.incrVec hp hnm hs2, (hS.fAux hp hnm hs2, hS.pAux hp hnm hs2),
      hS.aVec hp hnm hsum⟩,
    (fun i j => ⟨brB d i.val j.val, brB_lt hp.pos hS.bounded hsum _ _⟩,
      fun i j k => ⟨brCm d i.val j.val k.val, brCm_lt hp.pos hS.bounded hsum _ _ _⟩)⟩

section Readback

variable [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r) {m : ℕ} (hnm : d.n ≤ m)
  (hs2 : 2 ≤ d.s) (hsum : ∑ t, d.a t = m)

lemma SimsGen.rdC_enc : rdC (hS.enc hp m hnm hs2 hsum) = hS.nL := rfl

lemma SimsGen.rdS_enc : rdS (hS.enc hp m hnm hs2 hsum) = d.s := rfl

lemma SimsGen.rdR_enc (i : ℕ) :
    rdR (hS.enc hp m hnm hs2 hsum) i = dite (i < hS.nL) (fun _ => r i) (fun _ => 0) := rfl

lemma SimsGen.rdInc_enc (k : ℕ) :
    rdInc (hS.enc hp m hnm hs2 hsum) k =
      dite (k < d.s - 1) (fun _ => brFib d r k) (fun _ => 0) := rfl

lemma SimsGen.rdF_enc (j : ℕ) :
    rdF (hS.enc hp m hnm hs2 hsum) j =
      dite (j < (hS.rankVec hp hnm).r2) (fun _ => brPa d r j) (fun _ => 0) := rfl

lemma SimsGen.rdP_enc (j : ℕ) : rdP (hS.enc hp m hnm hs2 hsum) j = brPr d r j := by
  have e : rdP (hS.enc hp m hnm hs2 hsum) j = dite (j < (hS.rankVec hp hnm).r3)
      (fun _ => ((brPr d r j).1, (brPr d r j).2)) (fun _ => (0, 0)) := rfl
  rw [e, hS.rankVec_r3 hp hnm hs2]
  have h2 := hS.fOff_two_le hs2
  split_ifs with h
  · rfl
  · have h' : ¬ (fOff r 2 + j < d.n) := by omega
    unfold brPr
    rw [dif_neg h']

lemma SimsGen.rdA_enc (j : ℕ) : rdA (hS.enc hp m hnm hs2 hsum) j = brA d j := by
  have e : rdA (hS.enc hp m hnm hs2 hsum) j =
      dite (j < (hS.rankVec hp hnm).tot) (fun _ => brA d j) (fun _ => 0) := rfl
  rw [e, hS.rankVec_tot hp hnm]
  split_ifs with h
  · rfl
  · unfold brA
    rw [dif_neg h]

lemma SimsGen.rdB_enc (i j : ℕ) : rdB (hS.enc hp m hnm hs2 hsum) i j = brB d i j := by
  have e : rdB (hS.enc hp m hnm hs2 hsum) i j =
      dite (i < (hS.rankVec hp hnm).tot ∧ j < (hS.rankVec hp hnm).tot)
        (fun _ => brB d i j) (fun _ => 0) := rfl
  rw [e, hS.rankVec_tot hp hnm]
  split_ifs with h
  · rfl
  · unfold brB
    rw [dif_neg h]

lemma SimsGen.rdCm_enc (i j k : ℕ) :
    rdCm (hS.enc hp m hnm hs2 hsum) i j k = brCm d i j k := by
  have e : rdCm (hS.enc hp m hnm hs2 hsum) i j k =
      dite (i < (hS.rankVec hp hnm).tot ∧ j < (hS.rankVec hp hnm).tot ∧
        k < (hS.rankVec hp hnm).tot) (fun _ => brCm d i j k) (fun _ => 0) := rfl
  rw [e, hS.rankVec_tot hp hnm]
  split_ifs with h
  · rfl
  · unfold brCm
    rw [dif_neg h]

end Readback

/-- Injectivity of the code up to normalisation: two Sims generating sets with the same code
have the same normalised Sims data. -/
theorem SimsGen.normalize_eq_of_enc {G₁ G₂ : Type u} [Group G₁] [Group G₂] [Finite G₁]
    [Finite G₂] {p m : ℕ} (hp : p.Prime) {u₁ : ℕ → G₁} {d₁ : SimsData} {X₁ : Fin d₁.n → G₁}
    {r₁ : ℕ → ℕ} {u₂ : ℕ → G₂} {d₂ : SimsData} {X₂ : Fin d₂.n → G₂} {r₂ : ℕ → ℕ}
    (hS₁ : SimsGen p u₁ d₁ X₁ r₁) (hS₂ : SimsGen p u₂ d₂ X₂ r₂)
    (hnm₁ : d₁.n ≤ m) (hs₁ : 2 ≤ d₁.s) (hsum₁ : ∑ t, d₁.a t = m)
    (hnm₂ : d₂.n ≤ m) (hs₂ : 2 ≤ d₂.s) (hsum₂ : ∑ t, d₂.a t = m)
    (heq : hS₁.enc hp m hnm₁ hs₁ hsum₁ = hS₂.enc hp m hnm₂ hs₂ hsum₂) :
    d₁.normalize = d₂.normalize := by
  have hc : hS₁.nL = hS₂.nL := by
    have h := congrArg rdC heq
    rwa [hS₁.rdC_enc hp hnm₁ hs₁ hsum₁, hS₂.rdC_enc hp hnm₂ hs₂ hsum₂] at h
  have hs : d₁.s = d₂.s := by
    have h := congrArg rdS heq
    rwa [hS₁.rdS_enc hp hnm₁ hs₁ hsum₁, hS₂.rdS_enc hp hnm₂ hs₂ hsum₂] at h
  have hr : ∀ i < hS₁.nL, r₁ i = r₂ i := by
    intro i hi
    have hi2 : i < hS₂.nL := by rw [← hc]; exact hi
    have h := congrFun (congrArg rdR heq) i
    rw [hS₁.rdR_enc hp hnm₁ hs₁ hsum₁, hS₂.rdR_enc hp hnm₂ hs₂ hsum₂, dif_pos hi,
      dif_pos hi2] at h
    exact h
  have hfo : ∀ w ≤ hS₁.nL, fOff r₁ w = fOff r₂ w := fOff_congr hr
  have hn : d₁.n = d₂.n := by
    rw [← hS₁.nL_spec, ← hS₂.nL_spec, ← hc]
    exact hfo _ le_rfl
  have h1c : 1 < hS₁.nL := hS₁.one_lt_nL hs₁
  have hr1 : r₁ 1 = r₂ 1 := hr 1 h1c
  have hf1 : fOff r₁ 1 = fOff r₂ 1 := hfo 1 h1c.le
  have hf2 : fOff r₁ 2 = fOff r₂ 2 := hfo 2 h1c
  have hlv : ∀ i (h1 : i < d₁.n) (h2 : i < d₂.n), d₁.lv ⟨i, h1⟩ = d₂.lv ⟨i, h2⟩ := by
    intro i h1 h2
    have hw := hS₁.lv_lt hS₁.nL_spec.symm ⟨i, h1⟩
    obtain ⟨e1, e2⟩ := (hS₁.layer_iff ⟨i, h1⟩ (d₁.lv ⟨i, h1⟩)).mp rfl
    rw [hfo _ hw.le, hr _ hw] at e2
    rw [hfo _ hw.le] at e1
    exact ((hS₂.layer_iff ⟨i, h2⟩ (d₁.lv ⟨i, h1⟩)).mpr ⟨e1, e2⟩).symm
  have hA : brA d₁ = brA d₂ := by
    funext j
    have h := congrFun (congrArg rdA heq) j
    rwa [hS₁.rdA_enc hp hnm₁ hs₁ hsum₁, hS₂.rdA_enc hp hnm₂ hs₂ hsum₂] at h
  have hB : brB d₁ = brB d₂ := by
    funext i j
    have h := congrFun (congrFun (congrArg rdB heq) i) j
    rwa [hS₁.rdB_enc hp hnm₁ hs₁ hsum₁, hS₂.rdB_enc hp hnm₂ hs₂ hsum₂] at h
  have hCm : brCm d₁ = brCm d₂ := by
    funext i j k
    have h := congrFun (congrFun (congrFun (congrArg rdCm heq) i) j) k
    rwa [hS₁.rdCm_enc hp hnm₁ hs₁ hsum₁, hS₂.rdCm_enc hp hnm₂ hs₂ hsum₂] at h
  have hP : brPr d₁ r₁ = brPr d₂ r₂ := by
    funext j
    have h := congrFun (congrArg rdP heq) j
    rwa [hS₁.rdP_enc hp hnm₁ hs₁ hsum₁, hS₂.rdP_enc hp hnm₂ hs₂ hsum₂] at h
  have hPa : ∀ j < r₁ 1, brPa d₁ r₁ j = brPa d₂ r₂ j := by
    intro j hj
    have hj1 : j < (hS₁.rankVec hp hnm₁).r2 := by rw [hS₁.rankVec_r2 hp hnm₁ hs₁]; exact hj
    have hj2 : j < (hS₂.rankVec hp hnm₂).r2 := by rw [hS₂.rankVec_r2 hp hnm₂ hs₂, ← hr1]; exact hj
    have h := congrFun (congrArg rdF heq) j
    rw [hS₁.rdF_enc hp hnm₁ hs₁ hsum₁, hS₂.rdF_enc hp hnm₂ hs₂ hsum₂, dif_pos hj1,
      dif_pos hj2] at h
    exact h
  have hfib : ∀ k, ((Finset.range (r₁ 1)).filter (fun j => brCo d₁ r₁ j = k)).card =
      ((Finset.range (r₁ 1)).filter (fun j => brCo d₂ r₂ j = k)).card := by
    intro k
    by_cases hk : 1 ≤ k ∧ k < d₁.s
    · have hk1 : k - 1 < d₁.s - 1 := by omega
      have hk2 : k - 1 < d₂.s - 1 := by omega
      have h := congrFun (congrArg rdInc heq) (k - 1)
      rw [hS₁.rdInc_enc hp hnm₁ hs₁ hsum₁, hS₂.rdInc_enc hp hnm₂ hs₂ hsum₂, dif_pos hk1,
        dif_pos hk2] at h
      unfold brFib at h
      rw [← hr1, show k - 1 + 1 = k by omega] at h
      exact h
    · have e1 : (Finset.range (r₁ 1)).filter (fun j => brCo d₁ r₁ j = k) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun j hj => by
          have := hS₁.brCo_bounds hs₁ j (Finset.mem_range.mp hj)
          omega
      have e2 : (Finset.range (r₁ 1)).filter (fun j => brCo d₂ r₂ j = k) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun j hj => by
          have hj' : j < r₂ 1 := by rw [← hr1]; exact Finset.mem_range.mp hj
          have := hS₂.brCo_bounds hs₂ j hj'
          omega
      rw [e1, e2]
  have hmono₂ : ∀ i j, i ≤ j → j < r₁ 1 → brCo d₂ r₂ i ≤ brCo d₂ r₂ j :=
    fun i j hij hj => hS₂.brCo_mono hs₂ i j hij (by rw [← hr1]; exact hj)
  have hco : ∀ j < r₁ 1, brCo d₁ r₁ j = brCo d₂ r₂ j := fun j hj =>
    eq_of_mono_fiber _ _ _ (fun i j hij hj => hS₁.brCo_mono hs₁ i j hij hj) hmono₂ hfib j hj
  have hdf : ∀ i (h1 : i < d₁.n) (h2 : i < d₂.n), 1 ≤ d₁.lv ⟨i, h1⟩ →
      (d₁.df ⟨i, h1⟩).1.val = (d₂.df ⟨i, h2⟩).1.val ∧
        (d₁.df ⟨i, h1⟩).2.val = (d₂.df ⟨i, h2⟩).2.val := by
    intro i h1 h2 hl
    by_cases hw : d₁.lv ⟨i, h1⟩ = 1
    · obtain ⟨a1, a2⟩ := (hS₁.layer_iff ⟨i, h1⟩ 1).mp hw
      have a1' : fOff r₁ 1 ≤ i := a1
      have a2' : i < fOff r₁ 1 + r₁ 1 := a2
      have ej1 : fOff r₁ 1 + (i - fOff r₁ 1) = (⟨i, h1⟩ : Fin d₁.n).val := by
        show fOff r₁ 1 + (i - fOff r₁ 1) = i
        omega
      have ej2 : fOff r₂ 1 + (i - fOff r₁ 1) = (⟨i, h2⟩ : Fin d₂.n).val := by
        show fOff r₂ 1 + (i - fOff r₁ 1) = i
        omega
      have hj : i - fOff r₁ 1 < r₁ 1 := by omega
      constructor
      · rw [← brPa_eq d₁ r₁ ⟨i, h1⟩ _ ej1, ← brPa_eq d₂ r₂ ⟨i, h2⟩ _ ej2]
        exact hPa _ hj
      · rw [← brCo_eq d₁ r₁ ⟨i, h1⟩ _ ej1, ← brCo_eq d₂ r₂ ⟨i, h2⟩ _ ej2]
        exact hco _ hj
    · have hge : 2 ≤ d₁.lv ⟨i, h1⟩ := by omega
      have a1 := ((hS₁.layer_iff ⟨i, h1⟩ (d₁.lv ⟨i, h1⟩)).mp rfl).1
      have a1' : fOff r₁ (d₁.lv ⟨i, h1⟩) ≤ i := a1
      have a3 := fOff_mono r₁ hge
      have ej1 : fOff r₁ 2 + (i - fOff r₁ 2) = (⟨i, h1⟩ : Fin d₁.n).val := by
        show fOff r₁ 2 + (i - fOff r₁ 2) = i
        omega
      have ej2 : fOff r₂ 2 + (i - fOff r₁ 2) = (⟨i, h2⟩ : Fin d₂.n).val := by
        show fOff r₂ 2 + (i - fOff r₁ 2) = i
        omega
      have e := congrFun hP (i - fOff r₁ 2)
      rw [brPr_eq d₁ r₁ ⟨i, h1⟩ _ ej1, brPr_eq d₂ r₂ ⟨i, h2⟩ _ ej2] at e
      exact Prod.mk.inj e
  refine SimsData.normalize_eq hn hs hlv hdf ?_ ?_ ?_
  · intro i h1 h2
    have e := congrFun hA i
    unfold brA at e
    rwa [dif_pos h1, dif_pos h2] at e
  · intro i j h1 h1' h2 h2'
    have e := congrFun (congrFun hB i) j
    unfold brB at e
    rwa [dif_pos (And.intro h1 h1'), dif_pos (And.intro h2 h2')] at e
  · intro i j k h1 h1' h1'' h2 h2' h2''
    have e := congrFun (congrFun (congrFun hCm i) j) k
    unfold brCm at e
    rwa [dif_pos (And.intro h1 (And.intro h1' h1'')),
      dif_pos (And.intro h2 (And.intro h2' h2''))] at e

/-- `G` has Sims code `D`: some Sims generating set of `G` (in the sense of `SimsGen`) has
code `D`. -/
def SimsCode {p : ℕ} (hp : p.Prime) (m : ℕ) (G : Type u) [Group G] [Finite G]
    (D : FullData p m) : Prop :=
  ∃ (u : ℕ → G) (d : SimsData) (X : Fin d.n → G) (r : ℕ → ℕ) (hS : SimsGen p u d X r)
    (hnm : d.n ≤ m) (hs2 : 2 ≤ d.s) (hsum : ∑ t, d.a t = m), hS.enc hp m hnm hs2 hsum = D

theorem exists_simsCode {G : Type u} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ m) (hna : lcs G 1 ≠ ⊥) : ∃ D : FullData p m, SimsCode hp m G D := by
  obtain ⟨u, d, X, r, hs2, hds, -, -, -, -, hnm, -, hS⟩ := exists_sims_gen hp hG hna
  have hsum : ∑ t, d.a t = m := by
    have h1 := hS.realizes.card
    rw [hG] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hs2' : 2 ≤ d.s := by rw [hds]; exact hs2
  exact ⟨_, u, d, X, r, hS, hnm, hs2', hsum, rfl⟩

/-- Proposition 2.4 for codes: groups with the same Sims code are isomorphic. -/
theorem simsCode_rigid {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {p m : ℕ}
    (hp : p.Prime) {D : FullData p m} (hG : SimsCode hp m G D) (hH : SimsCode hp m H D) :
    Nonempty (G ≃* H) := by
  obtain ⟨u₁, d₁, X₁, r₁, hS₁, hnm₁, hs₁, hsum₁, e₁⟩ := hG
  obtain ⟨u₂, d₂, X₂, r₂, hS₂, hnm₂, hs₂, hsum₂, e₂⟩ := hH
  exact rigid_of_eq hp d₁.normalize d₂.normalize
    (SimsGen.normalize_eq_of_enc hp hS₁ hS₂ hnm₁ hs₁ hsum₁ hnm₂ hs₂ hsum₂ (e₁.trans e₂.symm))
    (SimsData.normalize_valid hS₁.valid) X₁ X₂ (SimsData.normalize_realizes hS₁.realizes)
    (SimsData.normalize_realizes hS₂.realizes)

/-- INF-1 with Propositions 2.4 and 2.5: the number of isomorphism classes of nonabelian
groups of order `p ^ m` is at most the number of full Sims codes. -/
theorem ncard_classes_le_fullData (p m : ℕ) (hp : p.Prime) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p ^ m ∧ lcs G 1 ≠ ⊥}).ncard ≤
        Fintype.card (FullData p m) :=
  ncard_classes_le_fintype_card _ (fun G D => SimsCode hp m G D)
    (fun G hG => by
      obtain ⟨h1, h2⟩ := hG
      exact exists_simsCode hp h1 h2)
    (fun _ _ _ _ _ hGD hHD => simsCode_rigid hp hGD hHD)

/-- The same with the Proposition 2.5 count of the recorded data and the trivial count of the
arrays. -/
theorem ncard_classes_le_recData (p m : ℕ) (hp : p.Prime) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p ^ m ∧ lcs G 1 ≠ ⊥}).ncard ≤
        Fintype.card (RecData m) * ((p ^ m) ^ (m * m) * (p ^ m) ^ (m * m * m)) :=
  (ncard_classes_le_fullData p m hp).trans (card_fullData_le p m hp.pos)

/-- Closed form, with `card_recData_le_pow`. -/
theorem ncard_classes_le_closed (p m : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p ^ m ∧ lcs G 1 ≠ ⊥}).ncard ≤
        (m + 1) ^ (5 * m + 2) * ((p ^ m) ^ (m * m) * (p ^ m) ^ (m * m * m)) :=
  (ncard_classes_le_recData p m hp).trans (Nat.mul_le_mul (card_recData_le_pow m hm) le_rfl)

end DataBridge

/-! ### Part 3: the fibrewise count and the link with Theorem 3.1

For a set `T` of groups and recorded data `D : RecData m`, `realizedB hp T D` and
`realizedC hp T D` are the power word arrays and commutator coefficient arrays occurring in the
Sims codes (with recorded component `D`) of groups of `T`. `ncard_classes_le_fiber` is INF-1
fibred over the recorded data: the number of classes of `T` is at most
`Σ_{D ∈ I} N_b(D) N_c(D)` whenever every group of `T` has a code whose recorded component lies in
`I`. `SimsGen.powerWords_toSimsGenSet` identifies the power word array of the code with the power
word array (27) of the `SimsGenSet` of Part 1, and `ncard_realizedB_le` bounds `N_b(D)` by the
number of realised power word arrays of Theorem 3.1 for the layer ranks and relative orders read
off `D`; `ncard_classes_le_fiber_pw` combines the two. -/

section FiberCount

variable {G : Type u} [Group G] {p : ℕ} {u : ℕ → G} {d : SimsData} {X : Fin d.n → G}
  {r : ℕ → ℕ}

lemma SimsGen.brA_brEquiv (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k : SimsIdx c (brR r c)) : brA d (fOff r k.1.val + k.2.val) = d.a (hS.brEquiv hn k) := by
  unfold brA
  exact dif_pos (hS.brEquiv hn k).isLt

lemma SimsGen.brB_brEquiv (hS : SimsGen p u d X r) {c : ℕ} (hn : d.n = fOff r c)
    (k k' : SimsIdx c (brR r c)) :
    brB d (fOff r k.1.val + k.2.val) (fOff r k'.1.val + k'.2.val) =
      d.b (hS.brEquiv hn k) (hS.brEquiv hn k') := by
  unfold brB
  exact dif_pos ⟨(hS.brEquiv hn k).isLt, (hS.brEquiv hn k').isLt⟩

/-- The power word array (27) of the `SimsGenSet` of Part 1 is the power word array `d.b` of
the Sims data, through `brEquiv`. -/
lemma SimsGen.powerWords_toSimsGenSet [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r)
    {c : ℕ} (hn : d.n = fOff r c) (k k' : SimsIdx c (brR r c)) :
    ((hS.toSimsGenSet hp hn).powerWords k k').val = d.b (hS.brEquiv hn k) (hS.brEquiv hn k') := by
  have hx := Classical.choose_spec
    (hS.nf_exists (X (hS.brEquiv hn k) ^ p ^ d.a (hS.brEquiv hn k)))
  have h2 := hS.nf_unique _ (d.b (hS.brEquiv hn k)) hx.1 (fun t => hS.bounded.1 _ t)
    (hx.2.symm.trans (hS.realizes.pow _))
  show Classical.choose (hS.nf_exists (X (hS.brEquiv hn k) ^ p ^ d.a (hS.brEquiv hn k)))
    (hS.brEquiv hn k') = _
  rw [h2]

/-- The flattened power word component `brB` of the code is the power word array of the
`SimsGenSet` of Part 1. -/
lemma SimsGen.brB_eq_powerWords [Finite G] (hp : p.Prime) (hS : SimsGen p u d X r)
    {c : ℕ} (hn : d.n = fOff r c) (k k' : SimsIdx c (brR r c)) :
    brB d (hS.brEquiv hn k).val (hS.brEquiv hn k').val =
      ((hS.toSimsGenSet hp hn).powerWords k k').val := by
  rw [hS.powerWords_toSimsGenSet hp hn]
  exact hS.brB_brEquiv hn k k'

lemma brLayer_of_lt (r : ℕ → ℕ) : ∀ c i, i < fOff r c → ∃ w < c, ∃ v < r w, i = fOff r w + v
  | 0, i, h => absurd h (by show ¬ i < 0; omega)
  | c + 1, i, h => by
    by_cases hi : i < fOff r c
    · obtain ⟨w, hw, v, hv, e⟩ := brLayer_of_lt r c i hi
      exact ⟨w, by omega, v, hv, e⟩
    · rw [fOff_succ] at h
      exact ⟨c, by omega, i - fOff r c, by omega, by omega⟩

/-- A flattened array as a function on `ℕ` (`0` outside the range). -/
def flatB {n q : ℕ} (B : Fin n → Fin n → Fin q) (i j : ℕ) : ℕ :=
  if h : i < n ∧ j < n then (B ⟨i, h.1⟩ ⟨j, h.2⟩).val else 0

lemma flatB_fin {n q : ℕ} (B : Fin n → Fin n → Fin q) (i j : Fin n) :
    flatB B i.val j.val = (B i j).val := by
  unfold flatB
  rw [dif_pos ⟨i.isLt, j.isLt⟩]

/-- The layer ranks of recorded data, on `ℕ`. -/
def fibR {m : ℕ} (D : RecData m) (i : ℕ) : ℕ :=
  if h : i < D.1.val then (D.2.2.1.1 ⟨i, h⟩).val else 0

/-- The relative order array of recorded data, flattened on `ℕ`. -/
def fibA {m : ℕ} (D : RecData m) (j : ℕ) : ℕ :=
  if h : j < D.2.2.1.tot then (D.2.2.2.2.2.1 ⟨j, h⟩).val else 0

/-- The layer ranks of recorded data, on `Fin c`. -/
abbrev fibRk {m : ℕ} (D : RecData m) : Fin D.1.val → ℕ := brR (fibR D) D.1.val

/-- The relative order array of recorded data, indexed by `SimsIdx`. -/
def fibAk {m : ℕ} (D : RecData m) : SimsIdx D.1.val (fibRk D) → ℕ :=
  fun k => fibA D (fOff (fibR D) k.1.val + k.2.val)

lemma fibTot {m : ℕ} (D : RecData m) : D.2.2.1.tot = fOff (fibR D) D.1.val := by
  unfold RankVec.tot
  rw [← sum_fin_eq_fOff]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold fibR
  rw [dif_pos i.isLt]

lemma fibPos_lt {m : ℕ} (D : RecData m) (k : SimsIdx D.1.val (fibRk D)) :
    fOff (fibR D) k.1.val + k.2.val < D.2.2.1.tot :=
  brPos_lt (fibR D) (fibTot D) k.1 k.2

lemma fibAk_pos {m : ℕ} (D : RecData m) (k : SimsIdx D.1.val (fibRk D)) : 1 ≤ fibAk D k := by
  show 1 ≤ fibA D (fOff (fibR D) k.1.val + k.2.val)
  unfold fibA
  rw [dif_pos (fibPos_lt D k)]
  exact D.2.2.2.2.2.2.1 _

/-- The power word arrays of the Sims codes, with recorded component `D`, of groups of `T`. -/
def realizedB {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0}) (D : RecData m) :
    Set (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) :=
  {B | ∃ G ∈ T, ∃ C, SimsCode hp m G (⟨D, (B, C)⟩ : FullData p m)}

/-- The commutator coefficient arrays of the Sims codes, with recorded component `D`, of groups
of `T`. -/
def realizedC {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0}) (D : RecData m) :
    Set (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) :=
  {C | ∃ G ∈ T, ∃ B, SimsCode hp m G (⟨D, (B, C)⟩ : FullData p m)}

/-- INF-1 fibred over the recorded data (Propositions 2.4 and 2.5): if every group of `T` has a
Sims code whose recorded component lies in `I`, the number of isomorphism classes of groups of
`T` is at most `Σ_{D ∈ I} N_b(D) N_c(D)`, with `N_b(D)`, `N_c(D)` the numbers of realised power
word and commutator coefficient arrays over `D`. -/
theorem ncard_classes_le_fiber {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0})
    (I : Finset (RecData m)) (hI : ∀ G ∈ T, ∃ D : FullData p m, SimsCode hp m G D ∧ D.1 ∈ I) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard ≤
      ∑ D ∈ I, (realizedB hp T D).ncard * (realizedC hp T D).ncard := by
  refine (ncard_le_sum_of_rel I
    (fun D => (Set.toFinite (realizedB hp T D)).toFinset ×ˢ
      (Set.toFinite (realizedC hp T D)).toFinset)
    (fun D s x => ∃ G ∈ T,
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) G = s ∧
        SimsCode hp m G (⟨D, x⟩ : FullData p m)) ?_ ?_).trans_eq
    (Finset.sum_congr rfl fun D _ => ?_)
  · rintro s ⟨G, hG, rfl⟩
    obtain ⟨⟨D, B, C⟩, hD, hDI⟩ := hI G hG
    refine ⟨D, hDI, (B, C), ?_, G, hG, rfl, hD⟩
    exact Finset.mem_product.mpr ⟨((Set.toFinite (realizedB hp T D)).mem_toFinset).mpr
      ⟨G, hG, C, hD⟩, ((Set.toFinite (realizedC hp T D)).mem_toFinset).mpr ⟨G, hG, B, hD⟩⟩
  · rintro s₁ - s₂ - D x ⟨G₁, hG₁, rfl, h₁⟩ ⟨G₂, hG₂, rfl, h₂⟩
    obtain ⟨e⟩ := simsCode_rigid hp h₁ h₂
    exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩
  · show ((Set.toFinite (realizedB hp T D)).toFinset ×ˢ
      (Set.toFinite (realizedC hp T D)).toFinset).card = _
    rw [Finset.card_product, Set.ncard_eq_toFinset_card (realizedB hp T D) (Set.toFinite _),
      Set.ncard_eq_toFinset_card (realizedC hp T D) (Set.toFinite _)]

/-- The fibrewise count with the selection given by a predicate on the recorded data that holds
for every Sims code of every group of `T`. -/
theorem ncard_classes_le_fiber_pred {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0})
    (hT : ∀ G ∈ T, Nat.card G = p ^ m ∧ lcs G 1 ≠ ⊥) (P : RecData m → Prop) [DecidablePred P]
    (hP : ∀ G ∈ T, ∀ D : FullData p m, SimsCode hp m G D → P D.1) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard ≤
      ∑ D ∈ Finset.univ.filter P, (realizedB hp T D).ncard * (realizedC hp T D).ncard :=
  ncard_classes_le_fiber hp T _ fun G hG => by
    obtain ⟨D, hD⟩ := exists_simsCode hp (hT G hG).1 (hT G hG).2
    exact ⟨D, hD, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP G hG D hD⟩⟩

/-- The set of isomorphism classes of a set of nonabelian groups of order `p ^ m` is finite. -/
theorem classes_finite {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0})
    (hT : ∀ G ∈ T, Nat.card G = p ^ m ∧ lcs G 1 ≠ ⊥) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).Finite := by
  have hsub : ∀ D : FullData p m, Set.Subsingleton {s | ∃ G ∈ T,
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) G = s ∧
        SimsCode hp m G D} := by
    intro D
    rintro s₁ ⟨G₁, hG₁, rfl, h₁⟩ s₂ ⟨G₂, hG₂, rfl, h₂⟩
    obtain ⟨e⟩ := simsCode_rigid hp h₁ h₂
    exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩
  refine Set.Finite.subset (Set.finite_iUnion fun D : FullData p m => (hsub D).finite) ?_
  rintro s ⟨G, hG, rfl⟩
  obtain ⟨D, hD⟩ := exists_simsCode hp (hT G hG).1 (hT G hG).2
  exact Set.mem_iUnion.mpr ⟨D, G, hG, rfl, hD⟩

/-- Readback of a Sims code with recorded component `D`. -/
lemma code_facts {m : ℕ} (hp : p.Prime) {H : Type u} [Group H] [Finite H] {D : RecData m}
    {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    (hc : SimsCode hp m H (⟨D, (B, C)⟩ : FullData p m)) :
    ∃ (u : ℕ → H) (d : SimsData) (X : Fin d.n → H) (r : ℕ → ℕ) (hS : SimsGen p u d X r),
      D.1.val = hS.nL ∧ (∀ i < hS.nL, fibR D i = r i) ∧ (∀ j, fibA D j = brA d j) ∧
        D.2.2.1.tot = d.n ∧ (∀ i j, flatB B i j = brB d i j) := by
  obtain ⟨u, d, X, r, hS, hnm, hs2, hsum, e⟩ := hc
  refine ⟨u, d, X, r, hS, (congrArg rdC e).symm, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h := congrFun (congrArg rdR e) i
    rw [hS.rdR_enc hp hnm hs2 hsum, dif_pos hi] at h
    exact h.symm
  · intro j
    have h := congrFun (congrArg rdA e) j
    rw [hS.rdA_enc hp hnm hs2 hsum] at h
    exact h.symm
  · have h : (hS.rankVec hp hnm).tot = D.2.2.1.tot :=
      congrArg (fun E : FullData p m => E.1.2.2.1.tot) e
    exact h.symm.trans (hS.rankVec_tot hp hnm)
  · intro i j
    have h := congrFun (congrFun (congrArg rdB e) i) j
    rw [hS.rdB_enc hp hnm hs2 hsum] at h
    exact h.symm

lemma flatB_lt_of_code {m : ℕ} (hp : p.Prime) {H : Type u} [Group H] [Finite H]
    {D : RecData m} {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    (hc : SimsCode hp m H (⟨D, (B, C)⟩ : FullData p m)) (i j : ℕ) (hj : j < D.2.2.1.tot) :
    flatB B i j < p ^ fibA D j := by
  obtain ⟨u, d, X, r, hS, -, -, hA, htot, hB⟩ := code_facts hp hc
  rw [hB, hA]
  rw [htot] at hj
  unfold brB brA
  rw [dif_pos hj]
  split_ifs with h
  · exact hS.bounded.1 _ _
  · exact pow_pos hp.pos _

/-- The power word array read off a flattened array, for the ranks and relative orders of `D`
(entries out of range are replaced by `0`). -/
def pwOfB {m : ℕ} (hp0 : 0 < p) (D : RecData m)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)) :
    PWArray p D.1.val (fibRk D) (fibAk D) :=
  fun k h => if hlt : flatB B (fOff (fibR D) k.1.val + k.2.val)
      (fOff (fibR D) h.1.val + h.2.val) < p ^ fibAk D h then ⟨_, hlt⟩
    else ⟨0, pow_pos hp0 _⟩

lemma pwOfB_val_of_code {m : ℕ} (hp : p.Prime) {H : Type u} [Group H] [Finite H]
    {D : RecData m} {B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    {C : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (p ^ m)}
    (hc : SimsCode hp m H (⟨D, (B, C)⟩ : FullData p m)) (k h : SimsIdx D.1.val (fibRk D)) :
    (pwOfB hp.pos D B k h).val =
      flatB B (fOff (fibR D) k.1.val + k.2.val) (fOff (fibR D) h.1.val + h.2.val) := by
  have hlt : flatB B (fOff (fibR D) k.1.val + k.2.val) (fOff (fibR D) h.1.val + h.2.val) <
      p ^ fibAk D h := flatB_lt_of_code hp hc _ _ (fibPos_lt D h)
  simp only [pwOfB, dif_pos hlt]

/-- Transport of realised power word arrays along equal ranks and relative orders. -/
lemma realizedPW_congr {c c' : ℕ} {r : Fin c → ℕ} {r' : Fin c' → ℕ} {a : SimsIdx c r → ℕ}
    {a' : SimsIdx c' r' → ℕ} {B : PWArray p c r a} {B' : PWArray p c' r' a'} (hc : c = c')
    (hr : ∀ i : Fin c, r i = r' (Fin.cast hc i))
    (ha : ∀ (i : Fin c) (v : Fin (r i)), a ⟨i, v⟩ = a' ⟨Fin.cast hc i, Fin.cast (hr i) v⟩)
    (hB : ∀ (i : Fin c) (v : Fin (r i)) (i' : Fin c) (v' : Fin (r i')),
      (B ⟨i, v⟩ ⟨i', v'⟩).val =
        (B' ⟨Fin.cast hc i, Fin.cast (hr i) v⟩ ⟨Fin.cast hc i', Fin.cast (hr i') v'⟩).val)
    (h : B ∈ realizedPW p c r a) : B' ∈ realizedPW p c' r' a' := by
  subst hc
  have er : r = r' := funext hr
  subst er
  have ea : a = a' := funext fun k => ha k.1 k.2
  subst ea
  have eB : B = B' := funext fun k => funext fun k' => Fin.ext (hB k.1 k.2 k'.1 k'.2)
  subst eB
  exact h

/-- Theorem 3.1 bounds the power word factor of the fibre: `N_b(D)` is at most the number of
power word arrays realised for the layer ranks and relative orders recorded in `D`. -/
theorem ncard_realizedB_le {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0}) (D : RecData m) :
    (realizedB hp T D).ncard ≤ (realizedPW p D.1.val (fibRk D) (fibAk D)).ncard := by
  have : Fact p.Prime := ⟨hp⟩
  refine Set.ncard_le_ncard_of_injOn (pwOfB hp.pos D) ?_ ?_ (Set.toFinite _)
  · rintro B ⟨G, -, C, hc⟩
    obtain ⟨u, d, X, r, hS, hc1, hR, hA, -, hBf⟩ := code_facts hp hc
    have hn : d.n = fOff r hS.nL := hS.nL_spec.symm
    have hG : IsPGroup p G := IsPGroup.of_card hS.realizes.card
    have hmem := (hS.toSimsGenSet hp hn).mem_realizedPW hG
    refine realizedPW_congr hc1.symm ?_ ?_ ?_ hmem
    · intro i
      exact (hR i.val i.isLt).symm
    · intro i v
      show d.a (hS.brEquiv hn ⟨i, v⟩) = fibA D (fOff (fibR D) i.val + v.val)
      rw [hA, fOff_congr hR i.val i.isLt.le]
      exact (hS.brA_brEquiv hn ⟨i, v⟩).symm
    · intro i v i' v'
      rw [hS.powerWords_toSimsGenSet hp hn, pwOfB_val_of_code hp hc]
      show _ = flatB B (fOff (fibR D) i.val + v.val) (fOff (fibR D) i'.val + v'.val)
      rw [hBf, fOff_congr hR i.val i.isLt.le, fOff_congr hR i'.val i'.isLt.le]
      exact (hS.brB_brEquiv hn ⟨i, v⟩ ⟨i', v'⟩).symm
  · rintro B₁ ⟨G₁, -, C₁, hc₁⟩ B₂ ⟨G₂, -, C₂, hc₂⟩ heq
    have hall : ∀ k k' : SimsIdx D.1.val (fibRk D),
        flatB B₁ (fOff (fibR D) k.1.val + k.2.val) (fOff (fibR D) k'.1.val + k'.2.val) =
          flatB B₂ (fOff (fibR D) k.1.val + k.2.val) (fOff (fibR D) k'.1.val + k'.2.val) := by
      intro k k'
      have h := congrArg Fin.val (congrFun (congrFun heq k) k')
      rw [pwOfB_val_of_code hp hc₁, pwOfB_val_of_code hp hc₂] at h
      exact h
    funext i j
    apply Fin.ext
    obtain ⟨w, hw, v, hv, ei⟩ :=
      brLayer_of_lt (fibR D) D.1.val i.val (lt_of_lt_of_eq i.isLt (fibTot D))
    obtain ⟨w', hw', v', hv', ej⟩ :=
      brLayer_of_lt (fibR D) D.1.val j.val (lt_of_lt_of_eq j.isLt (fibTot D))
    have h2 : flatB B₁ (fOff (fibR D) w + v) (fOff (fibR D) w' + v') =
        flatB B₂ (fOff (fibR D) w + v) (fOff (fibR D) w' + v') :=
      hall ⟨⟨w, hw⟩, ⟨v, hv⟩⟩ ⟨⟨w', hw'⟩, ⟨v', hv'⟩⟩
    rw [← ei, ← ej, flatB_fin, flatB_fin] at h2
    exact h2

/-- The fibrewise count with Theorem 3.1 plugged into the power word factor: the number of
classes of `T` is at most `Σ_{D ∈ I} p ^ PW(D) N_c(D)`, where `PW(D)` is the exponent
`Σ_i [ r_i m_{i+1} + (r_i - 1)(s_i - r_i) ]` of Theorem 3.1 for the ranks and relative orders
recorded in `D`. -/
theorem ncard_classes_le_fiber_pw {m : ℕ} (hp : p.Prime) (T : Set FiniteGrp.{0})
    (I : Finset (RecData m)) (hI : ∀ G ∈ T, ∃ D : FullData p m, SimsCode hp m G D ∧ D.1 ∈ I) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard ≤
      ∑ D ∈ I, p ^ pwBound2 (fibAk D) * (realizedC hp T D).ncard := by
  have : Fact p.Prime := ⟨hp⟩
  refine (ncard_classes_le_fiber hp T I hI).trans (Finset.sum_le_sum fun D _ => ?_)
  exact Nat.mul_le_mul ((ncard_realizedB_le hp T D).trans
    (liqiao_thm_3_1 D.1.val (fibRk D) (fibAk D) (fibAk_pos D))) le_rfl

end FiberCount

end OMA.SimsLite

#print axioms OMA.SimsLite.ncard_classes_le_fiber_pw
#print axioms OMA.SimsLite.ncard_classes_le_fiber_pred
#print axioms OMA.SimsLite.classes_finite
#print axioms OMA.SimsLite.SimsGen.brB_eq_powerWords
