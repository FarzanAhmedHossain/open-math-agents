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
      rw [Subgroup.mem_comap]
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
  rw [Subgroup.mem_subgroupOf] at h2 hz'
  have h3 : z = (z' : G) * ((z'⁻¹ * ⟨z, hz⟩ : lcs G i) : G) := by simp
  rw [h3]
  exact M.mul_mem hz' (Subgroup.mem_sup_right h2)

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

end OMA.SimsLite

#print axioms OMA.SimsLite.sims_powerWords_counted
