import H2Dev.Frame
import H2Dev.PowerWords

/-! Li-Qiao, Section 2.2 (the associated graded Lie ring of an N-series, pp.16-17), Section 2.3
(Sims data in the graded Lie ring, pp.17-19) and the breadth definitions (48)-(51) (pp.24-25).

Indexing is 0-based, as in the rest of the library: for a series `F : ℕ → Subgroup G` the layer
`GrL F i` is `F i / F (i + 1)`; for `F = lcs G` this is the paper's `L_{i+1} = G_{i+1} / G_{i+2}`.
An N-series (`NSeries F`) is a descending series of normal subgroups with
`⁅F a, F b⁆ ≤ F (a + b + 1)` (the paper's `[F_i, F_j] ≤ F_{i+j}` in 1-based indexing); the lower
central series is one (`nseries_lcs`).

Layers. `GrL F i = Additive (ElemQ 0 (F i) (F (i+1) ∩ F i))`, the abelian group
`(F i)^ab / (F (i+1))^ab` written additively (it is `F i / F (i+1)`, see `grOf_eq_iff`); it is a
`ℤ`-module (an additive commutative group), not in general an `F_p`-vector space: the
`ZMod p`-modules of the paper are `V = L_1 / p L_1` and `W = L_2 / p L_2` (`VQ`, `WQ` of `Frame`),
and `grToV`, `grToW`, `remark_2_6` identify `lamLin` with the reduction of the layer bracket.
`grOf F i g` is the class of `g ∈ F i` (junk `0` off `F i`), `grLift` a chosen lift.

Bracket (30). `grBr F a b n x y = grOf F n ⁅lift x, lift y⁆`, meaningful for `n = a + b + 1`:
* `grBr_mk` : `[gF_{a+1}, hF_{b+1}]_L = [g, h] F_{a+b+2}` (independence of lifts);
* `grBr_add_left`, `grBr_add_right` (biadditive), `grBrHom` (bundled), `grBr_self` (alternating),
  `grBr_swap` (antisymmetric), `grBr_jacobi` (Jacobi identity (31), from the Hall-Witt identity
  `hall_witt`); class-3 forms `grBr_jacobi_one`, `grBr_recover` (the recovery step of Sec 2.3).
Section 2.3:
* `coreC F s u` : `C_core = ⟨ḡ_{1,1}, ..., ḡ_{1,s}⟩` (33);
* `closure_grOf_eq_top` : the layer images of a generating set modulo `F (i+1)` generate `L_i`;
* `core_L2_closure` : `L_2 = ⟨[ḡ_{1,a}, ḡ_{1,b}]⟩` from the core condition (34);
* `core_L3_closure` : `L_3 = Σ_k [L_2, ḡ_{1,k}]` (34) for `i = 2`, via Jacobi;
* `grOf_block`, `grBr_block` (35)/(39)/(41), `grOf_power_block` (37), and
  `SimsGenSet.layer_power` : `p ^ a(i,j) ḡ_{i,j} = Σ_v b(i,j,i,v) ḡ_{i,v}` for the power word array
  of a Sims generating set (`PowerWords`).
Breadth (48)-(51):
* `imLog p f = log_p |im f|`, `breadthOf p ad S = max_{u ∈ S} log_p |im ad(u)|`;
* `adHom hF i u = ad(u) : L_i → L_{i+1}`, `grBreadth p hF i C` (48), `layerLog p F i = log_p |L_i|`;
* `grBreadth_spec` : maximiser `h*`, `|ker ad(h*)| = p ^ (s_i - b_i)` (49), `b_i ≤ min(s_i, s_{i+1})`;
* `layerLog_le_mul_grBreadth` : `s_{i+1} ≤ s b_i` (51);
* class 3: `breadthTwo`, `breadth_two_class3` : `m_3 ≤ s b_2`, `b_2 ≤ m_3`, `b_2 ≤ m_2 - m_3`
  and the kernel formula, for a finite p-group with `γ_4 = 1` and a Sims core of size `s`.

Commutator convention: Mathlib's `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`, as in the rest of the library. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section NSer

variable {G : Type u} [Group G]

/-- An N-series (0-based): descending normal subgroups with `⁅F a, F b⁆ ≤ F (a + b + 1)`. -/
structure NSeries (F : ℕ → Subgroup G) : Prop where
  normal : ∀ i, (F i).Normal
  succ_le : ∀ i, F (i + 1) ≤ F i
  comm_le : ∀ a b, ⁅F a, F b⁆ ≤ F (a + b + 1)

variable {F : ℕ → Subgroup G}

theorem NSeries.anti (hF : NSeries F) {a b : ℕ} (h : a ≤ b) : F b ≤ F a :=
  antitone_nat_of_succ_le hF.succ_le h

theorem NSeries.comm_mem (hF : NSeries F) {a b n : ℕ} {x y : G} (hx : x ∈ F a) (hy : y ∈ F b)
    (hn : n ≤ a + b + 1) : ⁅x, y⁆ ∈ F n :=
  hF.anti hn (hF.comm_le a b (Subgroup.commutator_mem_commutator hx hy))

/-- The lower central series is an N-series. -/
theorem nseries_lcs : NSeries (lcs G) where
  normal i := normal_of_sandwich (n := i) (lcs_antitone (Nat.le_succ i)) le_rfl
  succ_le i := lcs_antitone (Nat.le_succ i)
  comm_le a b := lcs_comm_le b a

lemma mem_lcs_zero (g : G) : g ∈ lcs G 0 := by
  rw [lcs_zero]
  exact Subgroup.mem_top g

/-! Layers. -/

/-- `F (i + 1)` as a subgroup of `F i`. -/
abbrev grK (F : ℕ → Subgroup G) (i : ℕ) : Subgroup (F i) := (F (i + 1)).subgroupOf (F i)

/-- The layer `L_i = F i / F (i + 1)`, written additively. -/
abbrev GrL (F : ℕ → Subgroup G) (i : ℕ) : Type u := Additive (ElemQ 0 (F i) (grK F i))

lemma grK_comm (hF : NSeries F) (i : ℕ) : commutator (F i) ≤ grK F i := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_subgroupOf]
  show ⁅(a : G), (b : G)⁆ ∈ F (i + 1)
  exact hF.comm_mem a.2 b.2 (by omega)

lemma grK_pow (i : ℕ) (g : F i) : g ^ 0 ∈ grK F i := by
  rw [pow_zero]
  exact Subgroup.one_mem _

theorem ker_grPi (hF : NSeries F) (i : ℕ) : (elemPi 0 (F i) (grK F i)).ker = grK F i :=
  ker_elemPi (grK_comm hF i) (grK_pow i)

instance grL_finite [Finite G] (F : ℕ → Subgroup G) (i : ℕ) : Finite (GrL F i) := by
  have : Finite (ElemQ 0 (F i) (grK F i)) :=
    Finite.of_surjective _ (elemPi_surjective (p := 0) (grK F i))
  exact inferInstanceAs (Finite (Additive (ElemQ 0 (F i) (grK F i))))

open Classical in
/-- The class `g F_{i+1} ∈ L_i` of `g ∈ F i` (junk `0` if `g ∉ F i`). -/
noncomputable def grOf (F : ℕ → Subgroup G) (i : ℕ) (g : G) : GrL F i :=
  if h : g ∈ F i then Additive.ofMul (elemPi 0 (F i) (grK F i) ⟨g, h⟩) else 0

theorem grOf_of_mem {i : ℕ} {g : G} (h : g ∈ F i) :
    grOf F i g = Additive.ofMul (elemPi 0 (F i) (grK F i) ⟨g, h⟩) := by
  rw [grOf, dif_pos h]

theorem grOf_of_not_mem {i : ℕ} {g : G} (h : g ∉ F i) : grOf F i g = 0 := by
  rw [grOf, dif_neg h]

theorem grOf_mul {i : ℕ} {g h : G} (hg : g ∈ F i) (hh : h ∈ F i) :
    grOf F i (g * h) = grOf F i g + grOf F i h := by
  rw [grOf_of_mem hg, grOf_of_mem hh, grOf_of_mem (Subgroup.mul_mem _ hg hh)]
  have e : (⟨g * h, Subgroup.mul_mem _ hg hh⟩ : F i) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
  rw [e, map_mul, Additive.ofMul_mul]

theorem grOf_one (i : ℕ) : grOf F i 1 = 0 := by
  rw [grOf_of_mem (Subgroup.one_mem _)]
  have e : (⟨1, Subgroup.one_mem _⟩ : F i) = 1 := rfl
  rw [e, map_one, Additive.ofMul_one]

theorem grOf_inv {i : ℕ} {g : G} (hg : g ∈ F i) : grOf F i g⁻¹ = - grOf F i g := by
  have h := grOf_mul hg (Subgroup.inv_mem _ hg)
  rw [mul_inv_cancel, grOf_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem grOf_pow {i : ℕ} {g : G} (hg : g ∈ F i) (k : ℕ) : grOf F i (g ^ k) = k • grOf F i g := by
  induction k with
  | zero => rw [pow_zero, grOf_one, zero_smul]
  | succ k ih => rw [pow_succ, grOf_mul (Subgroup.pow_mem _ hg k) hg, ih, succ_nsmul]

theorem grOf_eq_zero_iff (hF : NSeries F) {i : ℕ} {g : G} (hg : g ∈ F i) :
    grOf F i g = 0 ↔ g ∈ F (i + 1) := by
  rw [grOf_of_mem hg, Additive.ofMul_eq_zero, ← MonoidHom.mem_ker, ker_grPi hF i,
    Subgroup.mem_subgroupOf]

theorem grOf_of_mem_succ (hF : NSeries F) {i : ℕ} {g : G} (hg : g ∈ F (i + 1)) :
    grOf F i g = 0 :=
  (grOf_eq_zero_iff hF (hF.succ_le i hg)).mpr hg

/-- `gF_{i+1} = hF_{i+1}` iff `g h⁻¹ ∈ F (i + 1)`. -/
theorem grOf_eq_iff (hF : NSeries F) {i : ℕ} {g h : G} (hg : g ∈ F i) (hh : h ∈ F i) :
    grOf F i g = grOf F i h ↔ g * h⁻¹ ∈ F (i + 1) := by
  have e := grOf_mul hg (Subgroup.inv_mem _ hh)
  rw [grOf_inv hh] at e
  rw [← grOf_eq_zero_iff hF (Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hh)), e, add_neg_eq_zero]

theorem grOf_surjective (F : ℕ → Subgroup G) (i : ℕ) (z : GrL F i) :
    ∃ g ∈ F i, grOf F i g = z := by
  obtain ⟨x, hx⟩ := elemPi_surjective (p := 0) (grK F i) (Additive.toMul z)
  refine ⟨x, x.2, ?_⟩
  rw [grOf_of_mem x.2]
  show Additive.ofMul (elemPi 0 (F i) (grK F i) x) = z
  rw [hx, Additive.ofMul_toMul]

/-- A chosen lift of `z ∈ L_i` to `F i`. -/
noncomputable def grLift (F : ℕ → Subgroup G) (i : ℕ) (z : GrL F i) : G :=
  Classical.choose (grOf_surjective F i z)

theorem grLift_mem (F : ℕ → Subgroup G) (i : ℕ) (z : GrL F i) : grLift F i z ∈ F i :=
  (Classical.choose_spec (grOf_surjective F i z)).1

theorem grOf_grLift (F : ℕ → Subgroup G) (i : ℕ) (z : GrL F i) : grOf F i (grLift F i z) = z :=
  (Classical.choose_spec (grOf_surjective F i z)).2

/-- Conjugation acts trivially on the layers. -/
theorem grOf_conj (hF : NSeries F) {n a : ℕ} {g w : G} (hg : g ∈ F n) (hw : w ∈ F a) :
    grOf F n (w * g * w⁻¹) = grOf F n g := by
  rw [grOf_eq_iff hF ((hF.normal n).conj_mem g hg w) hg, ← commutatorElement_def]
  exact hF.comm_mem hw hg (by omega)

/-- `|F i| = |F (i + 1)| |L_i|`. -/
theorem card_grL_mul (hF : NSeries F) (i : ℕ) :
    Nat.card (F (i + 1)) * Nat.card (GrL F i) = Nat.card (F i) := by
  have h0 : Nat.card (GrL F i) = (grK F i).index := card_elemQ (grK_comm hF i) (grK_pow i)
  rw [h0]
  have h1 := Subgroup.card_mul_index ((F (i + 1)).subgroupOf (F i))
  have h2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hF.succ_le i)).toEquiv
  rw [h2] at h1
  exact h1

theorem card_grL_of_bot (hF : NSeries F) {i : ℕ} (h : F (i + 1) = ⊥) :
    Nat.card (GrL F i) = Nat.card (F i) := by
  have h1 := card_grL_mul hF i
  rw [h, Subgroup.card_bot, one_mul] at h1
  exact h1

theorem card_grL_dvd [Finite G] (hF : NSeries F) (i : ℕ) : Nat.card (GrL F i) ∣ Nat.card G :=
  (Dvd.intro_left (Nat.card (F (i + 1))) (card_grL_mul hF i)).trans
    (Subgroup.card_subgroup_dvd_card (F i))

/-- `s_i = log_p |L_i|` (0-based: `layerLog p (lcs G) i` is the paper's `s_{i+1}`). -/
noncomputable def layerLog (p : ℕ) (F : ℕ → Subgroup G) (i : ℕ) : ℕ := Nat.log p (Nat.card (GrL F i))

theorem card_grL_pow [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (hF : NSeries F) (i : ℕ) : Nat.card (GrL F i) = p ^ layerLog p F i := by
  have hd : Nat.card (GrL F i) ∣ p ^ m := hG ▸ card_grL_dvd hF i
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [layerLog, hj, Nat.log_pow hp.one_lt]

/-! Element-level commutator calculus modulo the series. -/

theorem grOf_comm_wd_left (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x x' y : G}
    (hx : x ∈ F a) (hxx : x' * x⁻¹ ∈ F (a + 1)) (hy : y ∈ F b) :
    grOf F n ⁅x', y⁆ = grOf F n ⁅x, y⁆ := by
  have hx' : x' ∈ F a := by
    have h := Subgroup.mul_mem _ (hF.succ_le a hxx) hx
    rwa [inv_mul_cancel_right] at h
  have m1 : ⁅x', y⁆ ∈ F n := hF.comm_mem hx' hy hn.ge
  have m2 : ⁅x, y⁆ ∈ F n := hF.comm_mem hx hy hn.ge
  rw [grOf_eq_iff hF m1 m2]
  have e : ⁅x', y⁆ * ⁅x, y⁆⁻¹ =
      ⁅x' * x⁻¹, ⁅x, y⁆⁆ * (⁅x, y⁆ * ⁅x' * x⁻¹, y⁆ * ⁅x, y⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact hF.comm_mem hxx m2 (by omega)
  · exact (hF.normal (n + 1)).conj_mem _ (hF.comm_mem hxx hy (by omega)) _

theorem grOf_comm_wd_right (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x y y' : G}
    (hx : x ∈ F a) (hy : y ∈ F b) (hyy : y' * y⁻¹ ∈ F (b + 1)) :
    grOf F n ⁅x, y'⁆ = grOf F n ⁅x, y⁆ := by
  have hy' : y' ∈ F b := by
    have h := Subgroup.mul_mem _ (hF.succ_le b hyy) hy
    rwa [inv_mul_cancel_right] at h
  have m1 : ⁅x, y'⁆ ∈ F n := hF.comm_mem hx hy' hn.ge
  have m2 : ⁅x, y⁆ ∈ F n := hF.comm_mem hx hy hn.ge
  rw [grOf_eq_iff hF m1 m2]
  have e : ⁅x, y'⁆ * ⁅x, y⁆⁻¹ = ⁅x, y' * y⁻¹⁆ * ⁅y' * y⁻¹, ⁅x, y⁆⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact hF.comm_mem hx hyy (by omega)
  · exact hF.comm_mem hyy m2 (by omega)

theorem grOf_comm_mul_left (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x x' y : G}
    (hx : x ∈ F a) (hx' : x' ∈ F a) (hy : y ∈ F b) :
    grOf F n ⁅x * x', y⁆ = grOf F n ⁅x, y⁆ + grOf F n ⁅x', y⁆ := by
  have h1 : ⁅x, y⁆ ∈ F n := hF.comm_mem hx hy hn.ge
  have h2 : ⁅x', y⁆ ∈ F n := hF.comm_mem hx' hy hn.ge
  rw [← grOf_mul h1 h2, grOf_eq_iff hF (hF.comm_mem (Subgroup.mul_mem _ hx hx') hy hn.ge)
    (Subgroup.mul_mem _ h1 h2)]
  have e : ⁅x * x', y⁆ * (⁅x, y⁆ * ⁅x', y⁆)⁻¹ = ⁅x, ⁅x', y⁆⁆ * ⁅⁅x', y⁆, ⁅x, y⁆⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (hF.comm_mem hx h2 (by omega)) (hF.comm_mem h2 h1 (by omega))

theorem grOf_comm_mul_right (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x y y' : G}
    (hx : x ∈ F a) (hy : y ∈ F b) (hy' : y' ∈ F b) :
    grOf F n ⁅x, y * y'⁆ = grOf F n ⁅x, y⁆ + grOf F n ⁅x, y'⁆ := by
  have h1 : ⁅x, y⁆ ∈ F n := hF.comm_mem hx hy hn.ge
  have h2 : ⁅x, y'⁆ ∈ F n := hF.comm_mem hx hy' hn.ge
  rw [← grOf_mul h1 h2, grOf_eq_iff hF (hF.comm_mem hx (Subgroup.mul_mem _ hy hy') hn.ge)
    (Subgroup.mul_mem _ h1 h2)]
  have e : ⁅x, y * y'⁆ * (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ = ⁅x, y⁆ * ⁅y, ⁅x, y'⁆⁆ * ⁅x, y⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (hF.normal (n + 1)).conj_mem _ (hF.comm_mem hy h2 (by omega)) _

theorem grOf_comm_swap (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x y : G}
    (hx : x ∈ F a) (hy : y ∈ F b) : grOf F n ⁅x, y⁆ = - grOf F n ⁅y, x⁆ := by
  have h : ⁅y, x⁆ ∈ F n := hF.comm_mem hy hx (by omega)
  rw [← commutatorElement_inv y x, grOf_inv h]

theorem grOf_comm_inv_left (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x y : G}
    (hx : x ∈ F a) (hy : y ∈ F b) : grOf F n ⁅x⁻¹, y⁆ = - grOf F n ⁅x, y⁆ := by
  have h := grOf_comm_mul_left hF hn (Subgroup.inv_mem _ hx) hx hy
  rw [inv_mul_cancel, commutatorElement_one_left, grOf_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem grOf_comm_inv_inner (hF : NSeries F) {a b c n : ℕ} (hn : a + b + c + 2 = n)
    {x y z : G} (hx : x ∈ F a) (hy : y ∈ F b) (hz : z ∈ F c) :
    grOf F n ⁅⁅x⁻¹, y⁆, z⁆ = - grOf F n ⁅⁅x, y⁆, z⁆ := by
  have m1 : ⁅x⁻¹, y⁆ ∈ F (a + b + 1) := hF.comm_mem (Subgroup.inv_mem _ hx) hy le_rfl
  have m2 : ⁅x, y⁆ ∈ F (a + b + 1) := hF.comm_mem hx hy le_rfl
  have e : grOf F (a + b + 1) ⁅x⁻¹, y⁆ = grOf F (a + b + 1) ⁅x, y⁆⁻¹ := by
    rw [grOf_comm_inv_left hF (n := a + b + 1) rfl hx hy, grOf_inv m2]
  have hd := (grOf_eq_iff hF m1 (Subgroup.inv_mem _ m2)).mp e
  rw [grOf_comm_wd_left hF (a := a + b + 1) (b := c) (n := n) (by omega)
    (Subgroup.inv_mem _ m2) hd hz,
    grOf_comm_inv_left hF (a := a + b + 1) (b := c) (n := n) (by omega) m2 hz]

/-- The Hall-Witt identity (for `⁅x, y⁆ = x y x⁻¹ y⁻¹`). -/
theorem hall_witt (x y z : G) :
    x * ⁅⁅x⁻¹, y⁆, z⁆ * x⁻¹ * (z * ⁅⁅z⁻¹, x⁆, y⁆ * z⁻¹) * (y * ⁅⁅y⁻¹, z⁆, x⁆ * y⁻¹) = 1 := by
  simp only [commutatorElement_def]
  group

/-- Jacobi identity modulo the series (from Hall-Witt). -/
theorem grOf_jacobi (hF : NSeries F) {a b c n : ℕ} (hn : a + b + c + 2 = n) {x y z : G}
    (hx : x ∈ F a) (hy : y ∈ F b) (hz : z ∈ F c) :
    grOf F n ⁅⁅x, y⁆, z⁆ + grOf F n ⁅⁅y, z⁆, x⁆ + grOf F n ⁅⁅z, x⁆, y⁆ = 0 := by
  have m1 : ⁅⁅x⁻¹, y⁆, z⁆ ∈ F n :=
    hF.comm_mem (hF.comm_mem (Subgroup.inv_mem _ hx) hy le_rfl) hz (by omega)
  have m2 : ⁅⁅z⁻¹, x⁆, y⁆ ∈ F n :=
    hF.comm_mem (hF.comm_mem (Subgroup.inv_mem _ hz) hx le_rfl) hy (by omega)
  have m3 : ⁅⁅y⁻¹, z⁆, x⁆ ∈ F n :=
    hF.comm_mem (hF.comm_mem (Subgroup.inv_mem _ hy) hz le_rfl) hx (by omega)
  have c1 : x * ⁅⁅x⁻¹, y⁆, z⁆ * x⁻¹ ∈ F n := (hF.normal n).conj_mem _ m1 x
  have c2 : z * ⁅⁅z⁻¹, x⁆, y⁆ * z⁻¹ ∈ F n := (hF.normal n).conj_mem _ m2 z
  have c3 : y * ⁅⁅y⁻¹, z⁆, x⁆ * y⁻¹ ∈ F n := (hF.normal n).conj_mem _ m3 y
  have h := congrArg (grOf F n) (hall_witt x y z)
  rw [grOf_mul (Subgroup.mul_mem _ c1 c2) c3, grOf_mul c1 c2, grOf_conj hF m1 hx,
    grOf_conj hF m2 hz, grOf_conj hF m3 hy, grOf_one,
    grOf_comm_inv_inner hF hn hx hy hz,
    grOf_comm_inv_inner hF (a := c) (b := a) (c := b) (by omega) hz hx hy,
    grOf_comm_inv_inner hF (a := b) (b := c) (c := a) (by omega) hy hz hx] at h
  calc _ = -(-grOf F n ⁅⁅x, y⁆, z⁆ + -grOf F n ⁅⁅z, x⁆, y⁆ + -grOf F n ⁅⁅y, z⁆, x⁆) := by
        abel
    _ = 0 := by rw [h, neg_zero]

/-! The bracket (30) on the layers. -/

/-- `[x, y]_L ∈ L_n` for `x ∈ L_a`, `y ∈ L_b` (meaningful for `n = a + b + 1`). -/
noncomputable def grBr (F : ℕ → Subgroup G) (a b n : ℕ) (x : GrL F a) (y : GrL F b) : GrL F n :=
  grOf F n ⁅grLift F a x, grLift F b y⁆

/-- (30): `[g F_{a+1}, h F_{b+1}]_L = [g, h] F_{a+b+2}`, independently of the lifts. -/
theorem grBr_mk (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) {x y : G} (hx : x ∈ F a)
    (hy : y ∈ F b) : grBr F a b n (grOf F a x) (grOf F b y) = grOf F n ⁅x, y⁆ := by
  unfold grBr
  have h1 : grLift F a (grOf F a x) * x⁻¹ ∈ F (a + 1) :=
    (grOf_eq_iff hF (grLift_mem F a _) hx).mp (grOf_grLift F a _)
  have h2 : grLift F b (grOf F b y) * y⁻¹ ∈ F (b + 1) :=
    (grOf_eq_iff hF (grLift_mem F b _) hy).mp (grOf_grLift F b _)
  rw [grOf_comm_wd_left hF hn hx h1 (grLift_mem F b _), grOf_comm_wd_right hF hn hx hy h2]

theorem grBr_add_left (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) (x x' : GrL F a)
    (y : GrL F b) : grBr F a b n (x + x') y = grBr F a b n x y + grBr F a b n x' y := by
  obtain ⟨g, hg, rfl⟩ := grOf_surjective F a x
  obtain ⟨g', hg', rfl⟩ := grOf_surjective F a x'
  obtain ⟨h, hh, rfl⟩ := grOf_surjective F b y
  rw [← grOf_mul hg hg', grBr_mk hF hn (Subgroup.mul_mem _ hg hg') hh, grBr_mk hF hn hg hh,
    grBr_mk hF hn hg' hh, grOf_comm_mul_left hF hn hg hg' hh]

theorem grBr_add_right (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) (x : GrL F a)
    (y y' : GrL F b) : grBr F a b n x (y + y') = grBr F a b n x y + grBr F a b n x y' := by
  obtain ⟨g, hg, rfl⟩ := grOf_surjective F a x
  obtain ⟨h, hh, rfl⟩ := grOf_surjective F b y
  obtain ⟨h', hh', rfl⟩ := grOf_surjective F b y'
  rw [← grOf_mul hh hh', grBr_mk hF hn hg (Subgroup.mul_mem _ hh hh'), grBr_mk hF hn hg hh,
    grBr_mk hF hn hg hh', grOf_comm_mul_right hF hn hg hh hh']

/-- The bracket `L_a × L_b → L_{a+b+1}` as a biadditive map. -/
noncomputable def grBrHom (hF : NSeries F) (a b n : ℕ) (hn : a + b + 1 = n) :
    GrL F a →+ GrL F b →+ GrL F n :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (grBr F a b n x) (grBr_add_right hF hn x))
    (fun x x' => AddMonoidHom.ext fun y => grBr_add_left hF hn x x' y)

theorem grBrHom_apply (hF : NSeries F) (a b n : ℕ) (hn : a + b + 1 = n) (x : GrL F a)
    (y : GrL F b) : grBrHom hF a b n hn x y = grBr F a b n x y := rfl

/-- Alternating: `[x, x]_L = 0`. -/
theorem grBr_self (hF : NSeries F) {a n : ℕ} (hn : a + a + 1 = n) (x : GrL F a) :
    grBr F a a n x x = 0 := by
  obtain ⟨g, hg, rfl⟩ := grOf_surjective F a x
  rw [grBr_mk hF hn hg hg, commutatorElement_self, grOf_one]

/-- Antisymmetric: `[x, y]_L = - [y, x]_L`. -/
theorem grBr_swap (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) (x : GrL F a)
    (y : GrL F b) : grBr F a b n x y = - grBr F b a n y x := by
  obtain ⟨g, hg, rfl⟩ := grOf_surjective F a x
  obtain ⟨h, hh, rfl⟩ := grOf_surjective F b y
  rw [grBr_mk hF hn hg hh, grBr_mk hF (n := n) (by omega) hh hg, grOf_comm_swap hF hn hg hh]

/-- The Jacobi identity (31). -/
theorem grBr_jacobi (hF : NSeries F) {a b c n : ℕ} (hn : a + b + c + 2 = n) (x : GrL F a)
    (y : GrL F b) (z : GrL F c) :
    grBr F (a + b + 1) c n (grBr F a b (a + b + 1) x y) z +
      grBr F (b + c + 1) a n (grBr F b c (b + c + 1) y z) x +
      grBr F (c + a + 1) b n (grBr F c a (c + a + 1) z x) y = 0 := by
  obtain ⟨g, hg, rfl⟩ := grOf_surjective F a x
  obtain ⟨h, hh, rfl⟩ := grOf_surjective F b y
  obtain ⟨k, hk, rfl⟩ := grOf_surjective F c z
  rw [grBr_mk hF (n := a + b + 1) rfl hg hh, grBr_mk hF (n := b + c + 1) rfl hh hk,
    grBr_mk hF (n := c + a + 1) rfl hk hg,
    grBr_mk hF (n := n) (by omega) (hF.comm_mem hg hh le_rfl) hk,
    grBr_mk hF (n := n) (by omega) (hF.comm_mem hh hk le_rfl) hg,
    grBr_mk hF (n := n) (by omega) (hF.comm_mem hk hg le_rfl) hh]
  exact grOf_jacobi hF hn hg hh hk

theorem grBr_neg_left (hF : NSeries F) {a b n : ℕ} (hn : a + b + 1 = n) (x : GrL F a)
    (y : GrL F b) : grBr F a b n (-x) y = - grBr F a b n x y := by
  rw [← grBrHom_apply hF a b n hn, map_neg, AddMonoidHom.neg_apply, grBrHom_apply]

/-- Jacobi on `L_1 × L_1 × L_1 → L_3` (paper indexing; layers `0, 1, 2` here). -/
theorem grBr_jacobi_one (hF : NSeries F) (x y z : GrL F 0) :
    grBr F 1 0 2 (grBr F 0 0 1 x y) z + grBr F 1 0 2 (grBr F 0 0 1 y z) x +
      grBr F 1 0 2 (grBr F 0 0 1 z x) y = 0 :=
  grBr_jacobi hF (a := 0) (b := 0) (c := 0) (n := 2) rfl x y z

/-- The recovery step of Section 2.3: `[[x, y], z] = [[x, z], y] - [[y, z], x]` on `L_1`. -/
theorem grBr_recover (hF : NSeries F) (x y z : GrL F 0) :
    grBr F 1 0 2 (grBr F 0 0 1 x y) z =
      grBr F 1 0 2 (grBr F 0 0 1 x z) y - grBr F 1 0 2 (grBr F 0 0 1 y z) x := by
  have hj := grBr_jacobi_one hF x y z
  rw [grBr_swap hF (n := 1) rfl z x, grBr_neg_left hF (a := 1) (b := 0) (n := 2) rfl] at hj
  calc grBr F 1 0 2 (grBr F 0 0 1 x y) z =
      (grBr F 1 0 2 (grBr F 0 0 1 x y) z + grBr F 1 0 2 (grBr F 0 0 1 y z) x +
        -grBr F 1 0 2 (grBr F 0 0 1 x z) y) + grBr F 1 0 2 (grBr F 0 0 1 x z) y -
          grBr F 1 0 2 (grBr F 0 0 1 y z) x := by abel
    _ = grBr F 1 0 2 (grBr F 0 0 1 x z) y - grBr F 1 0 2 (grBr F 0 0 1 y z) x := by
      rw [hj, zero_add]

/-! Remark 2.6: `β_G` is the reduction of the bracket `L_1 × L_1 → L_2`. -/

section Remark26

variable {p : ℕ}

/-- `L_1 → V = L_1 / p L_1`. -/
noncomputable def grToV (p : ℕ) (G : Type u) [Group G] (z : GrL (lcs G) 0) : Additive (VQ p G) :=
  Additive.ofMul (piV p G (grLift (lcs G) 0 z))

theorem grToV_mk (g : G) : grToV p G (grOf (lcs G) 0 g) = Additive.ofMul (piV p G g) := by
  have h := (grOf_eq_iff nseries_lcs (grLift_mem (lcs G) 0 _) (mem_lcs_zero g)).mp
    (grOf_grLift (lcs G) 0 (grOf (lcs G) 0 g))
  have h' : grLift (lcs G) 0 (grOf (lcs G) 0 g) * g⁻¹ ∈ commutator G := by
    rw [commutator_eq_lcs_one]
    exact h
  show Additive.ofMul (piV p G (grLift (lcs G) 0 (grOf (lcs G) 0 g))) = Additive.ofMul (piV p G g)
  rw [piV_eq_iff.mpr (commutator_le_pPhi (p := p) h')]

theorem grToV_add (z z' : GrL (lcs G) 0) : grToV p G (z + z') = grToV p G z + grToV p G z' := by
  obtain ⟨g, -, rfl⟩ := grOf_surjective (lcs G) 0 z
  obtain ⟨g', -, rfl⟩ := grOf_surjective (lcs G) 0 z'
  rw [← grOf_mul (mem_lcs_zero g) (mem_lcs_zero g'), grToV_mk, grToV_mk, grToV_mk, map_mul,
    Additive.ofMul_mul]

theorem grToV_surjective : Function.Surjective (grToV p G) := by
  intro v
  obtain ⟨g, hg⟩ := piV_surjective (p := p) (Additive.toMul v)
  refine ⟨grOf (lcs G) 0 g, ?_⟩
  rw [grToV_mk, hg, Additive.ofMul_toMul]

/-- `L_2 → W = L_2 / p L_2`. -/
noncomputable def grToW (p : ℕ) (G : Type u) [Group G] (z : GrL (lcs G) 1) :
    Additive (WQ p G) :=
  Additive.ofMul (piW p G ⟨grLift (lcs G) 1 z, grLift_mem (lcs G) 1 z⟩)

theorem grToW_mk {g : G} (hg : g ∈ lcs G 1) :
    grToW p G (grOf (lcs G) 1 g) = Additive.ofMul (piW p G ⟨g, hg⟩) := by
  have h := (grOf_eq_iff nseries_lcs (grLift_mem (lcs G) 1 _) hg).mp
    (grOf_grLift (lcs G) 1 (grOf (lcs G) 1 g))
  show Additive.ofMul (piW p G ⟨grLift (lcs G) 1 (grOf (lcs G) 1 g), grLift_mem (lcs G) 1 _⟩) =
    Additive.ofMul (piW p G ⟨g, hg⟩)
  rw [piW_eq_of (a := ⟨grLift (lcs G) 1 (grOf (lcs G) 1 g), grLift_mem (lcs G) 1 _⟩)
    (b := ⟨g, hg⟩) (lcs_two_le_pN p h)]

theorem grToW_add (z z' : GrL (lcs G) 1) : grToW p G (z + z') = grToW p G z + grToW p G z' := by
  obtain ⟨g, hg, rfl⟩ := grOf_surjective (lcs G) 1 z
  obtain ⟨g', hg', rfl⟩ := grOf_surjective (lcs G) 1 z'
  rw [← grOf_mul hg hg', grToW_mk hg, grToW_mk hg', grToW_mk (Subgroup.mul_mem _ hg hg')]
  have e : (⟨g * g', Subgroup.mul_mem _ hg hg'⟩ : lcs G 1) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
  rw [e, map_mul, Additive.ofMul_mul]

theorem grToW_surjective : Function.Surjective (grToW p G) := by
  intro w
  obtain ⟨a, ha⟩ := piW_surjective (p := p) (G := G) (Additive.toMul w)
  refine ⟨grOf (lcs G) 1 a, ?_⟩
  rw [grToW_mk a.2]
  show Additive.ofMul (piW p G a) = w
  rw [ha, Additive.ofMul_toMul]

/-- Remark 2.6: `β_G(x mod p, y mod p) = [x, y]_L mod p` for `x, y ∈ L_1`. -/
theorem remark_2_6 [Fact p.Prime] (x y : GrL (lcs G) 0) :
    lamLin (grToV p G x) (grToV p G y) = grToW p G (grBr (lcs G) 0 0 1 x y) := by
  obtain ⟨g, -, rfl⟩ := grOf_surjective (lcs G) 0 x
  obtain ⟨h, -, rfl⟩ := grOf_surjective (lcs G) 0 y
  rw [grToV_mk, grToV_mk, lamLin_mk, grBr_mk nseries_lcs (n := 1) rfl (mem_lcs_zero g)
    (mem_lcs_zero h), grToW_mk (commElem_mem_lcs_one g h)]
  rfl

end Remark26

/-! Section 2.3: the Sims data inside `L`. -/

/-- Elements of `F n` whose layer class lies in `S`. -/
def grSub (F : ℕ → Subgroup G) (n : ℕ) (S : AddSubgroup (GrL F n)) : Subgroup G where
  carrier := {g | g ∈ F n ∧ grOf F n g ∈ S}
  mul_mem' := by
    intro a b ha hb
    have ha' : a ∈ F n ∧ grOf F n a ∈ S := ha
    have hb' : b ∈ F n ∧ grOf F n b ∈ S := hb
    show a * b ∈ F n ∧ grOf F n (a * b) ∈ S
    refine ⟨Subgroup.mul_mem _ ha'.1 hb'.1, ?_⟩
    rw [grOf_mul ha'.1 hb'.1]
    exact S.add_mem ha'.2 hb'.2
  one_mem' := by
    show (1 : G) ∈ F n ∧ grOf F n 1 ∈ S
    refine ⟨Subgroup.one_mem _, ?_⟩
    rw [grOf_one]
    exact S.zero_mem
  inv_mem' := by
    intro a ha
    have ha' : a ∈ F n ∧ grOf F n a ∈ S := ha
    show a⁻¹ ∈ F n ∧ grOf F n a⁻¹ ∈ S
    refine ⟨Subgroup.inv_mem _ ha'.1, ?_⟩
    rw [grOf_inv ha'.1]
    exact S.neg_mem ha'.2

theorem mem_grSub (F : ℕ → Subgroup G) (n : ℕ) (S : AddSubgroup (GrL F n)) (g : G) :
    g ∈ grSub F n S ↔ g ∈ F n ∧ grOf F n g ∈ S := Iff.rfl

theorem grSub_top (hF : NSeries F) {n : ℕ} {S : AddSubgroup (GrL F n)} (h : F n ≤ grSub F n S) :
    S = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨g, hg, rfl⟩ := grOf_surjective F n z
  exact ((mem_grSub F n S g).mp (h hg)).2

theorem succ_le_grSub (hF : NSeries F) (n : ℕ) (S : AddSubgroup (GrL F n)) :
    F (n + 1) ≤ grSub F n S := by
  intro g hg
  refine (mem_grSub F n S g).mpr ⟨hF.succ_le n hg, ?_⟩
  rw [grOf_of_mem_succ hF hg]
  exact S.zero_mem

/-- The layer images of a generating set of `F i` modulo `F (i + 1)` generate `L_i`. -/
theorem closure_grOf_eq_top (hF : NSeries F) {i : ℕ} {X : Set G} (hX : X ⊆ F i)
    (h : F i ≤ Subgroup.closure X ⊔ F (i + 1)) :
    AddSubgroup.closure (grOf F i '' X) = ⊤ := by
  refine grSub_top hF (h.trans (sup_le ?_ (succ_le_grSub hF i _)))
  rw [Subgroup.closure_le]
  intro x hx
  exact (mem_grSub F i _ x).mpr ⟨hX hx, AddSubgroup.subset_closure ⟨x, hx, rfl⟩⟩

/-- A biadditive map sends a pair of closures into the closure of the values on generators. -/
theorem bil_mem_closure {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (B : M →+ N →+ P) {A : Set M} {A' : Set N} {S : AddSubgroup P}
    (h : ∀ a ∈ A, ∀ b ∈ A', B a b ∈ S) {x : M} {y : N}
    (hx : x ∈ AddSubgroup.closure A) (hy : y ∈ AddSubgroup.closure A') : B x y ∈ S := by
  have h1 : ∀ a ∈ A, B a y ∈ S := by
    intro a ha
    have hle : AddSubgroup.closure A' ≤ S.comap (B a) := by
      rw [AddSubgroup.closure_le]
      intro b hb
      exact h a ha b hb
    exact hle hy
  have h2 : AddSubgroup.closure A ≤ S.comap (B.flip y) := by
    rw [AddSubgroup.closure_le]
    intro a ha
    exact h1 a ha
  exact h2 hx

/-- The homogeneous core generators `ḡ_{1,k} = g_{1,k} G_2`, `k < s`. -/
def coreGen (F : ℕ → Subgroup G) (s : ℕ) (u : ℕ → G) : Set (GrL F 0) :=
  {z | ∃ k < s, grOf F 0 (u k) = z}

/-- (33): `C_core = ⟨ḡ_{1,1}, ..., ḡ_{1,s}⟩ ≤ L_1`. -/
def coreC (F : ℕ → Subgroup G) (s : ℕ) (u : ℕ → G) : AddSubgroup (GrL F 0) :=
  AddSubgroup.closure (coreGen F s u)

/-- The brackets `[ḡ_{1,a}, ḡ_{1,b}]_L`, `a, b < s`. -/
def coreBr2 (F : ℕ → Subgroup G) (s : ℕ) (u : ℕ → G) : Set (GrL F 1) :=
  {w | ∃ a < s, ∃ b < s, grBr F 0 0 1 (grOf F 0 (u a)) (grOf F 0 (u b)) = w}

/-- The brackets `[z, ḡ_{1,k}]_L`, `z ∈ L_2`, `k < s`. -/
def coreBr3 (F : ℕ → Subgroup G) (s : ℕ) (u : ℕ → G) : Set (GrL F 2) :=
  {w | ∃ z : GrL F 1, ∃ k < s, grBr F 1 0 2 z (grOf F 0 (u k)) = w}

theorem closure_le_grSub_coreC {s : ℕ} {u : ℕ → G} (hu : ∀ k < s, u k ∈ F 0) :
    Subgroup.closure (u '' Set.Iio s) ≤ grSub F 0 (coreC F s u) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (mem_grSub F 0 _ _).mpr ⟨hu k hk, AddSubgroup.subset_closure ⟨k, hk, rfl⟩⟩

/-- (34), `i = 1`: `L_2 = ⟨[ḡ_{1,a}, ḡ_{1,b}]_L : a, b ≤ s⟩` for a Sims core. -/
theorem core_L2_closure (hF : NSeries F) {s : ℕ} {u : ℕ → G} (hu : ∀ k < s, u k ∈ F 0)
    (hcore : F 1 ≤
      ⁅Subgroup.closure (u '' Set.Iio s), Subgroup.closure (u '' Set.Iio s)⁆ ⊔ F 2) :
    AddSubgroup.closure (coreBr2 F s u) = ⊤ := by
  have hH := closure_le_grSub_coreC (F := F) hu
  have hgen : ∀ a ∈ coreGen F s u, ∀ b ∈ coreGen F s u,
      grBrHom hF 0 0 1 rfl a b ∈ AddSubgroup.closure (coreBr2 F s u) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, b, hb, rfl⟩
  refine grSub_top hF (hcore.trans (sup_le ?_ (succ_le_grSub hF 1 _)))
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  obtain ⟨m1, c1⟩ := (mem_grSub F 0 _ _).mp (hH hg1)
  obtain ⟨m2, c2⟩ := (mem_grSub F 0 _ _).mp (hH hg2)
  refine (mem_grSub F 1 _ _).mpr ⟨hF.comm_mem m1 m2 (by omega), ?_⟩
  rw [← grBr_mk hF (n := 1) rfl m1 m2]
  have key := bil_mem_closure (grBrHom hF 0 0 1 rfl) hgen c1 c2
  rwa [grBrHom_apply] at key

/-- (34), `i = 2`: `L_3 = Σ_{k ≤ s} [L_2, ḡ_{1,k}]_L`, by the Jacobi identity. -/
theorem core_L3_closure (hF : NSeries F) {s : ℕ} {u : ℕ → G} (hu : ∀ k < s, u k ∈ F 0)
    (hcore : F 1 ≤
      ⁅Subgroup.closure (u '' Set.Iio s), Subgroup.closure (u '' Set.Iio s)⁆ ⊔ F 2)
    (h2 : F 2 ≤ ⁅F 1, F 0⁆ ⊔ F 3) :
    AddSubgroup.closure (coreBr3 F s u) = ⊤ := by
  have hL2 := core_L2_closure hF hu hcore
  have hgen : ∀ v ∈ coreBr2 F s u, ∀ w ∈ (Set.univ : Set (GrL F 0)),
      grBrHom hF 1 0 2 rfl v w ∈ AddSubgroup.closure (coreBr3 F s u) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ w -
    rw [grBrHom_apply]
    have hj := grBr_jacobi_one hF (grOf F 0 (u a)) (grOf F 0 (u b)) w
    have e : grBr F 1 0 2 (grBr F 0 0 1 (grOf F 0 (u a)) (grOf F 0 (u b))) w =
        -(grBr F 1 0 2 (grBr F 0 0 1 (grOf F 0 (u b)) w) (grOf F 0 (u a)) +
          grBr F 1 0 2 (grBr F 0 0 1 w (grOf F 0 (u a))) (grOf F 0 (u b))) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]
      exact hj
    rw [e]
    refine AddSubgroup.neg_mem _ (AddSubgroup.add_mem _ ?_ ?_)
    · exact AddSubgroup.subset_closure ⟨_, a, ha, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, b, hb, rfl⟩
  have hall : ∀ v : GrL F 1, ∀ w : GrL F 0,
      grBr F 1 0 2 v w ∈ AddSubgroup.closure (coreBr3 F s u) := by
    intro v w
    have hv : v ∈ AddSubgroup.closure (coreBr2 F s u) := by
      rw [hL2]
      exact AddSubgroup.mem_top v
    have hw : w ∈ AddSubgroup.closure (Set.univ : Set (GrL F 0)) :=
      AddSubgroup.subset_closure (Set.mem_univ w)
    have key := bil_mem_closure (grBrHom hF 1 0 2 rfl) hgen hv hw
    rwa [grBrHom_apply] at key
  refine grSub_top hF (h2.trans (sup_le ?_ (succ_le_grSub hF 2 _)))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine (mem_grSub F 2 _ _).mpr ⟨hF.comm_mem hx hy (by omega), ?_⟩
  rw [← grBr_mk hF (n := 2) rfl hx hy]
  exact hall _ _

theorem grOf_prod_ofFn {i : ℕ} : ∀ (r : ℕ) (f : Fin r → G), (∀ v, f v ∈ F i) →
    grOf F i (List.ofFn f).prod = ∑ v, grOf F i (f v)
  | 0, f, _ => by
    rw [List.ofFn_zero, List.prod_nil, grOf_one, Fin.sum_univ_zero]
  | r + 1, f, hf => by
    have hmem : (List.ofFn fun v : Fin r => f v.succ).prod ∈ F i := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      rw [List.mem_ofFn'] at hx
      obtain ⟨v, rfl⟩ := hx
      exact hf v.succ
    rw [List.ofFn_succ, List.prod_cons, grOf_mul (hf 0) hmem,
      grOf_prod_ofFn r (fun v : Fin r => f v.succ) (fun v => hf v.succ), Fin.sum_univ_succ]

/-- (35)/(39): the class of `(Π_v X_v ^ e_v) d`, `d ∈ F (i + 1)`, is `Σ_v e_v X̄_v`. -/
theorem grOf_block (hF : NSeries F) {i r : ℕ} (X : Fin r → G) (e : Fin r → ℕ)
    (hX : ∀ v, X v ∈ F i) {d : G} (hd : d ∈ F (i + 1)) :
    grOf F i ((List.ofFn fun v => X v ^ e v).prod * d) = ∑ v, e v • grOf F i (X v) := by
  have hb : (List.ofFn fun v => X v ^ e v).prod ∈ F i := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_ofFn'] at hx
    obtain ⟨v, rfl⟩ := hx
    exact Subgroup.pow_mem _ (hX v) _
  rw [grOf_mul hb (hF.succ_le i hd), grOf_of_mem_succ hF hd, add_zero,
    grOf_prod_ofFn r _ (fun v => Subgroup.pow_mem _ (hX v) (e v))]
  exact Finset.sum_congr rfl fun v _ => grOf_pow (hX v) (e v)

/-- (41): if `[g, h] = (Π_v X_v ^ c_v) d` with `X_v ∈ F_{a+b+1}` and `d` deeper, then
`[ḡ, h̄]_L = Σ_v c_v X̄_v`. -/
theorem grBr_block (hF : NSeries F) {a b n r : ℕ} (hn : a + b + 1 = n) {g h : G}
    (hg : g ∈ F a) (hh : h ∈ F b) (X : Fin r → G) (c : Fin r → ℕ) (hX : ∀ v, X v ∈ F n)
    {d : G} (hd : d ∈ F (n + 1)) (hc : ⁅g, h⁆ = (List.ofFn fun v => X v ^ c v).prod * d) :
    grBr F a b n (grOf F a g) (grOf F b h) = ∑ v, c v • grOf F n (X v) := by
  rw [grBr_mk hF hn hg hh, hc, grOf_block hF X c hX hd]

/-- (37): a power relation `g ^ q = (Π_v X_v ^ e_v) d` gives `q ḡ = Σ_v e_v X̄_v` in `L_i`. -/
theorem grOf_power_block (hF : NSeries F) {i r q : ℕ} {g : G} (hg : g ∈ F i) (X : Fin r → G)
    (e : Fin r → ℕ) (hX : ∀ v, X v ∈ F i) {d : G} (hd : d ∈ F (i + 1))
    (hpow : g ^ q = (List.ofFn fun v => X v ^ e v).prod * d) :
    q • grOf F i g = ∑ v, e v • grOf F i (X v) := by
  rw [← grOf_pow hg, hpow, grOf_block hF X e hX hd]

/-- (37) for the power word array of a Sims generating set (`PowerWords.SimsGenSet`):
`p ^ a(i,j) ḡ_{i,j} = Σ_v b(i,j,i,v) ḡ_{i,v}` in the layer `L_i`. -/
theorem SimsGenSet.layer_power {p c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ}
    {g : SimsIdx c r → G} (S : SimsGenSet p a g) (i : Fin c) (j : Fin (r i)) :
    (p ^ a ⟨i, j⟩) • grOf (lcs G) (i : ℕ) (g ⟨i, j⟩) =
      ∑ v : Fin (r i), (S.powerWords ⟨i, j⟩ ⟨i, v⟩).val • grOf (lcs G) (i : ℕ) (g ⟨i, v⟩) :=
  grOf_power_block nseries_lcs (S.mem ⟨i, j⟩) (fun v => g ⟨i, v⟩)
    (fun v => (S.powerWords ⟨i, j⟩ ⟨i, v⟩).val) (fun v => S.mem ⟨i, v⟩)
    (deeper_mem g S.mem (fun h => (S.powerWords ⟨i, j⟩ h).val) i) (S.powerData.pow i j)

end NSer

/-! Breadth (48)-(51), abstractly. -/

section Breadth

variable {C M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- `log_p |im f|`. -/
noncomputable def imLog (p : ℕ) (f : M →+ N) : ℕ := Nat.log p (Nat.card f.range)

/-- (48): `max_{u ∈ S} log_p |im ad(u)|`. -/
noncomputable def breadthOf (p : ℕ) (ad : C → M →+ N) (S : Set C) : ℕ :=
  sSup ((fun u => imLog p (ad u)) '' S)

theorem imLog_le_target [Finite N] (p : ℕ) (f : M →+ N) : imLog p f ≤ Nat.log p (Nat.card N) :=
  Nat.log_mono_right (Nat.card_le_card_of_injective (fun x : f.range => (x : N))
    Subtype.val_injective)

theorem imLog_le_source [Finite M] (p : ℕ) (f : M →+ N) : imLog p f ≤ Nat.log p (Nat.card M) :=
  Nat.log_mono_right (Nat.le_of_dvd Nat.card_pos (AddSubgroup.card_range_dvd f))

theorem breadthOf_bdd [Finite N] (p : ℕ) (ad : C → M →+ N) (S : Set C) :
    BddAbove ((fun u => imLog p (ad u)) '' S) := by
  refine ⟨Nat.log p (Nat.card N), ?_⟩
  rintro _ ⟨u, -, rfl⟩
  exact imLog_le_target p (ad u)

theorem le_breadthOf [Finite N] (p : ℕ) (ad : C → M →+ N) (S : Set C) {u : C} (hu : u ∈ S) :
    imLog p (ad u) ≤ breadthOf p ad S :=
  le_csSup (breadthOf_bdd p ad S) ⟨u, hu, rfl⟩

theorem exists_breadthOf [Finite N] (p : ℕ) (ad : C → M →+ N) {S : Set C} (hS : S.Nonempty) :
    ∃ h ∈ S, imLog p (ad h) = breadthOf p ad S := by
  obtain ⟨h, hh, e⟩ := Nat.sSup_mem (hS.image _) (breadthOf_bdd p ad S)
  exact ⟨h, hh, e⟩

theorem breadthOf_le_target [Finite N] (p : ℕ) (ad : C → M →+ N) {S : Set C}
    (hS : S.Nonempty) : breadthOf p ad S ≤ Nat.log p (Nat.card N) := by
  obtain ⟨h, -, e⟩ := exists_breadthOf p ad hS
  rw [← e]
  exact imLog_le_target p (ad h)

theorem breadthOf_le_source [Finite M] [Finite N] (p : ℕ) (ad : C → M →+ N) {S : Set C}
    (hS : S.Nonempty) : breadthOf p ad S ≤ Nat.log p (Nat.card M) := by
  obtain ⟨h, -, e⟩ := exists_breadthOf p ad hS
  rw [← e]
  exact imLog_le_source p (ad h)

/-- (49): `|ker f| = p ^ (s - log_p |im f|)` when `|M| = p ^ s`. -/
theorem card_ker_eq [Finite M] {p : ℕ} (hp : p.Prime) {sM : ℕ} (hM : Nat.card M = p ^ sM)
    (f : M →+ N) : Nat.card f.ker = p ^ (sM - imLog p f) ∧
      Nat.card f.range = p ^ imLog p f ∧ imLog p f ≤ sM := by
  have hd : Nat.card f.range ∣ p ^ sM := by
    rw [← hM]
    exact AddSubgroup.card_range_dvd f
  obtain ⟨j, hj, hcard⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hlog : imLog p f = j := by rw [imLog, hcard, Nat.log_pow hp.one_lt]
  have h1 := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, hcard, hM] at h1
  rw [hlog]
  refine ⟨?_, hcard, hj⟩
  have h2 : p ^ sM = p ^ (sM - j) * p ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos j) h1

/-- The join of the first `n` members of a family of subgroups. -/
def supUpTo (H : ℕ → AddSubgroup N) : ℕ → AddSubgroup N
  | 0 => ⊥
  | n + 1 => supUpTo H n ⊔ H n

theorem le_supUpTo (H : ℕ → AddSubgroup N) {k : ℕ} : ∀ n, k < n → H k ≤ supUpTo H n
  | 0, h => absurd h (Nat.not_lt_zero k)
  | n + 1, h => by
    show H k ≤ supUpTo H n ⊔ H n
    by_cases h' : k < n
    · exact (le_supUpTo H n h').trans le_sup_left
    · have hk : k = n := by omega
      rw [hk]
      exact le_sup_right

theorem card_sup_le [Finite N] (A B : AddSubgroup N) :
    Nat.card (A ⊔ B : AddSubgroup N) ≤ Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun ab : A × B => (⟨(ab.1 : N) + ab.2, AddSubgroup.add_mem_sup ab.1.2 ab.2.2⟩ :
      (A ⊔ B : AddSubgroup N))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

theorem card_supUpTo_le [Finite N] (H : ℕ → AddSubgroup N) :
    ∀ n, Nat.card (supUpTo H n) ≤ ∏ k ∈ Finset.range n, Nat.card (H k)
  | 0 => by
    show Nat.card (⊥ : AddSubgroup N) ≤ ∏ k ∈ Finset.range 0, Nat.card (H k)
    simp
  | n + 1 => by
    show Nat.card (supUpTo H n ⊔ H n : AddSubgroup N) ≤ _
    rw [Finset.prod_range_succ]
    exact (card_sup_le _ _).trans (Nat.mul_le_mul_right _ (card_supUpTo_le H n))

/-- The addition map `Π_k H_k → N` is onto when the `H_k` generate. -/
theorem card_le_prod_of_closure [Finite N] {s : ℕ} (H : ℕ → AddSubgroup N)
    (hgen : AddSubgroup.closure {y | ∃ k < s, y ∈ H k} = ⊤) :
    Nat.card N ≤ ∏ k ∈ Finset.range s, Nat.card (H k) := by
  have hle : AddSubgroup.closure {y | ∃ k < s, y ∈ H k} ≤ supUpTo H s := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨k, hk, hy⟩
    exact le_supUpTo H s hk hy
  rw [hgen, top_le_iff] at hle
  rw [← AddSubgroup.card_top (G := N), ← hle]
  exact card_supUpTo_le H s

/-- (51): if `N = Σ_{k < s} im ad(u_k)` with `u_k ∈ S`, then `log_p |N| ≤ s · breadth`. -/
theorem log_le_mul_breadthOf [Finite N] {p : ℕ} (hp : p.Prime) {sN : ℕ}
    (hN : Nat.card N = p ^ sN) (ad : C → M →+ N) (S : Set C) {s : ℕ} (u : ℕ → C)
    (hu : ∀ k < s, u k ∈ S) (hgen : AddSubgroup.closure {y | ∃ k < s, y ∈ (ad (u k)).range} = ⊤) :
    sN ≤ s * breadthOf p ad S := by
  have h1 : Nat.card N ≤ ∏ k ∈ Finset.range s, Nat.card (ad (u k)).range :=
    card_le_prod_of_closure (fun k => (ad (u k)).range) hgen
  have h2 : ∀ k ∈ Finset.range s, Nat.card (ad (u k)).range ≤ p ^ breadthOf p ad S := by
    intro k hk
    have hd : Nat.card (ad (u k)).range ∣ p ^ sN := by
      rw [← hN]
      exact AddSubgroup.card_subgroup_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hl : imLog p (ad (u k)) = j := by rw [imLog, hj, Nat.log_pow hp.one_lt]
    rw [hj]
    refine Nat.pow_le_pow_right hp.pos ?_
    rw [← hl]
    exact le_breadthOf p ad S (hu k (Finset.mem_range.mp hk))
  have h3 := h1.trans (Finset.prod_le_prod' h2)
  rw [Finset.prod_const, Finset.card_range, ← pow_mul, hN, mul_comm] at h3
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3

end Breadth

/-! Breadth of the core bracket maps of an N-series. -/

section GrBreadth

variable {G : Type u} [Group G] {F : ℕ → Subgroup G}

/-- `ad(u) : L_i → L_{i+1}`, `z ↦ [z, u]_L`, for `u ∈ L_1`. -/
noncomputable def adHom (hF : NSeries F) (i : ℕ) (u : GrL F 0) : GrL F i →+ GrL F (i + 1) :=
  AddMonoidHom.mk' (fun z => grBr F i 0 (i + 1) z u)
    (fun z z' => grBr_add_left hF (by omega) z z' u)

theorem adHom_apply (hF : NSeries F) (i : ℕ) (u : GrL F 0) (z : GrL F i) :
    adHom hF i u z = grBr F i 0 (i + 1) z u := rfl

/-- (48): `b = max_{u ∈ C} log_p |[L_i, u]_L|`. -/
noncomputable def grBreadth (p : ℕ) (hF : NSeries F) (i : ℕ) (C : AddSubgroup (GrL F 0)) : ℕ :=
  breadthOf p (adHom hF i) (C : Set (GrL F 0))

/-- (48)-(49) and `0 ≤ b ≤ min(s_i, s_{i+1})`. -/
theorem grBreadth_spec [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (hF : NSeries F) (i : ℕ) (C : AddSubgroup (GrL F 0)) :
    (∃ h ∈ C, imLog p (adHom hF i h) = grBreadth p hF i C ∧
        Nat.card (adHom hF i h).ker = p ^ (layerLog p F i - grBreadth p hF i C)) ∧
      (∀ x ∈ C, imLog p (adHom hF i x) ≤ grBreadth p hF i C) ∧
      grBreadth p hF i C ≤ layerLog p F i ∧ grBreadth p hF i C ≤ layerLog p F (i + 1) := by
  have hne : (C : Set (GrL F 0)).Nonempty := ⟨0, C.zero_mem⟩
  obtain ⟨h, hh, e⟩ := exists_breadthOf p (adHom hF i) hne
  refine ⟨⟨h, hh, e, ?_⟩, fun x hx => le_breadthOf p (adHom hF i) _ hx, ?_, ?_⟩
  · rw [← e]
    exact (card_ker_eq hp (card_grL_pow hp hG hF i) (adHom hF i h)).1
  · have h1 := breadthOf_le_source p (adHom hF i) hne
    rw [card_grL_pow hp hG hF i, Nat.log_pow hp.one_lt] at h1
    exact h1
  · have h1 := breadthOf_le_target p (adHom hF i) hne
    rw [card_grL_pow hp hG hF (i + 1), Nat.log_pow hp.one_lt] at h1
    exact h1

/-- (51): if `L_{i+1} = Σ_{k < s} [L_i, ḡ_{1,k}]_L` with the `ḡ_{1,k}` in `C`, then
`s_{i+1} ≤ s b_i`. -/
theorem layerLog_le_mul_grBreadth [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (hF : NSeries F) (i : ℕ) (C : AddSubgroup (GrL F 0)) {s : ℕ} (u : ℕ → G)
    (hu : ∀ k < s, grOf F 0 (u k) ∈ C)
    (hgen : AddSubgroup.closure
      {w | ∃ z : GrL F i, ∃ k < s, grBr F i 0 (i + 1) z (grOf F 0 (u k)) = w} = ⊤) :
    layerLog p F (i + 1) ≤ s * grBreadth p hF i C := by
  refine log_le_mul_breadthOf hp (card_grL_pow hp hG hF (i + 1)) (adHom hF i)
    (C : Set (GrL F 0)) (fun k => grOf F 0 (u k)) hu ?_
  rw [eq_top_iff, ← hgen]
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨z, k, hk, rfl⟩
  exact ⟨k, hk, AddMonoidHom.mem_range.mpr ⟨z, rfl⟩⟩

/-! Class 3: the breadth `b_2` of the core bracket map `L_2 × C_core → L_3`. -/

/-- The paper's `b_2` for the lower central series and the core `g_{1,1}, ..., g_{1,s}`. -/
noncomputable def breadthTwo (p : ℕ) (G : Type u) [Group G] (s : ℕ) (u : ℕ → G) : ℕ :=
  grBreadth p (nseries_lcs (G := G)) 1 (coreC (lcs G) s u)

theorem lcs_two_le_comm : lcs G 2 ≤ ⁅lcs G 1, lcs G 0⁆ ⊔ lcs G 3 := by
  show ⁅lcs G 1, ⊤⁆ ≤ ⁅lcs G 1, lcs G 0⁆ ⊔ lcs G 3
  rw [lcs_zero]
  exact le_sup_left

/-- Class 3 breadth bounds: for a finite p-group with `γ_4 = 1`, `|γ_2| = p ^ m_2`,
`|γ_3| = p ^ m_3` and a Sims core `g_{1,1}, ..., g_{1,s}` (`γ_2 = [H, H] γ_3`):
`m_3 ≤ s b_2`, `b_2 ≤ m_3`, `b_2 ≤ m_2 - m_3`, and a maximiser `h*` with
`|ker ad(h*)| = p ^ (m_2 - m_3 - b_2)` ((48)-(51) at `c = 3`). -/
theorem breadth_two_class3 [Finite G] {p m m2 m3 s : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (h2 : Nat.card (lcs G 1) = p ^ m2) (h3 : Nat.card (lcs G 2) = p ^ m3) (h4 : lcs G 3 = ⊥)
    {u : ℕ → G}
    (hcore : lcs G 1 = ⁅Subgroup.closure (u '' Set.Iio s), Subgroup.closure (u '' Set.Iio s)⁆ ⊔
      lcs G 2) :
    m3 ≤ s * breadthTwo p G s u ∧ breadthTwo p G s u ≤ m3 ∧ breadthTwo p G s u ≤ m2 - m3 ∧
      ∃ h ∈ coreC (lcs G) s u, imLog p (adHom nseries_lcs 1 h) = breadthTwo p G s u ∧
        Nat.card (adHom nseries_lcs 1 h).ker = p ^ (m2 - m3 - breadthTwo p G s u) := by
  have hu : ∀ k < s, u k ∈ lcs G 0 := fun k _ => mem_lcs_zero (u k)
  have hL3 : layerLog p (lcs G) 2 = m3 := by
    rw [layerLog, card_grL_of_bot nseries_lcs (i := 2) h4, h3, Nat.log_pow hp.one_lt]
  have hL2 : layerLog p (lcs G) 1 = m2 - m3 := by
    have e := card_grL_mul (nseries_lcs (G := G)) 1
    rw [card_grL_pow hp hG nseries_lcs 1, h2] at e
    rw [show (1 + 1 : ℕ) = 2 from rfl, h3, ← pow_add] at e
    have e' := Nat.pow_right_injective hp.two_le e
    omega
  obtain ⟨⟨h, hh, e1, e2⟩, -, hb1, hb2'⟩ :=
    grBreadth_spec hp hG (nseries_lcs (G := G)) 1 (coreC (lcs G) s u)
  have hb2 : breadthTwo p G s u ≤ layerLog p (lcs G) 2 := hb2'
  have h51 : layerLog p (lcs G) 2 ≤ s * breadthTwo p G s u := layerLog_le_mul_grBreadth hp hG (nseries_lcs (G := G)) 1 (coreC (lcs G) s u) u
    (fun k hk => AddSubgroup.subset_closure ⟨k, hk, rfl⟩)
    (core_L3_closure nseries_lcs hu hcore.le lcs_two_le_comm)
  rw [hL3] at h51 hb2
  rw [hL2] at hb1 e2
  exact ⟨h51, hb2, hb1, h, hh, e1, e2⟩

end GrBreadth

end OMA.SimsLite

#print axioms OMA.SimsLite.grBr_jacobi
#print axioms OMA.SimsLite.remark_2_6
#print axioms OMA.SimsLite.core_L3_closure
#print axioms OMA.SimsLite.SimsGenSet.layer_power
#print axioms OMA.SimsLite.breadth_two_class3
