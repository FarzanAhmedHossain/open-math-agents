import H2Dev.Burnside
import H2Dev.CoreFlag

/-! INF-3: the concrete frame of Li-Qiao (pp.12-13, eqs (16)-(20)).

For a group `G` and a natural number `p`:
* `VQ p G = G^ab ⧸ (pPhi p G)^ab (G^ab)^p`, with `piV : G →* VQ p G` of kernel `pPhi p G`
  (`ker_piV`); for a finite p-group this is `V = G ⧸ Φ(G)` (`vEquiv`, `frattini_eq_pPhi`);
* `WQ p G = γ_2^ab ⧸ (γ_3 γ_2^p)^ab (γ_2^ab)^p`, with `piW : γ_2 →* WQ p G` of kernel
  `pN p G ∩ γ_2 = γ_3 γ_2^p` (`ker_piW`); this is `W = G_2 ⧸ G_3 Φ(G_2)`.
Both are commutative of exponent `p`, hence `ZMod p`-modules (as `Additive _`).
* `finrank_V` : `dim V = Group.rank G = r_1`;  `card_W` : `|W| = p ^ r2 p G`, `r2 = dim W`;
* `lamV` : the commutator form `β_G : V × V → W` (`lamV_mk` : `β_G(xΦ, yΦ) = [x, y] G_3 Φ(G_2)`),
  biadditive, alternating, with values generating `W` (`lamV_closure`); `lamLin` is the same map
  as a `ZMod p`-bilinear map, with `lamLin_span`;
* `frame_hN3` ... `frame_hMN` : the hypotheses of `core_flag` for `N = pN p G`, `M = frattini G`;
  `frame_core_flag` and `frame_core_bounds` (`s - 1 ≤ r_2`, `s ≤ r_1`);
* `s1 p G = log_p |G : γ_2|` and `lambdaPar p G = s1 - r1` with `|G : γ_2| = p ^ (r1 + λ)`
  (`index_lcs_one_eq`) and `0 ≤ λ` as an integer (`lambdaPar_nonneg`). -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section ElemQ

variable {p : ℕ} {H : Type u} [Group H]

/-- The subgroup `K^ab (H^ab)^p` of the abelianization. -/
abbrev elemK (p : ℕ) (H : Type u) [Group H] (K : Subgroup H) : Subgroup (Abelianization H) :=
  K.map Abelianization.of ⊔ (powMonoidHom p : Abelianization H →* Abelianization H).range

/-- The elementary abelian quotient `H^ab ⧸ K^ab (H^ab)^p`. -/
abbrev ElemQ (p : ℕ) (H : Type u) [Group H] (K : Subgroup H) : Type u :=
  Abelianization H ⧸ elemK p H K

/-- The projection `H → H^ab ⧸ K^ab (H^ab)^p`. -/
def elemPi (p : ℕ) (H : Type u) [Group H] (K : Subgroup H) : H →* ElemQ p H K :=
  (QuotientGroup.mk' (elemK p H K)).comp Abelianization.of

lemma elemPi_surjective (K : Subgroup H) : Function.Surjective (elemPi p H K) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (a : H ⧸ commutator H)
  refine ⟨g, ?_⟩
  rw [← hg]
  rfl

lemma elemQ_pow (K : Subgroup H) (x : ElemQ p H K) : x ^ p = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨a, rfl⟩)

lemma elemQ_mul_comm (K : Subgroup H) (x y : ElemQ p H K) : x * y = y * x := mul_comm x y

/-- If `K` contains `[H, H]` and all `p`-th powers, the kernel of `elemPi` is `K`. -/
lemma ker_elemPi {K : Subgroup H} (h1 : commutator H ≤ K) (h2 : ∀ g : H, g ^ p ∈ K) :
    (elemPi p H K).ker = K := by
  have hle : (powMonoidHom p : Abelianization H →* Abelianization H).range ≤
      K.map Abelianization.of := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (a : H ⧸ commutator H)
    refine Subgroup.mem_map.mpr ⟨g ^ p, h2 g, ?_⟩
    rw [map_pow]
    rw [← hg]
    rfl
  have hK : elemK p H K = K.map Abelianization.of := sup_eq_left.mpr hle
  rw [elemPi, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hK, Subgroup.comap_map_eq,
    Abelianization.ker_of, sup_eq_left.mpr h1]

lemma card_elemQ {K : Subgroup H} (h1 : commutator H ≤ K) (h2 : ∀ g : H, g ^ p ∈ K) :
    Nat.card (ElemQ p H K) = K.index := by
  have e := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (elemPi p H K) (elemPi_surjective K)).toEquiv
  rw [ker_elemPi h1 h2] at e
  exact e.symm

variable [hp : Fact p.Prime]

lemma elemQ_nsmul (K : Subgroup H) (x : Additive (ElemQ p H K)) : p • x = 0 := by
  show Additive.ofMul (Additive.toMul x ^ p) = Additive.ofMul 1
  rw [elemQ_pow]

/-- `ElemQ p H K` is an `F_p`-vector space. -/
instance elemQ_module (K : Subgroup H) : Module (ZMod p) (Additive (ElemQ p H K)) :=
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  AddCommGroup.zmodModule (elemQ_nsmul K)

lemma elemQ_smul_eq_nsmul (K : Subgroup H) (c : ZMod p) (x : Additive (ElemQ p H K)) :
    c • x = c.val • x := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  exact Nat.cast_smul_eq_nsmul (ZMod p) c.val x

lemma card_eq_pow_finrank_elemQ [Finite H] (K : Subgroup H) :
    Nat.card (ElemQ p H K) = p ^ Module.finrank (ZMod p) (Additive (ElemQ p H K)) := by
  have : Finite (ElemQ p H K) := Finite.of_surjective _ (elemPi_surjective K)
  have : Finite (Additive (ElemQ p H K)) := inferInstance
  have : Module.Free (ZMod p) (Additive (ElemQ p H K)) :=
    Module.Free.of_divisionRing (ZMod p) (Additive (ElemQ p H K))
  have : Module.Finite (ZMod p) (Additive (ElemQ p H K)) := inferInstance
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (ElemQ p H K))
  rw [Nat.card_zmod] at h
  exact h

end ElemQ

section Frame0

variable (p : ℕ) (G : Type u) [Group G]

/-- `V = G ⧸ G^p γ_2` (the Frattini quotient of a finite p-group). -/
abbrev VQ : Type u := ElemQ p G (pPhi p G)

/-- `W = γ_2 ⧸ γ_3 γ_2^p`. -/
abbrev WQ : Type u := ElemQ p (lcs G 1) ((pN p G).subgroupOf (lcs G 1))

/-- The projection `G → V`. -/
def piV : G →* VQ p G := elemPi p G (pPhi p G)

/-- The projection `γ_2 → W`. -/
def piW : lcs G 1 →* WQ p G := elemPi p (lcs G 1) ((pN p G).subgroupOf (lcs G 1))

/-- The commutator `⁅g, h⁆` as an element of `γ_2`. -/
def cw {G : Type u} [Group G] (g h : G) : lcs G 1 := ⟨⁅g, h⁆, commElem_mem_lcs_one g h⟩

variable {p G}

lemma piV_surjective : Function.Surjective (piV p G) := elemPi_surjective _

lemma piW_surjective : Function.Surjective (piW p G) := elemPi_surjective _

lemma commutator_le_pPhi : commutator G ≤ pPhi p G := le_sup_right

lemma commutator_lcs_one_le :
    commutator (lcs G 1) ≤ (pN p G).subgroupOf (lcs G 1) := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_subgroupOf]
  show ⁅(a : G), (b : G)⁆ ∈ pN p G
  exact lcs_two_le_pN p (commElem_mem_lcs_succ (n := 1) a.2 (b : G))

lemma pow_mem_pN_subgroupOf (g : lcs G 1) : g ^ p ∈ (pN p G).subgroupOf (lcs G 1) := by
  rw [Subgroup.mem_subgroupOf]
  have e : ((g ^ p : lcs G 1) : G) = (g : G) ^ p := map_pow (lcs G 1).subtype g p
  rw [e]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨g, rfl⟩)

/-- The kernel of `G → V` is `G^p γ_2`. -/
theorem ker_piV : (piV p G).ker = pPhi p G :=
  ker_elemPi commutator_le_pPhi (pow_mem_pPhi p)

/-- The kernel of `γ_2 → W` is `γ_3 γ_2^p`. -/
theorem ker_piW : (piW p G).ker = (pN p G).subgroupOf (lcs G 1) :=
  ker_elemPi commutator_lcs_one_le pow_mem_pN_subgroupOf

lemma piV_eq_iff {g g' : G} : piV p G g = piV p G g' ↔ g * g'⁻¹ ∈ pPhi p G := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, ker_piV]

lemma piW_eq_of {a b : lcs G 1} (h : (a : G) * (b : G)⁻¹ ∈ pN p G) :
    piW p G a = piW p G b := by
  have hk : a * b⁻¹ ∈ (piW p G).ker := by
    rw [ker_piW, Subgroup.mem_subgroupOf]
    exact h
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
  exact hk

lemma piW_eq_one_of {a : lcs G 1} (h : (a : G) ∈ pN p G) : piW p G a = 1 := by
  rw [← MonoidHom.mem_ker, ker_piW, Subgroup.mem_subgroupOf]
  exact h

theorem V_pow_p (v : VQ p G) : v ^ p = 1 := elemQ_pow _ v

theorem W_pow_p (w : WQ p G) : w ^ p = 1 := elemQ_pow _ w

theorem V_mul_comm (v v' : VQ p G) : v * v' = v' * v := mul_comm v v'

theorem W_mul_comm (w w' : WQ p G) : w * w' = w' * w := mul_comm w w'

theorem card_V_eq_index : Nat.card (VQ p G) = (pPhi p G).index :=
  card_elemQ commutator_le_pPhi (pow_mem_pPhi p)

theorem card_W_eq_relindex : Nat.card (WQ p G) = ((pN p G).subgroupOf (lcs G 1)).index :=
  card_elemQ commutator_lcs_one_le pow_mem_pN_subgroupOf

/-! The commutator form `β_G : V × V → W`. -/

/-- A chosen lift `V → G`. -/
noncomputable def liftV (v : VQ p G) : G := Function.surjInv piV_surjective v

lemma piV_liftV (v : VQ p G) : piV p G (liftV v) = v := Function.surjInv_eq piV_surjective v

/-- `β_G(v, w) = [lift v, lift w] G_3 Φ(G_2)`. -/
noncomputable def lamV (v w : VQ p G) : WQ p G := piW p G (cw (liftV v) (liftV w))

/-- Eq. (19): `β_G(xΦ(G), yΦ(G)) = [x, y] G_3 Φ(G_2)`. -/
theorem lamV_mk (g h : G) : lamV (piV p G g) (piV p G h) = piW p G (cw g h) := by
  show piW p G (cw (liftV (piV p G g)) (liftV (piV p G h))) = piW p G (cw g h)
  apply piW_eq_of
  have hg : liftV (piV p G g) * g⁻¹ ∈ pPhi p G := piV_eq_iff.mp (piV_liftV _)
  have hh : liftV (piV p G h) * h⁻¹ ∈ pPhi p G := piV_eq_iff.mp (piV_liftV _)
  have e1 := commForm_wd_left p g (liftV (piV p G g)) (liftV (piV p G h)) hg
  have e2 := commForm_wd_right p g h (liftV (piV p G h)) hh
  have e3 := Subgroup.mul_mem _ e1 e2
  rw [mul_assoc, inv_mul_cancel_left] at e3
  exact e3

theorem lamV_mul_left (v v' w : VQ p G) : lamV (v * v') w = lamV v w * lamV v' w := by
  obtain ⟨g, rfl⟩ := piV_surjective v
  obtain ⟨g', rfl⟩ := piV_surjective v'
  obtain ⟨h, rfl⟩ := piV_surjective w
  have e : piV p G g * piV p G g' = piV p G (g * g') := (map_mul _ _ _).symm
  rw [e, lamV_mk, lamV_mk, lamV_mk, ← map_mul]
  apply piW_eq_of
  exact commForm_add_left p g g' h

theorem lamV_mul_right (v w w' : VQ p G) : lamV v (w * w') = lamV v w * lamV v w' := by
  obtain ⟨g, rfl⟩ := piV_surjective v
  obtain ⟨h, rfl⟩ := piV_surjective w
  obtain ⟨h', rfl⟩ := piV_surjective w'
  have e : piV p G h * piV p G h' = piV p G (h * h') := (map_mul _ _ _).symm
  rw [e, lamV_mk, lamV_mk, lamV_mk, ← map_mul]
  apply piW_eq_of
  exact commForm_add_right p g h h'

theorem lamV_self (v : VQ p G) : lamV v v = 1 := by
  obtain ⟨g, rfl⟩ := piV_surjective v
  have e : cw g g = 1 := Subtype.ext (commutatorElement_self g)
  rw [lamV_mk, e, map_one]

theorem lamV_swap (v w : VQ p G) : lamV v w * lamV w v = 1 := by
  obtain ⟨g, rfl⟩ := piV_surjective v
  obtain ⟨h, rfl⟩ := piV_surjective w
  have e : cw g h * cw h g = 1 := Subtype.ext (commForm_alt g h).2
  rw [lamV_mk, lamV_mk, ← map_mul, e, map_one]

/-- The values of `β_G` generate `W`. -/
theorem lamV_closure :
    Subgroup.closure (Set.range (fun vw : VQ p G × VQ p G => lamV vw.1 vw.2)) = ⊤ := by
  have h1 : Subgroup.closure (Set.range (fun xy : G × G => ⁅xy.1, xy.2⁆)) ≤
      ((Subgroup.closure (Set.range (fun vw : VQ p G × VQ p G => lamV vw.1 vw.2))).comap
        (piW p G)).map (lcs G 1).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨cw x y, ?_, rfl⟩
    rw [Subgroup.mem_comap, ← lamV_mk]
    exact Subgroup.subset_closure ⟨(piV p G x, piV p G y), rfl⟩
  have h2 : pN p G ≤
      ((Subgroup.closure (Set.range (fun vw : VQ p G × VQ p G => lamV vw.1 vw.2))).comap
        (piW p G)).map (lcs G 1).subtype := by
    intro n hn
    refine Subgroup.mem_map.mpr ⟨⟨n, pN_le_lcs_one p hn⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, piW_eq_one_of (a := ⟨n, pN_le_lcs_one p hn⟩) hn]
    exact Subgroup.one_mem _
  have h3 := (commForm_span (G := G) p).trans (sup_le h1 h2)
  rw [eq_top_iff]
  intro w _
  obtain ⟨a, rfl⟩ := piW_surjective w
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (h3 a.2)
  have e : b = a := Subtype.ext hba
  rw [← e]
  exact hb

section Lin

variable [hp : Fact p.Prime]

/-- `β_G` on the additive types. -/
noncomputable def lamAdd (v w : Additive (VQ p G)) : Additive (WQ p G) :=
  Additive.ofMul (lamV (Additive.toMul v) (Additive.toMul w))

lemma lamAdd_add_left (v v' w : Additive (VQ p G)) :
    lamAdd (v + v') w = lamAdd v w + lamAdd v' w := by
  show Additive.ofMul (lamV (Additive.toMul v * Additive.toMul v') (Additive.toMul w)) =
    Additive.ofMul (lamV (Additive.toMul v) (Additive.toMul w) *
      lamV (Additive.toMul v') (Additive.toMul w))
  rw [lamV_mul_left]

lemma lamAdd_add_right (v w w' : Additive (VQ p G)) :
    lamAdd v (w + w') = lamAdd v w + lamAdd v w' := by
  show Additive.ofMul (lamV (Additive.toMul v) (Additive.toMul w * Additive.toMul w')) =
    Additive.ofMul (lamV (Additive.toMul v) (Additive.toMul w) *
      lamV (Additive.toMul v) (Additive.toMul w'))
  rw [lamV_mul_right]

lemma lamAdd_smul_left (c : ZMod p) (v w : Additive (VQ p G)) :
    lamAdd (c • v) w = c • lamAdd v w := by
  rw [elemQ_smul_eq_nsmul, elemQ_smul_eq_nsmul]
  exact map_nsmul (AddMonoidHom.mk' (fun v => lamAdd v w) (fun a b => lamAdd_add_left a b w))
    c.val v

lemma lamAdd_smul_right (c : ZMod p) (v w : Additive (VQ p G)) :
    lamAdd v (c • w) = c • lamAdd v w := by
  rw [elemQ_smul_eq_nsmul, elemQ_smul_eq_nsmul]
  exact map_nsmul (AddMonoidHom.mk' (fun w => lamAdd v w) (fun a b => lamAdd_add_right v a b))
    c.val w

/-- `β_G : V × V → W` as an `F_p`-bilinear map. -/
noncomputable def lamLin :
    Additive (VQ p G) →ₗ[ZMod p] Additive (VQ p G) →ₗ[ZMod p] Additive (WQ p G) :=
  LinearMap.mk₂ (ZMod p) lamAdd lamAdd_add_left lamAdd_smul_left lamAdd_add_right
    lamAdd_smul_right

theorem lamLin_apply (v w : Additive (VQ p G)) :
    lamLin v w = Additive.ofMul (lamV (Additive.toMul v) (Additive.toMul w)) := rfl

theorem lamLin_mk (g h : G) :
    lamLin (Additive.ofMul (piV p G g)) (Additive.ofMul (piV p G h)) =
      Additive.ofMul (piW p G (cw g h)) := by
  rw [lamLin_apply]
  exact congrArg Additive.ofMul (lamV_mk g h)

theorem lamLin_self (v : Additive (VQ p G)) : lamLin v v = 0 := by
  rw [lamLin_apply, lamV_self]
  rfl

theorem lamLin_swap (v w : Additive (VQ p G)) : lamLin v w = - lamLin w v := by
  rw [eq_neg_iff_add_eq_zero, lamLin_apply, lamLin_apply]
  show Additive.ofMul (lamV (Additive.toMul v) (Additive.toMul w) *
    lamV (Additive.toMul w) (Additive.toMul v)) = Additive.ofMul 1
  rw [lamV_swap]

/-- The values of `β_G` span `W`. -/
theorem lamLin_span :
    Submodule.span (ZMod p)
      (Set.range (fun vw : Additive (VQ p G) × Additive (VQ p G) => lamLin vw.1 vw.2)) = ⊤ := by
  let T : Submodule (ZMod p) (Additive (WQ p G)) := Submodule.span (ZMod p)
    (Set.range (fun vw : Additive (VQ p G) × Additive (VQ p G) => lamLin vw.1 vw.2))
  let K : Subgroup (WQ p G) :=
    { carrier := {w | Additive.ofMul w ∈ T}
      mul_mem' := fun {a b} ha hb => by
        have ha' : Additive.ofMul a ∈ T := ha
        have hb' : Additive.ofMul b ∈ T := hb
        exact Submodule.add_mem T ha' hb'
      one_mem' := by
        have h0 : (0 : Additive (WQ p G)) ∈ T := Submodule.zero_mem T
        exact h0
      inv_mem' := fun {a} ha => by
        have ha' : Additive.ofMul a ∈ T := ha
        have h1 : - Additive.ofMul a ∈ T := Submodule.neg_mem T ha'
        exact h1 }
  have hle : Subgroup.closure (Set.range (fun vw : VQ p G × VQ p G => lamV vw.1 vw.2)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨v, w⟩, rfl⟩
    show Additive.ofMul (lamV v w) ∈ Submodule.span (ZMod p)
      (Set.range (fun vw : Additive (VQ p G) × Additive (VQ p G) => lamLin vw.1 vw.2))
    exact Submodule.subset_span ⟨(Additive.ofMul v, Additive.ofMul w), rfl⟩
  rw [eq_top_iff]
  intro x _
  have hx : Additive.toMul x ∈ K := hle (by rw [lamV_closure]; exact Subgroup.mem_top _)
  exact hx

/-- `r_2 = dim W`. -/
noncomputable def r2 (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] : ℕ :=
  Module.finrank (ZMod p) (Additive (WQ p G))

end Lin

end Frame0

section Frame

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [Finite G]

lemma pow_le_pow_cancel {a b : ℕ} (hp2 : 2 ≤ p) (h : p ^ a ≤ p ^ b) : a ≤ b := by
  by_contra hc
  push_neg at hc
  have h1 : p ^ (b + 1) ≤ p ^ a := Nat.pow_le_pow_right (by omega) hc
  have h2 : 0 < p ^ b := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  rw [pow_succ] at h1
  nlinarith

lemma le_of_mul_le_mul_pos {a b c : ℕ} (ha : 0 < a) (h : a * b ≤ a * c) : b ≤ c := by
  by_contra hc
  push_neg at hc
  nlinarith

/-- `V = G ⧸ Φ(G)` for a finite p-group. -/
noncomputable def vEquiv (hG : IsPGroup p G) : G ⧸ frattini G ≃* VQ p G :=
  (QuotientGroup.quotientMulEquivOfEq ((frattini_eq_pPhi hG).trans ker_piV.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (piV p G) piV_surjective)

theorem ker_piV_eq_frattini (hG : IsPGroup p G) : (piV p G).ker = frattini G :=
  ker_piV.trans (frattini_eq_pPhi hG).symm

/-- `|V| = p ^ r_1`. -/
theorem card_V (hG : IsPGroup p G) : Nat.card (VQ p G) = p ^ Group.rank G := by
  rw [card_V_eq_index]
  exact card_quot_pPhi hG

/-- `dim V = r_1 = rank G`. -/
theorem finrank_V (hG : IsPGroup p G) :
    Module.finrank (ZMod p) (Additive (VQ p G)) = Group.rank G := by
  have h1 := card_eq_pow_finrank_elemQ (p := p) (pPhi p G)
  rw [card_V hG] at h1
  exact (Nat.pow_right_injective hp.out.two_le h1).symm

/-- `|W| = p ^ r_2`. -/
theorem card_W : Nat.card (WQ p G) = p ^ r2 p G :=
  card_eq_pow_finrank_elemQ _

/-- `|γ_2| = |γ_3 γ_2^p| p ^ r_2`. -/
theorem card_lcs_one_eq : Nat.card (lcs G 1) = Nat.card (pN p G) * p ^ r2 p G := by
  have h1 := Subgroup.card_mul_index ((pN p G).subgroupOf (lcs G 1))
  have h2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pN_le_lcs_one (G := G) p)).toEquiv
  have h3 : ((pN p G).subgroupOf (lcs G 1)).index = p ^ r2 p G := by
    rw [← card_W (p := p) (G := G)]
    exact card_W_eq_relindex.symm
  rw [h3, h2] at h1
  exact h1.symm

/-! The hypotheses of `core_flag` for `N = γ_3 γ_2^p` and `M = Φ(G)`. -/

theorem frame_hN3 : lcs G 2 ≤ pN p G := lcs_two_le_pN p

theorem frame_hN2 : pN p G ≤ lcs G 1 := pN_le_lcs_one p

theorem frame_hM2 (hG : IsPGroup p G) : lcs G 1 ≤ frattini G := by
  rw [frattini_eq_pPhi hG, ← commutator_eq_lcs_one (G := G)]
  exact le_sup_right

theorem frame_hMp (hG : IsPGroup p G) (g : G) : g ^ p ∈ frattini G := by
  rw [frattini_eq_pPhi hG]
  exact pow_mem_pPhi p g

theorem frame_hMN (hG : IsPGroup p G) (g m : G) (hm : m ∈ frattini G) : ⁅g, m⁆ ∈ pN p G := by
  rw [frattini_eq_pPhi hG] at hm
  exact commElem_mem_symm (commElem_pPhi_mem p hm g)

/-- BNV Prop 5.2 for the concrete frame `N = γ_3 γ_2^p`, `M = Φ(G)`. -/
theorem frame_core_flag {n : ℕ} (hG : Nat.card G = p ^ n) (s : ℕ) (x : ℕ → G)
    (hcore : lcs G 1 ≤
      ⁅Subgroup.closure (x '' Set.Iio s), Subgroup.closure (x '' Set.Iio s)⁆ ⊔ pN p G)
    (hmin : ∀ t < s, ∀ v : ℕ → G, (∀ i < t, v i ∈ Subgroup.closure (x '' Set.Iio s)) →
      ¬ lcs G 1 ≤
        ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔ pN p G) :
    ∃ u : ℕ → G, (∀ i < s, u i ∈ Subgroup.closure (x '' Set.Iio s)) ∧
      StrictChainN (pN p G) u s ∧ WkN (pN p G) u s = lcs G 1 ∧
      (∀ k < s, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ frattini G) ∧
      Subgroup.closure (u '' Set.Iio s) ⊔ frattini G =
        Subgroup.closure (x '' Set.Iio s) ⊔ frattini G ∧
      (∀ k, 1 ≤ k → k ≤ s → p ^ (k - 1) * Nat.card (pN p G) ≤
        Nat.card (WkN (pN p G) u k)) := by
  have hP : IsPGroup p G := IsPGroup.of_card hG
  exact core_flag hp.out hG (pN p G) (frattini G) frame_hN3 frame_hN2 (frame_hM2 hP)
    (frame_hMp hP) (frame_hMN hP) s x hcore hmin

/-- Lemma 2.3 (lower half) and `s ≤ r_1` for a minimal core of size `s ≥ 1`. -/
theorem frame_core_bounds {n : ℕ} (hG : Nat.card G = p ^ n) (s : ℕ) (x : ℕ → G)
    (hcore : lcs G 1 ≤
      ⁅Subgroup.closure (x '' Set.Iio s), Subgroup.closure (x '' Set.Iio s)⁆ ⊔ pN p G)
    (hmin : ∀ t < s, ∀ v : ℕ → G, (∀ i < t, v i ∈ Subgroup.closure (x '' Set.Iio s)) →
      ¬ lcs G 1 ≤
        ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔ pN p G)
    (hs : 1 ≤ s) : s - 1 ≤ r2 p G ∧ s ≤ Group.rank G := by
  have hP : IsPGroup p G := IsPGroup.of_card hG
  obtain ⟨h1, h2⟩ := core_flag_card hp.out hG (pN p G) (frattini G) frame_hN3 frame_hN2
    (frame_hM2 hP) (frame_hMp hP) (frame_hMN hP) s x hcore hmin
  have hp2 := hp.out.two_le
  refine ⟨?_, ?_⟩
  · have h := h1 hs
    rw [card_lcs_one_eq (p := p) (G := G), mul_comm (Nat.card (pN p G))] at h
    have hpos : 0 < Nat.card (pN p G) := Nat.card_pos
    rw [mul_comm (p ^ (s - 1)), mul_comm (p ^ r2 p G)] at h
    exact pow_le_pow_cancel hp2 (le_of_mul_le_mul_pos hpos h)
  · have hc := Subgroup.card_mul_index (frattini G)
    have hi : (frattini G).index = p ^ Group.rank G := card_quot_frattini hP
    rw [hi] at hc
    rw [← hc, mul_comm (p ^ s)] at h2
    have hpos : 0 < Nat.card (frattini G) := Nat.card_pos
    exact pow_le_pow_cancel hp2 (le_of_mul_le_mul_pos hpos h2)

/-! The parameter `λ` with `|G : γ_2| = p ^ (r_1 + λ)`. -/

/-- `s_1 = log_p |G : γ_2| = log_p |L_1|`. -/
noncomputable def s1 (p : ℕ) (G : Type u) [Group G] : ℕ := Nat.log p (lcs G 1).index

/-- `λ = s_1 - r_1` (the defect `δ` of (75)). -/
noncomputable def lambdaPar (p : ℕ) (G : Type u) [Group G] [Finite G] : ℕ :=
  s1 p G - Group.rank G

theorem index_lcs_one_eq_pow_s1 (hG : IsPGroup p G) : (lcs G 1).index = p ^ s1 p G := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hd : (lcs G 1).index ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card (lcs G 1)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  rw [s1, hk, Nat.log_pow hp.out.one_lt]

theorem rank_le_s1 (hG : IsPGroup p G) : Group.rank G ≤ s1 p G := by
  have hd : (frattini G).index ∣ (lcs G 1).index := Subgroup.index_dvd_of_le (frame_hM2 hG)
  have hi : (frattini G).index = p ^ Group.rank G := card_quot_frattini hG
  rw [hi, index_lcs_one_eq_pow_s1 hG] at hd
  exact pow_le_pow_cancel hp.out.two_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)) hd)

/-- `|G : γ_2| = p ^ (r_1 + λ)`. -/
theorem index_lcs_one_eq (hG : IsPGroup p G) :
    (lcs G 1).index = p ^ (Group.rank G + lambdaPar p G) := by
  rw [index_lcs_one_eq_pow_s1 hG, lambdaPar, Nat.add_sub_of_le (rank_le_s1 hG)]

/-- `λ = s_1 - r_1 ≥ 0`. -/
theorem lambdaPar_nonneg (hG : IsPGroup p G) :
    (0 : ℤ) ≤ (s1 p G : ℤ) - (Group.rank G : ℤ) ∧
      (lambdaPar p G : ℤ) = (s1 p G : ℤ) - (Group.rank G : ℤ) := by
  have h := rank_le_s1 hG
  refine ⟨by omega, ?_⟩
  rw [lambdaPar]
  omega

end Frame

end OMA.SimsLite
