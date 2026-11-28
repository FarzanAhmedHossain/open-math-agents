import Mathlib
import H2Dev.CommForm

/-! INF-2: the Burnside basis theorem for finite p-groups.
For a finite p-group `G`:
* `frattini_eq_pPhi` : the Frattini subgroup equals `pPhi p G = G^p γ_2`;
* `quot_frattini_mul_comm`, `quot_frattini_pow_p` : `G ⧸ frattini G` is elementary abelian;
* `card_quot_frattini` : `Nat.card (G ⧸ frattini G) = p ^ Group.rank G`;
* `rank_eq_log_index_frattini` : `Group.rank G = Nat.log p (frattini G).index`;
* `closure_eq_top_of_sup_frattini`, `closure_image_frattini_eq_top_iff` : a subset generates `G`
  iff its image generates `G ⧸ frattini G`. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section BurnsideGeneral

variable {G : Type u} [Group G]

/-- A subgroup containing the commutator subgroup is normal. -/
lemma normal_of_commutator_le {H : Subgroup G} (h : commutator G ≤ H) : H.Normal :=
  ⟨fun n hn g => by
    have hc : ⁅g, n⁆ ∈ H := h (by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem hc hn⟩

/-- Modulo a maximal normal subgroup every nontrivial element generates the quotient. -/
lemma quot_coatom_zpowers {M : Subgroup G} [M.Normal] (hM : IsCoatom M) (x : G ⧸ M) :
    x = 1 ∨ Subgroup.zpowers x = ⊤ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G,
      K = Subgroup.comap (QuotientGroup.mk' M) (Subgroup.zpowers (g : G ⧸ M)) := ⟨_, rfl⟩
  have hMK : M ≤ K := by
    intro m hm
    rw [hK, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm]
    exact Subgroup.one_mem _
  have hgK : g ∈ K := by
    rw [hK, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    exact Subgroup.mem_zpowers _
  rcases eq_or_lt_of_le hMK with h | h
  · left
    rw [QuotientGroup.eq_one_iff, h]
    exact hgK
  · right
    have hKt := hM.2 K h
    rw [eq_top_iff]
    intro y _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hy : y ∈ K := by
      rw [hKt]
      exact Subgroup.mem_top y
    rw [hK, Subgroup.mem_comap, QuotientGroup.mk'_apply] at hy
    exact hy

end BurnsideGeneral

section Burnside

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [Finite G]

/-- Maximal subgroups of a finite p-group are normal. -/
lemma coatom_normal (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) : M.Normal := by
  haveI := hG.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom M normalizerCondition_of_isNilpotent hM

/-- Every maximal subgroup of a finite p-group contains `G^p γ_2`. -/
lemma pPhi_le_coatom (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) :
    pPhi p G ≤ M := by
  haveI := coatom_normal hG hM
  have hQ : IsPGroup p (G ⧸ M) := hG.to_quotient M
  have hnt : Nat.card (G ⧸ M) ≠ 1 := by
    intro h1
    apply hM.1
    rw [← Subgroup.index_eq_one]
    exact h1
  have hdvd : p ∣ Nat.card (G ⧸ M) := hQ.card_eq_or_dvd.resolve_left hnt
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have hxt : Subgroup.zpowers x = ⊤ := (quot_coatom_zpowers hM x).resolve_left hx1
  have hcard : Nat.card (G ⧸ M) = p := by
    rw [← hx, ← Nat.card_zpowers, hxt, Subgroup.card_top]
  have hcomm : ∀ a b : G ⧸ M, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.zpowers x := by
      rw [hxt]
      exact Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers x := by
      rw [hxt]
      exact Subgroup.mem_top b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self x i j).eq
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'
  · rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have e := map_commutatorElement (QuotientGroup.mk' M) a b
    simp only [QuotientGroup.mk'_apply] at e
    rw [← QuotientGroup.eq_one_iff, e, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _

/-- Elements outside `G^p γ_2` are avoided by some maximal subgroup. -/
lemma exists_coatom_not_mem (hG : IsPGroup p G) {g : G} (hg : g ∉ pPhi p G) :
    ∃ H : Subgroup G, IsCoatom H ∧ g ∉ H := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H, ⟨hPH, hgH⟩, hmax⟩ := (wellFounded_gt (α := Subgroup G)).has_min
    {H : Subgroup G | pPhi p G ≤ H ∧ g ∉ H} ⟨pPhi p G, le_rfl, hg⟩
  have key : ∀ K : Subgroup G, H < K → g ∈ K := by
    intro K hK
    by_contra hgK
    exact hmax K ⟨hPH.trans hK.le, hgK⟩ hK
  haveI : H.Normal := normal_of_commutator_le (le_sup_right.trans hPH)
  refine ⟨H, ⟨fun h => hgH (by rw [h]; exact Subgroup.mem_top g), fun K hK => ?_⟩, hgH⟩
  rw [eq_top_iff]
  intro y _
  by_cases hyH : y ∈ H
  · exact hK.le hyH
  · have hlt : H < H ⊔ Subgroup.zpowers y := by
      refine lt_of_le_of_ne le_sup_left (fun h => hyH ?_)
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hgs := key _ hlt
    rw [Subgroup.mem_sup_of_normal_left] at hgs
    obtain ⟨h, hh, z, hz, hhz⟩ := hgs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hgK := key K hK
    by_cases hpk : (p : ℤ) ∣ k
    · exfalso
      obtain ⟨m, rfl⟩ := hpk
      apply hgH
      rw [← hhz]
      refine H.mul_mem hh (hPH ?_)
      rw [zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨y, rfl⟩)) m
    · have hyk : y ^ k ∈ K := by
        have e : y ^ k = h⁻¹ * g := by
          rw [← hhz]
          group
        rw [e]
        exact K.mul_mem (K.inv_mem (hK.le hh)) hgK
      have hyp : y ^ (p : ℤ) ∈ K := by
        rw [zpow_natCast]
        exact hK.le (hPH (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨y, rfl⟩)))
      have hcop : Int.gcd k (p : ℤ) = 1 := by
        have hnd : ¬ p ∣ k.natAbs := fun h' => hpk (Int.ofNat_dvd_left.mpr h')
        have hc : Nat.Coprime p k.natAbs := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd
        exact hc.symm
      have e : y = (y ^ k) ^ (Int.gcdA k (p : ℤ)) * (y ^ (p : ℤ)) ^ (Int.gcdB k (p : ℤ)) := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← Int.gcd_eq_gcd_ab, hcop, Nat.cast_one, zpow_one]
      rw [e]
      exact K.mul_mem (K.zpow_mem hyk _) (K.zpow_mem hyp _)

/-- (a) The Frattini subgroup of a finite p-group is `G^p γ_2`. -/
theorem frattini_eq_pPhi (hG : IsPGroup p G) : frattini G = pPhi p G := by
  apply le_antisymm
  · intro g hg
    by_contra hgn
    obtain ⟨H, hH, hgH⟩ := exists_coatom_not_mem hG hgn
    exact hgH (frattini_le_coatom hH hg)
  · show pPhi p G ≤ ⨅ a ∈ {H : Subgroup G | IsCoatom H}, a
    exact le_iInf₂ fun M hM => pPhi_le_coatom hG hM

/-- (b) `G ⧸ frattini G` is commutative. -/
theorem quot_frattini_mul_comm (hG : IsPGroup p G) (a b : G ⧸ frattini G) : a * b = b * a := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have hc : ⁅a, b⁆ ∈ frattini G := by
    rw [frattini_eq_pPhi hG]
    refine Subgroup.mem_sup_right ?_
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [← QuotientGroup.eq_one_iff] at hc
  have e := map_commutatorElement (QuotientGroup.mk' (frattini G)) a b
  simp only [QuotientGroup.mk'_apply] at e
  rw [e, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

/-- (b) `G ⧸ frattini G` has exponent dividing `p`. -/
theorem quot_frattini_pow_p (hG : IsPGroup p G) (a : G ⧸ frattini G) : a ^ p = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, frattini_eq_pPhi hG]
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, rfl⟩)

/-- (b) `G ⧸ frattini G` is an elementary abelian p-group. -/
theorem quot_frattini_elementary (hG : IsPGroup p G) :
    (∀ a b : G ⧸ frattini G, a * b = b * a) ∧ ∀ a : G ⧸ frattini G, a ^ p = 1 :=
  ⟨quot_frattini_mul_comm hG, quot_frattini_pow_p hG⟩

/-- The commutative group structure on `G ⧸ frattini G`. -/
abbrev fratCommGroup (hG : IsPGroup p G) : CommGroup (G ⧸ frattini G) :=
  { (inferInstance : Group (G ⧸ frattini G)) with mul_comm := quot_frattini_mul_comm hG }

/-- (c) Frattini property: generating modulo the Frattini subgroup means generating. -/
theorem closure_eq_top_of_sup_frattini {s : Set G}
    (h : Subgroup.closure s ⊔ frattini G = ⊤) : Subgroup.closure s = ⊤ := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact frattini_nongenerating h

/-- (c) Burnside basis theorem: `s` generates `G` iff its image generates `G ⧸ frattini G`. -/
theorem closure_image_frattini_eq_top_iff (s : Set G) :
    Subgroup.closure ((QuotientGroup.mk : G → G ⧸ frattini G) '' s) = ⊤ ↔
      Subgroup.closure s = ⊤ := by
  have hm := MonoidHom.map_closure (QuotientGroup.mk' (frattini G)) s
  rw [QuotientGroup.coe_mk'] at hm
  constructor
  · intro h
    apply closure_eq_top_of_sup_frattini
    rw [← QuotientGroup.ker_mk' (frattini G), ← Subgroup.comap_map_eq, hm, h,
      Subgroup.comap_top]
  · intro h
    rw [← hm, h]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- (b) Burnside: `|G ⧸ Φ(G)| = p ^ rank G`. -/
theorem card_quot_frattini (hG : IsPGroup p G) :
    Nat.card (G ⧸ frattini G) = p ^ Group.rank G := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  letI := fratCommGroup hG
  letI : Module (ZMod p) (Additive (G ⧸ frattini G)) :=
    AddCommGroup.zmodModule (n := p) (fun x => by
      have h := congrArg Additive.ofMul (quot_frattini_pow_p hG (Additive.toMul x))
      exact h)
  haveI : Finite (Additive (G ⧸ frattini G)) :=
    Finite.of_equiv (G ⧸ frattini G) Additive.ofMul
  haveI : Module.Finite (ZMod p) (Additive (G ⧸ frattini G)) := Module.Finite.of_finite
  have hcard : Nat.card (Additive (G ⧸ frattini G)) =
      p ^ Module.finrank (ZMod p) (Additive (G ⧸ frattini G)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [show Nat.card (G ⧸ frattini G) = Nat.card (Additive (G ⧸ frattini G)) from rfl, hcard]
  congr 1
  apply le_antisymm
  · -- the image of a minimal generating set spans
    obtain ⟨S, hSc, hS⟩ := Group.rank_spec G
    let T : Finset (Additive (G ⧸ frattini G)) :=
      S.image (fun g => Additive.ofMul (g : G ⧸ frattini G))
    have hspan : Submodule.span (ZMod p) (T : Set (Additive (G ⧸ frattini G))) = ⊤ := by
      rw [eq_top_iff]
      rintro v -
      obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      let K : Subgroup G :=
        { carrier := {x | Additive.ofMul (x : G ⧸ frattini G) ∈
            Submodule.span (ZMod p) (T : Set (Additive (G ⧸ frattini G)))}
          mul_mem' := fun {a b} ha hb => by
            show Additive.ofMul ((a * b : G) : G ⧸ frattini G) ∈ _
            rw [QuotientGroup.mk_mul, ofMul_mul]
            exact Submodule.add_mem _ ha hb
          one_mem' := by
            show Additive.ofMul ((1 : G) : G ⧸ frattini G) ∈ _
            rw [QuotientGroup.mk_one, ofMul_one]
            exact Submodule.zero_mem _
          inv_mem' := fun {a} ha => by
            show Additive.ofMul ((a⁻¹ : G) : G ⧸ frattini G) ∈ _
            rw [QuotientGroup.mk_inv, ofMul_inv]
            exact Submodule.neg_mem _ ha }
      have hK : Subgroup.closure (S : Set G) ≤ K := by
        rw [Subgroup.closure_le]
        intro x hx
        exact Submodule.subset_span (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem (fun g : G => Additive.ofMul (g : G ⧸ frattini G)) hx))
      have hgK : g ∈ K := hK (by rw [hS]; exact Subgroup.mem_top g)
      exact hgK
    have h1 : Module.finrank (ZMod p)
        (Submodule.span (ZMod p) (T : Set (Additive (G ⧸ frattini G)))) ≤ T.card :=
      finrank_span_finset_le_card T
    rw [hspan, finrank_top] at h1
    exact h1.trans (Finset.card_image_le.trans hSc.le)
  · -- lifts of a basis generate
    let b := Module.finBasis (ZMod p) (Additive (G ⧸ frattini G))
    choose lift hlift using fun i =>
      QuotientGroup.mk_surjective (Additive.toMul (b i) : G ⧸ frattini G)
    let S : Finset G := Finset.univ.image lift
    have hgen : Subgroup.closure (S : Set G) = ⊤ := by
      apply closure_eq_top_of_sup_frattini
      rw [eq_top_iff]
      intro x _
      let W : Submodule (ZMod p) (Additive (G ⧸ frattini G)) :=
        { carrier := {v | ∃ y ∈ Subgroup.closure (S : Set G) ⊔ frattini G,
            Additive.ofMul (y : G ⧸ frattini G) = v}
          add_mem' := by
            rintro _ _ ⟨y1, h1, rfl⟩ ⟨y2, h2, rfl⟩
            exact ⟨y1 * y2, Subgroup.mul_mem _ h1 h2, by rw [QuotientGroup.mk_mul, ofMul_mul]⟩
          zero_mem' := ⟨1, Subgroup.one_mem _, by rw [QuotientGroup.mk_one, ofMul_one]⟩
          smul_mem' := by
            rintro c _ ⟨y, hy, rfl⟩
            refine ⟨y ^ c.val, Subgroup.pow_mem _ hy _, ?_⟩
            conv_rhs => rw [← ZMod.natCast_zmod_val c]
            rw [Nat.cast_smul_eq_nsmul, QuotientGroup.mk_pow, ofMul_pow] }
      have hW : (⊤ : Submodule (ZMod p) (Additive (G ⧸ frattini G))) ≤ W := by
        rw [← b.span_eq, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        show ∃ y ∈ Subgroup.closure (S : Set G) ⊔ frattini G,
          Additive.ofMul (y : G ⧸ frattini G) = b i
        refine ⟨lift i, Subgroup.mem_sup_left (Subgroup.subset_closure ?_), ?_⟩
        · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem lift (Finset.mem_univ i))
        · rw [hlift i, ofMul_toMul]
      have hmem : ∃ y ∈ Subgroup.closure (S : Set G) ⊔ frattini G,
          Additive.ofMul (y : G ⧸ frattini G) = Additive.ofMul (x : G ⧸ frattini G) :=
        hW (Submodule.mem_top (x := Additive.ofMul (x : G ⧸ frattini G)))
      obtain ⟨y, hy, hyx⟩ := hmem
      have hyx' : (y : G ⧸ frattini G) = x := Additive.ofMul.injective hyx
      rw [QuotientGroup.eq] at hyx'
      have e : x = y * (y⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy (Subgroup.mem_sup_right hyx')
    calc Group.rank G ≤ S.card := Group.rank_le hgen
      _ ≤ (Finset.univ : Finset (Fin (Module.finrank (ZMod p)
            (Additive (G ⧸ frattini G))))).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_univ, Fintype.card_fin]

/-- (b) Burnside: `rank G = log_p [G : Φ(G)]`. -/
theorem rank_eq_log_index_frattini (hG : IsPGroup p G) :
    Group.rank G = Nat.log p (frattini G).index := by
  rw [show (frattini G).index = Nat.card (G ⧸ frattini G) from rfl, card_quot_frattini hG,
    Nat.log_pow hp.out.one_lt]

/-- `|G ⧸ G^p γ_2| = p ^ rank G`. -/
theorem card_quot_pPhi (hG : IsPGroup p G) :
    Nat.card (G ⧸ pPhi p G) = p ^ Group.rank G := by
  rw [← card_quot_frattini hG, frattini_eq_pPhi hG]

end Burnside

end OMA.SimsLite
