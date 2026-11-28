import H2Dev.Alt2
import H2Dev.Frame
import H2Dev.SimsGen

/-! # Alt2Bridge: the group-level Sims rank as the Sims rank of a matrix tuple

For a finite `p`-group `G`, with `V = G ⧸ Φ(G)` and `W = γ_2 ⧸ γ_3 γ_2^p` (`OMA.SimsLite.VQ`,
`OMA.SimsLite.WQ`) and the commutator form `OMA.SimsLite.lamLin : V × V → W`:

* `simsRkLin_lamLin` : `simsRkLin lamLin = simsRank G`, i.e. the Sims rank of Def 2.1 / (17)
  (`OMA.SimsLite.simsRank`, an `sInf` over generating tuples of cores) is the linear Sims rank
  (91) of `β_G = lamLin`;
* `simsRk_lamLin_tuple` : in any bases `bV`, `bW` the coordinate tuple `matTuple lamLin bV bW` is
  an `r2`-tuple of alternating `r1 × r1` matrices over `ZMod p`, surjective, with
  `simsRk = simsRank G`;
* `exists_tuple_of_group` : the same with `r1 = Group.rank G`, `r2 = r2 p G`, so that at `p = 2`
  the tuple of `G` is one of the tuples counted by `N2 (Group.rank G) (r2 2 G) (simsRank G)`
  (`tuple_mem_N2`);
* `simsRank_bounds` : the CNT3 constraints `s - 1 ≤ r2 ≤ C(s, 2)` for `s = simsRank G`.
-/

namespace OMA.SimsLite.Alt2

open Module

universe u

section Bridge

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G]

/-- The image of a subgroup `H` in `V`, as an additive subgroup. -/
def imVsub (H : Subgroup G) : AddSubgroup (Additive (VQ p G)) where
  carrier := {x | ∃ h ∈ H, Additive.ofMul (piV p G h) = x}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, H.mul_mem ha hb, by rw [map_mul]; rfl⟩
  zero_mem' := ⟨1, H.one_mem, by rw [map_one]; rfl⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, H.inv_mem ha, by rw [map_inv]; rfl⟩

/-- The image of `K ∩ γ_2` in `W`, as an additive subgroup. -/
def imWsub (K : Subgroup G) : AddSubgroup (Additive (WQ p G)) where
  carrier := {w | ∃ a : lcs G 1, (a : G) ∈ K ∧ Additive.ofMul (piW p G a) = w}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, K.mul_mem ha hb, by rw [map_mul]; rfl⟩
  zero_mem' := ⟨1, K.one_mem, by rw [map_one]; rfl⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, K.inv_mem ha, by rw [map_inv]; rfl⟩

/-- The preimage in `G` of a subspace `U ≤ V`. -/
def preV (U : Submodule (ZMod p) (Additive (VQ p G))) : Subgroup G where
  carrier := {g | Additive.ofMul (piV p G g) ∈ U}
  mul_mem' := by
    intro a b ha hb
    show Additive.ofMul (piV p G (a * b)) ∈ U
    rw [map_mul]
    exact U.add_mem ha hb
  one_mem' := by
    show Additive.ofMul (piV p G 1) ∈ U
    rw [map_one]
    exact U.zero_mem
  inv_mem' := by
    intro a ha
    show Additive.ofMul (piV p G a⁻¹) ∈ U
    rw [map_inv]
    exact U.neg_mem ha

/-- The elements of `γ_2` whose image in `W` lies in `S`. -/
def preW (S : Submodule (ZMod p) (Additive (WQ p G))) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ lcs G 1, Additive.ofMul (piW p G ⟨g, hg⟩) ∈ S}
  mul_mem' := by
    rintro a b ⟨ha, hSa⟩ ⟨hb, hSb⟩
    refine ⟨(lcs G 1).mul_mem ha hb, ?_⟩
    show Additive.ofMul (piW p G (⟨a, ha⟩ * ⟨b, hb⟩)) ∈ S
    rw [map_mul]
    exact S.add_mem hSa hSb
  one_mem' := by
    refine ⟨(lcs G 1).one_mem, ?_⟩
    show Additive.ofMul (piW p G 1) ∈ S
    rw [map_one]
    exact S.zero_mem
  inv_mem' := by
    rintro a ⟨ha, hSa⟩
    refine ⟨(lcs G 1).inv_mem ha, ?_⟩
    show Additive.ofMul (piW p G (⟨a, ha⟩⁻¹)) ∈ S
    rw [map_inv]
    exact S.neg_mem hSa

/-- A core `H = ⟨u_0, ..., u_{k-1}⟩` (`γ_2 ≤ [H, H] γ_3`) gives a subspace of `V` of dimension
at most `k` on which `β_G` generates `W`. -/
theorem gensLin_of_core {k : ℕ} (u : Fin k → G)
    (hcore : lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
      lcs G 2) :
    GensLin (lamLin (p := p) (G := G))
      (Submodule.span (ZMod p) (Set.range (fun i => Additive.ofMul (piV p G (u i))))) := by
  set U := Submodule.span (ZMod p) (Set.range (fun i => Additive.ofMul (piV p G (u i))))
  set S := Submodule.span (ZMod p) {w | ∃ x ∈ U, ∃ y ∈ U, w = lamLin (p := p) (G := G) x y}
  have hHU : Subgroup.closure (Set.range u) ≤ preV U := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  have hle : ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔ lcs G 2 ≤
      preW S := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro g hg h hh
      refine ⟨commElem_mem_lcs_one g h, ?_⟩
      show Additive.ofMul (piW p G (cw g h)) ∈ S
      rw [← lamLin_mk]
      exact Submodule.subset_span ⟨Additive.ofMul (piV p G g), hHU hg,
        Additive.ofMul (piV p G h), hHU hh, rfl⟩
    · intro g hg
      have hg1 : g ∈ lcs G 1 := (lcs_two_le_pN p).trans (pN_le_lcs_one p) hg
      refine ⟨hg1, ?_⟩
      rw [piW_eq_one_of (a := ⟨g, hg1⟩) (lcs_two_le_pN p hg)]
      exact S.zero_mem
  show S = ⊤
  rw [eq_top_iff]
  intro w _
  obtain ⟨a, ha⟩ := piW_surjective (p := p) (G := G) (Additive.toMul w)
  obtain ⟨h, hS⟩ := hle (hcore a.2)
  have e : w = Additive.ofMul (piW p G a) := by
    rw [ha]
    rfl
  rw [e]
  exact hS

/-- Conversely, a subspace `U = span (v_0, ..., v_{d-1})` of `V` on which `β_G` generates `W`
gives a core generated by `d` elements, so `simsRank G ≤ d`. -/
theorem simsRank_le_of_gensLin [Finite G] (hG : IsPGroup p G) {d : ℕ}
    (v : Fin d → Additive (VQ p G))
    (hU : GensLin (lamLin (p := p) (G := G)) (Submodule.span (ZMod p) (Set.range v))) :
    simsRank G ≤ d := by
  set U := Submodule.span (ZMod p) (Set.range v)
  set x : Fin d → G := fun i => liftV (Additive.toMul (v i))
  set H := Subgroup.closure (Set.range x)
  set K := ⁅H, H⁆ ⊔ pN p G
  have hUP : U ≤ AddSubgroup.toZModSubmodule p (imVsub (p := p) H) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩, ?_⟩
    show Additive.ofMul (piV p G (liftV (Additive.toMul (v i)))) = v i
    rw [piV_liftV]
    rfl
  have hT : (⊤ : Submodule (ZMod p) (Additive (WQ p G))) ≤
      AddSubgroup.toZModSubmodule p (imWsub (p := p) K) := by
    unfold GensLin at hU
    rw [← hU, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' : a ∈ imVsub (p := p) H := hUP ha
    have hb' : b ∈ imVsub (p := p) H := hUP hb
    obtain ⟨g, hg, rfl⟩ := ha'
    obtain ⟨h, hh, rfl⟩ := hb'
    exact ⟨cw g h, Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hg hh),
      (lamLin_mk g h).symm⟩
  have hcore : lcs G 1 ≤ K := by
    intro g hg
    have hw : Additive.ofMul (piW p G ⟨g, hg⟩) ∈ imWsub (p := p) K :=
      hT Submodule.mem_top
    obtain ⟨a, haK, heq⟩ := hw
    have heq' : piW p G a = piW p G ⟨g, hg⟩ := congrArg Additive.toMul heq
    have hk : (⟨g, hg⟩ * a⁻¹ : lcs G 1) ∈ (piW p G).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← heq', mul_inv_cancel]
    rw [ker_piW, Subgroup.mem_subgroupOf] at hk
    have hk' : g * (a : G)⁻¹ ∈ pN p G := hk
    have e : g = g * (a : G)⁻¹ * a := by group
    rw [e]
    exact K.mul_mem (Subgroup.mem_sup_right hk') haK
  apply Nat.sInf_le
  exact ⟨x, ((core_iff_lcs hG H).1 hcore).ge⟩

/-- `β_G` generates `W` on all of `V` (`lamLin_span`). -/
theorem gensLin_lamLin_top : GensLin (lamLin (p := p) (G := G)) ⊤ := by
  have e : Set.range (fun vw : Additive (VQ p G) × Additive (VQ p G) => lamLin vw.1 vw.2) =
      {w | ∃ x ∈ (⊤ : Submodule (ZMod p) (Additive (VQ p G))),
        ∃ y ∈ (⊤ : Submodule (ZMod p) (Additive (VQ p G))), w = lamLin (p := p) (G := G) x y} := by
    ext w
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨x, Submodule.mem_top, y, Submodule.mem_top, rfl⟩
    · rintro ⟨x, -, y, -, rfl⟩
      exact ⟨(x, y), rfl⟩
  have h := lamLin_span (p := p) (G := G)
  rw [e] at h
  exact h

/-- Every subspace of `V` is spanned by `finrank` vectors. -/
lemma exists_span_eq [Finite G] (U : Submodule (ZMod p) (Additive (VQ p G))) :
    ∃ v : Fin (finrank (ZMod p) U) → Additive (VQ p G), Submodule.span (ZMod p) (Set.range v) = U := by
  have : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have : Finite (Additive (VQ p G)) := inferInstance
  have : Finite U := inferInstance
  have : Module.Finite (ZMod p) U := inferInstance
  let B := Module.finBasisOfFinrankEq (ZMod p) U rfl
  refine ⟨fun i => (B i : Additive (VQ p G)), ?_⟩
  have h := congrArg (Submodule.map U.subtype) B.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
  exact h

/-- The Sims rank of Def 2.1 / (17) is the linear Sims rank (91) of `β_G = lamLin`. -/
theorem simsRkLin_lamLin [Finite G] (hG : IsPGroup p G) :
    simsRkLin (lamLin (p := p) (G := G)) = simsRank G := by
  apply le_antisymm
  · have hne : {k | ∃ u : Fin k → G,
        lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
          lcs G 2}.Nonempty := by
      let e : Fin (Nat.card G) → G := (Finite.equivFin G).symm
      have he : Set.range e = Set.univ := Equiv.range_eq_univ _
      refine ⟨Nat.card G, e, ?_⟩
      rw [he, Subgroup.closure_univ]
      exact le_sup_left
    obtain ⟨u, hu⟩ := Nat.sInf_mem hne
    have hg := gensLin_of_core (p := p) u hu
    have h1 : simsRkLin (lamLin (p := p) (G := G)) ≤ finrank (ZMod p)
        (Submodule.span (ZMod p) (Set.range (fun i => Additive.ofMul (piV p G (u i))))) :=
      Nat.sInf_le ⟨_, rfl, hg⟩
    have h2 : finrank (ZMod p)
        (Submodule.span (ZMod p) (Set.range (fun i => Additive.ofMul (piV p G (u i))))) ≤
        Fintype.card (Fin (simsRank G)) :=
      finrank_range_le_card (fun i => Additive.ofMul (piV p G (u i)))
    rw [Fintype.card_fin] at h2
    exact h1.trans h2
  · have htop : GensLin (lamLin (p := p) (G := G)) ⊤ := gensLin_lamLin_top
    have hne : {d | ∃ U : Submodule (ZMod p) (Additive (VQ p G)), finrank (ZMod p) U = d ∧
        GensLin (lamLin (p := p) (G := G)) U}.Nonempty := ⟨_, ⊤, rfl, htop⟩
    obtain ⟨U, hU, hg⟩ := Nat.sInf_mem hne
    obtain ⟨v, hv⟩ := exists_span_eq (p := p) U
    rw [← hv] at hg
    have := simsRank_le_of_gensLin hG v hg
    exact this.trans hU.le

/-- The coordinate tuple of `β_G` in any bases: alternating, surjective, of Sims rank
`simsRank G`. -/
theorem simsRk_lamLin_tuple [Finite G] (hG : IsPGroup p G) {r1 r2 : ℕ}
    (bV : Basis (Fin r1) (ZMod p) (Additive (VQ p G)))
    (bW : Basis (Fin r2) (ZMod p) (Additive (WQ p G))) :
    (∀ k, IsAltMat (matTuple (lamLin (p := p) (G := G)) bV bW k)) ∧
      GensOn (matTuple (lamLin (p := p) (G := G)) bV bW) ⊤ ∧
      simsRk (matTuple (lamLin (p := p) (G := G)) bV bW) = simsRank G := by
  refine ⟨matTuple_isAlt _ (fun x => lamLin_self (p := p) (G := G) x) bV bW, ?_, ?_⟩
  · rw [gensOn_top_matTuple_iff]
    exact gensLin_lamLin_top
  · rw [simsRk_matTuple, simsRkLin_lamLin hG]

/-- The matrix tuple of `G`: an `r2`-tuple of alternating `r1 × r1` matrices over `ZMod p`
(`r1 = Group.rank G`, `r2 = r2 p G`), surjective, with Sims rank `simsRank G`. -/
theorem exists_tuple_of_group [Finite G] (hG : IsPGroup p G) :
    ∃ β : Fin (r2 p G) → Matrix (Fin (Group.rank G)) (Fin (Group.rank G)) (ZMod p),
      (∀ k, IsAltMat (β k)) ∧ GensOn β ⊤ ∧ simsRk β = simsRank G := by
  have : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have : Finite (Additive (VQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (VQ p G)) := inferInstance
  have : Finite (WQ p G) := Finite.of_surjective _ piW_surjective
  have : Finite (Additive (WQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (WQ p G)) := inferInstance
  let bV := Module.finBasisOfFinrankEq (ZMod p) (Additive (VQ p G)) (finrank_V (p := p) (G := G) hG)
  let bW := Module.finBasisOfFinrankEq (ZMod p) (Additive (WQ p G)) (rfl : finrank (ZMod p)
    (Additive (WQ p G)) = r2 p G)
  exact ⟨_, simsRk_lamLin_tuple hG bV bW⟩

/-- At `p = 2`, the matrix tuple of `G` is counted by `N2 (Group.rank G) (r2 2 G) (simsRank G)`;
in particular this count is positive. -/
theorem N2_pos_of_group {G : Type u} [Group G] [Finite G] [Fact (Nat.Prime 2)]
    (hG : IsPGroup 2 G) : 0 < N2 (Group.rank G) (r2 2 G) (simsRank G) := by
  classical
  obtain ⟨β, hA, hg, hs⟩ := exists_tuple_of_group (p := 2) hG
  unfold N2
  exact Finset.card_pos.2 ⟨β, Finset.mem_filter.2 ⟨Finset.mem_univ _, hA, hg, hs⟩⟩

/-- The CNT3 constraints for the Sims rank of a finite `p`-group:
`s - 1 ≤ r2 ≤ C(s, 2)` and `s ≤ r1`. -/
theorem simsRank_bounds [Finite G] (hG : IsPGroup p G) :
    simsRank G ≤ r2 p G + 1 ∧ r2 p G ≤ (simsRank G).choose 2 ∧ simsRank G ≤ Group.rank G := by
  obtain ⟨β, hA, hg, hs⟩ := exists_tuple_of_group hG
  refine ⟨?_, ?_, ?_⟩
  · rw [← hs]
    exact simsRk_le_succ β hg
  · rw [← hs]
    exact card_le_choose_simsRk β hA hg
  · rw [← hs]
    exact simsRk_le_R β hg

end Bridge

end OMA.SimsLite.Alt2

#print axioms OMA.SimsLite.Alt2.simsRank_bounds
#print axioms OMA.SimsLite.Alt2.N2_pos_of_group
#print axioms OMA.SimsLite.Alt2.N2_support_sims
#print axioms OMA.SimsLite.Alt2.N2_eq_ncard
#print axioms OMA.SimsLite.Alt2.pow_le_ncard_grass
#print axioms OMA.SimsLite.Alt2.ncard_subgroups_le
#print axioms OMA.SimsLite.Alt2.exists_le_card_pow
#print axioms OMA.SimsLite.Alt2.simsRk_lamLin_tuple
