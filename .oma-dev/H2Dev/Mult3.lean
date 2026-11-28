import H2Dev.CNT3Stmt

/-! # MULT3: the multiplicity saving at class 3 (statement and foundation)

Li-Qiao, Remark 6.4 (p.43), Section 13.1 (`S_{Z0}`, pp.78-79), the core centraliser `K`
(149)-(150), Propositions 13.1 (pp.79-80) and 13.2 (pp.80-81), Corollary 14.1 (pp.81-82), at
class `c = 3` and `p = 2`.

## The statement (`Mult3Stmt`, unproved)

`mult3Set m r1 r2 s lam m2 m3 r3 z k` is the set of groups `G ∈ cnt3Set m r1 r2 s lam m2 m3 r3`
admitting

* a Sims core `H` (`γ_2 = [H, H] γ_3`, `d(H) = s`), whose core centraliser
  `K = {v ∈ V : β_G(v, U) = 0}` (149) (`U` the image of `H` in `V = G/Φ(G)`) has dimension `k`;
  inline, `K` is described through its preimage `{g | ∀ h ∈ H, [g, h] ∈ γ_3 γ_2^2}` in `G`, whose
  order is `2^k |G| / 2^r1` (`|Φ(G)| = |G| / 2^r1`);
* a decomposition `G/γ_2 = A/γ_2 ⊕ B/γ_2` with `A/γ_2` elementary abelian of order `2^z`
  (this is `Z0`) and `H ≤ B` (the complementary summand contains the core image), as in
  Section 13.1 and Corollary 14.1.

`Mult3Stmt` is Corollary 14.1 (153) at `c = 3`, for `lam ≤ 1`, in the form of `CNT3Stmt` with
the `A`-alternative of (55) (`Δ_p` omitted, as Remark 6.4 requires):
`log_2 #classes ≤ C m (log_2 m + 1) + PW + A b2 - z^2 + k (r1 + z - k - s r2)`.
Here `-z^2 + z k` is the multiplicity saving of Proposition 13.1 (`|GL_z| / 2^(z k)` distinct
array pairs per group), and `k (r1 - k) - s k r2` is Proposition 13.2 (at most `2^(k (r1 - k))`
subspaces `K`, up to `O(m)`, each imposing `s k r2` affine conditions on the core-outside
coefficients); `mult3_exponent_eq` checks the bookkeeping.

Relation with the paper's form. Corollary 14.1 states (153) with the main term `F_{1/2}` and
assumes saturation `C(s-1, 2) < r2 ≤ C(s, 2)`; saturation is used there only to get `Δ_p = 0`
(Proposition 6.5), so that the bound of Theorem 6.3 matches `F_{1/2}`. Here `F_{1/2}` is replaced
by `PW + A b2` as in `CNT3Stmt` (the `A`-alternative of (55), i.e. (85) with `Δ_p` omitted, which
is valid since `Δ_p ≤ 0` by (86)), and saturation is dropped. The downstream assembly (plan
P12(e)) is stated with `F_{1/2} + 2 m2 e + r1 δ`; the comparison
`PW + A b2 ≤ F_{1/2} + 2 m2 e + r1 δ + O(m log m)` is not part of this module and must be checked
when the main arithmetic is written (or the main arithmetic must be stated in the `cnt3` form).

## Proved here

* the set-level bridges: `mult3Set_subset`, `mult3Classes_subset`, `mult3Classes_finite`,
  `mult3_ncard_le_cnt3`;
* the core centraliser `coreCent B U` of an alternating bilinear map, and (150):
  `coreCent_inf_eq_bot` (`K ∩ U = 0` for a Sims-minimal `U`), `finrank_coreCent_add_le`
  (`dim K + dim U ≤ dim V`);
* its group-level instance: `mem_coreCent_lamLin_iff` (the inline preimage condition),
  `group_coreCent_inf_eq_bot`, `group_finrank_coreCent_le` (`dim K ≤ r1 - s`);
* Proposition 13.1 (linear-algebra core): `coreRow_eq_imp_sub_mem` (equal leading core-free
  coefficients force `x_ℓ - y_ℓ ∈ K`) and `prop_13_1_count`
  (`q^(z (z - 1)) ≤ #{distinct coefficient rows} · q^(z dim K)`; the constant `π∞(2)` of the
  paper is replaced by the factor `q^(-z)`, an `O(m)` loss), with `card_bases_ge`;
* Remark 6.4 (linear-algebra core): `rem_6_4_fiber` (an affine system of rank `ρ` on a space of
  dimension `n` has at most `q^(n - ρ)` solutions);
* Proposition 13.2 (linear-algebra core): `prop_13_2_fiber` (maps prescribed on a `k`-dimensional
  subspace: at most `|Y|^(n - k)` of them), and the subspace count is `Alt2.ncard_grass_le_pivot`;
* the arithmetic of Corollary 14.1: `cor_14_1_dim_bound` (152) and `mult3_exponent_eq`;
* the range of `z` (Section 13.1, `max (0, r1 - s - lam) ≤ dim Z0 ≤ r1 - s`):
  `mult3_z_add_s_le` (`z + s ≤ r1` on `mult3Set`, via `summand_dim_le`), and the existence of
  `Z0`: `mult3Set_of_core` (every group of `cnt3Set` with every Sims core `H` lies in `mult3Set`
  for some `z` with `r1 ≤ z + s + lam`, via `exists_summand`) and `cnt3Set_mem_mult3Set`.

## Left for MULT3 (b)

The group-level family `S_{Z0}` (148) and the proof that its members share the recorded data
(Section 13.1), the transport of `prop_13_1_count` to coefficient arrays of Sims codes (needs the
identification of `c(1, k, j, 2, v) mod 2` with the `W`-coordinates of `β_G`, as for CNT3 (b)),
and the assembly with the CNT3 pipeline (`CNT3Final`), with the `s k r2` saving inserted into
the leading-layer count of `Lift.lf_realizedCB_ncard_le`. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

/-! ### The statement -/

section Mult3Defs

/-- The class-3 parameter set of MULT3: groups of `cnt3Set` with a Sims core `H` whose core
centraliser has dimension `k`, and an elementary abelian direct summand `Z0 = A/γ_2` of `G/γ_2`
of order `2^z` whose complement `B/γ_2` contains `Hγ_2/γ_2`. -/
def mult3Set (m r1 r2 s lam m2 m3 r3 z k : ℕ) : Set FiniteGrp.{0} :=
  {G | G ∈ cnt3Set m r1 r2 s lam m2 m3 r3 ∧
    ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
        ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = s ∧
      Nat.card {g : G // ∀ h ∈ H, ⁅g, h⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 ⊔
          Subgroup.closure (Set.range (fun x : (⊤ : Subgroup G).lowerCentralSeries 1 =>
            (x : G) ^ 2))} * 2 ^ r1 = 2 ^ k * Nat.card G ∧
      ∃ A B : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 ≤ A ∧
        (⊤ : Subgroup G).lowerCentralSeries 1 ≤ B ∧
        A ⊓ B = (⊤ : Subgroup G).lowerCentralSeries 1 ∧ A ⊔ B = ⊤ ∧ H ≤ B ∧
        (∀ a ∈ A, a ^ 2 ∈ (⊤ : Subgroup G).lowerCentralSeries 1) ∧
        Nat.card A = 2 ^ z * 2 ^ m2}

/-- The isomorphism classes of the groups of `mult3Set`. -/
def mult3Classes (m r1 r2 s lam m2 m3 r3 z k : ℕ) :
    Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
    mult3Set m r1 r2 s lam m2 m3 r3 z k

/-- MULT3: Corollary 14.1 (153) at `c = 3` for `lam ≤ 1`, in the form of `CNT3Stmt` (the
`A`-alternative of (55), `Δ_p` omitted). The paper's `F_{1/2}` is replaced by `PW + A b2`
(`cnt3PW + cnt3A`), and the saturation hypothesis of Corollary 14.1 is dropped (see the module
docstring). -/
def Mult3Stmt : Prop :=
  ∃ C : ℝ, ∀ m r1 r2 s lam m2 m3 r3 z k : ℕ, lam ≤ 1 →
    (mult3Set m r1 r2 s lam m2 m3 r3 z k).Nonempty →
    ∃ b2 : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧
      Real.logb 2 ((mult3Classes m r1 r2 s lam m2 m3 r3 z k).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) + (cnt3PW r1 r2 r3 lam m2 m3 : ℝ) +
          cnt3A r1 r2 s m2 m3 b2 - (z : ℝ) ^ 2 + (k : ℝ) * ((r1 : ℝ) + z - k - (s : ℝ) * r2)

end Mult3Defs

/-! ### Set-level bridges -/

section Mult3Bridge

variable {m r1 r2 s lam m2 m3 r3 z k : ℕ}

theorem mult3Set_subset : mult3Set m r1 r2 s lam m2 m3 r3 z k ⊆ cnt3Set m r1 r2 s lam m2 m3 r3 :=
  fun _ hG => hG.1

theorem mult3Classes_subset :
    mult3Classes m r1 r2 s lam m2 m3 r3 z k ⊆ cnt3Classes m r1 r2 s lam m2 m3 r3 :=
  Set.image_mono mult3Set_subset

theorem mult3Classes_finite : (mult3Classes m r1 r2 s lam m2 m3 r3 z k).Finite :=
  cnt3Classes_finite.subset mult3Classes_subset

/-- The MULT3 class count is at most the CNT3 class count. -/
theorem mult3_ncard_le_cnt3 :
    (mult3Classes m r1 r2 s lam m2 m3 r3 z k).ncard ≤ (cnt3Classes m r1 r2 s lam m2 m3 r3).ncard :=
  Set.ncard_le_ncard mult3Classes_subset cnt3Classes_finite

end Mult3Bridge

/-! ### The core centraliser (149)-(150) -/

namespace Mult3

open Module

section CoreCent

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The core centraliser `K = {v : B(v, U) = 0}` (149). -/
def coreCent (B : V →ₗ[F] V →ₗ[F] W) (U : Submodule F V) : Submodule F V where
  carrier := {v | ∀ u ∈ U, B v u = 0}
  add_mem' := by
    intro a b ha hb u hu
    rw [map_add, LinearMap.add_apply, ha u hu, hb u hu, add_zero]
  zero_mem' := by
    intro u _
    rw [map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c a ha u hu
    rw [map_smul, LinearMap.smul_apply, ha u hu, smul_zero]

lemma mem_coreCent {B : V →ₗ[F] V →ₗ[F] W} {U : Submodule F V} {v : V} :
    v ∈ coreCent B U ↔ ∀ u ∈ U, B v u = 0 := Iff.rfl

/-- An alternating bilinear map is skew. -/
lemma skew_of_alt (B : V →ₗ[F] V →ₗ[F] W) (hB : ∀ x, B x x = 0) (x y : V) :
    B x y = - B y x := by
  have h := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- (150), first part: for a Sims-minimal `U` (`B(U, U)` spans `W` and no subspace of smaller
dimension does), the core centraliser meets `U` trivially. -/
theorem coreCent_inf_eq_bot [FiniteDimensional F V] (B : V →ₗ[F] V →ₗ[F] W)
    (hB : ∀ x, B x x = 0) (U : Submodule F V) (hU : Alt2.GensLin B U)
    (hmin : ∀ U' : Submodule F V, Alt2.GensLin B U' → finrank F U ≤ finrank F U') :
    coreCent B U ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  obtain ⟨hvK, hvU⟩ := Submodule.mem_inf.mp hv
  have hvK' := mem_coreCent.mp hvK
  have hv'0 : (⟨v, hvU⟩ : U) ≠ 0 := by
    intro h
    apply hv0
    have := congrArg Subtype.val h
    exact this
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (F ∙ (⟨v, hvU⟩ : U))
  have hdim : finrank F (F ∙ (⟨v, hvU⟩ : U)) + finrank F C = finrank F U :=
    Submodule.finrank_add_eq_of_isCompl hC
  rw [finrank_span_singleton hv'0] at hdim
  have hU' : finrank F (C.map U.subtype) = finrank F C := Submodule.finrank_map_subtype_eq U C
  have hU'le : ∀ c ∈ C.map U.subtype, c ∈ U := by
    intro c hc
    obtain ⟨c', -, rfl⟩ := Submodule.mem_map.mp hc
    exact c'.2
  have hdec : ∀ x ∈ U, ∃ a : F, ∃ c ∈ C.map U.subtype, x = a • v + c := by
    intro x hx
    have hmem : (⟨x, hx⟩ : U) ∈ (F ∙ (⟨v, hvU⟩ : U)) ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨a, (c : V), Submodule.mem_map_of_mem hc, ?_⟩
    have := congrArg Subtype.val hyc
    rw [Submodule.coe_add, Submodule.coe_smul] at this
    exact this.symm
  have hsk : ∀ y ∈ U, B y v = 0 := by
    intro y hy
    rw [skew_of_alt B hB y v, hvK' y hy, neg_zero]
  have hG' : Alt2.GensLin B (C.map U.subtype) := by
    unfold Alt2.GensLin at hU ⊢
    rw [eq_top_iff, ← hU, Submodule.span_le]
    rintro w ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, c1, hc1, rfl⟩ := hdec x hx
    obtain ⟨b, c2, hc2, rfl⟩ := hdec y hy
    have e : B (a • v + c1) (b • v + c2) = B c1 c2 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hB v,
        hvK' c2 (hU'le c2 hc2), hsk c1 (hU'le c1 hc1), smul_zero, zero_add, add_zero]
    rw [e]
    exact Submodule.subset_span ⟨c1, hc1, c2, hc2, rfl⟩
  have := hmin _ hG'
  omega

/-- (150): `dim K + dim U ≤ dim V`, i.e. `dim K ≤ r1 - s`. -/
theorem finrank_coreCent_add_le [FiniteDimensional F V] (B : V →ₗ[F] V →ₗ[F] W)
    (hB : ∀ x, B x x = 0) (U : Submodule F V) (hU : Alt2.GensLin B U)
    (hmin : ∀ U' : Submodule F V, Alt2.GensLin B U' → finrank F U ≤ finrank F U') :
    finrank F (coreCent B U) + finrank F U ≤ finrank F V := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (coreCent B U) U
  rw [coreCent_inf_eq_bot B hB U hU hmin, finrank_bot] at h
  have h2 := Submodule.finrank_le (coreCent B U ⊔ U)
  omega

end CoreCent

/-! ### Proposition 13.1: the multiplicity of coefficient rows -/

section Prop131

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The leading core-free coefficients `(B(u_j, x_ℓ))_{ℓ, j}` of a tuple `x` of free generators
(the coordinates of `c(1, j, r1 - z + ℓ, 2, ·) mod p` in a basis of `W`). -/
def coreRow (B : V →ₗ[F] V →ₗ[F] W) {s z : ℕ} (u : Fin s → V) (x : Fin z → V) :
    Fin z → Fin s → W :=
  fun l j => B (u j) (x l)

/-- Proof of Proposition 13.1, first step: equal leading coefficients force `x_ℓ - y_ℓ ∈ K`. -/
theorem coreRow_eq_imp_sub_mem (B : V →ₗ[F] V →ₗ[F] W) (hB : ∀ x, B x x = 0) {s z : ℕ}
    (u : Fin s → V) {x y : Fin z → V} (h : coreRow B u x = coreRow B u y) (l : Fin z) :
    x l - y l ∈ coreCent B (Submodule.span F (Set.range u)) := by
  rw [mem_coreCent]
  have hle : Submodule.span F (Set.range u) ≤ LinearMap.ker (B (x l - y l)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : B (u j) (x l) = B (u j) (y l) := congrFun (congrFun h l) j
    show B (x l - y l) (u j) = 0
    rw [skew_of_alt B hB (x l - y l) (u j), map_sub, hj, sub_self, neg_zero]
  intro w hw
  exact LinearMap.mem_ker.mp (hle hw)

/-- Counting through fibres: `|α| ≤ |range f| · M` if every fibre has at most `M` points. -/
lemma card_le_card_range_mul {α β : Type*} [Finite α] (f : α → β) (M : ℕ)
    (h : ∀ a : α, Nat.card {a' : α // f a' = f a} ≤ M) :
    Nat.card α ≤ Nat.card (Set.range f) * M := by
  classical
  have := Fintype.ofFinite α
  have h1 := Finset.card_le_mul_card_image (f := f) (Finset.univ : Finset α) M (by
    intro b hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
    have e : (Finset.univ.filter fun x => f x = f a).card = Nat.card {a' : α // f a' = f a} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [e]
    exact h a)
  have e2 : Nat.card (Set.range f) = (Finset.univ.image f).card := by
    rw [show Set.range f = ((Finset.univ.image f : Finset β) : Set β) by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ], Nat.card_coe_set_eq,
      Set.ncard_coe_finset]
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  rw [e2, mul_comm]
  exact h1

/-- `q^(z (z - 1)) ≤ ∏_{i < z} (q^z - q^i)` for `q ≥ 2` (a crude form of (44)). -/
theorem pow_le_prod_gl {q : ℕ} (hq : 2 ≤ q) (z : ℕ) :
    q ^ (z * (z - 1)) ≤ ∏ i : Fin z, (q ^ z - q ^ (i : ℕ)) := by
  have key : ∀ A B X : ℕ, 2 * X ≤ A → B ≤ X → X ≤ A - B := by
    intro A B X h1 h2
    omega
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin z)), q ^ (z - 1) ≤ q ^ z - q ^ (i : ℕ) := by
    intro i _
    have h1 : q ^ (i : ℕ) ≤ q ^ (z - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : q ^ z = q * q ^ (z - 1) := by
      rw [← pow_succ']
      congr 1
      have := i.2
      omega
    have h3 : 2 * q ^ (z - 1) ≤ q * q ^ (z - 1) := Nat.mul_le_mul_right _ hq
    exact key _ _ _ (h2 ▸ h3) h1
  calc q ^ (z * (z - 1)) = ∏ _i : Fin z, q ^ (z - 1) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    _ ≤ ∏ i : Fin z, (q ^ z - q ^ (i : ℕ)) := Finset.prod_le_prod' hi

/-- The ordered bases of a `z`-dimensional space: at least `q^(z (z - 1))` of them. -/
theorem card_bases_ge [Fintype F] [Finite V] (Z : Submodule F V) :
    Nat.card F ^ (finrank F Z * (finrank F Z - 1)) ≤
      Nat.card {x : Fin (finrank F Z) → Z // LinearIndependent F x} := by
  rw [card_linearIndependent (K := F) (V := Z) (k := finrank F Z) le_rfl,
    Nat.card_eq_fintype_card]
  exact pow_le_prod_gl (Fintype.one_lt_card) _

/-- Proposition 13.1 (linear-algebra core): as the free generators run over the ordered bases
of `Z0`, the leading core-free coefficient rows take at least `q^(z (z - 1) - z dim K)` values,
`z = dim Z0`, in the multiplicative form `q^(z (z - 1)) ≤ #rows · q^(z dim K)`. -/
theorem prop_13_1_count [Fintype F] [Finite V] [FiniteDimensional F V]
    (B : V →ₗ[F] V →ₗ[F] W) (hB : ∀ x, B x x = 0) {s : ℕ} (u : Fin s → V)
    (Z : Submodule F V) :
    Nat.card F ^ (finrank F Z * (finrank F Z - 1)) ≤
      Nat.card (Set.range (fun x : {x : Fin (finrank F Z) → Z // LinearIndependent F x} =>
        coreRow B u (fun l => (x.1 l : V)))) *
        Nat.card F ^ (finrank F Z * finrank F (coreCent B (Submodule.span F (Set.range u)))) := by
  set K := coreCent B (Submodule.span F (Set.range u))
  set f := fun x : {x : Fin (finrank F Z) → Z // LinearIndependent F x} =>
    coreRow B u (fun l => (x.1 l : V))
  have hfib : ∀ a, Nat.card {a' // f a' = f a} ≤ Nat.card F ^ (finrank F Z * finrank F K) := by
    intro a
    let g : {a' // f a' = f a} → (Fin (finrank F Z) → K) := fun y l =>
      ⟨(y.1.1 l : V) - (a.1 l : V), coreRow_eq_imp_sub_mem B hB u y.2 l⟩
    have hg : Function.Injective g := by
      intro y y' hyy
      apply Subtype.ext
      apply Subtype.ext
      funext l
      have h1 := congrArg Subtype.val (congrFun hyy l)
      have h2 : (y.1.1 l : V) = (y'.1.1 l : V) := sub_left_injective h1
      exact Subtype.ext h2
    calc Nat.card {a' // f a' = f a} ≤ Nat.card (Fin (finrank F Z) → K) :=
          Nat.card_le_card_of_injective g hg
      _ = Nat.card F ^ (finrank F Z * finrank F K) := by
          rw [Nat.card_fun, Nat.card_fin, Module.natCard_eq_pow_finrank (K := F) (V := K),
            ← pow_mul, mul_comm]
  exact (card_bases_ge Z).trans (card_le_card_range_mul f _ hfib)

end Prop131

/-! ### Remark 6.4 and Proposition 13.2: savings from prescribed affine equations -/

section Rem64

variable {F X Y : Type*} [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

/-- Remark 6.4 (linear-algebra core): an affine system `T x = c` of rank `ρ = dim (range T)` on
an `n`-dimensional space of freely counted coefficients has at most `q^(n - ρ)` solutions, so `ρ`
may be subtracted from the exponent. -/
theorem rem_6_4_fiber [Finite F] [Finite X] [FiniteDimensional F X] (T : X →ₗ[F] Y) (c : Y) :
    Nat.card {x : X // T x = c} ≤
      Nat.card F ^ (finrank F X - finrank F (LinearMap.range T)) := by
  by_cases hne : ∃ x0, T x0 = c
  · obtain ⟨x0, hx0⟩ := hne
    let g : {x : X // T x = c} → LinearMap.ker T := fun x =>
      ⟨x.1 - x0, by rw [LinearMap.mem_ker, map_sub, x.2, hx0, sub_self]⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      apply Subtype.ext
      exact sub_left_injective (congrArg Subtype.val hxx)
    have hrk := LinearMap.finrank_range_add_finrank_ker T
    calc Nat.card {x : X // T x = c} ≤ Nat.card (LinearMap.ker T) :=
          Nat.card_le_card_of_injective g hg
      _ = Nat.card F ^ finrank F (LinearMap.ker T) :=
          Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker T)
      _ = Nat.card F ^ (finrank F X - finrank F (LinearMap.range T)) := by
          congr 1
          omega
  · push Not at hne
    have : IsEmpty {x : X // T x = c} := ⟨fun x => hne x.1 x.2⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- Proposition 13.2 (linear-algebra core): the linear maps `X → Y` with prescribed values on a
`k`-dimensional subspace `K'` number at most `|Y|^(dim X - k)` (with `Y = W^s`, the core-outside
leading values `β(v_j, ·)`, the saving is `s k r2`). -/
theorem prop_13_2_fiber [Finite Y] [FiniteDimensional F X] (K' : Submodule F X)
    (g : X →ₗ[F] Y) :
    Nat.card {f : X →ₗ[F] Y // ∀ x ∈ K', f x = g x} ≤
      Nat.card Y ^ (finrank F X - finrank F K') := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K'
  have hdim : finrank F K' + finrank F C = finrank F X := Submodule.finrank_add_eq_of_isCompl hC
  let b := Module.finBasis F C
  let Ψ : {f : X →ₗ[F] Y // ∀ x ∈ K', f x = g x} → (Fin (finrank F C) → Y) :=
    fun f i => f.1 (b i : X)
  have hΨ : Function.Injective Ψ := by
    intro f1 f2 h12
    apply Subtype.ext
    have hC0 : (f1.1 - f2.1).comp C.subtype = 0 := by
      apply b.ext
      intro i
      have := congrFun h12 i
      rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply, Submodule.subtype_apply]
      exact sub_eq_zero.mpr this
    have hle : K' ⊔ C ≤ LinearMap.ker (f1.1 - f2.1) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [LinearMap.mem_ker, LinearMap.sub_apply, f1.2 x hx, f2.2 x hx, sub_self]
      · intro x hx
        rw [LinearMap.mem_ker]
        have := LinearMap.congr_fun hC0 ⟨x, hx⟩
        rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply] at this
        exact this
    rw [hC.sup_eq_top] at hle
    apply LinearMap.ext
    intro x
    have hx := hle (Submodule.mem_top (x := x))
    rw [LinearMap.mem_ker, LinearMap.sub_apply] at hx
    exact sub_eq_zero.mp hx
  calc Nat.card {f : X →ₗ[F] Y // ∀ x ∈ K', f x = g x} ≤ Nat.card (Fin (finrank F C) → Y) :=
        Nat.card_le_card_of_injective Ψ hΨ
    _ = Nat.card Y ^ (finrank F X - finrank F K') := by
        rw [Nat.card_fun, Nat.card_fin]
        congr 1
        omega

end Rem64

/-! ### The arithmetic of Corollary 14.1 -/

section Cor141

/-- (152): `0 ≤ r1^2 - z^2 ≤ 2 r1 (s + δ)` when `r1 - s - δ ≤ z ≤ r1`. -/
theorem cor_14_1_dim_bound {r1 s δ z : ℕ} (hz : z ≤ r1) (hz' : r1 ≤ z + s + δ) :
    0 ≤ (r1 : ℤ) ^ 2 - (z : ℤ) ^ 2 ∧ (r1 : ℤ) ^ 2 - (z : ℤ) ^ 2 ≤ 2 * r1 * (s + δ) := by
  have h0 : (z : ℤ) ≤ r1 := by exact_mod_cast hz
  have h0' : (r1 : ℤ) ≤ z + s + δ := by exact_mod_cast hz'
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hs0 : (0 : ℤ) ≤ (s : ℤ) + δ := by positivity
  constructor
  · nlinarith
  · have h1 : ((r1 : ℤ) - z) * (r1 + z) ≤ ((s : ℤ) + δ) * (r1 + z) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : ((s : ℤ) + δ) * (r1 + z) ≤ ((s : ℤ) + δ) * (2 * r1) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    nlinarith [h1, h2]

/-- The division step of Corollary 14.1 (with Proposition 2.4): if each of the classes in `S`
produces at least `T` array pairs, pairs of distinct classes are distinct (rigidity), and all of
them lie among `E` counted pairs, then `#S · T ≤ #E`. -/
theorem cor_14_1_div {ι α : Type*} [DecidableEq α] (S : Finset ι) (P : ι → Finset α)
    (hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (P x) (P y)) (E : Finset α)
    (hsub : ∀ i ∈ S, P i ⊆ E) (T : ℕ) (hT : ∀ i ∈ S, T ≤ (P i).card) :
    S.card * T ≤ E.card := by
  calc S.card * T = ∑ _i ∈ S, T := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ S, (P i).card := Finset.sum_le_sum hT
    _ = (S.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ E.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-- The exponent of (153): the saving of Proposition 13.2 (`k (r1 - k)` subspaces `K`, each
imposing `s k r2` conditions) minus the multiplicity `z^2 - z k` of Proposition 13.1. -/
theorem mult3_exponent_eq (r1 r2 s z k : ℝ) :
    (k * (r1 - k) - s * k * r2) - (z ^ 2 - z * k) = - z ^ 2 + k * (r1 + z - k - s * r2) := by
  ring

end Cor141

end Mult3

/-! ### The group-level core centraliser -/

namespace Mult3

open Module

section GroupCore

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G]

/-- The image in `V` of a tuple `u` of elements of `G`. -/
def coreImg {k : ℕ} (u : Fin k → G) : Submodule (ZMod p) (Additive (VQ p G)) :=
  Submodule.span (ZMod p) (Set.range (fun i => Additive.ofMul (piV p G (u i))))

lemma lamLin_alt (x : Additive (VQ p G)) : lamLin (p := p) (G := G) x x = 0 := lamLin_self x

lemma piV_mem_coreImg {k : ℕ} (u : Fin k → G) {h : G}
    (hh : h ∈ Subgroup.closure (Set.range u)) :
    Additive.ofMul (piV p G h) ∈ coreImg (p := p) u := by
  have hle : Subgroup.closure (Set.range u) ≤ Alt2.preV (p := p) (coreImg (p := p) u) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hle hh

/-- The inline condition of `mult3Set`: `[g, h] ∈ γ_3 γ_2^p` for all `h ∈ H = ⟨u⟩` iff the image
of `g` in `V` lies in the core centraliser of `U = image of H`. -/
theorem mem_coreCent_lamLin_iff {k : ℕ} (u : Fin k → G) (g : G) :
    (∀ h ∈ Subgroup.closure (Set.range u), ⁅g, h⁆ ∈ pN p G) ↔
      Additive.ofMul (piV p G g) ∈ coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u) := by
  constructor
  · intro hg
    rw [mem_coreCent]
    have hle : coreImg (p := p) u ≤
        LinearMap.ker (lamLin (p := p) (G := G) (Additive.ofMul (piV p G g))) := by
      unfold coreImg
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show Additive.ofMul (piV p G (u i)) ∈
        LinearMap.ker (lamLin (p := p) (G := G) (Additive.ofMul (piV p G g)))
      rw [LinearMap.mem_ker, lamLin_mk,
        piW_eq_one_of (a := cw g (u i)) (hg (u i) (Subgroup.subset_closure ⟨i, rfl⟩))]
      rfl
    intro w hw
    exact LinearMap.mem_ker.mp (hle hw)
  · intro hg h hh
    have h0 := (mem_coreCent.mp hg) _ (piV_mem_coreImg (p := p) u hh)
    rw [lamLin_mk] at h0
    have h1 : piW p G (cw g h) = 1 := congrArg Additive.toMul h0
    have h2 : cw g h ∈ (piW p G).ker := MonoidHom.mem_ker.mpr h1
    rw [ker_piW, Subgroup.mem_subgroupOf] at h2
    exact h2

/-- (150) at group level: for a Sims core `H = ⟨u_0, ..., u_{s-1}⟩` with `s = simsRank G`, the
core centraliser meets the core image trivially. -/
theorem group_coreCent_inf_eq_bot [Finite G] (hG : IsPGroup p G) {k : ℕ} (u : Fin k → G)
    (hcore : lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
      lcs G 2) (hk : k = simsRank G) :
    coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u) ⊓ coreImg (p := p) u = ⊥ ∧
      finrank (ZMod p) (coreImg (p := p) u) = k := by
  have : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have : Finite (Additive (VQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (VQ p G)) := inferInstance
  have hgen : Alt2.GensLin (lamLin (p := p) (G := G)) (coreImg (p := p) u) :=
    Alt2.gensLin_of_core (p := p) u hcore
  have hlow : ∀ U' : Submodule (ZMod p) (Additive (VQ p G)),
      Alt2.GensLin (lamLin (p := p) (G := G)) U' → k ≤ finrank (ZMod p) U' := by
    intro U' hU'
    rw [hk, ← Alt2.simsRkLin_lamLin (p := p) hG]
    exact Nat.sInf_le ⟨U', rfl, hU'⟩
  have hup : finrank (ZMod p) (coreImg (p := p) u) ≤ k := by
    have h2 : finrank (ZMod p) (coreImg (p := p) u) ≤ Fintype.card (Fin k) :=
      finrank_range_le_card (fun i => Additive.ofMul (piV p G (u i)))
    rw [Fintype.card_fin] at h2
    exact h2
  have heq : finrank (ZMod p) (coreImg (p := p) u) = k := le_antisymm hup (hlow _ hgen)
  refine ⟨coreCent_inf_eq_bot _ lamLin_alt _ hgen ?_, heq⟩
  intro U' hU'
  rw [heq]
  exact hlow U' hU'

/-- (150) at group level: `dim K ≤ r1 - s`. -/
theorem group_finrank_coreCent_le [Finite G] (hG : IsPGroup p G) {k : ℕ} (u : Fin k → G)
    (hcore : lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
      lcs G 2) (hk : k = simsRank G) :
    finrank (ZMod p) (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)) + simsRank G ≤
      Group.rank G := by
  have : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have : Finite (Additive (VQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (VQ p G)) := inferInstance
  obtain ⟨hbot, hdim⟩ := group_coreCent_inf_eq_bot hG u hcore hk
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)) (coreImg (p := p) u)
  rw [hbot, finrank_bot, hdim] at h
  have h2 := Submodule.finrank_le
    (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u) ⊔ coreImg (p := p) u)
  rw [finrank_V hG] at h2
  omega

/-- The core centraliser as a subgroup of `V` (multiplicative form). -/
def coreCentSub {k : ℕ} (u : Fin k → G) : Subgroup (VQ p G) where
  carrier := {x | Additive.ofMul x ∈ coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)}
  mul_mem' := by
    intro a b ha hb
    exact (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)).add_mem ha hb
  one_mem' := (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)).zero_mem
  inv_mem' := by
    intro a ha
    exact (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)).neg_mem ha

/-- The inline order condition of `mult3Set`:
`|{g : [g, H] ⊆ γ_3 γ_2^p}| · p^r1 = p^(dim K) |G|`. -/
theorem card_coreCent_pre [Finite G] (hG : IsPGroup p G) {k : ℕ} (u : Fin k → G) :
    Nat.card {g : G // ∀ h ∈ Subgroup.closure (Set.range u), ⁅g, h⁆ ∈ pN p G} *
        p ^ Group.rank G =
      p ^ finrank (ZMod p) (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)) *
        Nat.card G := by
  have : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have : Finite (Additive (VQ p G)) := inferInstance
  have : Module.Finite (ZMod p) (Additive (VQ p G)) := inferInstance
  set KS := coreCentSub (p := p) u
  have e1 : Nat.card {g : G // ∀ h ∈ Subgroup.closure (Set.range u), ⁅g, h⁆ ∈ pN p G} =
      Nat.card (KS.comap (piV p G)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (q := fun g => g ∈ KS.comap (piV p G))
      (fun g => (mem_coreCent_lamLin_iff (p := p) u g).trans Iff.rfl))
  have e2 := Subgroup.card_mul_index (KS.comap (piV p G))
  have e3 : (KS.comap (piV p G)).index = KS.index :=
    Subgroup.index_comap_of_surjective (H := KS) piV_surjective
  have e4 := Subgroup.card_mul_index KS
  rw [card_V hG] at e4
  let eK : KS ≃ coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u) :=
    { toFun := fun x => ⟨Additive.ofMul x.1, x.2⟩
      invFun := fun x => ⟨Additive.toMul x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e5 : Nat.card KS =
      p ^ finrank (ZMod p) (coreCent (lamLin (p := p) (G := G)) (coreImg (p := p) u)) := by
    rw [Nat.card_congr eK, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [e1, ← e4, e5, ← e2, e3]
  ring

end GroupCore

section Mult3Group

variable {m r1 r2 s lam m2 m3 r3 z k : ℕ}

/-- (150) on `mult3Set`: the parameter `k` is the dimension of the core centraliser of a Sims
core, and `k + s ≤ r1`. -/
theorem mult3_k_add_s_le {G : FiniteGrp.{0}} (hG : G ∈ mult3Set m r1 r2 s lam m2 m3 r3 z k) :
    k + s ≤ r1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, H, hH, hrk, hK, -⟩ := hG
  obtain ⟨hcard, -, -, hr1, -, hs, -⟩ := (mem_cnt3Set_iff G).mp hc
  have hP : IsPGroup 2 G := IsPGroup.of_card hcard
  obtain ⟨x, hx⟩ := exists_enum_closure H
  let u : Fin s → G := fun i => x i.val
  have hu : Subgroup.closure (Set.range u) = H := by
    have e : Set.range u = x '' Set.Iio (Group.rank H) := by
      rw [hrk]
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.isLt, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [e, hx]
  have hcore : lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
      lcs G 2 := by
    rw [hu]
    exact hH.le
  have hk' := group_finrank_coreCent_le hP u hcore hs.symm
  have hcardK := card_coreCent_pre hP u
  rw [hu, hr1] at hcardK
  have heq : 2 ^ k * Nat.card G = 2 ^ finrank (ZMod 2)
      (coreCent (lamLin (p := 2) (G := G)) (coreImg (p := 2) u)) * Nat.card G :=
    hK.symm.trans hcardK
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h2 := Nat.eq_of_mul_eq_mul_right hpos heq
  have h3 := Nat.pow_right_injective (le_refl 2) h2
  rw [hr1, hs] at hk'
  omega

end Mult3Group

/-! ### The summand `Z0` of Section 13.1: existence and the dimension bounds

`max (0, r1 - s - lam) ≤ dim Z0 ≤ r1 - s` (Section 13.1, after (148)). The construction runs in
`Ω = {x ∈ G^ab : x^p = 1}`, an `F_p`-space mapping linearly to `V` (`omPsi`): a complement `Z` of
`omPsi⁻¹ (U)` (`U` the core image) maps injectively to `V`, avoiding `U`, and has dimension
`≥ r1 - s - lam` since `|Ω| ≥ p^r1` and `|ker omPsi| ≤ |G^ab : ...| = p^lam`. Then `A` is the preimage
of `Z` in `G`, and `B` the preimage in `G` of a complement of `omPsi (Z)` in `V` containing `U`. -/

section Summand

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G]

lemma abel_of_surjective : Function.Surjective (Abelianization.of : G →* Abelianization G) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x : G ⧸ commutator G)
  exact ⟨g, hg⟩

lemma abel_of_eq_one_iff {g : G} : Abelianization.of g = 1 ↔ g ∈ lcs G 1 := by
  rw [← MonoidHom.mem_ker, Abelianization.ker_of, commutator_eq_lcs_one]

lemma piV_eq_one_of_mem_lcs {g : G} (hg : g ∈ lcs G 1) : piV p G g = 1 := by
  rw [← MonoidHom.mem_ker, ker_piV]
  exact commutator_le_pPhi (p := p) (G := G) (by rw [commutator_eq_lcs_one]; exact hg)

lemma card_abel_eq_index : Nat.card (Abelianization G) = (lcs G 1).index :=
  (rfl : Nat.card (Abelianization G) = (commutator G).index).trans
    (congrArg Subgroup.index commutator_eq_lcs_one)

/-- `Ω = {x ∈ G^ab : x^p = 1}`. -/
abbrev omQ (p : ℕ) (G : Type u) [Group G] : Subgroup (Abelianization G) :=
  (powMonoidHom p : Abelianization G →* Abelianization G).ker

lemma omQ_pow (x : omQ p G) : (x : Abelianization G) ^ p = 1 := MonoidHom.mem_ker.mp x.2

lemma omQ_nsmul (x : Additive (omQ p G)) : p • x = 0 := by
  show Additive.ofMul (Additive.toMul x ^ p) = Additive.ofMul 1
  have h : Additive.toMul x ^ p = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact omQ_pow _)
  rw [h]

/-- `Ω` is an `F_p`-vector space. -/
instance omQ_module : Module (ZMod p) (Additive (omQ p G)) :=
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  AddCommGroup.zmodModule omQ_nsmul

/-- The linear map `Ω → V = G^ab ⧸ Φ(G)^ab`. -/
def omPsi : Additive (omQ p G) →ₗ[ZMod p] Additive (VQ p G) :=
  AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive
    ((QuotientGroup.mk' (elemK p G (pPhi p G))).comp (omQ p G).subtype))

lemma omPsi_apply (x : Additive (omQ p G)) :
    omPsi x = Additive.ofMul (QuotientGroup.mk' (elemK p G (pPhi p G))
      ((Additive.toMul x : omQ p G) : Abelianization G)) := rfl

lemma omPsi_of {w : Additive (omQ p G)} {g : G}
    (h : ((Additive.toMul w : omQ p G) : Abelianization G) = Abelianization.of g) :
    omPsi w = Additive.ofMul (piV p G g) :=
  (omPsi_apply w).trans
    (congrArg (fun y => Additive.ofMul (QuotientGroup.mk' (elemK p G (pPhi p G)) y)) h)

/-- The subgroup of `G^ab` underlying a subspace of `Ω`. -/
def omSubQ (Z : Submodule (ZMod p) (Additive (omQ p G))) : Subgroup (Abelianization G) where
  carrier := {x | ∃ w ∈ Z, ((Additive.toMul w : omQ p G) : Abelianization G) = x}
  mul_mem' := by
    rintro _ _ ⟨w1, h1, rfl⟩ ⟨w2, h2, rfl⟩
    exact ⟨w1 + w2, Z.add_mem h1 h2, rfl⟩
  one_mem' := ⟨0, Z.zero_mem, rfl⟩
  inv_mem' := by
    rintro _ ⟨w, h, rfl⟩
    exact ⟨-w, Z.neg_mem h, rfl⟩

lemma mem_omSubQ {Z : Submodule (ZMod p) (Additive (omQ p G))} {x : Abelianization G} :
    x ∈ omSubQ Z ↔ ∃ w ∈ Z, ((Additive.toMul w : omQ p G) : Abelianization G) = x := Iff.rfl

/-- The subgroup of `V` underlying a subspace. -/
def vSub (C : Submodule (ZMod p) (Additive (VQ p G))) : Subgroup (VQ p G) where
  carrier := {v | Additive.ofMul v ∈ C}
  mul_mem' := by
    intro a b ha hb
    exact C.add_mem ha hb
  one_mem' := C.zero_mem
  inv_mem' := by
    intro a ha
    exact C.neg_mem ha

lemma mem_vSub {C : Submodule (ZMod p) (Additive (VQ p G))} {v : VQ p G} :
    v ∈ vSub C ↔ Additive.ofMul v ∈ C := Iff.rfl

/-- The image in `V` of a subgroup of `G`, as a subspace. -/
def imgSub (K : Subgroup G) : Submodule (ZMod p) (Additive (VQ p G)) where
  carrier := {x | ∃ b ∈ K, Additive.ofMul (piV p G b) = x}
  add_mem' := by
    rintro _ _ ⟨b1, h1, rfl⟩ ⟨b2, h2, rfl⟩
    exact ⟨b1 * b2, K.mul_mem h1 h2, by rw [map_mul, ofMul_mul]⟩
  zero_mem' := ⟨1, K.one_mem, by rw [map_one, ofMul_one]⟩
  smul_mem' := by
    rintro c _ ⟨b, hb, rfl⟩
    refine ⟨b ^ c.val, K.pow_mem hb _, ?_⟩
    rw [elemQ_smul_eq_nsmul, map_pow, ofMul_pow]

lemma mem_imgSub {K : Subgroup G} {x : Additive (VQ p G)} :
    x ∈ imgSub (p := p) K ↔ ∃ b ∈ K, Additive.ofMul (piV p G b) = x := Iff.rfl

lemma card_abel_eq_mul [Finite G] :
    Nat.card (Abelianization G) = Nat.card (VQ p G) * Nat.card (elemK p G (pPhi p G)) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

/-- `|G^ab| ≤ |(G^ab)^p ...| · |Ω|`, through the `p`-power map. -/
lemma card_abel_le_omQ [Finite G] :
    Nat.card (Abelianization G) ≤ Nat.card (elemK p G (pPhi p G)) * Nat.card (omQ p G) := by
  haveI : Finite (Abelianization G) := Finite.of_surjective _ abel_of_surjective
  have h := card_le_card_range_mul (fun x : Abelianization G => x ^ p) (Nat.card (omQ p G)) (by
    intro a
    let g : {a' : Abelianization G // a' ^ p = a ^ p} → omQ p G := fun y =>
      ⟨y.1 * a⁻¹, by
        rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_pow, inv_pow, y.2, mul_inv_cancel]⟩
    have hg : Function.Injective g := by
      intro y y' hyy
      apply Subtype.ext
      have h1 : y.1 * a⁻¹ = y'.1 * a⁻¹ := congrArg Subtype.val hyy
      exact mul_right_cancel h1
    exact Nat.card_le_card_of_injective g hg)
  have hsub : Set.range (fun x : Abelianization G => x ^ p) ⊆
      ((elemK p G (pPhi p G) : Subgroup (Abelianization G)) : Set (Abelianization G)) := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hr : Nat.card (Set.range (fun x : Abelianization G => x ^ p)) ≤
      Nat.card ((elemK p G (pPhi p G) : Subgroup (Abelianization G)) : Set (Abelianization G)) :=
    Nat.card_mono (Set.toFinite _) hsub
  exact h.trans (Nat.mul_le_mul_right _ hr)

lemma card_ker_omPsi_le [Finite G] :
    Nat.card (LinearMap.ker (omPsi (p := p) (G := G))) ≤ Nat.card (elemK p G (pPhi p G)) := by
  haveI : Finite (Abelianization G) := Finite.of_surjective _ abel_of_surjective
  let g : LinearMap.ker (omPsi (p := p) (G := G)) → elemK p G (pPhi p G) := fun w =>
    ⟨((Additive.toMul w.1 : omQ p G) : Abelianization G), by
      have h0 : omPsi (p := p) (G := G) w.1 = 0 := LinearMap.mem_ker.mp w.2
      have h1 : ((((Additive.toMul w.1 : omQ p G) : Abelianization G)) :
          Abelianization G ⧸ elemK p G (pPhi p G)) = 1 := congrArg Additive.toMul h0
      exact (QuotientGroup.eq_one_iff _).mp h1⟩
  have hg : Function.Injective g := by
    intro w w' h
    apply Subtype.ext
    have h1 : ((Additive.toMul w.1 : omQ p G) : Abelianization G) =
        ((Additive.toMul w'.1 : omQ p G) : Abelianization G) := congrArg Subtype.val h
    exact Additive.toMul.injective (Subtype.ext h1)
  exact Nat.card_le_card_of_injective g hg

/-- A subgroup of rank `s` is generated by an `s`-tuple. -/
lemma exists_fin_enum [Finite G] (H : Subgroup G) {s : ℕ} (hrk : Group.rank H = s) :
    ∃ u : Fin s → G, Subgroup.closure (Set.range u) = H := by
  obtain ⟨x, hx⟩ := exists_enum_closure H
  refine ⟨fun i => x i.val, ?_⟩
  have e : Set.range (fun i : Fin s => x i.val) = x '' Set.Iio (Group.rank H) := by
    rw [hrk]
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [e, hx]

/-- Section 13.1: existence of the summand `Z0`. For any subspace `U` of `V` of dimension `≤ t`
there is a decomposition `G/γ_2 = A/γ_2 ⊕ B/γ_2`, `A/γ_2` elementary abelian of order `p^z` with
`r1 ≤ z + t + lam`, such that `B` contains every element whose image in `V` lies in `U`. -/
theorem exists_summand [Finite G] (hG : IsPGroup p G)
    (U : Submodule (ZMod p) (Additive (VQ p G))) {r1 lam t : ℕ} (hr1 : Group.rank G = r1)
    (hidx : (lcs G 1).index = p ^ (r1 + lam)) (hU : finrank (ZMod p) U ≤ t) :
    ∃ A B : Subgroup G, lcs G 1 ≤ A ∧ lcs G 1 ≤ B ∧ A ⊓ B = lcs G 1 ∧ A ⊔ B = ⊤ ∧
      (∀ g : G, Additive.ofMul (piV p G g) ∈ U → g ∈ B) ∧ (∀ a ∈ A, a ^ p ∈ lcs G 1) ∧
      ∃ z : ℕ, r1 ≤ z + t + lam ∧ Nat.card A = p ^ z * Nat.card (lcs G 1) := by
  haveI : Finite (Abelianization G) := Finite.of_surjective _ abel_of_surjective
  haveI : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have hp2 : 2 ≤ p := hp.out.two_le
  have hppos : 0 < p := hp.out.pos
  -- the orders
  have hQ : Nat.card (Abelianization G) = p ^ (r1 + lam) := card_abel_eq_index.trans hidx
  have hV : Nat.card (VQ p G) = p ^ r1 := by rw [card_V hG, hr1]
  have hK : Nat.card (elemK p G (pPhi p G)) = p ^ lam := by
    have h := card_abel_eq_mul (p := p) (G := G)
    rw [hQ, hV, pow_add] at h
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hppos _) h).symm
  have hX : p ^ r1 ≤ Nat.card (Additive (omQ p G)) := by
    have h := card_abel_le_omQ (p := p) (G := G)
    rw [hQ, hK, pow_add, mul_comm (p ^ r1)] at h
    exact Nat.le_of_mul_le_mul_left h (pow_pos hppos _)
  have hfX : Nat.card (Additive (omQ p G)) = p ^ finrank (ZMod p) (Additive (omQ p G)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hrX : r1 ≤ finrank (ZMod p) (Additive (omQ p G)) := by
    rw [hfX] at hX
    exact pow_le_pow_cancel hp2 hX
  -- the complement `Z` of `T = omPsi⁻¹ (U)`
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (U.comap (omPsi (p := p) (G := G)))
  have hZT := Submodule.finrank_add_eq_of_isCompl hZ
  have hTcard : Nat.card (U.comap (omPsi (p := p) (G := G))) ≤
      Nat.card U * Nat.card (LinearMap.ker (omPsi (p := p) (G := G))) := by
    have h := card_le_card_range_mul (fun x : U.comap (omPsi (p := p) (G := G)) => omPsi x.1)
      (Nat.card (LinearMap.ker (omPsi (p := p) (G := G)))) (by
        intro a
        let g : {a' : U.comap (omPsi (p := p) (G := G)) // omPsi a'.1 = omPsi a.1} →
            LinearMap.ker (omPsi (p := p) (G := G)) := fun y =>
          ⟨y.1.1 - a.1, by rw [LinearMap.mem_ker, map_sub, y.2, sub_self]⟩
        have hg : Function.Injective g := by
          intro y y' hyy
          have h1 : y.1.1 - a.1 = y'.1.1 - a.1 := congrArg Subtype.val hyy
          exact Subtype.ext (Subtype.ext (sub_left_injective h1))
        exact Nat.card_le_card_of_injective g hg)
    have hsub : Set.range (fun x : U.comap (omPsi (p := p) (G := G)) => omPsi x.1) ⊆
        (U : Set (Additive (VQ p G))) := by
      rintro _ ⟨x, rfl⟩
      exact x.2
    have hr : Nat.card (Set.range (fun x : U.comap (omPsi (p := p) (G := G)) => omPsi x.1)) ≤
        Nat.card (U : Set (Additive (VQ p G))) := Nat.card_mono (Set.toFinite _) hsub
    exact h.trans (Nat.mul_le_mul_right _ hr)
  have hfT : Nat.card (U.comap (omPsi (p := p) (G := G))) =
      p ^ finrank (ZMod p) (U.comap (omPsi (p := p) (G := G))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hfU : Nat.card U = p ^ finrank (ZMod p) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hU' : Nat.card U ≤ p ^ t := by
    rw [hfU]
    exact Nat.pow_le_pow_right hppos hU
  have hTle : finrank (ZMod p) (U.comap (omPsi (p := p) (G := G))) ≤ t + lam := by
    have h1 : Nat.card (U.comap (omPsi (p := p) (G := G))) ≤ p ^ t * p ^ lam :=
      hTcard.trans (Nat.mul_le_mul hU' ((card_ker_omPsi_le (p := p) (G := G)).trans hK.le))
    rw [hfT, ← pow_add] at h1
    exact pow_le_pow_cancel hp2 h1
  have hz : r1 ≤ finrank (ZMod p) Z + t + lam := by omega
  have hZinj : ∀ w ∈ Z, omPsi (p := p) (G := G) w ∈ U → w = 0 := by
    intro w hw hwU
    have hmem : w ∈ U.comap (omPsi (p := p) (G := G)) ⊓ Z := Submodule.mem_inf.mpr ⟨hwU, hw⟩
    rw [hZ.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  have hZU : Z.map (omPsi (p := p) (G := G)) ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv1
    rw [hZinj w hw hv2, map_zero]
    exact Submodule.zero_mem _
  -- the complement `C = U ⊔ C0` of `omPsi (Z)` containing `U`
  obtain ⟨C0, hC0⟩ := Submodule.exists_isCompl (Z.map (omPsi (p := p) (G := G)) ⊔ U)
  have hsup : Z.map (omPsi (p := p) (G := G)) ⊔ (U ⊔ C0) = ⊤ := by
    rw [← sup_assoc]
    exact hC0.sup_eq_top
  have hinf : Z.map (omPsi (p := p) (G := G)) ⊓ (U ⊔ C0) = ⊥ := by
    have d1 := Submodule.finrank_sup_add_finrank_inf_eq (Z.map (omPsi (p := p) (G := G))) U
    rw [hZU, finrank_bot] at d1
    have d2 := Submodule.finrank_add_eq_of_isCompl hC0
    have d3 := Submodule.finrank_sup_add_finrank_inf_eq U C0
    have d4 := Submodule.finrank_sup_add_finrank_inf_eq (Z.map (omPsi (p := p) (G := G)))
      (U ⊔ C0)
    rw [hsup, finrank_top] at d4
    rw [← Submodule.finrank_eq_zero]
    omega
  -- the subgroups `A` and `B`
  have hA1 : lcs G 1 ≤ (omSubQ Z).comap Abelianization.of := by
    intro g hg
    exact Subgroup.mem_comap.mpr (mem_omSubQ.mpr ⟨0, Z.zero_mem, (abel_of_eq_one_iff.mpr hg).symm⟩)
  have hB1 : lcs G 1 ≤ (vSub (U ⊔ C0)).comap (piV p G) := by
    intro g hg
    apply Subgroup.mem_comap.mpr
    apply mem_vSub.mpr
    rw [piV_eq_one_of_mem_lcs hg, ofMul_one]
    exact Submodule.zero_mem _
  refine ⟨(omSubQ Z).comap Abelianization.of, (vSub (U ⊔ C0)).comap (piV p G), hA1, hB1,
    ?_, ?_, ?_, ?_, finrank (ZMod p) Z, hz, ?_⟩
  · -- `A ⊓ B = γ_2`
    refine le_antisymm ?_ (le_inf hA1 hB1)
    intro g hg
    obtain ⟨hgA, hgB⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨w, hw, hwg⟩ := mem_omSubQ.mp (Subgroup.mem_comap.mp hgA)
    have hψ : omPsi w = Additive.ofMul (piV p G g) := omPsi_of hwg
    have hgB' : Additive.ofMul (piV p G g) ∈ U ⊔ C0 := mem_vSub.mp (Subgroup.mem_comap.mp hgB)
    have hψC : omPsi w ∈ U ⊔ C0 := by
      rw [hψ]
      exact hgB'
    have hmem : omPsi w ∈ Z.map (omPsi (p := p) (G := G)) ⊓ (U ⊔ C0) :=
      Submodule.mem_inf.mpr ⟨Submodule.mem_map_of_mem hw, hψC⟩
    rw [hinf, Submodule.mem_bot] at hmem
    have hw0 : w = 0 := hZinj w hw (by rw [hmem]; exact U.zero_mem)
    have h1 : Abelianization.of g = 1 := by
      have h2 := hwg
      subst hw0
      exact h2.symm
    exact abel_of_eq_one_iff.mp h1
  · -- `A ⊔ B = G`
    rw [eq_top_iff]
    intro g _
    have hv : Additive.ofMul (piV p G g) ∈ Z.map (omPsi (p := p) (G := G)) ⊔ (U ⊔ C0) := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha⟩ := abel_of_surjective ((Additive.toMul w : omQ p G) : Abelianization G)
    have haA : a ∈ (omSubQ Z).comap Abelianization.of :=
      Subgroup.mem_comap.mpr (mem_omSubQ.mpr ⟨w, hw, ha.symm⟩)
    have hψ : omPsi w = Additive.ofMul (piV p G a) := omPsi_of ha.symm
    have e : Additive.ofMul (piV p G (a⁻¹ * g)) = c := by
      rw [map_mul, map_inv, ofMul_mul, ofMul_inv, ← hψ, ← hyc, neg_add_cancel_left]
    have hb : a⁻¹ * g ∈ (vSub (U ⊔ C0)).comap (piV p G) := by
      apply Subgroup.mem_comap.mpr
      apply mem_vSub.mpr
      rw [e]
      exact hc
    have hm := Subgroup.mul_mem_sup haA hb
    rwa [mul_inv_cancel_left] at hm
  · -- `B` contains the preimage of `U`
    intro g hg
    exact Subgroup.mem_comap.mpr (mem_vSub.mpr (Submodule.mem_sup_left hg))
  · -- `A/γ_2` is elementary abelian
    intro a ha
    obtain ⟨w, -, hwa⟩ := mem_omSubQ.mp (Subgroup.mem_comap.mp ha)
    apply abel_of_eq_one_iff.mp
    rw [map_pow, ← hwa]
    exact omQ_pow _
  · -- `|A| = p^z |γ_2|`
    have hZQ : Nat.card (omSubQ Z) = Nat.card Z := by
      symm
      apply Nat.card_congr
      refine Equiv.ofBijective (fun w : Z => (⟨((Additive.toMul w.1 : omQ p G) :
        Abelianization G), mem_omSubQ.mpr ⟨w.1, w.2, rfl⟩⟩ : omSubQ Z)) ⟨?_, ?_⟩
      · intro w w' h
        have h1 : ((Additive.toMul w.1 : omQ p G) : Abelianization G) =
            ((Additive.toMul w'.1 : omQ p G) : Abelianization G) := congrArg Subtype.val h
        exact Subtype.ext (Additive.toMul.injective (Subtype.ext h1))
      · rintro ⟨x, hx⟩
        obtain ⟨w, hw, rfl⟩ := mem_omSubQ.mp hx
        exact ⟨⟨w, hw⟩, rfl⟩
    have hZc : Nat.card Z = p ^ finrank (ZMod p) Z := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    have e1 := Subgroup.card_mul_index ((omSubQ Z).comap Abelianization.of)
    have e2 : ((omSubQ Z).comap Abelianization.of).index = (omSubQ Z).index :=
      Subgroup.index_comap_of_surjective abel_of_surjective
    have e3 := Subgroup.card_mul_index (omSubQ Z)
    have e4 := Subgroup.card_mul_index (lcs G 1)
    have hcQ := card_abel_eq_index (G := G)
    haveI : Finite (Abelianization G ⧸ omSubQ Z) :=
      Finite.of_surjective (fun x : Abelianization G => (x : Abelianization G ⧸ omSubQ Z))
        QuotientGroup.mk_surjective
    have hpos : 0 < (omSubQ Z).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [e2] at e1
    rw [← hZc, ← hZQ]
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [e1, ← e4, ← hcQ, ← e3]
    ring

/-- `Φ(G) ≤ B` for a decomposition `G/γ_2 = A/γ_2 ⊕ B/γ_2` with `A/γ_2` of exponent `p`. -/
theorem pPhi_le_of_summand {A B : Subgroup G} (hB : lcs G 1 ≤ B) (hsup : A ⊔ B = ⊤)
    (hsq : ∀ a ∈ A, a ^ p ∈ lcs G 1) : pPhi p G ≤ B := by
  have hcB : commutator G ≤ B := by
    rw [commutator_eq_lcs_one]
    exact hB
  haveI : B.Normal := normal_of_commutator_le hcB
  refine sup_le ?_ hcB
  rw [Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ A ⊔ B := by
    rw [hsup]
    exact Subgroup.mem_top g
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have h1 : Abelianization.of ((a * b) ^ p * (b ^ p)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, map_pow, map_mul, mul_pow,
      ← map_pow Abelianization.of a p, abel_of_eq_one_iff.mpr (hsq a ha), one_mul,
      mul_inv_cancel]
  have h2 : (a * b) ^ p * (b ^ p)⁻¹ ∈ B := hB (abel_of_eq_one_iff.mp h1)
  have h3 := B.mul_mem h2 (B.pow_mem hb p)
  rwa [inv_mul_cancel_right] at h3

/-- Section 13.1, `dim Z0 ≤ r1 - s`: for a decomposition `G/γ_2 = A/γ_2 ⊕ B/γ_2` with `A/γ_2`
elementary abelian of order `p^z`, and a subspace `U` of `V` lifting into `B`,
`z + dim U ≤ d(G)`. -/
theorem summand_dim_le [Finite G] (hG : IsPGroup p G) {A B : Subgroup G}
    (hAB : A ⊓ B = lcs G 1) (hB : lcs G 1 ≤ B) (hsup : A ⊔ B = ⊤)
    (hsq : ∀ a ∈ A, a ^ p ∈ lcs G 1) (U : Submodule (ZMod p) (Additive (VQ p G)))
    (hUB : ∀ x ∈ U, ∃ b ∈ B, Additive.ofMul (piV p G b) = x) {z : ℕ}
    (hz : Nat.card A = p ^ z * Nat.card (lcs G 1)) :
    z + finrank (ZMod p) U ≤ Group.rank G := by
  haveI : Finite (VQ p G) := Finite.of_surjective _ piV_surjective
  have hp2 : 2 ≤ p := hp.out.two_le
  have hΦ := pPhi_le_of_summand hB hsup hsq
  have key : ∀ a ∈ A, ∀ b ∈ B, piV p G a = piV p G b → a ∈ lcs G 1 := by
    intro a ha b hb hab
    have h1 : a * b⁻¹ ∈ B := hΦ (piV_eq_iff.mp hab)
    have h2 : a ∈ B := by
      have h3 := B.mul_mem h1 hb
      rwa [inv_mul_cancel_right] at h3
    rw [← hAB]
    exact Subgroup.mem_inf.mpr ⟨ha, h2⟩
  have hcardA : Nat.card A ≤
      Nat.card (Set.range (fun a : A => Additive.ofMul (piV p G (a : G)))) *
        Nat.card (lcs G 1) := by
    apply card_le_card_range_mul
    intro a
    let g : {a' : A // Additive.ofMul (piV p G (a' : G)) = Additive.ofMul (piV p G (a : G))} →
        lcs G 1 := fun y =>
      ⟨(y.1 : G) * (a : G)⁻¹, key _ (A.mul_mem y.1.2 (A.inv_mem a.2)) 1 B.one_mem (by
        rw [map_one, map_mul, map_inv, mul_inv_eq_one]
        exact Additive.ofMul.injective y.2)⟩
    have hg : Function.Injective g := by
      intro y y' hyy
      have h1 : (y.1 : G) * (a : G)⁻¹ = (y'.1 : G) * (a : G)⁻¹ := congrArg Subtype.val hyy
      exact Subtype.ext (Subtype.ext (mul_right_cancel h1))
    exact Nat.card_le_card_of_injective g hg
  have hR : p ^ z ≤ Nat.card (Set.range (fun a : A => Additive.ofMul (piV p G (a : G)))) := by
    rw [hz] at hcardA
    exact Nat.le_of_mul_le_mul_right hcardA Nat.card_pos
  have hinj : Function.Injective
      (fun q : Set.range (fun a : A => Additive.ofMul (piV p G (a : G))) × U =>
        (q.1 : Additive (VQ p G)) + (q.2 : Additive (VQ p G))) := by
    rintro ⟨⟨x, a, rfl⟩, y⟩ ⟨⟨x', a', rfl⟩, y'⟩ h
    have h' : Additive.ofMul (piV p G (a : G)) + (y : Additive (VQ p G)) =
        Additive.ofMul (piV p G (a' : G)) + (y' : Additive (VQ p G)) := h
    have hd : Additive.ofMul (piV p G (a : G)) - Additive.ofMul (piV p G (a' : G)) =
        (y' : Additive (VQ p G)) - y := by
      rw [sub_eq_sub_iff_add_eq_add, h', add_comm]
    have hd' : Additive.ofMul (piV p G ((a : G) * (a' : G)⁻¹)) = (y' : Additive (VQ p G)) - y := by
      rw [map_mul, map_inv, ofMul_mul, ofMul_inv, ← sub_eq_add_neg]
      exact hd
    obtain ⟨b, hb, hbe⟩ := hUB _ (U.sub_mem y'.2 y.2)
    have hpa : piV p G ((a : G) * (a' : G)⁻¹) = piV p G b :=
      Additive.ofMul.injective (hd'.trans hbe.symm)
    have h1 := key _ (A.mul_mem a.2 (A.inv_mem a'.2)) b hb hpa
    have h2 : piV p G ((a : G) * (a' : G)⁻¹) = 1 := piV_eq_one_of_mem_lcs h1
    have haa : piV p G (a : G) = piV p G (a' : G) := by
      rw [map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
    have hxa : Additive.ofMul (piV p G (a : G)) = Additive.ofMul (piV p G (a' : G)) :=
      congrArg Additive.ofMul haa
    have hyy : (y : Additive (VQ p G)) = y' := by
      rw [hxa] at h'
      exact add_left_cancel h'
    exact Prod.ext (Subtype.ext hxa) (Subtype.ext hyy)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  have hUc : Nat.card U = p ^ finrank (ZMod p) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hVc : Nat.card (Additive (VQ p G)) = p ^ Group.rank G := card_V hG
  rw [hUc, hVc] at hcard
  have h3 : p ^ (z + finrank (ZMod p) U) ≤ p ^ Group.rank G := by
    rw [pow_add]
    exact (Nat.mul_le_mul_right _ hR).trans hcard
  exact pow_le_pow_cancel hp2 h3

end Summand

section Mult3Cover

variable {m r1 r2 s lam m2 m3 r3 z k : ℕ}

/-- Section 13.1, `dim Z0 ≤ r1 - s`, on `mult3Set`. -/
theorem mult3_z_add_s_le {G : FiniteGrp.{0}} (hG : G ∈ mult3Set m r1 r2 s lam m2 m3 r3 z k) :
    z + s ≤ r1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, H, hH, hrk, -, A, B, -, hB, hAB, hsup, hHB, hsq, hAc⟩ := hG
  obtain ⟨hcard, -, -, hr1, -, hs, -, hm2, -⟩ := (mem_cnt3Set_iff G).mp hc
  have hP : IsPGroup 2 G := IsPGroup.of_card hcard
  obtain ⟨u, hu⟩ := exists_fin_enum H hrk
  have hcore : lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
      lcs G 2 := by
    rw [hu]
    exact hH.le
  have hdim := (group_coreCent_inf_eq_bot hP u hcore hs.symm).2
  have hle : coreImg (p := 2) u ≤ imgSub (p := 2) B := by
    unfold coreImg
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_imgSub (p := 2) (K := B)).mpr
      ⟨u i, hHB (by rw [← hu]; exact Subgroup.subset_closure ⟨i, rfl⟩), rfl⟩
  have hUB : ∀ x ∈ coreImg (p := 2) u, ∃ b ∈ B, Additive.ofMul (piV 2 G b) = x :=
    fun x hx => mem_imgSub.mp (hle hx)
  have hz : Nat.card A = 2 ^ z * Nat.card (lcs G 1) :=
    hAc.trans (congrArg (fun x => 2 ^ z * x) hm2.symm)
  have h := summand_dim_le hP hAB hB hsup hsq (coreImg (p := 2) u) hUB hz
  rw [hdim, hr1] at h
  exact h

/-- Section 13.1 (existence of `Z0`): for every group of `cnt3Set` and every Sims core `H`, the
group lies in `mult3Set` with `H`, some `z` with `r1 - s - lam ≤ z ≤ r1 - s`, and `k = dim K`. -/
theorem mult3Set_of_core {G : FiniteGrp.{0}} (hG : G ∈ cnt3Set m r1 r2 s lam m2 m3 r3)
    (H : Subgroup G) (hH : (⊤ : Subgroup G).lowerCentralSeries 1 =
      ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2) (hrk : Group.rank H = s) :
    ∃ z k : ℕ, r1 ≤ z + s + lam ∧ z + s ≤ r1 ∧ G ∈ mult3Set m r1 r2 s lam m2 m3 r3 z k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG0 := hG
  obtain ⟨hcard, -, -, hr1, -, -, hidx, hm2, -, -⟩ := hG
  have hP : IsPGroup 2 G := IsPGroup.of_card hcard
  obtain ⟨u, hu⟩ := exists_fin_enum H hrk
  have hUle : finrank (ZMod 2) (coreImg (p := 2) u) ≤ s := by
    have h2 : finrank (ZMod 2) (coreImg (p := 2) u) ≤ Fintype.card (Fin s) :=
      finrank_range_le_card (fun i => Additive.ofMul (piV 2 G (u i)))
    rw [Fintype.card_fin] at h2
    exact h2
  obtain ⟨A, B, hA, hB, hAB, hsup, hUB, hsq, z, hz, hAc⟩ :=
    exists_summand hP (coreImg (p := 2) u) hr1 hidx hUle
  have hHB : H ≤ B := by
    intro h hh
    apply hUB
    exact piV_mem_coreImg (p := 2) u (by rw [hu]; exact hh)
  have hcardK := card_coreCent_pre hP u
  rw [hu, hr1] at hcardK
  have hmem : G ∈ mult3Set m r1 r2 s lam m2 m3 r3 z
      (finrank (ZMod 2) (coreCent (lamLin (p := 2) (G := G)) (coreImg (p := 2) u))) :=
    ⟨hG0, H, hH, hrk, hcardK, A, B, hA, hB, hAB, hsup, hHB, hsq,
      hAc.trans (congrArg (fun x => 2 ^ z * x) hm2)⟩
  exact ⟨z, _, hz, mult3_z_add_s_le hmem, hmem⟩

/-- Every group of `cnt3Set` lies in some `mult3Set` with `r1 - s - lam ≤ z ≤ r1 - s`. -/
theorem cnt3Set_mem_mult3Set {G : FiniteGrp.{0}} (hG : G ∈ cnt3Set m r1 r2 s lam m2 m3 r3) :
    ∃ z k : ℕ, r1 ≤ z + s + lam ∧ z + s ≤ r1 ∧ G ∈ mult3Set m r1 r2 s lam m2 m3 r3 z k := by
  have hne : {k | ∃ H : Subgroup G, (⊤ : Subgroup G).lowerCentralSeries 1 =
      ⁅H, H⁆ ⊔ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ Group.rank H = k}.Nonempty :=
    ⟨_, ⊤, (sup_eq_left.mpr (lcs_antitone (by norm_num) : lcs G 2 ≤ lcs G 1)).symm, rfl⟩
  obtain ⟨H, hH, hk⟩ := Nat.sInf_mem hne
  have hG0 := hG
  obtain ⟨-, -, -, -, -, hs, -⟩ := hG0
  exact mult3Set_of_core hG H hH (hk.trans hs)

end Mult3Cover

end Mult3

end OMA.SimsLite
