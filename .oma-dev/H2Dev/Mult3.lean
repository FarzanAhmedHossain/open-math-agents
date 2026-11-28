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
* the arithmetic of Corollary 14.1: `cor_14_1_dim_bound` (152) and `mult3_exponent_eq`.

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
`A`-alternative of (55), `Δ_p` omitted). -/
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

end Mult3

end OMA.SimsLite

#print axioms OMA.SimsLite.Mult3.mult3_k_add_s_le
#print axioms OMA.SimsLite.Mult3.prop_13_1_count
#print axioms OMA.SimsLite.Mult3.prop_13_2_fiber
#print axioms OMA.SimsLite.Mult3.rem_6_4_fiber
#print axioms OMA.SimsLite.Mult3.cor_14_1_dim_bound
#print axioms OMA.SimsLite.Mult3.cor_14_1_div
#print axioms OMA.SimsLite.mult3_ncard_le_cnt3
