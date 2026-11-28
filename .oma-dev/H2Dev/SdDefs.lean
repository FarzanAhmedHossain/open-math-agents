import Mathlib

/-!
# Barycentric subdivision for singular chains: definitions

Target (step `PoincareConjecture.poincare_conjecture.R1.H2.R1.H1.R1.H2.R1.H1.R1.H1`):
on the quotient of the singular chains of `U ∪ V` by the chains coming from `U` and `V`,
subdivision is homotopic to the identity and repeated subdivision kills every chain.

Plan (Hatcher, Prop. 2.21):
* `Ch X` : the ℤ-chain complex of a simplicial set; `gen x` the generator of a simplex.
* `Tup P` : the simplicial set of vertex tuples in `P` (faces delete entries).
* `cone b` : `[v₀,…,vₖ] ↦ [b,v₀,…,vₖ]` on chains of `Tup P`.
* `SL k`, `TL k` : subdivision and its homotopy on linear chains in `Δᵐ` (`P := Δᵐ`).
* `affS m` : `Tup Δᵐ ⟶ toSSet Δᵐ`, a vertex tuple ↦ its affine simplex.
* model chains `cS n`, `cT n` in `C(Δⁿ)`, and the natural operators
  `sdY Y n`, `thY Y n` on singular chains, `σ ↦ σ_♯ (model)`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

/-- The coefficient group `ℤ`. -/
abbrev Zg : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ

/-- The ℤ-chain complex of a simplicial set. -/
abbrev Ch (X : SSet.{0}) : ChainComplex AddCommGrpCat.{0} ℕ := X.chainComplex Zg

/-- The chain map induced by a map of simplicial sets. -/
abbrev chMap {X Y : SSet.{0}} (f : X ⟶ Y) : Ch X ⟶ Ch Y := SSet.chainComplexMap f Zg

/-- The generator of the chain group attached to an `n`-simplex. -/
def gen {X : SSet.{0}} {n : ℕ} (x : X _⦋n⦌) : (Ch X).X n :=
  (X.ιChainComplex (R := Zg) x).hom (1 : ℤ)

/-- The additive map out of `n`-chains determined by its values on generators. -/
def descGen {X : SSet.{0}} {n : ℕ} {T : AddCommGrpCat.{0}} (F : X _⦋n⦌ → T) :
    (Ch X).X n ⟶ T :=
  (X.isColimitChainComplexXCofan Zg n).desc
    (Cofan.mk T fun x => AddCommGrpCat.ofHom (zmultiplesHom T (F x)))

/-! ## Singular chains -/

/-- Singular ℤ-chains of a space. -/
abbrev SC (Y : TopCat.{0}) : ChainComplex AddCommGrpCat.{0} ℕ := Ch (TopCat.toSSet.obj Y)

/-- Singular chain map of a continuous map. -/
abbrev scMap {Y Y' : TopCat.{0}} (f : Y ⟶ Y') : SC Y ⟶ SC Y' := chMap (TopCat.toSSet.map f)

/-- The topological `n`-simplex. -/
abbrev Δt (n : ℕ) : TopCat.{0} := SimplexCategory.toTop.{0}.obj ⦋n⦌

/-- The singular `n`-simplex given by a continuous map from `Δⁿ`. -/
def sing {Y : TopCat.{0}} {n : ℕ} (f : Δt n ⟶ Y) : (TopCat.toSSet.obj Y) _⦋n⦌ := ULift.up f

/-- The continuous map underlying a singular simplex. -/
def unsing {Y : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) : Δt n ⟶ Y := σ.down

/-! ## Vertex tuples -/

/-- The simplicial set whose `k`-simplices are `(k+1)`-tuples of points of `P`. -/
def Tup (P : Type) : SSet.{0} where
  obj n := Fin (n.unop.len + 1) → P
  map f := ↾fun v => v ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `Tup` is functorial in the point set. -/
def tupMap {P Q : Type} (φ : P → Q) : Tup P ⟶ Tup Q where
  app _ := ↾fun v => φ ∘ v
  naturality _ _ _ := rfl

/-- The cone operator `[v₀,…,vₖ] ↦ [b,v₀,…,vₖ]`. -/
def cone {P : Type} (b : P) (k : ℕ) : (Ch (Tup P)).X k ⟶ (Ch (Tup P)).X (k + 1) :=
  descGen (X := Tup P) (n := k) fun v => gen (X := Tup P) (n := k + 1) (Fin.cons b v : Fin (k + 2) → P)

/-- Points of the standard simplex `Δᵐ` (as a subset of `Fin (m+1) → ℝ`). -/
abbrev Pt (m : ℕ) : Type := stdSimplex ℝ (Fin (m + 1))

/-- The barycenter of a vertex tuple in `Δᵐ`. -/
def bary {m k : ℕ} (v : Fin (k + 1) → Pt m) : Pt m :=
  ⟨((k : ℝ) + 1)⁻¹ • ∑ i, (v i : Fin (m + 1) → ℝ), by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (v i).2.1 j)
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [← Finset.mul_sum, Finset.sum_comm,
        Finset.sum_congr rfl (fun i _ => (v i).2.2)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        Nat.cast_add, Nat.cast_one]
      field_simp⟩

/-- The generator of a vertex tuple of `Δᵐ`. -/
abbrev tgen {m k : ℕ} (v : Fin (k + 1) → Pt m) : (Ch (Tup (Pt m))).X k :=
  gen (X := Tup (Pt m)) (n := k) v

/-- Subdivision on linear chains: `S [v] = b_v · S (∂ [v])`, and `S = id` in degree 0. -/
def SL (m : ℕ) : (k : ℕ) → ((Ch (Tup (Pt m))).X k ⟶ (Ch (Tup (Pt m))).X k)
  | 0 => 𝟙 _
  | k + 1 => descGen (X := Tup (Pt m)) (n := k + 1) (fun v =>
      (cone (bary v) k).hom ((SL m k).hom (((Ch (Tup (Pt m))).d (k + 1) k).hom (tgen v))))

/-- The subdivision homotopy on linear chains: `T [v] = b_v · ([v] - T (∂ [v]))`,
and `T [v] = b_v · [v]` in degree 0. -/
def TL (m : ℕ) : (k : ℕ) → ((Ch (Tup (Pt m))).X k ⟶ (Ch (Tup (Pt m))).X (k + 1))
  | 0 => descGen (X := Tup (Pt m)) (n := 0) (fun v => (cone (bary v) 0).hom (tgen v))
  | k + 1 => descGen (X := Tup (Pt m)) (n := k + 1) (fun v =>
      (cone (bary v) (k + 1)).hom
        (tgen v - (TL m k).hom (((Ch (Tup (Pt m))).d (k + 1) k).hom (tgen v))))

/-! ## Affine simplices -/

/-- The affine map `Δᵏ → Δᵐ` with prescribed vertices. -/
def affFun {m k : ℕ} (v : Fin (k + 1) → Pt m) (t : Pt k) : Pt m :=
  ⟨∑ i, (t : Fin (k + 1) → ℝ) i • (v i : Fin (m + 1) → ℝ), by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (t.2.1 i) ((v i).2.1 j)
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i _ => by rw [(v i).2.2])]
      simpa using t.2.2⟩

lemma continuous_affFun {m k : ℕ} (v : Fin (k + 1) → Pt m) : Continuous (affFun v) := by
  apply Continuous.subtype_mk
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

/-- The affine singular simplex of `Δᵐ` with vertices `v`. -/
def affSimplex {m k : ℕ} (v : Fin (k + 1) → Pt m) : Δt k ⟶ Δt m :=
  TopCat.ofHom ⟨fun t => ULift.up (affFun v t.down),
    continuous_uliftUp.comp ((continuous_affFun v).comp continuous_uliftDown)⟩

/-- Vertex tuples of `Δᵐ` ↦ affine singular simplices of `Δᵐ`. -/
def affS (m : ℕ) : Tup (Pt m) ⟶ TopCat.toSSet.obj (Δt m) where
  app n := ↾fun v => sing (affSimplex (k := n.unop.len) v)
  naturality _ _ _ := by
    sorry

/-- The vertices of `Δⁿ`. -/
def verts (n : ℕ) : Fin (n + 1) → Pt n := fun i => stdSimplex.vertex (S := ℝ) i

/-- The map from linear chains of `Δᵐ` to singular chains of `Δᵐ`. -/
abbrev ρ (m : ℕ) : Ch (Tup (Pt m)) ⟶ SC (Δt m) := chMap (affS m)

/-- Model chain for subdivision in degree `n`: `S (ι_n)` in `C_n(Δⁿ)`. -/
def cS (n : ℕ) : (SC (Δt n)).X n := ((ρ n).f n).hom ((SL n n).hom (tgen (verts n)))

/-- Model chain for the homotopy in degree `n`: `T (ι_n)` in `C_{n+1}(Δⁿ)`. -/
def cT (n : ℕ) : (SC (Δt n)).X (n + 1) := ((ρ n).f (n + 1)).hom ((TL n n).hom (tgen (verts n)))

/-- Natural subdivision on singular `n`-chains: `σ ↦ σ_♯ (cS n)`. -/
def sdY (Y : TopCat.{0}) (n : ℕ) : (SC Y).X n ⟶ (SC Y).X n :=
  descGen fun σ => ((scMap (unsing σ)).f n).hom (cS n)

/-- Natural subdivision homotopy on singular `n`-chains: `σ ↦ σ_♯ (cT n)`. -/
def thY (Y : TopCat.{0}) (n : ℕ) : (SC Y).X n ⟶ (SC Y).X (n + 1) :=
  descGen fun σ => ((scMap (unsing σ)).f (n + 1)).hom (cT n)

end SdDev
