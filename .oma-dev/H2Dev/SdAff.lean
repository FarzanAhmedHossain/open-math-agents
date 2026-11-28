import H2Dev.SdChains

/-! Affine simplices: vertices, composition, faces, and naturality of `ρ`. -/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

theorem affS_app {m k : ℕ} (v : Fin (k + 1) → Pt m) :
    (affS m).app (Opposite.op ⦋k⦌) v = sing (affSimplex v) := by
  sorry

/-- The affine simplex on the vertices of `Δⁿ` is the identity. -/
theorem affSimplex_verts (n : ℕ) : affSimplex (verts n) = 𝟙 (Δt n) := by
  sorry

/-- Composition of affine simplices. -/
theorem affSimplex_comp {n m k : ℕ} (w : Fin (n + 1) → Pt m) (v : Fin (k + 1) → Pt n) :
    affSimplex v ≫ affSimplex w = affSimplex (affFun w ∘ v) := by
  sorry

/-- The coface inclusions of topological simplices are affine. -/
theorem toTop_δ_eq (n : ℕ) (i : Fin (n + 2)) :
    SimplexCategory.toTop.{0}.map (SimplexCategory.δ i) =
      affSimplex (verts (n + 1) ∘ Fin.succAbove i) := by
  sorry

/-- The faces of the vertex tuple of `Δⁿ⁺¹` are images of the vertex tuple of `Δⁿ`. -/
theorem verts_succAbove (n : ℕ) (i : Fin (n + 2)) :
    verts (n + 1) ∘ Fin.succAbove i = affFun (verts (n + 1) ∘ Fin.succAbove i) ∘ verts n := by
  sorry

/-- `ρ` is natural for affine maps between simplices. -/
theorem ρ_aff (n m k : ℕ) (w : Fin (n + 1) → Pt m) :
    (chMap (tupMap (affFun w))).f k ≫ (ρ m).f k = (ρ n).f k ≫ (scMap (affSimplex w)).f k := by
  sorry

end SdDev
