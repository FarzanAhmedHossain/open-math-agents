import H2Dev.SdCone

/-! Repeated subdivision of a linear simplex has small simplices. -/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

/-- The subgroup of linear `k`-chains spanned by tuples satisfying `p`. -/
def spanOf {m k : ℕ} (p : (Fin (k + 1) → Pt m) → Prop) : AddSubgroup ((Ch (Tup (Pt m))).X k) :=
  AddSubgroup.closure {x | ∃ v, p v ∧ x = tgen v}

/-- After `j` subdivisions of `[v]` (with all vertex distances `≤ D`), every tuple that occurs
has its points in the convex hull of `v` and all its distances `≤ (k/(k+1))^j * D`. -/
theorem SL_iterate_support (m k j : ℕ) (v : Fin (k + 1) → Pt m) (D : ℝ)
    (hD : ∀ i i', dist (v i) (v i') ≤ D) :
    ((SL m k).hom)^[j] (tgen v) ∈ spanOf (m := m) (k := k) (fun w =>
      (∀ i, (w i : Fin (m + 1) → ℝ) ∈
        convexHull ℝ (Set.range fun i => (v i : Fin (m + 1) → ℝ))) ∧
      ∀ i i', dist (w i) (w i') ≤ ((k : ℝ) / (k + 1)) ^ j * D) := by
  sorry

end SdDev
