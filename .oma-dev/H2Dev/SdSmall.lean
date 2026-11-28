import H2Dev.SdModel
import H2Dev.SdDiam

/-! Iterated subdivision of a singular simplex eventually lies in an open cover. -/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

theorem sdY_iterate_small {Y A B : TopCat.{0}} (l : A ⟶ Y) (r : B ⟶ Y)
    (hl : Topology.IsOpenEmbedding l.hom) (hr : Topology.IsOpenEmbedding r.hom)
    (hcov : Set.range l.hom ∪ Set.range r.hom = Set.univ) {n : ℕ}
    (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    ∃ k, ((sdY Y n).hom)^[k] (gen σ) ∈
      (((scMap l).f n).hom.range ⊔ ((scMap r).f n).hom.range) := by
  sorry

end SdDev
