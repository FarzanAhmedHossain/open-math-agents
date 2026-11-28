import H2Dev.SdSmall

/-! Assembly: the statement of step H1. -/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

namespace SdDev

theorem main_H1 :
  ∀ (X : Type) [TopologicalSpace X] (U V : Set X), IsOpen U → IsOpen V →
    let C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
    let i : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩
    let j : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩
    let l : TopCat.of U ⟶ TopCat.of (U ∪ V : Set X) :=
      TopCat.ofHom ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
    let r : TopCat.of V ⟶ TopCat.of (U ∪ V : Set X) :=
      TopCat.ofHom ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
    let h : CategoryStruct.comp (C.map i) (C.map l) = CategoryStruct.comp (C.map j) (C.map r) := by
      rw [← C.map_comp, ← C.map_comp]
      rfl
    let Q := cokernel (pushout.desc (C.map l) (C.map r) h)
    ∃ S : End Q, Nonempty (Homotopy S (𝟙 Q)) ∧
      ∀ n (z : Q.X n), ∃ k : ℕ, ((S ^ k).f n) z = 0 := by
  sorry

end SdDev
