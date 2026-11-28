import H2Dev.SdDefs

/-! Generic facts about `Ch X`, generators, and singular simplices. -/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

theorem descGen_gen {X : SSet.{0}} {n : ℕ} {T : AddCommGrpCat.{0}} (F : X _⦋n⦌ → T)
    (x : X _⦋n⦌) : (descGen F).hom (gen x) = F x := by
  sorry

theorem hom_ext_gen {X : SSet.{0}} {n : ℕ} {T : AddCommGrpCat.{0}} {f g : (Ch X).X n ⟶ T}
    (h : ∀ x : X _⦋n⦌, f.hom (gen x) = g.hom (gen x)) : f = g := by
  sorry

theorem closure_gen (X : SSet.{0}) (n : ℕ) :
    AddSubgroup.closure (Set.range (gen (X := X) (n := n))) = ⊤ := by
  sorry

theorem d_gen {X : SSet.{0}} {n : ℕ} (x : X _⦋n + 1⦌) :
    ((Ch X).d (n + 1) n).hom (gen x) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • gen (X.δ i x) := by
  sorry

theorem chMap_gen {X Y : SSet.{0}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    ((chMap f).f n).hom (gen x) = gen (f.app _ x) := by
  sorry

theorem sing_unsing {Y : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    sing (unsing σ) = σ := rfl

theorem unsing_sing {Y : TopCat.{0}} {n : ℕ} (f : Δt n ⟶ Y) : unsing (sing f) = f := rfl

theorem toSSet_map_sing {Y Y' : TopCat.{0}} (g : Y ⟶ Y') {n : ℕ} (f : Δt n ⟶ Y) :
    (TopCat.toSSet.map g).app _ (sing f) = sing (f ≫ g) := by
  sorry

theorem δ_sing {Y : TopCat.{0}} {n : ℕ} (i : Fin (n + 2)) (f : Δt (n + 1) ⟶ Y) :
    (TopCat.toSSet.obj Y).δ i (sing f) =
      sing (SimplexCategory.toTop.{0}.map (SimplexCategory.δ i) ≫ f) := by
  sorry

theorem tup_δ {P : Type} {k : ℕ} (i : Fin (k + 2)) (v : Fin (k + 2) → P) :
    (Tup P).δ i v = v ∘ Fin.succAbove i := by
  sorry

theorem tupMap_app {P Q : Type} (φ : P → Q) {k : ℕ} (v : Fin (k + 1) → P) :
    (tupMap φ).app (Opposite.op ⦋k⦌) v = φ ∘ v := by
  sorry

end SdDev
