import H2Dev.SdCone
import H2Dev.SdAff

/-! The natural subdivision operator on singular chains and its homotopy to the identity. -/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

theorem sdY_gen (Y : TopCat.{0}) (n : ℕ) (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    (sdY Y n).hom (gen σ) = ((scMap (unsing σ)).f n).hom (cS n) := by
  sorry

theorem thY_gen (Y : TopCat.{0}) (n : ℕ) (σ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    (thY Y n).hom (gen σ) = ((scMap (unsing σ)).f (n + 1)).hom (cT n) := by
  sorry

theorem sdY_natural {Y Y' : TopCat.{0}} (g : Y ⟶ Y') (n : ℕ) :
    (scMap g).f n ≫ sdY Y' n = sdY Y n ≫ (scMap g).f n := by
  sorry

theorem thY_natural {Y Y' : TopCat.{0}} (g : Y ⟶ Y') (n : ℕ) :
    (scMap g).f n ≫ thY Y' n = thY Y n ≫ (scMap g).f (n + 1) := by
  sorry

theorem sdY_d (Y : TopCat.{0}) (n : ℕ) :
    sdY Y (n + 1) ≫ (SC Y).d (n + 1) n = (SC Y).d (n + 1) n ≫ sdY Y n := by
  sorry

theorem thY_d_zero (Y : TopCat.{0}) : thY Y 0 ≫ (SC Y).d 1 0 = 𝟙 _ - sdY Y 0 := by
  sorry

theorem thY_d_succ (Y : TopCat.{0}) (n : ℕ) :
    thY Y (n + 1) ≫ (SC Y).d (n + 2) (n + 1) + (SC Y).d (n + 1) n ≫ thY Y n =
      𝟙 _ - sdY Y (n + 1) := by
  sorry

/-- The subdivision chain map. -/
def sdMap (Y : TopCat.{0}) : SC Y ⟶ SC Y where
  f n := sdY Y n
  comm' i j hij := by
    sorry

theorem sdMap_f (Y : TopCat.{0}) (n : ℕ) : (sdMap Y).f n = sdY Y n := rfl

/-- Subdivision is homotopic to the identity, by the homotopy `-thY`. -/
def sdHomotopy (Y : TopCat.{0}) : Homotopy (sdMap Y) (𝟙 (SC Y)) := by
  sorry

/-- The homotopy has components `-thY`. -/
theorem sdHomotopy_hom (Y : TopCat.{0}) (n : ℕ) :
    (sdHomotopy Y).hom n (n + 1) = -thY Y n := by
  sorry

end SdDev
