import H2Dev.SdChains

/-! The cone operator and the algebra of subdivision on linear chains. -/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace SdDev

theorem cone_gen {P : Type} (b : P) {k : ℕ} (v : Fin (k + 1) → P) :
    (cone b k).hom (gen (X := Tup P) (n := k) v) =
      gen (X := Tup P) (n := k + 1) (Fin.cons b v : Fin (k + 2) → P) := by
  sorry

/-- `∂ (b · x) = x - b · ∂ x` in positive degree. -/
theorem d_cone_succ {P : Type} (b : P) {k : ℕ} (x : (Ch (Tup P)).X (k + 1)) :
    ((Ch (Tup P)).d (k + 2) (k + 1)).hom ((cone b (k + 1)).hom x) =
      x - (cone b k).hom (((Ch (Tup P)).d (k + 1) k).hom x) := by
  sorry

/-- `∂ (b · [v]) = [v] - [b]` in degree 0. -/
theorem d_cone_zero_gen {P : Type} (b : P) (v : Fin 1 → P) :
    ((Ch (Tup P)).d 1 0).hom ((cone b 0).hom (gen (X := Tup P) (n := 0) v)) =
      gen (X := Tup P) (n := 0) v - gen (X := Tup P) (n := 0) (fun _ => b) := by
  sorry

theorem SL_zero (m : ℕ) : SL m 0 = 𝟙 _ := rfl

theorem SL_succ_gen (m k : ℕ) (v : Fin (k + 2) → Pt m) :
    (SL m (k + 1)).hom (tgen v) =
      (cone (bary v) k).hom ((SL m k).hom (((Ch (Tup (Pt m))).d (k + 1) k).hom (tgen v))) := by
  sorry

theorem TL_zero_gen (m : ℕ) (v : Fin 1 → Pt m) :
    (TL m 0).hom (tgen v) = (cone (bary v) 0).hom (tgen v) := by
  sorry

theorem TL_succ_gen (m k : ℕ) (v : Fin (k + 2) → Pt m) :
    (TL m (k + 1)).hom (tgen v) = (cone (bary v) (k + 1)).hom
      (tgen v - (TL m k).hom (((Ch (Tup (Pt m))).d (k + 1) k).hom (tgen v))) := by
  sorry

/-- Subdivision of linear chains is a chain map. -/
theorem SL_d (m k : ℕ) :
    SL m (k + 1) ≫ (Ch (Tup (Pt m))).d (k + 1) k = (Ch (Tup (Pt m))).d (k + 1) k ≫ SL m k := by
  sorry

/-- `∂ T = 1 - S` in degree 0. -/
theorem TL_d_zero (m : ℕ) : TL m 0 ≫ (Ch (Tup (Pt m))).d 1 0 = 𝟙 _ - SL m 0 := by
  sorry

/-- `∂ T + T ∂ = 1 - S` in positive degree. -/
theorem TL_d_succ (m k : ℕ) :
    TL m (k + 1) ≫ (Ch (Tup (Pt m))).d (k + 2) (k + 1) +
      (Ch (Tup (Pt m))).d (k + 1) k ≫ TL m k = 𝟙 _ - SL m (k + 1) := by
  sorry

/-- Affine maps commute with subdivision (barycenters are preserved). -/
theorem SL_aff (n m k : ℕ) (w : Fin (n + 1) → Pt m) :
    (chMap (tupMap (affFun w))).f k ≫ SL m k = SL n k ≫ (chMap (tupMap (affFun w))).f k := by
  sorry

theorem TL_aff (n m k : ℕ) (w : Fin (n + 1) → Pt m) :
    (chMap (tupMap (affFun w))).f k ≫ TL m k = TL n k ≫ (chMap (tupMap (affFun w))).f (k + 1) := by
  sorry

end SdDev
