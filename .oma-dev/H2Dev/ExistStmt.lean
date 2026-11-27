import H2Dev.Code
import H2Dev.Stmt

/-! DEVELOPMENT STUB of the existence theorem (statement fixed; proved in `Existence.lean`). -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

theorem existence {p : ℕ} (hp : p.Prime) (m : ℕ) (G : Type u) [Group G] [Finite G]
    (hG : Nat.card G = p ^ m) : ∃ (X : Fin m → G) (c : Code p m), Realizes X c := by
  sorry

end OMA.SimsLite
