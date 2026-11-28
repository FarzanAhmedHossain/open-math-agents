import H2Dev.Alt2

/-! # Isotropic: Li-Qiao Lemmas 8.1 and 8.2 (counting totally isotropic subspaces)

Li-Qiao (arXiv:2610.14509v3), Sec. 8, pp. 45-50, over a finite field `F` with `q = |F|`
(the target is `F = ZMod 2`), `X = Fin R → F`, `A` an alternating `R × R` matrix with
`dim rad A = r0` and `R = r0 + 2a` (rank `2a`).  All counts are normalised by `x = 1/q`.

Method (an ordered-basis version of the paper's `(J, L, f)` parametrisation).  Count the ordered
linearly independent, pairwise `A`-orthogonal `i`-tuples `v` whose span `S` meets `K = rad A` in
dimension `j` (`isoTupCount A i j`).  Appending a vector `y` to such a tuple keeps it isotropic and
independent iff `y ∈ S^⊥ \ S`; the new intersection with `K` has dimension `j + 1` iff `y ∈ S + K`.
Since `dim (S + K) = i + r0 - j` and `dim S^⊥ = R + j - i`, this gives the exact recursion

  `N(i+1, j+1) ≤ N(i, j) (q^(i+r0-j) - q^i) + N(i, j+1) (q^(R+j+1-i) - q^(i+r0-j-1))`

(`isoTupCount_succ_le`, `isoTupCount_succ_zero_le`).  The real potential

  `P(i, j) = x^E(i,j) · G(j) · S(i-j) · B(i, j)`, `E(i,j) = C(i-j,2) + j (2a - (i-j))`,
  `G(j) = ∏_{m<j} (1 - x^(r0-m))`, `S(l) = ∏_{t<l} (1 - x^(2a-2t))`, `B` = Gaussian binomial in `x`

is an exact solution of the normalised recursion, so `N(i, j) x^(iR) ≤ P(i, j)` (`isoTupCount_le`).
(For `i = h`, `x^(hR) N(h, j) / |GL_h|` is the paper's summand `T_{a, h-j}` of (93) divided by
`q^(h(R-h))`; cf. (100).)  Dividing by the number of ordered bases of an `h`-space gives

* `isoCount_mul_isoQ_le` (Lemma 8.1, upper bound, normalised):
  `I_h(A) · Q(h) ≤ |Gr(h, X)| · Σ_{j ≤ h} P(h, j)`, where `Q(h) = ∏_{t<h} (1 - x^(R-t))`
  (so `|Gr(h,X)| = q^(h(R-h)) π_R / (π_h π_(R-h))` corresponds to `Q(h) / (x^(h(R-h)) π_h)`).
* `isoCount_uniform` (Lemma 8.2, (95), constant `32` in place of `(4/3) π_∞(2)^(-4)`):
  `I_h(A) q^(κ_h(a)) ≤ 32 |Gr(h, X)|`, with `κ_h(a) = C(h,2) - C(h - a_h, 2)` (`kappaH`), which
  equals `a_h (2h - a_h - 1)/2` of (94), `a_h = min(a, max(h-1, 0))`.
* `isoCount_saturated` (Lemma 8.2, (96) with `γ_q ≤ 15/8 < 2` for every `q ≥ 2`):
  if `a ≥ h - 1` then `I_h(A) q^(C(h,2)) ≤ (15/8) |Gr(h, X)|`; `isoCount_saturated_two` is the
  `F = ZMod 2` case.  The paper only needs `γ_2 < 2` (proof of Prop 9.2 at `ℓ = 1`).

Auxiliary: `card_isoOrth` (`#{independent isotropic h-tuples} = I_h(A) · |GL_h|`-style basis
count), `card_isoOrth_eq_sum`, `grass_mul_card` (`|Gr(h,X)| ∏(q^h - q^t) = ∏(q^R - q^t)`),
`qBinom_mul_piQ_le` (`B(i,j) π_j ≤ 1`), `piQ_ge_quarter`, `isoQ_ge`, `isoE_ge_kappa`,
`isoE_two_mul`.
-/

namespace OMA.SimsLite.Alt2

open Module Finset

/-! ### Elementary natural-number facts -/

section NatFacts

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  show (n + 1).choose (1 + 1) = n.choose (1 + 1) + n
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

lemma two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [choose_two_succ]
    nlinarith [ih]

end NatFacts

/-! ### The potential -/

section Potential

/-- `E(i, j) = C(i - j, 2) + j (2a - (i - j))`, the exponent of `x` in the potential. -/
def isoE (a i j : ℕ) : ℕ := (i - j).choose 2 + j * (2 * a - (i - j))

/-- `G(j) = ∏_{m < j} (1 - x^(r0 - m))`: the radical factor. -/
noncomputable def isoG (x : ℝ) (r0 j : ℕ) : ℝ := ∏ m ∈ range j, (1 - x ^ (r0 - m))

/-- `S(l) = ∏_{t < l} (1 - x^(2a - 2t))`: the symplectic factor. -/
noncomputable def isoS (x : ℝ) (a l : ℕ) : ℝ := ∏ t ∈ range l, (1 - x ^ (2 * a - 2 * t))

/-- The Gaussian binomial in `x`, by the `q`-Pascal rule
`B(i+1, j+1) = B(i, j) + x^(j+1) B(i, j+1)`. -/
noncomputable def qBinom (x : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | i + 1, j + 1 => qBinom x i j + x ^ (j + 1) * qBinom x i (j + 1)

/-- The potential `P(i, j) = x^E(i,j) G(j) S(i-j) B(i,j)`. -/
noncomputable def isoP (x : ℝ) (a r0 i j : ℕ) : ℝ :=
  x ^ isoE a i j * isoG x r0 j * isoS x a (i - j) * qBinom x i j

/-- `π_j(q) = ∏_{m < j} (1 - x^(m+1))`. -/
noncomputable def piQ (x : ℝ) (j : ℕ) : ℝ := ∏ m ∈ range j, (1 - x ^ (m + 1))

/-- `Q(h) = ∏_{t < h} (1 - x^(R - t)) = x^(hR) ∏_{t<h} (q^R - q^t)`. -/
noncomputable def isoQ (x : ℝ) (R h : ℕ) : ℝ := ∏ t ∈ range h, (1 - x ^ (R - t))

/-- `κ_h(a) = C(h, 2) - C(h - a_h, 2)` with `a_h = min(a, h - 1)`; this is `a_h(2h - a_h - 1)/2`,
eq. (94). -/
def kappaH (h a : ℕ) : ℕ := h.choose 2 - (h - min a (h - 1)).choose 2

variable {x : ℝ}

lemma one_sub_pow_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) : 0 ≤ 1 - x ^ n :=
  sub_nonneg.2 (pow_le_one₀ hx0 hx1)

lemma one_sub_pow_le_one (hx0 : 0 ≤ x) (n : ℕ) : 1 - x ^ n ≤ 1 :=
  sub_le_self _ (pow_nonneg hx0 n)

lemma isoG_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r0 j : ℕ) : 0 ≤ isoG x r0 j :=
  Finset.prod_nonneg fun _ _ => one_sub_pow_nonneg hx0 hx1 _

lemma isoG_le_one (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r0 j : ℕ) : isoG x r0 j ≤ 1 :=
  Finset.prod_le_one (fun _ _ => one_sub_pow_nonneg hx0 hx1 _) (fun _ _ => one_sub_pow_le_one hx0 _)

lemma isoS_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a l : ℕ) : 0 ≤ isoS x a l :=
  Finset.prod_nonneg fun _ _ => one_sub_pow_nonneg hx0 hx1 _

lemma isoS_le_one (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a l : ℕ) : isoS x a l ≤ 1 :=
  Finset.prod_le_one (fun _ _ => one_sub_pow_nonneg hx0 hx1 _) (fun _ _ => one_sub_pow_le_one hx0 _)

lemma piQ_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) : 0 ≤ piQ x j :=
  Finset.prod_nonneg fun _ _ => one_sub_pow_nonneg hx0 hx1 _

lemma isoQ_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (R h : ℕ) : 0 ≤ isoQ x R h :=
  Finset.prod_nonneg fun _ _ => one_sub_pow_nonneg hx0 hx1 _

lemma isoG_eq_zero {r0 j : ℕ} (h : r0 < j) : isoG x r0 j = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.2 h) (by simp)

lemma isoS_eq_zero {a l : ℕ} (h : a < l) : isoS x a l = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.2 h) (by simp)

/-- `G(j) ≤ 1 - x^r0` for `j ≥ 1`. -/
lemma isoG_le_first (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (r0 n : ℕ) :
    isoG x r0 (n + 1) ≤ 1 - x ^ r0 := by
  unfold isoG
  rw [Finset.prod_range_succ', Nat.sub_zero]
  exact mul_le_of_le_one_left (one_sub_pow_nonneg hx0 hx1 _)
    (Finset.prod_le_one (fun _ _ => one_sub_pow_nonneg hx0 hx1 _)
      (fun _ _ => one_sub_pow_le_one hx0 _))

/-- `S(n+1) ≤ 1 - x^(2a - 2n)`. -/
lemma isoS_le_last (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a n : ℕ) :
    isoS x a (n + 1) ≤ 1 - x ^ (2 * a - 2 * n) := by
  unfold isoS
  rw [Finset.prod_range_succ]
  exact mul_le_of_le_one_left (one_sub_pow_nonneg hx0 hx1 _)
    (Finset.prod_le_one (fun _ _ => one_sub_pow_nonneg hx0 hx1 _)
      (fun _ _ => one_sub_pow_le_one hx0 _))

lemma qBinom_zero_right (x : ℝ) : ∀ i, qBinom x i 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

lemma qBinom_succ_succ (x : ℝ) (i j : ℕ) :
    qBinom x (i + 1) (j + 1) = qBinom x i j + x ^ (j + 1) * qBinom x i (j + 1) := rfl

lemma qBinom_eq_zero (x : ℝ) : ∀ i j, i < j → qBinom x i j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | i + 1, j + 1, h => by
    rw [qBinom_succ_succ, qBinom_eq_zero x i j (by omega), qBinom_eq_zero x i (j + 1) (by omega)]
    ring

lemma qBinom_nonneg (hx0 : 0 ≤ x) : ∀ i j, 0 ≤ qBinom x i j
  | 0, 0 => by rw [qBinom_zero_right]; exact zero_le_one
  | 0, _ + 1 => le_refl (0 : ℝ)
  | _ + 1, 0 => by rw [qBinom_zero_right]; exact zero_le_one
  | i + 1, j + 1 => by
    rw [qBinom_succ_succ]
    exact add_nonneg (qBinom_nonneg hx0 i j)
      (mul_nonneg (pow_nonneg hx0 _) (qBinom_nonneg hx0 i (j + 1)))

/-- `B(i, j) π_j ≤ 1`, i.e. the Gaussian binomial is at most `1/π_j`. -/
lemma qBinom_mul_piQ_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ∀ i j, qBinom x i j * piQ x j ≤ 1
  | 0, 0 => by simp [qBinom_zero_right, piQ]
  | 0, j + 1 => by
    rw [show qBinom x 0 (j + 1) = 0 from rfl, zero_mul]
    exact zero_le_one
  | i + 1, 0 => by simp [qBinom_zero_right, piQ]
  | i + 1, j + 1 => by
    have h1 := qBinom_mul_piQ_le hx0 hx1 i j
    have h2 := qBinom_mul_piQ_le hx0 hx1 i (j + 1)
    have hp : piQ x (j + 1) = piQ x j * (1 - x ^ (j + 1)) := Finset.prod_range_succ _ _
    have hy0 : 0 ≤ x ^ (j + 1) := pow_nonneg hx0 _
    have hy1 : 0 ≤ 1 - x ^ (j + 1) := one_sub_pow_nonneg hx0 hx1 _
    rw [qBinom_succ_succ]
    calc (qBinom x i j + x ^ (j + 1) * qBinom x i (j + 1)) * piQ x (j + 1)
        = (qBinom x i j * piQ x j) * (1 - x ^ (j + 1)) +
            x ^ (j + 1) * (qBinom x i (j + 1) * piQ x (j + 1)) := by rw [hp]; ring
      _ ≤ 1 * (1 - x ^ (j + 1)) + x ^ (j + 1) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hy1) (mul_le_mul_of_nonneg_left h2 hy0)
      _ = 1 := by ring

lemma piQ_one (x : ℝ) : piQ x 1 = 1 - x := by simp [piQ]

lemma piQ_two (x : ℝ) : piQ x 2 = (1 - x) * (1 - x ^ 2) := by
  simp [piQ, Finset.prod_range_succ]

lemma piQ_succ_ge (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ∀ n, 1 - x - x ^ 2 + x ^ (n + 2) ≤ piQ x (n + 1)
  | 0 => by
    simp only [zero_add]
    rw [piQ_one]
    linarith
  | n + 1 => by
    have ih := piQ_succ_ge hx0 hx1 n
    have hp : piQ x (n + 1 + 1) = piQ x (n + 1) * (1 - x ^ (n + 2)) := Finset.prod_range_succ _ _
    rw [hp]
    have hy0 : 0 ≤ x ^ (n + 2) := pow_nonneg hx0 _
    have hyx : x ^ (n + 2) ≤ x ^ 2 := pow_le_pow_of_le_one hx0 hx1 (by omega)
    have h1y : 0 ≤ 1 - x ^ (n + 2) := one_sub_pow_nonneg hx0 hx1 _
    have e3 : x ^ (n + 1 + 2) = x * x ^ (n + 2) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]; ring
    rw [e3]
    nlinarith [mul_nonneg (sub_nonneg.2 ih) h1y, mul_nonneg hy0 (sub_nonneg.2 hyx)]

lemma piQ_ge_quarter (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) (j : ℕ) : 1 / 4 ≤ piQ x j := by
  have hx1 : x ≤ 1 := by linarith
  rcases j with _ | n
  · simp only [piQ, Finset.range_zero, Finset.prod_empty]; norm_num
  · have h := piQ_succ_ge hx0 hx1 n
    have := pow_nonneg hx0 (n + 2)
    nlinarith

lemma qBinom_le_four (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) (i j : ℕ) : qBinom x i j ≤ 4 := by
  have hx1 : x ≤ 1 := by linarith
  have h1 := qBinom_mul_piQ_le hx0 hx1 i j
  have h2 := piQ_ge_quarter hx0 hx12 j
  have h3 := qBinom_nonneg hx0 i j
  nlinarith [mul_nonneg h3 (sub_nonneg.2 h2)]

lemma qBinom_one_le (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) (i : ℕ) :
    qBinom x i 1 * (1 - x) ≤ 1 := by
  have hx1 : x ≤ 1 := by linarith
  have h1 := qBinom_mul_piQ_le hx0 hx1 i 1
  rwa [piQ_one] at h1

lemma qBinom_two_le (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) (i : ℕ) : qBinom x i 2 ≤ 8 / 3 := by
  have hx1 : x ≤ 1 := by linarith
  have h1 := qBinom_mul_piQ_le hx0 hx1 i 2
  rw [piQ_two] at h1
  have h3 := qBinom_nonneg hx0 i 2
  have hq : 0 ≤ (1 / 2 - x) * (5 / 4 + x / 2 - x ^ 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hp : 3 / 8 ≤ (1 - x) * (1 - x ^ 2) := by nlinarith
  nlinarith [mul_nonneg h3 (sub_nonneg.2 hp)]

/-- `Q(h) ≥ 1 - x^(R - h)` for `x ≤ 1/2`. -/
lemma isoQ_ge (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) {R : ℕ} :
    ∀ h, h ≤ R → 1 - x ^ (R - h) ≤ isoQ x R h
  | 0, _ => by
    simp only [isoQ, Finset.range_zero, Finset.prod_empty]
    linarith [pow_nonneg hx0 (R - 0)]
  | h + 1, hh => by
    have ih := isoQ_ge (R := R) hx0 hx12 h (by omega)
    have hp : isoQ x R (h + 1) = isoQ x R h * (1 - x ^ (R - h)) := Finset.prod_range_succ _ _
    rw [hp]
    have e : R - h = (R - (h + 1)) + 1 := by omega
    rw [e, pow_succ] at ih ⊢
    have hy0 : 0 ≤ x ^ (R - (h + 1)) := pow_nonneg hx0 _
    have hy1 : x ^ (R - (h + 1)) ≤ 1 := pow_le_one₀ hx0 (by linarith)
    have h1yx : 0 ≤ 1 - x ^ (R - (h + 1)) * x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ih h1yx, mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 2 * x),
      sq_nonneg (x ^ (R - (h + 1)) * x)]

/-- `Q(h) ≥ π_h` for `h ≤ R`. -/
lemma piQ_le_isoQ (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {R h : ℕ} (hh : h ≤ R) : piQ x h ≤ isoQ x R h := by
  calc piQ x h = ∏ t ∈ range h, (1 - x ^ ((h - 1 - t) + 1)) := by
        unfold piQ
        exact (Finset.prod_range_reflect (fun m => 1 - x ^ (m + 1)) h).symm
    _ ≤ isoQ x R h := by
        refine Finset.prod_le_prod (fun t _ => one_sub_pow_nonneg hx0 hx1 _) (fun t ht => ?_)
        have := Finset.mem_range.1 ht
        exact sub_le_sub_left (pow_le_pow_of_le_one hx0 hx1 (by omega : h - 1 - t + 1 ≤ R - t)) 1

lemma isoQ_pos (hx0 : 0 ≤ x) (hx1 : x < 1) {R h : ℕ} (hh : h ≤ R) : 0 < isoQ x R h :=
  Finset.prod_pos fun t ht => by
    have := Finset.mem_range.1 ht
    exact sub_pos.2 (pow_lt_one₀ hx0 hx1 (by omega))

lemma isoP_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a r0 i j : ℕ) : 0 ≤ isoP x a r0 i j := by
  unfold isoP
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (isoG_nonneg hx0 hx1 _ _))
    (isoS_nonneg hx0 hx1 _ _)) (qBinom_nonneg hx0 _ _)

/-- Generic upper bound for the potential, factor by factor. -/
lemma isoP_le_of (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {a r0 i j e : ℕ} {g s b : ℝ}
    (he : e ≤ isoE a i j) (hg : isoG x r0 j ≤ g) (hs : isoS x a (i - j) ≤ s)
    (hb : qBinom x i j ≤ b) : isoP x a r0 i j ≤ x ^ e * g * s * b := by
  unfold isoP
  have g0 := isoG_nonneg hx0 hx1 r0 j
  have s0 := isoS_nonneg hx0 hx1 a (i - j)
  have b0 := qBinom_nonneg hx0 i j
  have hE : x ^ isoE a i j ≤ x ^ e := pow_le_pow_of_le_one hx0 hx1 he
  have e0 : 0 ≤ x ^ isoE a i j := pow_nonneg hx0 _
  have e0' : 0 ≤ x ^ e := pow_nonneg hx0 _
  apply mul_le_mul _ hb b0 (mul_nonneg (mul_nonneg e0' (g0.trans hg)) (s0.trans hs))
  apply mul_le_mul _ hs s0 (mul_nonneg e0' (g0.trans hg))
  exact mul_le_mul hE hg g0 e0'

lemma isoP_succ_succ (x : ℝ) (a r0 i j : ℕ) :
    isoP x a r0 (i + 1) (j + 1) =
      x ^ isoE a (i + 1) (j + 1) * isoG x r0 (j + 1) * isoS x a (i - j) * qBinom x i j +
      x ^ isoE a (i + 1) (j + 1) * isoG x r0 (j + 1) * isoS x a (i - j) *
        (x ^ (j + 1) * qBinom x i (j + 1)) := by
  unfold isoP
  rw [show i + 1 - (j + 1) = i - j by omega, qBinom_succ_succ]
  ring

end Potential

/-! ### The potential is a solution of the normalised recursion -/

section Steps

variable {x : ℝ} {qN : ℕ}

/-- The fiber sizes of the recursion: `q^(i+r0-j) - q^i` (append a vector of `(S+K) \ S`). -/
def isoC1 (q r0 i j : ℕ) : ℕ := q ^ (i + r0 - j) - q ^ i

/-- `q^(R+j-i) - q^(i+r0-j)` (append a vector of `S^⊥ \ (S+K)`). -/
def isoC2 (q R r0 i j : ℕ) : ℕ := q ^ (R + j - i) - q ^ (i + r0 - j)

lemma xq_pow (hxq : x * (qN : ℝ) = 1) {n m : ℕ} (h : m ≤ n) :
    x ^ n * (qN : ℝ) ^ m = x ^ (n - m) := by
  have e : x ^ n = x ^ (n - m) * x ^ m := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [e, mul_assoc, ← mul_pow, hxq, one_pow, mul_one]

lemma cast_pow_sub (hq : 0 < qN) {m n : ℕ} (h : m ≤ n) :
    ((qN ^ n - qN ^ m : ℕ) : ℝ) = (qN : ℝ) ^ n - (qN : ℝ) ^ m := by
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq h), Nat.cast_pow, Nat.cast_pow]

lemma isoP_stay0 (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxq : x * (qN : ℝ) = 1) (hq : 0 < qN)
    {a r0 R : ℕ} (hR : r0 + 2 * a = R) (i : ℕ) :
    isoP x a r0 i 0 * (x ^ R * (isoC2 qN R r0 i 0 : ℝ)) ≤ isoP x a r0 (i + 1) 0 := by
  by_cases hi : i ≤ a
  · apply le_of_eq
    unfold isoC2
    rw [cast_pow_sub hq (by omega : i + r0 - 0 ≤ R + 0 - i), mul_sub,
      xq_pow hxq (by omega : R + 0 - i ≤ R), xq_pow hxq (by omega : i + r0 - 0 ≤ R)]
    have e1 : R - (R + 0 - i) = i := by omega
    have e2 : R - (i + r0 - 0) = i + (2 * a - 2 * i) := by omega
    rw [e1, e2, pow_add x i (2 * a - 2 * i)]
    have hS : isoS x a (i + 1) = isoS x a i * (1 - x ^ (2 * a - 2 * i)) :=
      Finset.prod_range_succ _ _
    have hE0 : ∀ n, isoE a n 0 = n.choose 2 := fun n => by simp [isoE]
    have hG0 : isoG x r0 0 = 1 := by simp [isoG]
    unfold isoP
    rw [hE0, hE0, hG0, Nat.sub_zero, Nat.sub_zero, qBinom_zero_right, qBinom_zero_right, hS,
      choose_two_succ, pow_add]
    ring
  · push_neg at hi
    have h0 : isoP x a r0 i 0 = 0 := by
      unfold isoP
      rw [Nat.sub_zero, isoS_eq_zero hi]
      ring
    rw [h0, zero_mul]
    exact isoP_nonneg hx0 hx1 _ _ _ _

lemma isoP_inc (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxq : x * (qN : ℝ) = 1) (hq : 0 < qN)
    {a r0 R : ℕ} (hR : r0 + 2 * a = R) (i j : ℕ) :
    isoP x a r0 i j * (x ^ R * (isoC1 qN r0 i j : ℝ)) ≤
      x ^ isoE a (i + 1) (j + 1) * isoG x r0 (j + 1) * isoS x a (i - j) * qBinom x i j := by
  by_cases hf : j ≤ r0 ∧ j ≤ i ∧ i - j ≤ a
  · obtain ⟨h1, h2, h3⟩ := hf
    apply le_of_eq
    unfold isoC1
    rw [cast_pow_sub hq (by omega : i ≤ i + r0 - j), mul_sub,
      xq_pow hxq (by omega : i + r0 - j ≤ R), xq_pow hxq (by omega : i ≤ R)]
    have e1 : R - (i + r0 - j) = 2 * a - (i - j) := by omega
    have e2 : R - i = (2 * a - (i - j)) + (r0 - j) := by omega
    have eE : isoE a (i + 1) (j + 1) = isoE a i j + (2 * a - (i - j)) := by
      unfold isoE
      rw [show i + 1 - (j + 1) = i - j by omega]
      ring
    have eG : isoG x r0 (j + 1) = isoG x r0 j * (1 - x ^ (r0 - j)) := Finset.prod_range_succ _ _
    rw [e1, e2, eE, eG, pow_add x (2 * a - (i - j)) (r0 - j),
      pow_add x (isoE a i j) (2 * a - (i - j))]
    unfold isoP
    ring
  · push_neg at hf
    have h0 : isoP x a r0 i j = 0 := by
      unfold isoP
      by_cases h1 : j ≤ r0
      · by_cases h2 : j ≤ i
        · rw [isoS_eq_zero (hf h1 h2)]; ring
        · rw [qBinom_eq_zero x i j (by omega)]; ring
      · rw [isoG_eq_zero (by omega : r0 < j)]; ring
    rw [h0, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (isoG_nonneg hx0 hx1 _ _))
      (isoS_nonneg hx0 hx1 _ _)) (qBinom_nonneg hx0 _ _)

lemma isoP_stay (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hxq : x * (qN : ℝ) = 1) (hq : 0 < qN)
    {a r0 R : ℕ} (hR : r0 + 2 * a = R) (i j : ℕ) :
    isoP x a r0 i (j + 1) * (x ^ R * (isoC2 qN R r0 i (j + 1) : ℝ)) ≤
      x ^ isoE a (i + 1) (j + 1) * isoG x r0 (j + 1) * isoS x a (i - j) *
        (x ^ (j + 1) * qBinom x i (j + 1)) := by
  by_cases hf : j + 1 ≤ i ∧ i - (j + 1) ≤ a
  · obtain ⟨hji, hla⟩ := hf
    obtain ⟨l, rfl⟩ : ∃ l, i = l + (j + 1) := ⟨i - (j + 1), by omega⟩
    have el : l + (j + 1) - (j + 1) = l := by omega
    have el1 : l + (j + 1) - j = l + 1 := by omega
    rw [el] at hla
    apply le_of_eq
    unfold isoC2
    rw [cast_pow_sub hq (by omega : l + (j + 1) + r0 - (j + 1) ≤ R + (j + 1) - (l + (j + 1))),
      mul_sub, xq_pow hxq (by omega : R + (j + 1) - (l + (j + 1)) ≤ R),
      xq_pow hxq (by omega : l + (j + 1) + r0 - (j + 1) ≤ R)]
    have e1 : R - (R + (j + 1) - (l + (j + 1))) = l := by omega
    have e2 : R - (l + (j + 1) + r0 - (j + 1)) = l + (2 * a - 2 * l) := by omega
    rw [e1, e2, pow_add x l (2 * a - 2 * l), el1]
    have hS : isoS x a (l + 1) = isoS x a l * (1 - x ^ (2 * a - 2 * l)) :=
      Finset.prod_range_succ _ _
    rw [hS]
    unfold isoP
    rw [el]
    rcases Nat.lt_or_ge l a with hl | hl
    · have eE : isoE a (l + (j + 1)) (j + 1) + l = isoE a (l + (j + 1) + 1) (j + 1) + (j + 1) := by
        unfold isoE
        rw [el, show l + (j + 1) + 1 - (j + 1) = l + 1 by omega,
          show 2 * a - l = (2 * a - (l + 1)) + 1 by omega, choose_two_succ]
        ring
      have hpw : x ^ isoE a (l + (j + 1)) (j + 1) * x ^ l =
          x ^ isoE a (l + (j + 1) + 1) (j + 1) * x ^ (j + 1) := by
        rw [← pow_add, ← pow_add, eE]
      linear_combination (isoG x r0 (j + 1) * isoS x a l * qBinom x (l + (j + 1)) (j + 1) *
        (1 - x ^ (2 * a - 2 * l))) * hpw
    · rw [show 2 * a - 2 * l = 0 by omega, pow_zero]
      ring
  · push_neg at hf
    have h0 : isoP x a r0 i (j + 1) = 0 := by
      unfold isoP
      by_cases h2 : j + 1 ≤ i
      · rw [isoS_eq_zero (hf h2)]; ring
      · rw [qBinom_eq_zero x i (j + 1) (by omega)]; ring
    rw [h0, zero_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (isoG_nonneg hx0 hx1 _ _))
      (isoS_nonneg hx0 hx1 _ _)) (mul_nonneg (pow_nonneg hx0 _) (qBinom_nonneg hx0 _ _))

end Steps

/-! ### Counting isotropic tuples -/

section Count

open Classical

variable {F : Type*} [Field F] [Fintype F] {R : ℕ}

/-- Pairwise `A`-orthogonality of a tuple. -/
def PairOrth (A : Matrix (Fin R) (Fin R) F) {i : ℕ} (v : Fin i → (Fin R → F)) : Prop :=
  ∀ s t, bfL (v s) (v t) A = 0

/-- `v` is a linearly independent, pairwise orthogonal `i`-tuple whose span meets `rad A` in
dimension `j`. -/
def IsoTup (A : Matrix (Fin R) (Fin R) F) (i j : ℕ) (v : Fin i → (Fin R → F)) : Prop :=
  LinearIndependent F v ∧ PairOrth A v ∧
    finrank F (Submodule.span F (Set.range v) ⊓ rad A : Submodule F (Fin R → F)) = j

/-- `N(i, j)`: the number of such tuples. -/
noncomputable def isoTupCount (A : Matrix (Fin R) (Fin R) F) (i j : ℕ) : ℕ :=
  (univ.filter (fun v : Fin i → (Fin R → F) => IsoTup A i j v)).card

lemma IsoTup_unique {A : Matrix (Fin R) (Fin R) F} {i j j' : ℕ} {u : Fin i → (Fin R → F)}
    (h1 : IsoTup A i j u) (h2 : IsoTup A i j' u) : j = j' :=
  h1.2.2.symm.trans h2.2.2

lemma card_filter_mem (P : Submodule F (Fin R → F)) :
    (univ.filter (fun y : Fin R → F => y ∈ P)).card = Fintype.card F ^ finrank F P := by
  rw [← Fintype.card_subtype]
  convert Module.card_eq_pow_finrank (K := F) (V := P)

lemma finrank_span_sup {P : Submodule F (Fin R → F)} {y : Fin R → F} (hy : y ∉ P) :
    finrank F ↥(Submodule.span F {y} ⊔ P) = finrank F P + 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ P.zero_mem)
  have hinf : Submodule.span F {y} ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz1
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply hy
      have := P.smul_mem c⁻¹ hz2
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {y}) P
  rw [hinf, finrank_bot, finrank_span_singleton hy0] at this
  omega

lemma finrank_orth (A : Matrix (Fin R) (Fin R) F) (S : Submodule F (Fin R → F)) :
    finrank F S + finrank F ((Matrix.toBilin' A).orthogonal S) =
      R + finrank F (S ⊓ rad A : Submodule F (Fin R → F)) := by
  have := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Matrix.toBilin' A) S
  rwa [Module.finrank_fin_fun] at this

lemma mem_orth_of_forall {A : Matrix (Fin R) (Fin R) F} {i : ℕ} {u : Fin i → (Fin R → F)}
    {y : Fin R → F} (hy : ∀ s, bfL (u s) y A = 0) :
    y ∈ (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u)) := by
  have hle : Submodule.span F (Set.range u) ≤ LinearMap.ker ((Matrix.toBilin' A).flip y) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show Matrix.toBilin' A (u s) y = 0
    rw [Matrix.toBilin'_apply', ← bfL_apply]
    exact hy s
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have := hle hn
  rw [LinearMap.mem_ker] at this
  exact this

lemma isotropic_span {A : Matrix (Fin R) (Fin R) F} {i : ℕ} {v : Fin i → (Fin R → F)}
    (hv : PairOrth A v) : Isotropic A (Submodule.span F (Set.range v)) := by
  have hle : Submodule.span F (Set.range v) ≤
      (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range v)) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun t => mem_orth_of_forall fun s => hv s t)
  intro y hy z hz
  have := (LinearMap.BilinForm.mem_orthogonal_iff.1 (hle hz)) y hy
  rw [Matrix.toBilin'_apply'] at this
  rw [bfL_apply]
  exact this

lemma span_cons {i : ℕ} (y : Fin R → F) (u : Fin i → (Fin R → F)) :
    Submodule.span F (Set.range (Fin.cons y u : Fin (i + 1) → (Fin R → F))) =
      Submodule.span F {y} ⊔ Submodule.span F (Set.range u) := by
  rw [Fin.range_cons, Submodule.span_insert]

/-- Analysis of a one-vector extension `cons y u` of an isotropic tuple. -/
lemma cons_iso {A : Matrix (Fin R) (Fin R) F} (_hA : IsAltMat A) {r0 : ℕ}
    (hr : finrank F (rad A) = r0) {i J : ℕ} {u : Fin i → (Fin R → F)} {y : Fin R → F}
    (h : IsoTup A (i + 1) J (Fin.cons y u)) :
    LinearIndependent F u ∧ PairOrth A u ∧ y ∉ Submodule.span F (Set.range u) ∧
      y ∈ (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u)) ∧
      (y ∈ Submodule.span F (Set.range u) ⊔ rad A →
        J = finrank F (Submodule.span F (Set.range u) ⊓ rad A : Submodule F (Fin R → F)) + 1) ∧
      (y ∉ Submodule.span F (Set.range u) ⊔ rad A →
        J = finrank F (Submodule.span F (Set.range u) ⊓ rad A : Submodule F (Fin R → F))) := by
  obtain ⟨hli, hpo, hJ⟩ := h
  have hli' := hli
  rw [linearIndependent_finCons] at hli'
  obtain ⟨hu, hy⟩ := hli'
  have hpu : PairOrth A u := fun s t => by
    have := hpo s.succ t.succ
    rwa [Fin.cons_succ, Fin.cons_succ] at this
  have hyO : y ∈ (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u)) :=
    mem_orth_of_forall fun s => by
      have := hpo s.succ 0
      rwa [Fin.cons_succ, Fin.cons_zero] at this
  have hS : finrank F (Submodule.span F (Set.range u)) = i := by
    rw [finrank_span_eq_card hu, Fintype.card_fin]
  have hS' : finrank F (Submodule.span F (Set.range (Fin.cons y u : Fin (i + 1) → (Fin R → F))))
      = i + 1 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  rw [span_cons] at hS' hJ
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (Set.range u)) (rad A)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span F {y} ⊔ Submodule.span F (Set.range u)) (rad A)
  rw [hS'] at e2
  rw [hS] at e1
  refine ⟨hu, hpu, hy, hyO, fun hyK => ?_, fun hyK => ?_⟩
  · have hsup : Submodule.span F {y} ⊔ Submodule.span F (Set.range u) ⊔ rad A =
        Submodule.span F (Set.range u) ⊔ rad A := by
      apply le_antisymm
      · exact sup_le (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hyK) le_sup_left)
          le_sup_right
      · exact sup_le_sup_right le_sup_right _
    rw [hsup] at e2
    omega
  · have hsup : finrank F ↥(Submodule.span F {y} ⊔ Submodule.span F (Set.range u) ⊔ rad A) =
        finrank F ↥(Submodule.span F (Set.range u) ⊔ rad A) + 1 := by
      rw [sup_assoc]
      exact finrank_span_sup hyK
    rw [hsup] at e2
    omega

/-- The isotropic subspace `S + K` lies in `S^⊥`. -/
lemma sup_rad_le_orth {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A) {i : ℕ}
    {u : Fin i → (Fin R → F)} (hpu : PairOrth A u) :
    Submodule.span F (Set.range u) ⊔ rad A ≤
      (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u)) := by
  apply sup_le
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 fun t => mem_orth_of_forall fun s => hpu s t)
  · intro k hk
    exact mem_orth_of_forall fun s => bfL_rad_right hA hk (u s)

variable {A : Matrix (Fin R) (Fin R) F}

lemma card_ext_inc (hA : IsAltMat A) {r0 : ℕ} (hr : finrank F (rad A) = r0) {i j : ℕ}
    {u : Fin i → (Fin R → F)} (hj : IsoTup A i j u) :
    (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) (j + 1) (Fin.cons y u))).card ≤
      isoC1 (Fintype.card F) r0 i j := by
  have hsub : univ.filter (fun y : Fin R → F => IsoTup A (i + 1) (j + 1) (Fin.cons y u)) ⊆
      univ.filter (fun y => y ∈ Submodule.span F (Set.range u) ⊔ rad A) \
        univ.filter (fun y => y ∈ Submodule.span F (Set.range u)) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, _, hyS, _, _, hout⟩ := cons_iso hA hr hy.2
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_⟩, fun h => hyS h.2⟩
    by_contra hyK
    have := hout hyK
    have := hj.2.2
    omega
  have hsub2 : univ.filter (fun y : Fin R → F => y ∈ Submodule.span F (Set.range u)) ⊆
      univ.filter (fun y => y ∈ Submodule.span F (Set.range u) ⊔ rad A) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, Submodule.mem_sup_left hy.2⟩
  have hdim : finrank F ↥(Submodule.span F (Set.range u) ⊔ rad A) = i + r0 - j := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (Set.range u)) (rad A)
    rw [finrank_span_eq_card hj.1, Fintype.card_fin, hr, hj.2.2] at e1
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = _ := by
      rw [Finset.card_sdiff_of_subset hsub2, card_filter_mem, card_filter_mem, hdim,
        finrank_span_eq_card hj.1, Fintype.card_fin]
      rfl

lemma card_ext_stay (hA : IsAltMat A) {r0 : ℕ} (hr : finrank F (rad A) = r0) {i j : ℕ}
    {u : Fin i → (Fin R → F)} (hj : IsoTup A i j u) :
    (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) j (Fin.cons y u))).card ≤
      isoC2 (Fintype.card F) R r0 i j := by
  have hsub : univ.filter (fun y : Fin R → F => IsoTup A (i + 1) j (Fin.cons y u)) ⊆
      univ.filter (fun y => y ∈ (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u))) \
        univ.filter (fun y => y ∈ Submodule.span F (Set.range u) ⊔ rad A) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, _, _, hyO, hin, _⟩ := cons_iso hA hr hy.2
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, hyO⟩, fun h => ?_⟩
    have := hin h.2
    have := hj.2.2
    omega
  have hsub2 : univ.filter (fun y : Fin R → F => y ∈ Submodule.span F (Set.range u) ⊔ rad A) ⊆
      univ.filter (fun y => y ∈ (Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u))) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, sup_rad_le_orth hA hj.2.1 hy.2⟩
  have hdim : finrank F ↥(Submodule.span F (Set.range u) ⊔ rad A) = i + r0 - j := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (Set.range u)) (rad A)
    rw [finrank_span_eq_card hj.1, Fintype.card_fin, hr, hj.2.2] at e1
    omega
  have hdimO : finrank F ((Matrix.toBilin' A).orthogonal (Submodule.span F (Set.range u))) =
      R + j - i := by
    have e1 := finrank_orth A (Submodule.span F (Set.range u))
    rw [finrank_span_eq_card hj.1, Fintype.card_fin, hj.2.2] at e1
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = _ := by
      rw [Finset.card_sdiff_of_subset hsub2, card_filter_mem, card_filter_mem, hdim, hdimO]
      rfl

lemma card_ext_other (hA : IsAltMat A) {r0 : ℕ} (hr : finrank F (rad A) = r0) {i j J : ℕ}
    {u : Fin i → (Fin R → F)} (hj : IsoTup A i j u) (h1 : J ≠ j) (h2 : J ≠ j + 1) :
    (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) J (Fin.cons y u))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ hy
  obtain ⟨_, _, _, _, hin, hout⟩ := cons_iso hA hr hy
  have := hj.2.2
  by_cases hyK : y ∈ Submodule.span F (Set.range u) ⊔ rad A
  · have := hin hyK; omega
  · have := hout hyK; omega

lemma card_ext_zero (hA : IsAltMat A) {r0 : ℕ} (hr : finrank F (rad A) = r0) {i J : ℕ}
    {u : Fin i → (Fin R → F)} (hu : ∀ j, ¬ IsoTup A i j u) :
    (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) J (Fin.cons y u))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ hy
  obtain ⟨hli, hpo, _⟩ := cons_iso hA hr hy
  exact hu _ ⟨hli, hpo, rfl⟩

lemma isoTupCount_succ_eq_sum (A : Matrix (Fin R) (Fin R) F) (i J : ℕ) :
    isoTupCount A (i + 1) J = ∑ u : Fin i → (Fin R → F),
      (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) J (Fin.cons y u))).card := by
  unfold isoTupCount
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ : Fin (i + 1) => (Fin R → F)).sum_comp,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.card_filter]
  rfl

/-- The recursion, `j + 1` case. -/
theorem isoTupCount_succ_le (hA : IsAltMat A) {r0 : ℕ} (hr : finrank F (rad A) = r0) (i j : ℕ) :
    isoTupCount A (i + 1) (j + 1) ≤ isoTupCount A i j * isoC1 (Fintype.card F) r0 i j +
      isoTupCount A i (j + 1) * isoC2 (Fintype.card F) R r0 i (j + 1) := by
  rw [isoTupCount_succ_eq_sum]
  have key : ∀ u : Fin i → (Fin R → F),
      (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) (j + 1) (Fin.cons y u))).card ≤
        (if IsoTup A i j u then isoC1 (Fintype.card F) r0 i j else 0) +
        (if IsoTup A i (j + 1) u then isoC2 (Fintype.card F) R r0 i (j + 1) else 0) := by
    intro u
    by_cases h1 : IsoTup A i j u
    · rw [if_pos h1]
      exact (card_ext_inc hA hr h1).trans (Nat.le_add_right _ _)
    · by_cases h2 : IsoTup A i (j + 1) u
      · rw [if_neg h1, if_pos h2, zero_add]
        exact card_ext_stay hA hr h2
      · rw [if_neg h1, if_neg h2, add_zero, Nat.le_zero]
        by_cases hu : ∃ j', IsoTup A i j' u
        · obtain ⟨j', hj'⟩ := hu
          apply card_ext_other hA hr hj'
          · intro h
            exact h2 (by rw [h]; exact hj')
          · intro h
            exact h1 (by rw [show j = j' by omega]; exact hj')
        · push_neg at hu
          exact card_ext_zero hA hr hu
  calc _ ≤ ∑ u : Fin i → (Fin R → F),
        ((if IsoTup A i j u then isoC1 (Fintype.card F) r0 i j else 0) +
        (if IsoTup A i (j + 1) u then isoC2 (Fintype.card F) R r0 i (j + 1) else 0)) :=
        Finset.sum_le_sum (fun u _ => key u)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
        Finset.sum_const, smul_eq_mul, smul_eq_mul]
      rfl

/-- The recursion, `j = 0` case. -/
theorem isoTupCount_succ_zero_le (hA : IsAltMat A) {r0 : ℕ} (hr : finrank F (rad A) = r0)
    (i : ℕ) :
    isoTupCount A (i + 1) 0 ≤ isoTupCount A i 0 * isoC2 (Fintype.card F) R r0 i 0 := by
  rw [isoTupCount_succ_eq_sum]
  have key : ∀ u : Fin i → (Fin R → F),
      (univ.filter (fun y : Fin R → F => IsoTup A (i + 1) 0 (Fin.cons y u))).card ≤
        (if IsoTup A i 0 u then isoC2 (Fintype.card F) R r0 i 0 else 0) := by
    intro u
    by_cases h1 : IsoTup A i 0 u
    · rw [if_pos h1]
      exact card_ext_stay hA hr h1
    · rw [if_neg h1, Nat.le_zero]
      by_cases hu : ∃ j', IsoTup A i j' u
      · obtain ⟨j', hj'⟩ := hu
        apply card_ext_other hA hr hj'
        · intro h
          exact h1 (by rw [h]; exact hj')
        · omega
      · push_neg at hu
        exact card_ext_zero hA hr hu
  calc _ ≤ ∑ u : Fin i → (Fin R → F),
        (if IsoTup A i 0 u then isoC2 (Fintype.card F) R r0 i 0 else 0) :=
        Finset.sum_le_sum (fun u _ => key u)
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rfl

lemma isoTupCount_zero_le (A : Matrix (Fin R) (Fin R) F) : isoTupCount A 0 0 ≤ 1 := by
  unfold isoTupCount
  exact (Finset.card_le_univ _).trans (by simp)

lemma isoTupCount_eq_zero_of_lt (A : Matrix (Fin R) (Fin R) F) {i j : ℕ} (h : i < j) :
    isoTupCount A i j = 0 := by
  unfold isoTupCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hv
  have h1 : finrank F (Submodule.span F (Set.range v) ⊓ rad A : Submodule F (Fin R → F)) ≤
      finrank F (Submodule.span F (Set.range v)) := Submodule.finrank_mono inf_le_left
  rw [finrank_span_eq_card hv.1, Fintype.card_fin, hv.2.2] at h1
  omega

/-- The normalised count is bounded by the potential: `N(i, j) x^(iR) ≤ P(i, j)`. -/
theorem isoTupCount_le (hA : IsAltMat A) {a r0 : ℕ} (hr : finrank F (rad A) = r0)
    (hR : r0 + 2 * a = R) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxq : x * (Fintype.card F : ℝ) = 1) :
    ∀ i j, (isoTupCount A i j : ℝ) * x ^ (i * R) ≤ isoP x a r0 i j := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  intro i
  induction i with
  | zero =>
    intro j
    rcases j with _ | j
    · have h1 : isoP x a r0 0 0 = 1 := by
        simp [isoP, isoE, isoG, isoS, qBinom_zero_right]
      rw [h1, zero_mul, pow_zero, mul_one]
      exact_mod_cast isoTupCount_zero_le A
    · rw [isoTupCount_eq_zero_of_lt A (by omega : 0 < j + 1), Nat.cast_zero, zero_mul]
      exact isoP_nonneg hx0 hx1 _ _ _ _
  | succ i ih =>
    intro j
    have hpow : x ^ ((i + 1) * R) = x ^ (i * R) * x ^ R := by
      rw [← pow_add, add_mul, one_mul]
    rcases j with _ | j
    · have hc := isoTupCount_succ_zero_le hA hr i
      calc (isoTupCount A (i + 1) 0 : ℝ) * x ^ ((i + 1) * R)
          ≤ ((isoTupCount A i 0 * isoC2 (Fintype.card F) R r0 i 0 : ℕ) : ℝ) *
              x ^ ((i + 1) * R) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg hx0 _)
        _ = ((isoTupCount A i 0 : ℝ) * x ^ (i * R)) *
              (x ^ R * (isoC2 (Fintype.card F) R r0 i 0 : ℝ)) := by
            rw [hpow, Nat.cast_mul]; ring
        _ ≤ isoP x a r0 i 0 * (x ^ R * (isoC2 (Fintype.card F) R r0 i 0 : ℝ)) :=
            mul_le_mul_of_nonneg_right (ih 0) (mul_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
        _ ≤ isoP x a r0 (i + 1) 0 := isoP_stay0 hx0 hx1 hxq hq hR i
    · have hc := isoTupCount_succ_le hA hr i j
      calc (isoTupCount A (i + 1) (j + 1) : ℝ) * x ^ ((i + 1) * R)
          ≤ ((isoTupCount A i j * isoC1 (Fintype.card F) r0 i j +
              isoTupCount A i (j + 1) * isoC2 (Fintype.card F) R r0 i (j + 1) : ℕ) : ℝ) *
              x ^ ((i + 1) * R) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg hx0 _)
        _ = ((isoTupCount A i j : ℝ) * x ^ (i * R)) *
              (x ^ R * (isoC1 (Fintype.card F) r0 i j : ℝ)) +
            ((isoTupCount A i (j + 1) : ℝ) * x ^ (i * R)) *
              (x ^ R * (isoC2 (Fintype.card F) R r0 i (j + 1) : ℝ)) := by
            rw [hpow, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]; ring
        _ ≤ isoP x a r0 i j * (x ^ R * (isoC1 (Fintype.card F) r0 i j : ℝ)) +
            isoP x a r0 i (j + 1) * (x ^ R * (isoC2 (Fintype.card F) R r0 i (j + 1) : ℝ)) :=
            add_le_add
              (mul_le_mul_of_nonneg_right (ih j)
                (mul_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)))
              (mul_le_mul_of_nonneg_right (ih (j + 1))
                (mul_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)))
        _ ≤ isoP x a r0 (i + 1) (j + 1) := by
            rw [isoP_succ_succ]
            exact add_le_add (isoP_inc hx0 hx1 hxq hq hR i j) (isoP_stay hx0 hx1 hxq hq hR i j)

/-! ### From tuples to subspaces -/

/-- Ordered bases of an isotropic `h`-space `H` = linearly independent `h`-tuples in `H`. -/
noncomputable def fiberEquiv (A : Matrix (Fin R) (Fin R) F) {h : ℕ}
    {H : Submodule F (Fin R → F)} (hH : H ∈ isoLocus A h) :
    {v : Fin h → (Fin R → F) //
      (LinearIndependent F v ∧ PairOrth A v) ∧ Submodule.span F (Set.range v) = H} ≃
      {w : Fin h → H // LinearIndependent F w} where
  toFun v := ⟨fun s => ⟨v.1 s, by
      have hs : v.1 s ∈ Submodule.span F (Set.range v.1) :=
        Submodule.subset_span (Set.mem_range_self s)
      rw [v.2.2] at hs
      exact hs⟩,
    LinearIndependent.of_comp H.subtype v.2.1.1⟩
  invFun w := by
    have hli : LinearIndependent F (fun s => ((w.1 s : H) : Fin R → F)) :=
      w.2.map' H.subtype (by simp)
    exact ⟨fun s => (w.1 s : Fin R → F), ⟨hli, fun s t => hH.2 _ (w.1 s).2 _ (w.1 t).2⟩,
      Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.2 (Set.range_subset_iff.2 fun s => (w.1 s).2))
        (by rw [finrank_span_eq_card hli, Fintype.card_fin, hH.1])⟩
  left_inv v := by ext s; rfl
  right_inv w := by ext s; rfl

lemma card_fiber_basis (A : Matrix (Fin R) (Fin R) F) {h : ℕ} {H : Submodule F (Fin R → F)}
    (hH : H ∈ isoLocus A h) :
    ((univ.filter (fun v : Fin h → (Fin R → F) => LinearIndependent F v ∧ PairOrth A v)).filter
      (fun v => Submodule.span F (Set.range v) = H)).card =
        ∏ t : Fin h, (Fintype.card F ^ h - Fintype.card F ^ (t : ℕ)) := by
  rw [Finset.filter_filter, ← Fintype.card_subtype]
  rw [Fintype.card_congr (fiberEquiv A hH), ← Nat.card_eq_fintype_card,
    card_linearIndependent (K := F) (V := H) (k := h) hH.1.ge]
  rw [hH.1]

/-- `#{independent pairwise orthogonal h-tuples} = I_h(A) · ∏_{t<h} (q^h - q^t)`. -/
theorem card_isoOrth (A : Matrix (Fin R) (Fin R) F) (h : ℕ) :
    (univ.filter (fun v : Fin h → (Fin R → F) => LinearIndependent F v ∧ PairOrth A v)).card =
      isoCount A h * ∏ t : Fin h, (Fintype.card F ^ h - Fintype.card F ^ (t : ℕ)) := by
  have hfin : (isoLocus A h).Finite := (grass_finite R h).subset (fun H hH => hH.1)
  have hmaps : Set.MapsTo (fun v : Fin h → (Fin R → F) => Submodule.span F (Set.range v))
      ↑(univ.filter (fun v : Fin h → (Fin R → F) => LinearIndependent F v ∧ PairOrth A v))
      ↑hfin.toFinset := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨by rw [finrank_span_eq_card hv.2.1, Fintype.card_fin], isotropic_span hv.2.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, isoCount, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl (fun H hH => ?_)
  rw [Set.Finite.mem_toFinset] at hH
  exact card_fiber_basis A hH

theorem card_isoOrth_eq_sum (A : Matrix (Fin R) (Fin R) F) (h : ℕ) :
    (univ.filter (fun v : Fin h → (Fin R → F) => LinearIndependent F v ∧ PairOrth A v)).card =
      ∑ J ∈ range (h + 1), isoTupCount A h J := by
  have hmaps : Set.MapsTo
      (fun v : Fin h → (Fin R → F) =>
        finrank F (Submodule.span F (Set.range v) ⊓ rad A : Submodule F (Fin R → F)))
      ↑(univ.filter (fun v : Fin h → (Fin R → F) => LinearIndependent F v ∧ PairOrth A v))
      ↑(range (h + 1)) := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    calc _ ≤ finrank F (Submodule.span F (Set.range v)) := Submodule.finrank_mono inf_le_left
      _ = h := by rw [finrank_span_eq_card hv.2.1, Fintype.card_fin]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  unfold isoTupCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_assoc

/-- `|Gr(h, X)| · ∏_{t<h} (q^h - q^t) = ∏_{t<h} (q^R - q^t)`. -/
theorem grass_mul_card {h : ℕ} (hh : h ≤ R) :
    {H : Submodule F (Fin R → F) | finrank F H = h}.ncard *
        ∏ t : Fin h, (Fintype.card F ^ h - Fintype.card F ^ (t : ℕ)) =
      ∏ t : Fin h, (Fintype.card F ^ R - Fintype.card F ^ (t : ℕ)) := by
  have h0 := card_isoOrth (0 : Matrix (Fin R) (Fin R) F) h
  rw [isoCount, isoLocus_zero] at h0
  rw [← h0]
  have e : univ.filter (fun v : Fin h → (Fin R → F) =>
      LinearIndependent F v ∧ PairOrth (0 : Matrix (Fin R) (Fin R) F) v) =
      univ.filter (fun v : Fin h → (Fin R → F) => LinearIndependent F v) := by
    ext v
    simp [PairOrth]
  rw [e, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    card_linearIndependent (K := F) (V := Fin R → F) (k := h)
      (by rw [Module.finrank_fin_fun]; exact hh), Module.finrank_fin_fun]

/-- `x^(hR) ∏_{t<h} (q^R - q^t) = Q(h)`. -/
lemma cast_prod_eq_isoQ {x : ℝ} (hxq : x * (Fintype.card F : ℝ) = 1) {h : ℕ} (hh : h ≤ R) :
    ((∏ t : Fin h, (Fintype.card F ^ R - Fintype.card F ^ (t : ℕ)) : ℕ) : ℝ) * x ^ (h * R) =
      isoQ x R h := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hx : x ^ (h * R) = ∏ _t : Fin h, x ^ R := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  rw [Nat.cast_prod, hx, ← Finset.prod_mul_distrib, isoQ, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have ht := t.isLt
  rw [cast_pow_sub hq (by omega : (t : ℕ) ≤ R), sub_mul]
  have h1 : (Fintype.card F : ℝ) ^ R * x ^ R = 1 := by rw [← mul_pow, mul_comm, hxq, one_pow]
  have h2 : (Fintype.card F : ℝ) ^ (t : ℕ) * x ^ R = x ^ (R - t) := by
    rw [mul_comm]; exact xq_pow hxq (by omega)
  rw [h1, h2]

/-- **Lemma 8.1 (upper bound, normalised form).** For an alternating `A` with `dim rad A = r0`
and `R = r0 + 2a`:  `I_h(A) · Q(h) ≤ |Gr(h, X)| · Σ_{j ≤ h} P(h, j)`, `x = 1/q`.
Only this upper bound is formalized: the equality (93) and the identification of `P(h, j)`
with the paper's summand are not proved here (the latter was checked numerically only).
Downstream uses go through (95)/(96) (`isoCount_uniform`, `isoCount_saturated`). -/
theorem isoCount_mul_isoQ_le (hA : IsAltMat A) {a r0 h : ℕ} (hr : finrank F (rad A) = r0)
    (hR : r0 + 2 * a = R) (hh : h ≤ R) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxq : x * (Fintype.card F : ℝ) = 1) :
    (isoCount A h : ℝ) * isoQ x R h ≤
      ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) *
        ∑ J ∈ range (h + 1), isoP x a r0 h J := by
  have h1 : ((isoCount A h * ∏ t : Fin h, (Fintype.card F ^ h - Fintype.card F ^ (t : ℕ)) : ℕ)
      : ℝ) * x ^ (h * R) ≤ ∑ J ∈ range (h + 1), isoP x a r0 h J := by
    rw [← card_isoOrth, card_isoOrth_eq_sum, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun J _ => isoTupCount_le hA hr hR hx0 hx1 hxq h J
  have h2 : (({H : Submodule F (Fin R → F) | finrank F H = h}.ncard *
      ∏ t : Fin h, (Fintype.card F ^ h - Fintype.card F ^ (t : ℕ)) : ℕ) : ℝ) *
      x ^ (h * R) = isoQ x R h := by
    rw [grass_mul_card hh]
    exact cast_prod_eq_isoQ hxq hh
  rw [← h2]
  rw [Nat.cast_mul] at h1 ⊢
  have h3 := mul_le_mul_of_nonneg_left h1
    (Nat.cast_nonneg (α := ℝ) {H : Submodule F (Fin R → F) | finrank F H = h}.ncard)
  linarith

/-! ### The rank of an alternating form is even

A maximal isotropic subspace `H` containing `rad A` satisfies `H^⊥ = H`; then
`2 dim H = R + dim rad A` by `finrank_orth`, so `R - dim rad A = 2 (dim H - dim rad A)`. -/

lemma toBilin'_eq_bfL (A : Matrix (Fin R) (Fin R) F) (x z : Fin R → F) :
    Matrix.toBilin' A x z = bfL x z A := by
  rw [Matrix.toBilin'_apply', bfL_apply]

lemma mem_orth_iff_bfL {A : Matrix (Fin R) (Fin R) F} {U : Submodule F (Fin R → F)}
    {y : Fin R → F} :
    y ∈ (Matrix.toBilin' A).orthogonal U ↔ ∀ u ∈ U, bfL u y A = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun u _ => ?_
  show Matrix.toBilin' A u y = 0 ↔ _
  rw [toBilin'_eq_bfL]

/-- Adjoining a vector of `U^⊥` to an isotropic `U` keeps it isotropic. -/
lemma isotropic_sup_span {A : Matrix (Fin R) (Fin R) F} (hA : IsAltMat A)
    {U : Submodule F (Fin R → F)} (hU : Isotropic A U) {y : Fin R → F}
    (hy : y ∈ (Matrix.toBilin' A).orthogonal U) :
    Isotropic A (Submodule.span F {y} ⊔ U) := by
  have hy' := mem_orth_iff_bfL.1 hy
  intro w1 hw1 w2 hw2
  obtain ⟨a1, ha1, u1, hu1, rfl⟩ := Submodule.mem_sup.1 hw1
  obtain ⟨a2, ha2, u2, hu2, rfl⟩ := Submodule.mem_sup.1 hw2
  obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.1 ha1
  obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.1 ha2
  have e1 := bfL_self_eq_zero hA y
  have e2 : bfL y u2 A = 0 := by rw [bfL_swap hA, hy' u2 hu2, neg_zero]
  have e3 := hy' u1 hu1
  have e4 := hU u1 hu1 u2 hu2
  rw [← toBilin'_eq_bfL]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [toBilin'_eq_bfL, e1, e2, e3, e4, mul_zero, add_zero]

/-- Every isotropic `U ⊇ rad A` lies in an isotropic `H` with `H^⊥ ≤ H`. -/
lemma exists_isotropic_orth_le (hA : IsAltMat A) :
    ∀ n (U : Submodule F (Fin R → F)), Isotropic A U → rad A ≤ U → R - finrank F U = n →
      ∃ H : Submodule F (Fin R → F),
        Isotropic A H ∧ rad A ≤ H ∧ (Matrix.toBilin' A).orthogonal H ≤ H := by
  intro n
  induction n with
  | zero =>
    intro U hU hrU hn
    by_cases hle : (Matrix.toBilin' A).orthogonal U ≤ U
    · exact ⟨U, hU, hrU, hle⟩
    · exfalso
      obtain ⟨y, -, hyU⟩ := SetLike.not_le_iff_exists.1 hle
      have h1 := finrank_span_sup hyU
      have h2 := Submodule.finrank_le (Submodule.span F {y} ⊔ U)
      rw [Module.finrank_fin_fun] at h2
      omega
  | succ n ih =>
    intro U hU hrU hn
    by_cases hle : (Matrix.toBilin' A).orthogonal U ≤ U
    · exact ⟨U, hU, hrU, hle⟩
    · obtain ⟨y, hy, hyU⟩ := SetLike.not_le_iff_exists.1 hle
      refine ih _ (isotropic_sup_span hA hU hy) (hrU.trans le_sup_right) ?_
      rw [finrank_span_sup hyU]
      omega

/-- **The rank of an alternating form is even**: `dim rad A + 2a = R` for some `a`. -/
theorem exists_finrank_rad_add_two_mul (hA : IsAltMat A) :
    ∃ a : ℕ, finrank F (rad A) + 2 * a = R := by
  obtain ⟨H, hH, hrH, hHo⟩ := exists_isotropic_orth_le hA _ (rad A)
    (fun x hx y _ => bfL_rad_left hx y) le_rfl rfl
  have hle : H ≤ (Matrix.toBilin' A).orthogonal H :=
    fun y hy => mem_orth_iff_bfL.2 fun u hu => hH u hu y hy
  have hEq : (Matrix.toBilin' A).orthogonal H = H := le_antisymm hHo hle
  have hf := finrank_orth A H
  rw [hEq, inf_eq_right.2 hrH] at hf
  have hm := Submodule.finrank_mono hrH
  exact ⟨finrank F H - finrank F (rad A), by omega⟩

/-- `R - dim rad A` is even for alternating `A`. -/
theorem even_sub_finrank_rad (hA : IsAltMat A) : Even (R - finrank F (rad A)) := by
  obtain ⟨a, ha⟩ := exists_finrank_rad_add_two_mul hA
  exact ⟨a, by omega⟩

end Count

/-! ### Lemma 8.2: the exponent bounds and the final estimates -/

section Exponents

/-- `κ_h(a) + (j - j_0) ≤ E(h, j)` on the feasible range `h - a ≤ j ≤ h`, `j_0 = h - min(a, h)`
(the loss function (101) grows at least linearly from its minimum `κ_h(a)`). -/
lemma isoE_ge_kappa {a h J : ℕ} (hJ : J ≤ h) (hl : h - J ≤ a) :
    kappaH h a + (J - (h - min a h)) ≤ isoE a h J := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · obtain rfl : J = 0 := by omega
    simp [kappaH, isoE]
  · by_cases hah : a < h
    · obtain ⟨e, m, d, rfl, rfl, rfl⟩ : ∃ e m d, h = e + m + d ∧ a = e + m ∧ J = d + m :=
        ⟨h - J, J - (h - a), h - a, by omega, by omega, by omega⟩
      have k1 : min (e + m) (e + m + d - 1) = e + m := by omega
      have k2 : min (e + m) (e + m + d) = e + m := by omega
      unfold kappaH isoE
      rw [k1, k2, show e + m + d - (e + m) = d by omega, show e + m + d - (d + m) = e by omega,
        show 2 * (e + m) - e = e + 2 * m by omega, show d + m - d = m by omega]
      have T1 := two_mul_choose_two_add (e + m + d)
      have T2 := two_mul_choose_two_add d
      have T3 := two_mul_choose_two_add e
      have hle : d.choose 2 ≤ (e + m + d).choose 2 := Nat.choose_le_choose 2 (by omega)
      have key : (e + m + d).choose 2 + m ≤ e.choose 2 + (d + m) * (e + 2 * m) + d.choose 2 := by
        nlinarith [Nat.zero_le (d * m), Nat.le_mul_self m]
      omega
    · push_neg at hah
      obtain ⟨l, rfl⟩ : ∃ l, h = l + J := ⟨h - J, by omega⟩
      have k1 : min a (l + J - 1) = l + J - 1 := by omega
      have k2 : min a (l + J) = l + J := by omega
      unfold kappaH isoE
      rw [k1, k2, show l + J - (l + J - 1) = 1 by omega, show l + J - (l + J) = 0 by omega,
        show l + J - J = l by omega, Nat.sub_zero,
        Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2), Nat.sub_zero]
      have c : l + 2 * J ≤ 2 * a - l := by omega
      have T1 := two_mul_choose_two_add (l + J)
      have T2 := two_mul_choose_two_add l
      have hc := Nat.mul_le_mul_left J c
      nlinarith [Nat.le_mul_self J]

/-- The exact identity `2 E(h, j) + 4hj = 2 C(h,2) + j (4a + 3j + 1)` (cf. (101)). -/
lemma isoE_two_mul {a h J : ℕ} (hJ : J ≤ h) (hl : h - J ≤ 2 * a) :
    2 * isoE a h J + 4 * h * J = 2 * h.choose 2 + J * (4 * a + 3 * J + 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, h = l + J := ⟨h - J, by omega⟩
  unfold isoE
  rw [show l + J - J = l by omega]
  obtain ⟨c, hc⟩ : ∃ c, 2 * a = c + l := ⟨2 * a - l, by omega⟩
  rw [show 2 * a - l = c by omega]
  have T1 := two_mul_choose_two_add (l + J)
  have T2 := two_mul_choose_two_add l
  have hc' : J * (2 * a) = J * (c + l) := by rw [hc]
  apply le_antisymm <;> nlinarith [hc']

/-- `kappaH` is the paper's `κ_h(a) = a_h (2h - a_h - 1) / 2`, eq. (94), `a_h = min(a, h - 1)`. -/
lemma two_mul_kappaH (h a : ℕ) :
    2 * kappaH h a = min a (h - 1) * (2 * h - min a (h - 1) - 1) := by
  unfold kappaH
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  · obtain ⟨b, hb⟩ : ∃ b, min a (h - 1) = b := ⟨_, rfl⟩
    rw [hb]
    have hbh : b + 1 ≤ h := by omega
    obtain ⟨d, rfl⟩ : ∃ d, h = b + d := ⟨h - b, by omega⟩
    rw [show b + d - b = d by omega, show 2 * (b + d) - b - 1 = b + 2 * d - 1 by omega]
    have T1 := two_mul_choose_two_add (b + d)
    have T2 := two_mul_choose_two_add d
    have hle : d.choose 2 ≤ (b + d).choose 2 := Nat.choose_le_choose 2 (by omega)
    have h1 : b + 2 * d - 1 + 1 = b + 2 * d := by omega
    have hP : b * (b + 2 * d - 1) + b = b * (b + 2 * d) := by
      calc b * (b + 2 * d - 1) + b = b * (b + 2 * d - 1 + 1) := by ring
        _ = b * (b + 2 * d) := by rw [h1]
    have H : 2 * (b + d).choose 2 + b = b * (b + 2 * d) + 2 * d.choose 2 := by
      apply le_antisymm <;> nlinarith [T1, T2]
    omega

lemma kappaH_of_le {h a : ℕ} (hah : h ≤ a + 1) : kappaH h a = h.choose 2 := by
  unfold kappaH
  rw [show min a (h - 1) = h - 1 by omega,
    Nat.choose_eq_zero_of_lt (by omega : h - (h - 1) < 2), Nat.sub_zero]

lemma kappaH_mono (h : ℕ) {a b : ℕ} (hab : a ≤ b) : kappaH h a ≤ kappaH h b := by
  unfold kappaH
  exact Nat.sub_le_sub_left (Nat.choose_le_choose 2 (by omega)) _

/-- `κ_h(1) = h - 1`. -/
lemma kappaH_one (h : ℕ) : kappaH h 1 = h - 1 := by
  unfold kappaH
  rcases Nat.lt_or_ge h 2 with hh | hh
  · interval_cases h <;> rfl
  · obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
    rw [show min 1 (n + 2 - 1) = 1 by omega, show n + 2 - 1 = n + 1 by omega,
      show n + 2 = n + 1 + 1 by omega, choose_two_succ (n + 1)]
    omega

/-- `κ_h(a) ≥ κ_h(1) = h - 1` for `a ≥ 1`. -/
lemma sub_one_le_kappaH {h a : ℕ} (ha : 1 ≤ a) : h - 1 ≤ kappaH h a := by
  rw [← kappaH_one]
  exact kappaH_mono h ha

end Exponents

section Final

variable {x : ℝ}

lemma geom_le_two (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) : ∀ n, ∑ m ∈ range n, x ^ m ≤ 2 - 2 * x ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := geom_le_two hx0 hx12 n
    have h2 := mul_nonneg (pow_nonneg hx0 n) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)
    nlinarith

/-- Uniform estimate behind (95): `Σ_j P(h, j) ≤ 8 x^(κ_h(a))`. -/
lemma sum_isoP_le_uniform (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) (a r0 h : ℕ) :
    ∑ J ∈ range (h + 1), isoP x a r0 h J ≤ 8 * x ^ kappaH h a := by
  have hx1 : x ≤ 1 := by linarith
  have hsplit : h + 1 = (h - min a h) + (min a h + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst : ∑ J ∈ range (h - min a h), isoP x a r0 h J = 0 := by
    refine Finset.sum_eq_zero (fun J hJ => ?_)
    have := Finset.mem_range.1 hJ
    unfold isoP
    rw [isoS_eq_zero (show a < h - J by omega)]
    ring
  rw [hfirst, zero_add]
  have hterm : ∀ m ∈ range (min a h + 1),
      isoP x a r0 h (h - min a h + m) ≤ 4 * x ^ kappaH h a * x ^ m := by
    intro m hm
    have hm' := Finset.mem_range.1 hm
    have hE := isoE_ge_kappa (a := a) (h := h) (J := h - min a h + m) (by omega) (by omega)
    rw [show h - min a h + m - (h - min a h) = m by omega] at hE
    have := isoP_le_of (a := a) (r0 := r0) (i := h) (j := h - min a h + m) hx0 hx1 hE
      (isoG_le_one hx0 hx1 _ _) (isoS_le_one hx0 hx1 _ _) (qBinom_le_four hx0 hx12 _ _)
    calc _ ≤ _ := this
      _ = 4 * x ^ kappaH h a * x ^ m := by rw [pow_add]; ring
  calc _ ≤ ∑ m ∈ range (min a h + 1), 4 * x ^ kappaH h a * x ^ m := Finset.sum_le_sum hterm
    _ = 4 * x ^ kappaH h a * ∑ m ∈ range (min a h + 1), x ^ m := by rw [Finset.mul_sum]
    _ ≤ 4 * x ^ kappaH h a * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (pow_nonneg hx0 _))
        have := geom_le_two hx0 hx12 (min a h + 1)
        have := pow_nonneg hx0 (min a h + 1)
        linarith
    _ = 8 * x ^ kappaH h a := by ring

/-- Saturated estimate behind (96): for `a ≥ h - 1 ≥ 1`, `Σ_j P(h, j) ≤ (15/8) x^C(h,2) Q(h)`. -/
lemma sum_isoP_le_sat (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) {a r0 R h : ℕ} (hR : r0 + 2 * a = R)
    (h2 : 2 ≤ h) (hah : h ≤ a + 1) :
    ∑ J ∈ range (h + 1), isoP x a r0 h J ≤ 15 / 8 * x ^ h.choose 2 * isoQ x R h := by
  have hx1 : x ≤ 1 := by linarith
  have hhR : h ≤ R := by omega
  have hQ : 1 - x ^ (R - h) ≤ isoQ x R h := isoQ_ge hx0 hx12 h hhR
  have hQ0 : 0 ≤ isoQ x R h := isoQ_nonneg hx0 hx1 R h
  have hC0 : 0 ≤ x ^ h.choose 2 := pow_nonneg hx0 _
  have hCQ : 0 ≤ x ^ h.choose 2 * isoQ x R h := mul_nonneg hC0 hQ0
  have hGQ : ∀ n, isoG x r0 (n + 1) ≤ isoQ x R h := fun n =>
    (isoG_le_first hx0 hx1 r0 n).trans
      ((sub_le_sub_left (pow_le_pow_of_le_one hx0 hx1 (by omega : r0 ≤ R - h)) 1).trans hQ)
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hx3 : x ^ 3 ≤ 1 / 8 := by
    have : x ^ 3 = x ^ 2 * x := pow_succ x 2
    nlinarith [pow_nonneg hx0 2]
  have hE : ∀ J, J ≤ h → 2 * isoE a h J + 4 * h * J = 2 * h.choose 2 + J * (4 * a + 3 * J + 1) :=
    fun J hJ => isoE_two_mul hJ (by omega)
  rw [show h + 1 = 3 + (h - 2) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- the terms `j = 0, 1`
  have b01 : isoP x a r0 h 0 + isoP x a r0 h 1 ≤ 3 / 2 * (x ^ h.choose 2 * isoQ x R h) := by
    have hB1 := qBinom_one_le hx0 hx12 h
    have hB1' : qBinom x h 1 ≤ 2 := by nlinarith [qBinom_nonneg hx0 h 1]
    by_cases hah' : h ≤ a
    · have hE1 := hE 1 (by omega)
      have hSh : isoS x a h ≤ 1 - x ^ (2 * a - 2 * (h - 1)) := by
        have := isoS_le_last hx0 hx1 a (h - 1)
        rwa [show h - 1 + 1 = h by omega] at this
      have hsh : isoS x a (h - 0) ≤ isoQ x R h := by
        rw [Nat.sub_zero]
        exact hSh.trans ((sub_le_sub_left
          (pow_le_pow_of_le_one hx0 hx1 (by omega : 2 * a - 2 * (h - 1) ≤ R - h)) 1).trans hQ)
      have hE0 : h.choose 2 ≤ isoE a h 0 := by simp [isoE]
      have p0 : isoP x a r0 h 0 ≤ x ^ h.choose 2 * 1 * isoQ x R h * 1 :=
        isoP_le_of hx0 hx1 hE0 (isoG_le_one hx0 hx1 _ _) hsh (le_of_eq (qBinom_zero_right x h))
      have p1 : isoP x a r0 h 1 ≤ x ^ (h.choose 2 + 2) * isoQ x R h * 1 * 2 :=
        isoP_le_of hx0 hx1 (by omega) (hGQ 0) (isoS_le_one hx0 hx1 _ _) hB1'
      rw [pow_add] at p1
      nlinarith [mul_le_mul_of_nonneg_left hx2 hCQ]
    · have hah2 : a + 1 = h := by omega
      have p0 : isoP x a r0 h 0 = 0 := by
        unfold isoP
        rw [isoS_eq_zero (by omega : a < h - 0)]
        ring
      have hE1 := hE 1 (by omega)
      have hS : isoS x a (h - 1) ≤ 1 - x ^ 2 := by
        rw [show h - 1 = (h - 2) + 1 by omega]
        refine (isoS_le_last hx0 hx1 a (h - 2)).trans ?_
        rw [show 2 * a - 2 * (h - 2) = 2 by omega]
      have p1 : isoP x a r0 h 1 ≤ x ^ h.choose 2 * isoQ x R h * (1 - x ^ 2) * qBinom x h 1 :=
        isoP_le_of hx0 hx1 (by omega) (hGQ 0) hS le_rfl
      have hB : (1 - x ^ 2) * qBinom x h 1 ≤ 3 / 2 := by
        have : (1 - x ^ 2) * qBinom x h 1 = (1 + x) * (qBinom x h 1 * (1 - x)) := by ring
        rw [this]
        nlinarith
      rw [p0, zero_add]
      calc _ ≤ _ := p1
        _ = (x ^ h.choose 2 * isoQ x R h) * ((1 - x ^ 2) * qBinom x h 1) := by ring
        _ ≤ (x ^ h.choose 2 * isoQ x R h) * (3 / 2) := mul_le_mul_of_nonneg_left hB hCQ
        _ = _ := by ring
  -- the term `j = 2`
  have b2 : isoP x a r0 h 2 ≤ 1 / 3 * (x ^ h.choose 2 * isoQ x R h) := by
    have hE2 := hE 2 (by omega)
    have p2 : isoP x a r0 h 2 ≤ x ^ (h.choose 2 + 3) * isoQ x R h * 1 * (8 / 3) :=
      isoP_le_of hx0 hx1 (by omega) (hGQ 1) (isoS_le_one hx0 hx1 _ _) (qBinom_two_le hx0 hx12 h)
    rw [pow_add] at p2
    nlinarith [mul_le_mul_of_nonneg_left hx3 hCQ]
  -- the tail `j ≥ 3`
  have bt : ∑ k ∈ range (h - 2), isoP x a r0 h (3 + k) ≤
      1 / 64 * (x ^ h.choose 2 * isoQ x R h) := by
    have hterm : ∀ k ∈ range (h - 2),
        isoP x a r0 h (3 + k) ≤ (4 * x ^ 9 * (x ^ h.choose 2 * isoQ x R h)) * x ^ k := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hEk := hE (3 + k) (by omega)
      have hge : h.choose 2 + 9 + 6 * k ≤ isoE a h (3 + k) := by
        have hmul : (3 + k) * (4 * h) ≤ (3 + k) * (4 * a + 4) := Nat.mul_le_mul_left _ (by omega)
        nlinarith [hmul]
      have hGk : isoG x r0 (3 + k) ≤ isoQ x R h := by
        have := hGQ (2 + k)
        rwa [show 2 + k + 1 = 3 + k by omega] at this
      have pk := isoP_le_of (a := a) (r0 := r0) (i := h) (j := 3 + k) hx0 hx1 hge hGk
        (isoS_le_one hx0 hx1 _ _) (qBinom_le_four hx0 hx12 _ _)
      have hxk : x ^ (6 * k) ≤ x ^ k := pow_le_pow_of_le_one hx0 hx1 (by omega)
      have e : x ^ (h.choose 2 + 9 + 6 * k) = x ^ h.choose 2 * x ^ 9 * x ^ (6 * k) := by
        rw [pow_add, pow_add]
      rw [e] at pk
      have h9 : 0 ≤ x ^ 9 := pow_nonneg hx0 9
      calc _ ≤ _ := pk
        _ = (4 * x ^ 9 * (x ^ h.choose 2 * isoQ x R h)) * x ^ (6 * k) := by ring
        _ ≤ (4 * x ^ 9 * (x ^ h.choose 2 * isoQ x R h)) * x ^ k :=
            mul_le_mul_of_nonneg_left hxk (mul_nonneg (mul_nonneg (by norm_num) h9) hCQ)
    have hx9 : x ^ 9 ≤ 1 / 512 := by
      have : x ^ 9 = (x ^ 3) ^ 3 := by rw [← pow_mul]
      rw [this]
      have h30 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
      calc (x ^ 3) ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ h30 hx3 3
        _ = 1 / 512 := by norm_num
    have hg := geom_le_two hx0 hx12 (h - 2)
    have hg0 := pow_nonneg hx0 (h - 2)
    calc _ ≤ ∑ k ∈ range (h - 2), (4 * x ^ 9 * (x ^ h.choose 2 * isoQ x R h)) * x ^ k :=
          Finset.sum_le_sum hterm
      _ = (4 * x ^ 9 * (x ^ h.choose 2 * isoQ x R h)) * ∑ k ∈ range (h - 2), x ^ k := by
          rw [Finset.mul_sum]
      _ ≤ (4 * x ^ 9 * (x ^ h.choose 2 * isoQ x R h)) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 9)) hCQ)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hx9 hCQ]
  have hsum : isoP x a r0 h 0 + isoP x a r0 h 1 + isoP x a r0 h 2 +
      ∑ k ∈ range (h - 2), isoP x a r0 h (3 + k) ≤ 15 / 8 * x ^ h.choose 2 * isoQ x R h := by
    nlinarith
  linarith

variable {F : Type*} [Field F] [Fintype F] {R : ℕ} {A : Matrix (Fin R) (Fin R) F}

lemma inv_card_facts :
    0 ≤ (Fintype.card F : ℝ)⁻¹ ∧ (Fintype.card F : ℝ)⁻¹ ≤ 1 / 2 ∧
      (Fintype.card F : ℝ)⁻¹ * (Fintype.card F : ℝ) = 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  refine ⟨inv_nonneg.2 hq0.le, ?_, inv_mul_cancel₀ hq0.ne'⟩
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hq2

lemma isoCount_eq_zero_of_lt {h : ℕ} (hh : R < h) : isoCount A h = 0 := by
  have hle := isoCount_le_grass A h
  have he : {H : Submodule F (Fin R → F) | finrank F H = h} = ∅ := by
    ext H
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hH
    have := Submodule.finrank_le H
    rw [Module.finrank_fin_fun] at this
    omega
  rw [he, Set.ncard_empty] at hle
  omega

/-- **Lemma 8.2, (95)** (crude constant `32`): `I_h(A) q^(κ_h(a)) ≤ 32 |Gr(h, X)|` when
`dim rad A = r0` and `R = r0 + 2a`. -/
theorem isoCount_uniform (hA : IsAltMat A) {a r0 : ℕ} (hr : finrank F (rad A) = r0)
    (hR : r0 + 2 * a = R) (h : ℕ) :
    (isoCount A h : ℝ) * (Fintype.card F : ℝ) ^ kappaH h a ≤
      32 * ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) := by
  obtain ⟨x, hx0, hx12, hxq⟩ : ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 / 2 ∧ x * (Fintype.card F : ℝ) = 1 :=
    ⟨_, inv_card_facts (F := F)⟩
  have hx1 : x ≤ 1 := by linarith
  by_cases hhR : h ≤ R
  · have main := isoCount_mul_isoQ_le hA hr hR hhR hx0 hx1 hxq
    have hs := sum_isoP_le_uniform hx0 hx12 a r0 h
    have hQ : 1 / 4 ≤ isoQ x R h := (piQ_ge_quarter hx0 hx12 h).trans (piQ_le_isoQ hx0 hx1 hhR)
    have hI0 : (0 : ℝ) ≤ isoCount A h := Nat.cast_nonneg _
    have hGr0 : (0 : ℝ) ≤ ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) :=
      Nat.cast_nonneg _
    have h1 : (isoCount A h : ℝ) * (1 / 4) ≤
        ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) * (8 * x ^ kappaH h a) :=
      (mul_le_mul_of_nonneg_left hQ hI0).trans (main.trans (mul_le_mul_of_nonneg_left hs hGr0))
    have hk : x ^ kappaH h a * (Fintype.card F : ℝ) ^ kappaH h a = 1 := by
      rw [← mul_pow, hxq, one_pow]
    have hpk : 0 ≤ (Fintype.card F : ℝ) ^ kappaH h a := by positivity
    have h2 := mul_le_mul_of_nonneg_right h1 hpk
    calc (isoCount A h : ℝ) * (Fintype.card F : ℝ) ^ kappaH h a
        = 4 * ((isoCount A h : ℝ) * (1 / 4) * (Fintype.card F : ℝ) ^ kappaH h a) := by ring
      _ ≤ 4 * (({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) *
            (8 * x ^ kappaH h a) * (Fintype.card F : ℝ) ^ kappaH h a) := by linarith
      _ = 32 * ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) *
            (x ^ kappaH h a * (Fintype.card F : ℝ) ^ kappaH h a) := by ring
      _ = _ := by rw [hk, mul_one]
  · push_neg at hhR
    rw [isoCount_eq_zero_of_lt hhR, Nat.cast_zero, zero_mul]
    positivity

/-- **Lemma 8.2, (96)** with `γ_q ≤ 15/8 < 2`: if `a ≥ h - 1` then
`I_h(A) q^(C(h,2)) ≤ (15/8) |Gr(h, X)|`. -/
theorem isoCount_saturated (hA : IsAltMat A) {a r0 : ℕ} (hr : finrank F (rad A) = r0)
    (hR : r0 + 2 * a = R) {h : ℕ} (hah : h ≤ a + 1) :
    (isoCount A h : ℝ) * (Fintype.card F : ℝ) ^ h.choose 2 ≤
      15 / 8 * ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) := by
  obtain ⟨x, hx0, hx12, hxq⟩ : ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 / 2 ∧ x * (Fintype.card F : ℝ) = 1 :=
    ⟨_, inv_card_facts (F := F)⟩
  have hx1 : x < 1 := by linarith
  have hx1' : x ≤ 1 := by linarith
  have hGr0 : (0 : ℝ) ≤ ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) :=
    Nat.cast_nonneg _
  by_cases h2 : 2 ≤ h
  · have hhR : h ≤ R := by omega
    have main := isoCount_mul_isoQ_le hA hr hR hhR hx0 hx1' hxq
    have hs := sum_isoP_le_sat hx0 hx12 hR h2 hah
    have hQpos : 0 < isoQ x R h := isoQ_pos hx0 hx1 hhR
    have h1 : (isoCount A h : ℝ) * isoQ x R h ≤
        (({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) * (15 / 8 * x ^ h.choose 2))
          * isoQ x R h := by
      calc _ ≤ _ := main.trans (mul_le_mul_of_nonneg_left hs hGr0)
        _ = _ := by ring
    have h3 := le_of_mul_le_mul_right h1 hQpos
    have hk : x ^ h.choose 2 * (Fintype.card F : ℝ) ^ h.choose 2 = 1 := by
      rw [← mul_pow, hxq, one_pow]
    have hpk : 0 ≤ (Fintype.card F : ℝ) ^ h.choose 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 hpk
    calc _ ≤ _ := h4
      _ = 15 / 8 * ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) *
            (x ^ h.choose 2 * (Fintype.card F : ℝ) ^ h.choose 2) := by ring
      _ = _ := by rw [hk, mul_one]
  · push_neg at h2
    rw [Nat.choose_eq_zero_of_lt h2, pow_zero, mul_one]
    have := isoCount_le_grass A h
    have : (isoCount A h : ℝ) ≤ ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) := by
      exact_mod_cast this
    linarith

/-- (96) over `F_2`: `I_h(A) 2^(C(h,2)) ≤ (15/8) |Gr(h, F_2^R)|` for `rank A = 2a ≥ 2h - 2`. -/
theorem isoCount_saturated_two {A : Matrix (Fin R) (Fin R) (ZMod 2)} (hA : IsAltMat A)
    {a r0 : ℕ} (hr : finrank (ZMod 2) (rad A) = r0) (hR : r0 + 2 * a = R) {h : ℕ}
    (hah : h ≤ a + 1) :
    (isoCount A h : ℝ) * 2 ^ h.choose 2 ≤
      15 / 8 * ({H : Submodule (ZMod 2) (Fin R → ZMod 2) | finrank (ZMod 2) H = h}.ncard : ℝ) := by
  have := isoCount_saturated hA hr hR hah
  rwa [ZMod.card, Nat.cast_ofNat] at this

/-- (95) for an alternating `A` given only a rank lower bound: if `2b ≤ R - dim rad A` then
`I_h(A) q^(κ_h(b)) ≤ 32 |Gr(h, X)|` (uses evenness of the rank and monotonicity of `κ_h`). -/
theorem isoCount_uniform_of_le (hA : IsAltMat A) {b : ℕ} (hb : 2 * b ≤ R - finrank F (rad A))
    (h : ℕ) :
    (isoCount A h : ℝ) * (Fintype.card F : ℝ) ^ kappaH h b ≤
      32 * ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) := by
  obtain ⟨a, ha⟩ := exists_finrank_rad_add_two_mul hA
  have main := isoCount_uniform hA rfl ha h
  have hk : kappaH h b ≤ kappaH h a := kappaH_mono h (by omega)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hpow : (Fintype.card F : ℝ) ^ kappaH h b ≤ (Fintype.card F : ℝ) ^ kappaH h a := by
    exact_mod_cast Nat.pow_le_pow_right hq hk
  have hI0 : (0 : ℝ) ≤ isoCount A h := Nat.cast_nonneg _
  exact (mul_le_mul_of_nonneg_left hpow hI0).trans main

/-- (96) for an alternating `A` given only a rank lower bound: if `2(h-1) ≤ R - dim rad A` then
`I_h(A) q^(C(h,2)) ≤ (15/8) |Gr(h, X)|`. -/
theorem isoCount_saturated_of_le (hA : IsAltMat A) {h : ℕ}
    (hh : 2 * (h - 1) ≤ R - finrank F (rad A)) :
    (isoCount A h : ℝ) * (Fintype.card F : ℝ) ^ h.choose 2 ≤
      15 / 8 * ({H : Submodule F (Fin R → F) | finrank F H = h}.ncard : ℝ) := by
  obtain ⟨a, ha⟩ := exists_finrank_rad_add_two_mul hA
  exact isoCount_saturated hA rfl ha (by omega)

/-- `isoCount_saturated_of_le` over `F_2`. -/
theorem isoCount_saturated_two_of_le {A : Matrix (Fin R) (Fin R) (ZMod 2)} (hA : IsAltMat A)
    {h : ℕ} (hh : 2 * (h - 1) ≤ R - finrank (ZMod 2) (rad A)) :
    (isoCount A h : ℝ) * 2 ^ h.choose 2 ≤
      15 / 8 * ({H : Submodule (ZMod 2) (Fin R → ZMod 2) | finrank (ZMod 2) H = h}.ncard : ℝ) := by
  have := isoCount_saturated_of_le hA hh
  rwa [ZMod.card, Nat.cast_ofNat] at this

end Final

end OMA.SimsLite.Alt2
