import H2Dev.CNT3Stmt
import H2Dev.Lift

/-! # CNT3: the final assembly, conditional on the power word and term-B inputs

Li-Qiao, Theorem 6.3 / (55) / (54) at `c = 3`, `p = 2`: the assembly of `CNT3Stmt` from the
fibrewise count `lf_ncard_classes_le_fiberB_pw` (INF-1 over the recorded data and the power word
array, with Theorem 3.1), the data count (Prop 2.5) and the commutator coefficient factor.

## Interface (the statements other modules should deliver)

* `cnt3Layers r1 r2 s m2 m3 D` : the recorded data `D` has `c = 3` layers, Sims rank `s`, layer
  ranks `r1`, `r2` and layer sizes `s_2 = m2 - m3`, `s_3 = m3` (`Σ_v a(i, v)`).
* `cnt3Adm s m2 m3` : the admissible breadths `b2` (`b2 ≤ min (m2 - m3) m3`, `m3 ≤ s b2`), the
  exact index set of `lf_realizedCB_ncard_le` after the layer identifications.
* `cnt3Aterm`, `cnt3Bterm` : the natural number summands of the term-A count
  (`lf_realizedCB_ncard_le`, deeper factor included) and of the term-B count (Remark 4.4 with
  `N_2`), for one breadth `b2`; `cnt3Aterm_cast`, `cnt3Bterm_le` : they are at most
  `2 ^ cnt3A`, `2 ^ cnt3B`.
* `HypPW` : every group of `cnt3Set` has a Sims code whose recorded data satisfies
  `cnt3Layers` and `pwBound2 (fibAk D) ≤ cnt3PW` (the identification of Theorem 3.1's exponent).
* `HypData` : the Prop 2.5 data count `|RecData m| ≤ 2 ^ (C0 m (log_2 m + 1))`; PROVED here
  (`hypData`, `C0 = 7`, from `card_recData_le_pow`).
* `HypB` : the term-B commutator count, summed over the admissible breadths, for each recorded
  data with `cnt3Layers` and each power word array.
* `HypStrat` : the breadth-stratified count: the realised commutator arrays are covered by sets
  `S b2` (`b2` admissible), each bounded by BOTH the term-A summand and the term-B summand.

## Results

* `cnt3_cfactor_A` (proved): the term-A commutator count from `lf_realizedCB_ncard_le`.
* `cnt3_main_mm (hPW) (hD) (hB) : CNT3StmtMM` (proved): CNT3 (b) in the plan's form
  `min (max_b A b) (max_b B b)` (two independently chosen admissible breadths).
* `cnt3_main (hPW) (hD) (hS) : CNT3Stmt` (proved): CNT3 (b) exactly as stated, from the
  stratified hypothesis.
* `cnt3Stmt_imp_mm` : `CNT3Stmt → CNT3StmtMM`.

## Why `CNT3Stmt` needs the stratified hypothesis

`CNT3Stmt` asks for ONE admissible `b2` with `min (A b2) (B b2)`. The unstratified bounds
`N ≤ Σ_b 2 ^ A b` and `N ≤ Σ_b 2 ^ B b` only give `min (max A) (max B)` (up to `log (m + 1)`),
which can exceed `max_b min (A b) (B b)` by an amount not absorbed in `C m log m`: here
`A b - B b = (C(r1,2) - r2) r2 - logN2 - C(r1-s,2) b` decreases in `b`, and when `A` and `B`
cross between two consecutive admissible breadths `b, b + 1` (with `B` increasing and `A`
decreasing there) the gap is up to `s (r2 + m3 - 2 b)`. The paper's (54) is indeed a per-breadth
statement ("for each fixed family of higher core maps"), so the faithful input is a per-breadth
count on both sides (`HypStrat`). -/

namespace OMA.SimsLite

open scoped commutatorElement

section CNT3MainDefs

/-- The layer identifications of recorded data at class 3: `c = 3`, Sims rank `s`, ranks
`r_1 = r1`, `r_2 = r2`, layer sizes `s_2 = Σ_v a(1, v) = m2 - m3` and `s_3 = Σ_v a(2, v) = m3`
(0-indexed layers `lfI0`, `lfI1`, `lfI2` as in `lf_realizedCB_ncard_le`). -/
def cnt3Layers {m : ℕ} (r1 r2 s m2 m3 : ℕ) (D : RecData m) : Prop :=
  ∃ h2 : 2 < D.1.val, D.1.val = 3 ∧ D.2.1.val = s ∧ fibRk D (lfI0 h2) = r1 ∧
    fibRk D (lfI1 h2) = r2 ∧ (∑ v, fibAk D ⟨lfI1 h2, v⟩) = m2 - m3 ∧
    (∑ v, fibAk D ⟨lfI2 h2, v⟩) = m3

/-- The admissible breadths `b2`: `b2 ≤ min (m2 - m3) m3` and `m3 ≤ s b2` ((48)/(51)). -/
def cnt3Adm (s m2 m3 : ℕ) : Finset ℕ :=
  (Finset.range (min (m2 - m3) m3 + 1)).filter (fun β => m3 ≤ s * β)

/-- The term-A summand for breadth `b2` (eq. (53) with `|D| = r2` defining pairs, times the
deeper factor `2 ^ ((C(r1,2) - r2) m3)`), as in `lf_realizedCB_ncard_le`. -/
def cnt3Aterm (r1 r2 s m2 m3 b2 : ℕ) : ℕ :=
  2 ^ (s * (b2 * (r2 + m3 + 1 - b2))) *
    2 ^ ((r1.choose 2 - r2) * (m2 - m3) - (r1 - s).choose 2 * b2) *
      2 ^ ((r1.choose 2 - r2) * m3)

/-- The term-B summand for breadth `b2`: `N_2(r1, r2, s)` reductions mod `p L_2`, the lifts
`2 ^ ((C(r1,2) - r2)(s2 - r2))` of the non-defining values (Remark 4.4), the deeper factor
`2 ^ ((C(r1,2) - r2) m3)`, and the higher core maps of breadth `b2`,
`2 ^ (s b2 (r2 + m3 + 1 - b2))` (Prop 4.2). -/
noncomputable def cnt3Bterm (r1 r2 s m2 m3 b2 : ℕ) : ℕ :=
  Alt2.N2 r1 r2 s * 2 ^ ((r1.choose 2 - r2) * (m2 - m3 - r2)) * 2 ^ ((r1.choose 2 - r2) * m3) *
    2 ^ (s * (b2 * (r2 + m3 + 1 - b2)))

/-- Power word input: every group of `cnt3Set` has a Sims code whose recorded data has the
class-3 layer identifications and power word exponent at most `cnt3PW` (Theorem 3.1's
`pwBound2` evaluated at the recorded relative orders). -/
def HypPW : Prop :=
  ∀ m r1 r2 s lam m2 m3 r3 : ℕ, ∀ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3,
    ∃ D : FullData 2 m, SimsCode Nat.prime_two m G D ∧ cnt3Layers r1 r2 s m2 m3 D.1 ∧
      pwBound2 (fibAk D.1) ≤ cnt3PW r1 r2 r3 lam m2 m3

/-- Data input (Proposition 2.5): the recorded data number at most `2 ^ (C0 m (log_2 m + 1))`.
Proved below (`hypData`). -/
def HypData : Prop :=
  ∃ C0 : ℝ, ∀ m : ℕ, 1 ≤ m →
    (Fintype.card (RecData m) : ℝ) ≤ (2 : ℝ) ^ (C0 * m * ((Nat.log 2 m : ℝ) + 1))

/-- Term-B input: for recorded data with the class-3 layer identifications and any power word
array, the commutator arrays of the realised codes of `cnt3Set` number at most the sum over the
admissible breadths of the term-B summand. -/
def HypB : Prop :=
  ∀ m r1 r2 s lam m2 m3 r3 : ℕ, ∀ D : RecData m, cnt3Layers r1 r2 s m2 m3 D →
    ∀ B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m),
      (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard ≤
        ∑ β ∈ cnt3Adm s m2 m3, cnt3Bterm r1 r2 s m2 m3 β

/-- Breadth-stratified input: the realised commutator arrays are covered by sets `S b2`, `b2`
admissible (e.g. the arrays of codes whose graded bracket has core breadth `b2`), each bounded by
both the term-A and the term-B summand of breadth `b2`. -/
def HypStrat : Prop :=
  ∀ m r1 r2 s lam m2 m3 r3 : ℕ, ∀ D : RecData m, cnt3Layers r1 r2 s m2 m3 D →
    ∀ B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m),
      ∃ S : ℕ → Set (Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)),
        realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B ⊆
            ⋃ β ∈ cnt3Adm s m2 m3, S β ∧
          ∀ β ∈ cnt3Adm s m2 m3,
            (S β).ncard ≤ cnt3Aterm r1 r2 s m2 m3 β ∧ (S β).ncard ≤ cnt3Bterm r1 r2 s m2 m3 β

/-- CNT3 (b) in the plan's form `min (max_b A b) (max_b B b)`. -/
def CNT3StmtMM : Prop :=
  ∃ C : ℝ, ∀ m r1 r2 s lam m2 m3 r3 : ℕ, (cnt3Set m r1 r2 s lam m2 m3 r3).Nonempty →
    ∃ b2 b2' : ℕ, m3 ≤ s * b2 ∧ b2 ≤ m2 - m3 ∧ b2 ≤ m3 ∧
      m3 ≤ s * b2' ∧ b2' ≤ m2 - m3 ∧ b2' ≤ m3 ∧
      Real.logb 2 ((cnt3Classes m r1 r2 s lam m2 m3 r3).ncard : ℝ) ≤
        C * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) + (cnt3PW r1 r2 r3 lam m2 m3 : ℝ) +
          min (cnt3A r1 r2 s m2 m3 b2) (cnt3B r1 r2 s m2 m3 b2')

end CNT3MainDefs

section CNT3MainArith

lemma cnt3Adm_mem {s m2 m3 β : ℕ} :
    β ∈ cnt3Adm s m2 m3 ↔ β ≤ min (m2 - m3) m3 ∧ m3 ≤ s * β := by
  unfold cnt3Adm
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]

lemma cnt3Adm_card_le (s m2 m3 : ℕ) : (cnt3Adm s m2 m3).card ≤ min (m2 - m3) m3 + 1 :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

lemma cnt3_choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  have h := Nat.choose_succ_succ' n 1
  rw [Nat.choose_one_right] at h
  exact h

lemma cnt3_choose_two_add_le (a b : ℕ) : a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2), Nat.add_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, cnt3_choose_two_succ (a + b), cnt3_choose_two_succ b]
    omega

lemma cnt3_two_pow_cast (e : ℕ) : ((2 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ (e : ℝ) := by
  rw [Real.rpow_natCast]
  norm_cast

/-- The term-A summand is `2 ^ cnt3A` on the admissible breadths. -/
theorem cnt3Aterm_cast {r1 r2 s m2 m3 β : ℕ} (hsr : s ≤ r1) (hr2 : r2 ≤ s.choose 2)
    (h32 : m3 ≤ m2) (hb2 : β ≤ m2 - m3) (hb3 : β ≤ m3) :
    (cnt3Aterm r1 r2 s m2 m3 β : ℝ) = (2 : ℝ) ^ (cnt3A r1 r2 s m2 m3 β) := by
  have hK : (r1 - s).choose 2 + s.choose 2 ≤ r1.choose 2 := by
    have := cnt3_choose_two_add_le (r1 - s) s
    rwa [Nat.sub_add_cancel hsr] at this
  have hC : r2 ≤ r1.choose 2 := by omega
  have hKb : (r1 - s).choose 2 * β ≤ (r1.choose 2 - r2) * (m2 - m3) :=
    Nat.mul_le_mul (by omega) hb2
  have hb1 : β ≤ r2 + m3 + 1 := by omega
  have e : cnt3Aterm r1 r2 s m2 m3 β = 2 ^ (s * (β * (r2 + m3 + 1 - β)) +
      ((r1.choose 2 - r2) * (m2 - m3) - (r1 - s).choose 2 * β) +
        (r1.choose 2 - r2) * m3) := by
    unfold cnt3Aterm
    rw [pow_add, pow_add]
  rw [e, cnt3_two_pow_cast]
  congr 1
  unfold cnt3A
  push_cast [Nat.cast_sub hKb, Nat.cast_sub hC, Nat.cast_sub h32, Nat.cast_sub hb1]
  ring

/-- The term-B summand is at most `2 ^ cnt3B` on the admissible breadths. -/
theorem cnt3Bterm_le {r1 r2 s m2 m3 β : ℕ} (hsr : s ≤ r1) (hr2 : r2 ≤ s.choose 2)
    (h32 : m3 ≤ m2) (hr2s : r2 ≤ m2 - m3) (hb3 : β ≤ m3) :
    (cnt3Bterm r1 r2 s m2 m3 β : ℝ) ≤ (2 : ℝ) ^ (cnt3B r1 r2 s m2 m3 β) := by
  have hC : r2 ≤ r1.choose 2 := le_trans hr2 (Nat.choose_le_choose 2 hsr)
  have hb1 : β ≤ r2 + m3 + 1 := by omega
  have e : cnt3Bterm r1 r2 s m2 m3 β = Alt2.N2 r1 r2 s * 2 ^ ((r1.choose 2 - r2) * (m2 - m3 - r2) +
      (r1.choose 2 - r2) * m3 + s * (β * (r2 + m3 + 1 - β))) := by
    unfold cnt3Bterm
    rw [pow_add, pow_add]
    ring
  rw [e]
  rcases Nat.eq_zero_or_pos (Alt2.N2 r1 r2 s) with h0 | hpos
  · rw [h0, zero_mul, Nat.cast_zero]
    positivity
  · rw [Nat.cast_mul, cnt3_two_pow_cast]
    have hN : (Alt2.N2 r1 r2 s : ℝ) = (2 : ℝ) ^ (Alt2.logN2 r1 r2 s) := by
      unfold Alt2.logN2
      rw [Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hpos)]
    rw [hN, ← Real.rpow_add (by norm_num)]
    apply le_of_eq
    congr 1
    unfold cnt3B
    push_cast [Nat.cast_sub hC, Nat.cast_sub hr2s, Nat.cast_sub h32, Nat.cast_sub hb1]
    ring

/-- A sum of terms each at most `2 ^ e β` with `e β ≤ e b` over at most `n + 1` indices. -/
lemma cnt3_sum_rpow_le {I : Finset ℕ} {n : ℕ} (hI : I.card ≤ n + 1) (g e : ℕ → ℝ) (b : ℕ)
    (hg : ∀ β ∈ I, g β ≤ (2 : ℝ) ^ (e β)) (hb : ∀ β ∈ I, e β ≤ e b) :
    ∑ β ∈ I, g β ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ (e b) := by
  calc ∑ β ∈ I, g β ≤ ∑ _β ∈ I, (2 : ℝ) ^ (e b) := Finset.sum_le_sum fun β h =>
        (hg β h).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hb β h))
    _ = (I.card : ℝ) * (2 : ℝ) ^ (e b) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℝ) + 1) * (2 : ℝ) ^ (e b) := by
        gcongr
        exact_mod_cast hI

/-- The final real arithmetic: from the count `N ≤ |RecData m| 2 ^ PW (n + 1) 2 ^ E` to the
logarithmic form. -/
theorem cnt3_final {N m n PW : ℕ} {C0 E : ℝ}
    (hD : ∀ m : ℕ, 1 ≤ m →
      (Fintype.card (RecData m) : ℝ) ≤ (2 : ℝ) ^ (C0 * m * ((Nat.log 2 m : ℝ) + 1)))
    (hm : 1 ≤ m) (hn : n ≤ m) (hN : 1 ≤ N)
    (h : (N : ℝ) ≤ (Fintype.card (RecData m) : ℝ) * 2 ^ PW * (((n : ℝ) + 1) * (2 : ℝ) ^ E)) :
    Real.logb 2 (N : ℝ) ≤ (C0 + 1) * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) + (PW : ℝ) + E := by
  have h1 := hD m hm
  have h2n : n + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
    have h' : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    omega
  have hL : (n : ℝ) + 1 ≤ (2 : ℝ) ^ ((Nat.log 2 m : ℝ) + 1) := by
    have h' : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 m + 1) : ℕ) : ℝ) := by exact_mod_cast h2n
    rw [cnt3_two_pow_cast] at h'
    push_cast at h'
    exact h'
  have hPWr : (2 : ℝ) ^ PW = (2 : ℝ) ^ (PW : ℝ) := (Real.rpow_natCast 2 PW).symm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 m : ℝ) := Nat.cast_nonneg _
  rw [Real.logb_le_iff_le_rpow (by norm_num) hNpos]
  calc (N : ℝ) ≤ (Fintype.card (RecData m) : ℝ) * 2 ^ PW * (((n : ℝ) + 1) * (2 : ℝ) ^ E) := h
    _ ≤ (2 : ℝ) ^ (C0 * m * ((Nat.log 2 m : ℝ) + 1)) * (2 : ℝ) ^ (PW : ℝ) *
          ((2 : ℝ) ^ ((Nat.log 2 m : ℝ) + 1) * (2 : ℝ) ^ E) := by
        rw [hPWr]
        gcongr
    _ = (2 : ℝ) ^ (C0 * m * ((Nat.log 2 m : ℝ) + 1) + (PW : ℝ) +
          (((Nat.log 2 m : ℝ) + 1) + E)) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
          ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ ((C0 + 1) * (m : ℝ) * ((Nat.log 2 m : ℝ) + 1) + (PW : ℝ) + E) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr hm') hL0]

/-- Proposition 2.5 in the form of `HypData`, with `C0 = 7`. -/
theorem hypData : HypData := by
  refine ⟨7, fun m hm => ?_⟩
  have h1 := card_recData_le_pow m hm
  have hlt : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h2 : (m + 1) ^ (5 * m + 2) ≤ 2 ^ ((Nat.log 2 m + 1) * (5 * m + 2)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by omega) _
  have h3 : (Nat.log 2 m + 1) * (5 * m + 2) ≤ 7 * m * (Nat.log 2 m + 1) := by
    rw [Nat.mul_comm (Nat.log 2 m + 1)]
    exact Nat.mul_le_mul_right _ (by omega)
  have h4 : Fintype.card (RecData m) ≤ 2 ^ (7 * m * (Nat.log 2 m + 1)) :=
    h1.trans (h2.trans (Nat.pow_le_pow_right (by norm_num) h3))
  calc (Fintype.card (RecData m) : ℝ) ≤ ((2 ^ (7 * m * (Nat.log 2 m + 1)) : ℕ) : ℝ) := by
        exact_mod_cast h4
    _ = (2 : ℝ) ^ ((7 : ℝ) * m * ((Nat.log 2 m : ℝ) + 1)) := by
        rw [cnt3_two_pow_cast]
        congr 1
        first | norm_num | (push_cast; ring)

end CNT3MainArith

section CNT3MainCount

variable {m r1 r2 s lam m2 m3 r3 : ℕ}

/-- The term-A commutator count (`lf_realizedCB_ncard_le` after the layer identifications). -/
theorem cnt3_cfactor_A (D : RecData m) (hL : cnt3Layers r1 r2 s m2 m3 D)
    (B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m)) :
    (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard ≤
      ∑ β ∈ cnt3Adm s m2 m3, cnt3Aterm r1 r2 s m2 m3 β := by
  obtain ⟨h2, h3, hs, hr1, hr2, hs2, hs3⟩ := hL
  have h := lf_realizedCB_ncard_le Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D h2 h3 B
  rw [hs2, hs3, hr1, hr2, hs] at h
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  rfl

/-- The facts used by the assembly, for a nonempty parameter set. -/
theorem cnt3_setup (hPW : HypPW) (hne : (cnt3Set m r1 r2 s lam m2 m3 r3).Nonempty) :
    1 ≤ m ∧ s ≤ r1 ∧ r2 ≤ s.choose 2 ∧ m3 ≤ m2 ∧ r2 ≤ m2 - m3 ∧
      (cnt3Adm s m2 m3).Nonempty ∧ 1 ≤ (cnt3Classes m r1 r2 s lam m2 m3 r3).ncard := by
  obtain ⟨G, hG⟩ := hne
  have hm := cnt3_m_eq hG
  obtain ⟨c1, c2, -, c4, -, -⟩ := cnt3_constraints_of_mem hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, hm2, hm3, -⟩ := (mem_cnt3Set_iff G).mp hG
  have h32 : m3 ≤ m2 := by
    have hle : Nat.card (lcs G 2) ≤ Nat.card (lcs G 1) :=
      Subgroup.card_le_of_le (lcs_antitone (by norm_num))
    rw [hm2, hm3] at hle
    exact pow_le_pow_cancel (p := 2) (le_refl 2) hle
  obtain ⟨⟨D, B, C⟩, hcode, hL, -⟩ := hPW m r1 r2 s lam m2 m3 r3 G hG
  have hr2s2 : r2 ≤ m2 - m3 := by
    obtain ⟨h2, -, -, -, hr2, hs2, -⟩ := hL
    have hsum : ∑ _v : Fin (fibRk D (lfI1 h2)), 1 ≤ ∑ v, fibAk D ⟨lfI1 h2, v⟩ :=
      Finset.sum_le_sum fun v _ => fibAk_pos D _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hsum
    omega
  have hC : C ∈ realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B :=
    ⟨G, hG, hcode⟩
  have hA := cnt3_cfactor_A (lam := lam) (r3 := r3) D hL B
  have hpos : 0 < (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨C, hC⟩
  have hadm : (cnt3Adm s m2 m3).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (cnt3Adm s m2 m3) with h | h
    · rw [h, Finset.sum_empty] at hA
      omega
    · exact h
  have hcl : 1 ≤ (cnt3Classes m r1 r2 s lam m2 m3 r3).ncard :=
    (Set.ncard_pos cnt3Classes_finite).mpr ⟨_, G, hG, rfl⟩
  exact ⟨by omega, c2, c4, h32, hr2s2, hadm, hcl⟩

/-- The fibrewise count (`lf_ncard_classes_le_fiberB_pw`) with a uniform real bound `M` on the
commutator factor: `#classes ≤ |RecData m| 2 ^ PW M`. -/
theorem cnt3_count_le (hPW : HypPW) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ D : RecData m, cnt3Layers r1 r2 s m2 m3 D →
      ∀ B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m),
        ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤ M) :
    ((cnt3Classes m r1 r2 s lam m2 m3 r3).ncard : ℝ) ≤
      (Fintype.card (RecData m) : ℝ) * 2 ^ cnt3PW r1 r2 r3 lam m2 m3 * M := by
  classical
  let I : Finset (RecData m) := Finset.univ.filter (fun D => cnt3Layers r1 r2 s m2 m3 D ∧
    pwBound2 (fibAk D) ≤ cnt3PW r1 r2 r3 lam m2 m3)
  have hI : ∀ G ∈ cnt3Set m r1 r2 s lam m2 m3 r3, ∃ D : FullData 2 m,
      SimsCode Nat.prime_two m G D ∧ D.1 ∈ I := by
    intro G hG
    obtain ⟨D, hc, hL, hpw⟩ := hPW m r1 r2 s lam m2 m3 r3 G hG
    exact ⟨D, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL, hpw⟩⟩
  have h := lf_ncard_classes_le_fiberB_pw Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) I hI
    (fun _ => ⌊M⌋₊) (fun D hD B _ => Nat.le_floor (hM D (Finset.mem_filter.mp hD).2.1 B))
  have h2 : ∑ D ∈ I, 2 ^ pwBound2 (fibAk D) * ⌊M⌋₊ ≤
      Fintype.card (RecData m) * (2 ^ cnt3PW r1 r2 r3 lam m2 m3 * ⌊M⌋₊) := by
    calc ∑ D ∈ I, 2 ^ pwBound2 (fibAk D) * ⌊M⌋₊
        ≤ ∑ _D ∈ I, 2 ^ cnt3PW r1 r2 r3 lam m2 m3 * ⌊M⌋₊ :=
          Finset.sum_le_sum fun D hD => Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by norm_num) (Finset.mem_filter.mp hD).2.2)
      _ = I.card * (2 ^ cnt3PW r1 r2 r3 lam m2 m3 * ⌊M⌋₊) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_univ I)
  have h3 : (cnt3Classes m r1 r2 s lam m2 m3 r3).ncard ≤
      Fintype.card (RecData m) * (2 ^ cnt3PW r1 r2 r3 lam m2 m3 * ⌊M⌋₊) := by
    unfold cnt3Classes
    exact h.trans h2
  calc ((cnt3Classes m r1 r2 s lam m2 m3 r3).ncard : ℝ)
      ≤ ((Fintype.card (RecData m) * (2 ^ cnt3PW r1 r2 r3 lam m2 m3 * ⌊M⌋₊) : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ = (Fintype.card (RecData m) : ℝ) * 2 ^ cnt3PW r1 r2 r3 lam m2 m3 * (⌊M⌋₊ : ℝ) := by
        push_cast
        ring
    _ ≤ (Fintype.card (RecData m) : ℝ) * 2 ^ cnt3PW r1 r2 r3 lam m2 m3 * M := by
        gcongr
        exact Nat.floor_le hM0

end CNT3MainCount

section CNT3MainThm

/-- CNT3 (b) in the plan's `min (max A) (max B)` form, from the power word and term-B inputs
(the data count is `hD`, provable as `hypData`; term A is proved, `cnt3_cfactor_A`). -/
theorem cnt3_main_mm (hPW : HypPW) (hD : HypData) (hB : HypB) : CNT3StmtMM := by
  obtain ⟨C0, hC0⟩ := hD
  refine ⟨C0 + 1, fun m r1 r2 s lam m2 m3 r3 hne => ?_⟩
  obtain ⟨hm, hsr, hr2C, h32, hr2s2, hadm, hN⟩ := cnt3_setup hPW hne
  obtain ⟨b2, hb2, hmax⟩ :=
    Finset.exists_max_image (cnt3Adm s m2 m3) (fun β => cnt3A r1 r2 s m2 m3 β) hadm
  obtain ⟨b2', hb2', hmax'⟩ :=
    Finset.exists_max_image (cnt3Adm s m2 m3) (fun β => cnt3B r1 r2 s m2 m3 β) hadm
  obtain ⟨hb2a, hb2b⟩ := cnt3Adm_mem.mp hb2
  obtain ⟨hb2a', hb2b'⟩ := cnt3Adm_mem.mp hb2'
  refine ⟨b2, b2', hb2b, (le_min_iff.mp hb2a).1, (le_min_iff.mp hb2a).2, hb2b',
    (le_min_iff.mp hb2a').1, (le_min_iff.mp hb2a').2, ?_⟩
  set n := min (m2 - m3) m3 with hn
  have hcard := cnt3Adm_card_le s m2 m3
  have hM : ∀ D : RecData m, cnt3Layers r1 r2 s m2 m3 D →
      ∀ B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m),
        ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
          ((n : ℝ) + 1) * (2 : ℝ) ^ (min (cnt3A r1 r2 s m2 m3 b2) (cnt3B r1 r2 s m2 m3 b2')) := by
    intro D hL B
    have hA : ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
        ((n : ℝ) + 1) * (2 : ℝ) ^ (cnt3A r1 r2 s m2 m3 b2) := by
      have h : ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
          ∑ β ∈ cnt3Adm s m2 m3, (cnt3Aterm r1 r2 s m2 m3 β : ℝ) := by
        exact_mod_cast cnt3_cfactor_A (lam := lam) (r3 := r3) D hL B
      refine h.trans (cnt3_sum_rpow_le hcard _ (fun β => cnt3A r1 r2 s m2 m3 β) b2
        (fun β hβ => le_of_eq ?_) hmax)
      obtain ⟨h1, -⟩ := cnt3Adm_mem.mp hβ
      exact cnt3Aterm_cast hsr hr2C h32 (le_min_iff.mp h1).1 (le_min_iff.mp h1).2
    have hB' : ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
        ((n : ℝ) + 1) * (2 : ℝ) ^ (cnt3B r1 r2 s m2 m3 b2') := by
      have h : ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
          ∑ β ∈ cnt3Adm s m2 m3, (cnt3Bterm r1 r2 s m2 m3 β : ℝ) := by
        exact_mod_cast hB m r1 r2 s lam m2 m3 r3 D hL B
      refine h.trans (cnt3_sum_rpow_le hcard _ (fun β => cnt3B r1 r2 s m2 m3 β) b2'
        (fun β hβ => ?_) hmax')
      obtain ⟨h1, -⟩ := cnt3Adm_mem.mp hβ
      exact cnt3Bterm_le hsr hr2C h32 hr2s2 (le_min_iff.mp h1).2
    rcases le_total (cnt3A r1 r2 s m2 m3 b2) (cnt3B r1 r2 s m2 m3 b2') with hle | hle
    · rw [min_eq_left hle]
      exact hA
    · rw [min_eq_right hle]
      exact hB'
  have hcount := cnt3_count_le hPW _ (by positivity) hM
  have hnm : n ≤ m := by
    have := cnt3_m_eq hne.some_mem
    omega
  exact cnt3_final hC0 hm hnm hN hcount

/-- CNT3 (b) exactly as stated in `CNT3Stmt`, from the power word input and the
breadth-stratified commutator count (the data count is `hD`, provable as `hypData`). -/
theorem cnt3_main (hPW : HypPW) (hD : HypData) (hS : HypStrat) : CNT3Stmt := by
  obtain ⟨C0, hC0⟩ := hD
  refine ⟨C0 + 1, fun m r1 r2 s lam m2 m3 r3 hne => ?_⟩
  obtain ⟨hm, hsr, hr2C, h32, hr2s2, hadm, hN⟩ := cnt3_setup hPW hne
  obtain ⟨b2, hb2, hmax⟩ := Finset.exists_max_image (cnt3Adm s m2 m3)
    (fun β => min (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β)) hadm
  obtain ⟨hb2a, hb2b⟩ := cnt3Adm_mem.mp hb2
  refine ⟨b2, hb2b, (le_min_iff.mp hb2a).1, (le_min_iff.mp hb2a).2, ?_⟩
  set n := min (m2 - m3) m3 with hn
  have hcard := cnt3Adm_card_le s m2 m3
  have hM : ∀ D : RecData m, cnt3Layers r1 r2 s m2 m3 D →
      ∀ B : Fin D.2.2.1.tot → Fin D.2.2.1.tot → Fin (2 ^ m),
        ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
          ((n : ℝ) + 1) * (2 : ℝ) ^ (min (cnt3A r1 r2 s m2 m3 b2) (cnt3B r1 r2 s m2 m3 b2)) := by
    intro D hL B
    obtain ⟨S, hcov, hSb⟩ := hS m r1 r2 s lam m2 m3 r3 D hL B
    have h1 : (realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard ≤
        ∑ β ∈ cnt3Adm s m2 m3, (S β).ncard :=
      (Set.ncard_le_ncard hcov (Set.toFinite _)).trans (br_ncard_biUnion_le _ _)
    have h1' : ((realizedCB Nat.prime_two (cnt3Set m r1 r2 s lam m2 m3 r3) D B).ncard : ℝ) ≤
        ∑ β ∈ cnt3Adm s m2 m3, ((S β).ncard : ℝ) := by
      exact_mod_cast h1
    refine h1'.trans (cnt3_sum_rpow_le hcard _
      (fun β => min (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β)) b2 (fun β hβ => ?_) hmax)
    obtain ⟨hβa, -⟩ := cnt3Adm_mem.mp hβ
    obtain ⟨hSA, hSB⟩ := hSb β hβ
    have eA := cnt3Aterm_cast (β := β) hsr hr2C h32 (le_min_iff.mp hβa).1 (le_min_iff.mp hβa).2
    have eB := cnt3Bterm_le (β := β) hsr hr2C h32 hr2s2 (le_min_iff.mp hβa).2
    have hSA' : ((S β).ncard : ℝ) ≤ (cnt3Aterm r1 r2 s m2 m3 β : ℝ) := by exact_mod_cast hSA
    have hSB' : ((S β).ncard : ℝ) ≤ (cnt3Bterm r1 r2 s m2 m3 β : ℝ) := by exact_mod_cast hSB
    show ((S β).ncard : ℝ) ≤ (2 : ℝ) ^ (min (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β))
    rcases le_total (cnt3A r1 r2 s m2 m3 β) (cnt3B r1 r2 s m2 m3 β) with hle | hle
    · rw [min_eq_left hle, ← eA]
      exact hSA'
    · rw [min_eq_right hle]
      exact hSB'.trans eB
  have hcount := cnt3_count_le hPW _ (by positivity) hM
  have hnm : n ≤ m := by
    have := cnt3_m_eq hne.some_mem
    omega
  exact cnt3_final hC0 hm hnm hN hcount

/-- The exact statement implies the plan's form. -/
theorem cnt3Stmt_imp_mm (h : CNT3Stmt) : CNT3StmtMM := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun m r1 r2 s lam m2 m3 r3 hne => ?_⟩
  obtain ⟨b2, h1, h2, h3, h4⟩ := hC m r1 r2 s lam m2 m3 r3 hne
  exact ⟨b2, b2, h1, h2, h3, h1, h2, h3, h4⟩

end CNT3MainThm

end OMA.SimsLite

#print axioms OMA.SimsLite.cnt3_main
#print axioms OMA.SimsLite.cnt3_main_mm
#print axioms OMA.SimsLite.hypData
