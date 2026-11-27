import H2Dev.Code
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Theorem C (the count of codes).

For a valid shape on `m` positions, let `a`, `b`, `c` be the numbers of positions of level `0`,
`1` and `≥ 2`, and `t` the number of core positions. The index set splits by kind:
* kind `0`: at most `m * m` indices;
* kind `1`: increasing pairs of level-0 positions times the positions of level `≥ 1`;
* kind `2`: for each level-1 position `i`, the core positions of core index `≤ st i`
  (at most `st i + 1` of them), times the positions of level `≥ 2`;
* kind `3`: increasing pairs of positions of level `≥ 2` times the core.
The steps of (V6) give the saving `Σ (st i + 1) ≤ t b - (t - 1) (t - 2) / 2`, and a cubic
inequality with explicit polynomial certificates gives `25 |Idx| ≤ 2 m^3 + 50 m^2`. -/

namespace OMA.SimsLite

open scoped commutatorElement

section Count

/-! Finsets attached to a shape -/

/-- Positions of level `0`. -/
def Shape.cntA {m : ℕ} (s : Shape m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => s.lv i = 0)

/-- Positions of level `≥ 1`. -/
def Shape.cntN {m : ℕ} (s : Shape m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ¬ s.lv i = 0)

/-- Positions of level `1`. -/
def Shape.cntB {m : ℕ} (s : Shape m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => s.lv i = 1)

/-- Positions of level `≥ 2`. -/
def Shape.cntC {m : ℕ} (s : Shape m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => 2 ≤ s.lv i)

/-- Core positions. -/
def Shape.cntK {m : ℕ} (s : Shape m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (s.cidx i).isSome)

/-- Core positions whose core index is at most `st i`. -/
def Shape.cntKs {m : ℕ} (s : Shape m) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => ∃ c : Fin m, s.cidx k = some c ∧ c.val ≤ s.st i)

/-- Increasing pairs of elements of a finset. -/
def cntPairs {m : ℕ} (S : Finset (Fin m)) : Finset (Fin m × Fin m) :=
  (S ×ˢ S).filter (fun q => q.1 < q.2)

lemma Shape.mem_cntA {m : ℕ} (s : Shape m) (i : Fin m) : i ∈ s.cntA ↔ s.lv i = 0 := by
  simp [Shape.cntA]

lemma Shape.mem_cntN {m : ℕ} (s : Shape m) (i : Fin m) : i ∈ s.cntN ↔ ¬ s.lv i = 0 := by
  simp [Shape.cntN]

lemma Shape.mem_cntB {m : ℕ} (s : Shape m) (i : Fin m) : i ∈ s.cntB ↔ s.lv i = 1 := by
  simp [Shape.cntB]

lemma Shape.mem_cntC {m : ℕ} (s : Shape m) (i : Fin m) : i ∈ s.cntC ↔ 2 ≤ s.lv i := by
  simp [Shape.cntC]

lemma Shape.mem_cntK {m : ℕ} (s : Shape m) (i : Fin m) :
    i ∈ s.cntK ↔ (s.cidx i).isSome = true := by
  simp [Shape.cntK]

lemma Shape.mem_cntKs {m : ℕ} (s : Shape m) (i k : Fin m) :
    k ∈ s.cntKs i ↔ ∃ c : Fin m, s.cidx k = some c ∧ c.val ≤ s.st i := by
  simp [Shape.cntKs]

lemma mem_cntPairs {m : ℕ} (S : Finset (Fin m)) (q : Fin m × Fin m) :
    q ∈ cntPairs S ↔ q.1 ∈ S ∧ q.2 ∈ S ∧ q.1 < q.2 := by
  unfold cntPairs
  rw [Finset.mem_filter, Finset.mem_product, and_assoc]

/-! Elementary counts -/

lemma cnt_two_mul_pairs_le {m : ℕ} (S : Finset (Fin m)) :
    2 * (cntPairs S).card ≤ S.card * S.card := by
  have hXY : (cntPairs S).card ≤
      ((S ×ˢ S).filter (fun q : Fin m × Fin m => ¬ q.1 < q.2)).card := by
    rw [← Finset.card_image_of_injective (cntPairs S) Prod.swap_injective]
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    rw [mem_cntPairs] at hr
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hr.2.1, hr.1⟩, not_lt.2 hr.2.2.le⟩
  have h : (cntPairs S).card + ((S ×ˢ S).filter (fun q : Fin m × Fin m => ¬ q.1 < q.2)).card =
      S.card * S.card := by
    rw [← Finset.card_product]
    exact Finset.card_filter_add_card_filter_not (fun q : Fin m × Fin m => q.1 < q.2)
  omega

lemma Shape.cnt_card_A_N {m : ℕ} (s : Shape m) : s.cntA.card + s.cntN.card = m := by
  have h : s.cntA.card + s.cntN.card = (Finset.univ : Finset (Fin m)).card :=
    Finset.card_filter_add_card_filter_not (fun i => s.lv i = 0)
  rw [h, Finset.card_univ, Fintype.card_fin]

lemma Shape.cnt_card_N {m : ℕ} (s : Shape m) : s.cntN.card = s.cntB.card + s.cntC.card := by
  have e1 : s.cntN.filter (fun i => s.lv i = 1) = s.cntB := by
    ext i
    rw [Finset.mem_filter, s.mem_cntN, s.mem_cntB]
    omega
  have e2 : s.cntN.filter (fun i => ¬ s.lv i = 1) = s.cntC := by
    ext i
    rw [Finset.mem_filter, s.mem_cntN, s.mem_cntC]
    omega
  rw [← e1, ← e2]
  exact (Finset.card_filter_add_card_filter_not (fun i => s.lv i = 1)).symm

lemma Shape.cnt_ncore_eq {m : ℕ} (s : Shape m) : s.ncore = s.cntK.card := by
  unfold Shape.ncore
  exact Nat.subtype_card _ (fun x => s.mem_cntK x)

/-- `t ≤ l1`: core positions are free, hence of level `0`. -/
lemma Shape.cnt_ncore_le {m : ℕ} (s : Shape m) (hs : s.Valid) : s.ncore ≤ s.cntA.card := by
  rw [s.cnt_ncore_eq]
  apply Finset.card_le_card
  intro i hi
  rw [s.mem_cntK] at hi
  rw [s.mem_cntA]
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hi
  exact hs.free i (hs.core i k hk).1

/-- At most `st i + 1` core positions have core index `≤ st i` (`core_inj`). -/
lemma Shape.cnt_card_Ks_le {m : ℕ} (s : Shape m) (hs : s.Valid) (i : Fin m) :
    (s.cntKs i).card ≤ s.st i + 1 := by
  calc (s.cntKs i).card ≤ (Finset.range (s.st i + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun k => ((s.cidx k).map Fin.val).getD 0)
        · intro k hk
          rw [Finset.mem_coe, s.mem_cntKs] at hk
          obtain ⟨c, hc, hle⟩ := hk
          simp only [Finset.mem_coe, Finset.mem_range, Finset.coe_range, Set.mem_Iio, hc,
            Option.map_some, Option.getD_some]
          omega
        · intro k1 hk1 k2 hk2 hfeq
          rw [Finset.mem_coe, s.mem_cntKs] at hk1 hk2
          obtain ⟨c1, hc1, -⟩ := hk1
          obtain ⟨c2, hc2, -⟩ := hk2
          simp only [hc1, hc2, Option.map_some, Option.getD_some] at hfeq
          have h12 : c1 = c2 := Fin.ext hfeq
          rw [← h12] at hc2
          exact hs.core_inj k1 k2 c1 hc1 hc2
    _ = s.st i + 1 := Finset.card_range _

lemma cnt_gauss (n : ℕ) : (∑ i ∈ Finset.range n, i) * 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    nlinarith [ih]

/-- The rho bound: the steps of (V6) give distinct witnesses, so
`2 Σ_{lv i = 1} (st i + 1) + (t - 1)^2 ≤ 2 t l2 + (t - 1)`, and `t - 1 ≤ l2`. -/
lemma Shape.cnt_rho {m : ℕ} (s : Shape m) (hs : s.Valid) :
    s.ncore - 1 ≤ s.cntB.card ∧
      2 * (∑ i ∈ s.cntB, (s.st i + 1)) + (s.ncore - 1) * (s.ncore - 1) ≤
        2 * (s.cntB.card * s.ncore) + (s.ncore - 1) := by
  have hsum : ∑ i ∈ s.cntB, (s.st i + 1) + ∑ i ∈ s.cntB, (s.ncore - 1 - s.st i) =
      s.cntB.card * s.ncore := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_const_nat
    intro i hi
    have h1 := hs.st_range i ((s.mem_cntB i).1 hi)
    omega
  have hsub : Finset.range (s.ncore - 1) ⊆ s.cntB.image (fun i => s.ncore - 1 - s.st i) := by
    intro g hg
    rw [Finset.mem_range] at hg
    obtain ⟨i, hi1, hi2⟩ := hs.steps (s.ncore - 1 - g) (by omega) (by omega)
    rw [Finset.mem_image]
    exact ⟨i, (s.mem_cntB i).2 hi1, show s.ncore - 1 - s.st i = g by omega⟩
  have hdef : ∑ i ∈ Finset.range (s.ncore - 1), i ≤ ∑ i ∈ s.cntB, (s.ncore - 1 - s.st i) := by
    calc ∑ i ∈ Finset.range (s.ncore - 1), i
        ≤ ∑ i ∈ s.cntB.image (fun i => s.ncore - 1 - s.st i), i :=
          Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ i ∈ s.cntB, (s.ncore - 1 - s.st i) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  have hg := cnt_gauss (s.ncore - 1)
  have hcard : s.ncore - 1 ≤ s.cntB.card := by
    have h1 := Finset.card_le_card hsub
    have h2 : (s.cntB.image (fun i => s.ncore - 1 - s.st i)).card ≤ s.cntB.card :=
      Finset.card_image_le
    rw [Finset.card_range] at h1
    omega
  exact ⟨hcard, by omega⟩

/-! Splitting the index set by kind -/

/-- Kind-0 indices. -/
def cntS0 (n : ℕ) : Finset (Fin 4 × Fin n × Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).image
    (fun q => ((⟨0, by omega⟩ : Fin 4), q.1, q.1, q.2))

/-- Kind-1 indices. -/
def Shape.cntS1 {m : ℕ} (s : Shape m) : Finset (Fin 4 × Fin m × Fin m × Fin m) :=
  ((cntPairs s.cntA) ×ˢ s.cntN).image (fun q => ((⟨1, by omega⟩ : Fin 4), q.1.1, q.1.2, q.2))

/-- Kind-2 indices. -/
def Shape.cntS2 {m : ℕ} (s : Shape m) : Finset (Fin 4 × Fin m × Fin m × Fin m) :=
  s.cntB.biUnion
    (fun i => (s.cntKs i ×ˢ s.cntC).image (fun q => ((⟨2, by omega⟩ : Fin 4), i, q.1, q.2)))

/-- Kind-3 indices. -/
def Shape.cntS3 {m : ℕ} (s : Shape m) : Finset (Fin 4 × Fin m × Fin m × Fin m) :=
  ((cntPairs s.cntC) ×ˢ s.cntK).image (fun q => ((⟨3, by omega⟩ : Fin 4), q.1.1, q.2, q.1.2))

lemma Shape.cnt_idx_parts {m : ℕ} (s : Shape m) (hs : s.Valid) :
    Nat.card s.Idx ≤ m * m + (cntPairs s.cntA).card * s.cntN.card +
      (∑ i ∈ s.cntB, (s.cntKs i).card) * s.cntC.card + (cntPairs s.cntC).card * s.ncore := by
  classical
  have e : Nat.card s.Idx = (Finset.univ.filter s.IdxP).card :=
    Nat.subtype_card _ (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
  have hsub : Finset.univ.filter s.IdxP ⊆ cntS0 m ∪ s.cntS1 ∪ s.cntS2 ∪ s.cntS3 := by
    rintro ⟨κ, i, k, j⟩ hq
    have hq2 : (κ.val = 0 ∧ k = i ∧ i < j) ∨
        (κ.val = 1 ∧ s.lv i = 0 ∧ s.lv k = 0 ∧ i < k ∧ 1 ≤ s.lv j) ∨
        (κ.val = 2 ∧ s.lv i = 1 ∧ (∃ c : Fin m, s.cidx k = some c ∧ c.val ≤ s.st i) ∧
          2 ≤ s.lv j) ∨
        (κ.val = 3 ∧ 2 ≤ s.lv i ∧ (s.cidx k).isSome ∧ s.lv i + 1 ≤ s.lv j) :=
      (Finset.mem_filter.1 hq).2
    simp only [Finset.mem_union]
    rcases hq2 with ⟨h0, rfl, -⟩ | ⟨h1, hi, hk, hik, hj⟩ | ⟨h2, hi, hk, hj⟩ |
      ⟨h3, hi, hk, hj⟩
    · obtain rfl : κ = ⟨0, by omega⟩ := Fin.ext h0
      exact Or.inl (Or.inl (Or.inl (Finset.mem_image.2 ⟨(_, j), Finset.mem_univ _, rfl⟩)))
    · obtain rfl : κ = ⟨1, by omega⟩ := Fin.ext h1
      refine Or.inl (Or.inl (Or.inr (Finset.mem_image.2 ⟨((i, k), j), ?_, rfl⟩)))
      exact Finset.mem_product.2
        ⟨(mem_cntPairs _ _).2 ⟨(s.mem_cntA i).2 hi, (s.mem_cntA k).2 hk, hik⟩,
          (s.mem_cntN j).2 (by omega)⟩
    · obtain rfl : κ = ⟨2, by omega⟩ := Fin.ext h2
      refine Or.inl (Or.inr (Finset.mem_biUnion.2 ⟨i, (s.mem_cntB i).2 hi,
        Finset.mem_image.2 ⟨(k, j), ?_, rfl⟩⟩))
      exact Finset.mem_product.2 ⟨(s.mem_cntKs i k).2 hk, (s.mem_cntC j).2 hj⟩
    · obtain rfl : κ = ⟨3, by omega⟩ := Fin.ext h3
      have hij : i < j := not_le.1 (fun h => by have := hs.mono j i h; omega)
      refine Or.inr (Finset.mem_image.2 ⟨((i, j), k), ?_, rfl⟩)
      exact Finset.mem_product.2
        ⟨(mem_cntPairs _ _).2 ⟨(s.mem_cntC i).2 hi, (s.mem_cntC j).2 (by omega), hij⟩,
          (s.mem_cntK k).2 hk⟩
  have hu := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (cntS0 m ∪ s.cntS1 ∪ s.cntS2) s.cntS3
  have hu2 := Finset.card_union_le (cntS0 m ∪ s.cntS1) s.cntS2
  have hu3 := Finset.card_union_le (cntS0 m) s.cntS1
  have h0 : (cntS0 m).card ≤ m * m := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have h1 : s.cntS1.card ≤ (cntPairs s.cntA).card * s.cntN.card :=
    Finset.card_image_le.trans (Finset.card_product _ _).le
  have h2 : s.cntS2.card ≤ (∑ i ∈ s.cntB, (s.cntKs i).card) * s.cntC.card := by
    refine Finset.card_biUnion_le.trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => Finset.card_image_le.trans (Finset.card_product _ _).le)
  have h3 : s.cntS3.card ≤ (cntPairs s.cntC).card * s.ncore := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_product, s.cnt_ncore_eq]
  omega

/-! The cubic inequality and the final arithmetic -/

/-- The cubic inequality of section 8, with explicit polynomial certificates. -/
lemma cnt_cubic (a b c u : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hua : u ≤ a) (hub : u ≤ b) :
    25 * (a ^ 2 * (b + c) + c * u * (2 * b - u + c)) ≤ 4 * (a + (b + c)) ^ 3 := by
  have hn : 0 ≤ b + c := add_nonneg hb hc
  rcases le_total b a with hba | hab
  · have P3 : 0 ≤ c * (b - u) * (b - u + c) :=
      mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)
    rcases le_total (b + c) (4 * a) with h4 | h4
    · have P1 : 0 ≤ (2 * a - 3 * (b + c)) ^ 2 * (4 * a - (b + c)) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have P2 : 0 ≤ (b + c) * (b - c) ^ 2 := mul_nonneg hn (sq_nonneg _)
      first | linarith | nlinarith [P1, P2, P3]
    · have Q1 : 0 ≤ (a + (b + c)) * ((b + c) - 4 * a) * (4 * (b + c) - a) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      have Q2 : 0 ≤ (b + c) * a * b := mul_nonneg (mul_nonneg hn ha) hb
      have Q3 : 0 ≤ (b + c) * c * (a - b) := mul_nonneg (mul_nonneg hn hc) (by linarith)
      first | linarith | nlinarith [Q1, Q2, Q3, P3]
  · have R1 : 0 ≤ a ^ 3 := pow_nonneg ha 3
    have R2 : 0 ≤ (b + c) * (24 * a - 13 * (b + c)) ^ 2 := mul_nonneg hn (sq_nonneg _)
    have R3 : 0 ≤ (b + c) ^ 3 := pow_nonneg hn 3
    have R4 : 0 ≤ a * b * (b - a) := mul_nonneg (mul_nonneg ha hb) (by linarith)
    have R5 : 0 ≤ c * (a - u) * (2 * b - a - u + c) :=
      mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)
    first | linarith | nlinarith [R1, R2, R3, R4, R5]

/-- The final arithmetic: `a, b, c` are the level counts, `t` the core size, `u = t - 1`. -/
lemma cnt_final (m a b c u t X1 X3 R I : ℕ) (hm : a + b + c = m) (hua : u ≤ a) (hub : u ≤ b)
    (htu : t ≤ u + 1) (hX1 : 2 * X1 ≤ a * a) (hX3 : 2 * X3 ≤ c * c)
    (hR : 2 * R + u * u ≤ 2 * (b * t) + u)
    (hI : I ≤ m * m + X1 * (b + c) + R * c + X3 * t) :
    I ≤ (2 * m ^ 3 + 50 * m ^ 2) / 25 := by
  refine (Nat.le_div_iff_mul_le (show (0 : ℕ) < 25 by norm_num)).2 ?_
  subst hm
  have hcub := cnt_cubic (a : ℤ) b c u (by positivity) (by positivity) (by positivity)
    (by positivity) (by exact_mod_cast hua) (by exact_mod_cast hub)
  have hua' : (u : ℤ) ≤ a := by exact_mod_cast hua
  have htu' : (t : ℤ) ≤ u + 1 := by exact_mod_cast htu
  have hX1' : 2 * (X1 : ℤ) ≤ a * a := by exact_mod_cast hX1
  have hX3' : 2 * (X3 : ℤ) ≤ c * c := by exact_mod_cast hX3
  have hR' : 2 * (R : ℤ) + u * u ≤ 2 * (b * t) + u := by exact_mod_cast hR
  have hI' : (I : ℤ) ≤ (a + b + c) * (a + b + c) + X1 * (b + c) + R * c + X3 * t := by
    exact_mod_cast hI
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have e1 : 2 * (X1 : ℤ) * (b + c) ≤ a * a * (b + c) :=
    mul_le_mul_of_nonneg_right hX1' (by positivity)
  have e2 : (2 * (R : ℤ) + u * u) * c ≤ (2 * (b * t) + u) * c :=
    mul_le_mul_of_nonneg_right hR' hc0
  have e3 : 2 * (X3 : ℤ) * t ≤ c * c * t := mul_le_mul_of_nonneg_right hX3' ht0
  have e4 : 0 ≤ ((u : ℤ) + 1 - t) * (b * c) := mul_nonneg (by linarith) (by positivity)
  have e5 : 0 ≤ ((u : ℤ) + 1 - t) * (c * c) := mul_nonneg (by linarith) (by positivity)
  have e6 : 0 ≤ ((a : ℤ) - u) * c := mul_nonneg (by linarith) hc0
  have e7 : (0 : ℤ) ≤ a * a := by positivity
  have e8 : (0 : ℤ) ≤ b * b := by positivity
  have e9 : (0 : ℤ) ≤ a * b := by positivity
  have e10 : (0 : ℤ) ≤ a * c := by positivity
  have e11 : (0 : ℤ) ≤ c * c := by positivity
  have e12 : (0 : ℤ) ≤ b * c := by positivity
  have goal : (I : ℤ) * 25 ≤ 2 * ((a : ℤ) + b + c) ^ 3 + 50 * ((a : ℤ) + b + c) ^ 2 := by
    first
      | linarith
      | nlinarith [hcub, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hI']
  exact_mod_cast goal

/-- Every valid shape has at most `(2 m^3 + 50 m^2) / 25` indices. -/
lemma Shape.cnt_card_idx_le {m : ℕ} (s : Shape m) (hs : s.Valid) :
    Nat.card s.Idx ≤ (2 * m ^ 3 + 50 * m ^ 2) / 25 := by
  have hparts := s.cnt_idx_parts hs
  rw [s.cnt_card_N] at hparts
  have hAN := s.cnt_card_A_N
  have hN := s.cnt_card_N
  have hKA := s.cnt_ncore_le hs
  have hrho := s.cnt_rho hs
  have hks : ∑ i ∈ s.cntB, (s.cntKs i).card ≤ ∑ i ∈ s.cntB, (s.st i + 1) :=
    Finset.sum_le_sum (fun i _ => s.cnt_card_Ks_le hs i)
  have hPA := cnt_two_mul_pairs_le s.cntA
  have hPC := cnt_two_mul_pairs_le s.cntC
  exact cnt_final m s.cntA.card s.cntB.card s.cntC.card (s.ncore - 1) s.ncore
    (cntPairs s.cntA).card (cntPairs s.cntC).card (∑ i ∈ s.cntB, (s.cntKs i).card)
    (Nat.card s.Idx) (by omega) (by omega) (by omega) (by omega) hPA hPC (by omega) hparts

/-! The number of shapes and Theorem C -/

lemma cnt_card_shape_le (m : ℕ) : Nat.card (Shape m) ≤ (m + 2) ^ (5 * m) := by
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  have h1 : (m + 1) ^ m ≤ (m + 2) ^ m := Nat.pow_le_pow_left (by omega) m
  have h2 : (m * m + 1 + 1) ^ m ≤ (m + 2) ^ (2 * m) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) m
  have h3 : m ^ m ≤ (m + 2) ^ m := Nat.pow_le_pow_left (by omega) m
  have h5 : (m + 2) ^ (5 * m) =
      (m + 2) ^ m * ((m + 2) ^ (2 * m) * ((m + 2) ^ m * (m + 2) ^ m)) := by
    first
      | ring
      | (rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega)
  rw [h5]
  exact Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h1 h3))

/-- Theorem C: the number of codes. -/
theorem card_code_le (p m : ℕ) (hp : 0 < p) :
    Nat.card (Code p m) ≤ (m + 2) ^ (5 * m) * p ^ ((2 * m ^ 3 + 50 * m ^ 2) / 25) := by
  classical
  unfold Code
  rw [Nat.card_sigma]
  have key : ∀ s : {s : Shape m // s.Valid},
      Nat.card (s.1.Idx → Fin p) ≤ p ^ ((2 * m ^ 3 + 50 * m ^ 2) / 25) := by
    intro s
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]
    exact Nat.pow_le_pow_right hp (s.1.cnt_card_idx_le s.2)
  have hS : Fintype.card {s : Shape m // s.Valid} ≤ (m + 2) ^ (5 * m) := by
    have h1 := Fintype.card_subtype_le (fun s : Shape m => s.Valid)
    have h2 := cnt_card_shape_le m
    rw [Nat.card_eq_fintype_card] at h2
    exact h1.trans h2
  refine (Finset.sum_le_sum (fun s _ => key s)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact Nat.mul_le_mul_right _ hS

end Count

end OMA.SimsLite
