import Mathlib
import H2Dev.Burnside

/-! Li-Qiao, Theorem 3.1 (counting power word arrays, p.22).

Indexing is 0-based. A Sims generating set of a group with `c` layers and layer ranks
`r : Fin c → ℕ` is indexed by `SimsIdx c r = Σ i : Fin c, Fin (r i)`; the index `⟨i, j⟩` is the
paper generator `g_{i+1, j+1}`, and layer `i` is `L = γ_{i+1} / γ_{i+2} = lcs G i / lcs G (i+1)`.
`a : SimsIdx c r → ℕ` is the relative order array. A power word array `B : PWArray p c r a`
records, for every generator `k` and every generator `h`, the exponent `B k h < p ^ a h` of `g_h`
in the Sims normal form of `g_k ^ p ^ a k` (equation (27)).

Counting part (`card_pwArrayOK_le`, `pw_count_bound1`, `pw_count_bound2`).
`pwArrayOK p B` says: coordinate `h` of the word of `k` is free if `h` is deeper (`k.1 < h.1`),
is a multiple of `p` if `h` is an earlier generator of the same layer, and is `0` otherwise.
The number of such arrays is at most `p ^ pwBound1 a`, where
`pwBound1 a = Σ_i [ r_i m_{i+1} + Σ_v (r_i - 1 - v)(a(i,v) - 1) ]` (the first bound in (47),
with 0-based `v`, so `r_i - 1 - v` is the paper's `r_i - v`), and `pwBound1 a ≤ pwBound2 a`,
`pwBound2 a = Σ_i [ r_i m_{i+1} + (r_i - 1)(s_i - r_i) ]` (the second bound in (47)), when all
`a(i,j) ≥ 1`. Here `s_i = sL a i = Σ_v a(i,v)` and `m_{i+1} = mAbove a i = Σ_{u > i} s_u`.

Group-theoretic part (`SimsPowerData`, `SimsPowerData.arrayOK`, `liqiao_thm_3_1`).
`SimsPowerData p a g B` says that `g` is a family in a group `G` with `g ⟨i, j⟩ ∈ γ_{i+1}`, whose
layer-`i` images generate `L_i` irredundantly, all `a ≥ 1`, `B` has the Sims normal form support
(zero unless deeper or same-layer earlier), and the power relation (27) holds in the form
`g_k ^ p ^ a k = (weight-i block) * (product of the deeper blocks)`.
For a finite p-group this forces the same-layer coordinates to be multiples of `p` (Sims
[Sim65, p.160]; the argument of Li-Qiao in the proof of Theorem 3.1, via the Burnside basis
theorem in each layer), so the power word arrays realised by finite p-groups form a set of
cardinality at most `p ^ pwBound1 a ≤ p ^ pwBound2 a`.
This is valid for every nilpotency class, not only class 3. The hypotheses are weaker than the
paper's: the `a(i,j)` need not be the true relative orders, and the layer generators need only be
irredundant (a minimum generating set is irredundant). -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

/-- Index type of a Sims generating set: `⟨i, j⟩` is the generator `g_{i+1, j+1}`. -/
abbrev SimsIdx (c : ℕ) (r : Fin c → ℕ) : Type := Σ i : Fin c, Fin (r i)

/-- Power word arrays: `B k h < p ^ a h` is the exponent of `g_h` in the word of `g_k ^ p ^ a k`. -/
abbrev PWArray (p c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ) : Type :=
  (k : SimsIdx c r) → (h : SimsIdx c r) → Fin (p ^ a h)

section PowerWordCount

variable (p : ℕ) {c : ℕ} {r : Fin c → ℕ} (a : SimsIdx c r → ℕ)

/-- The admissible values `x` of coordinate `h` in the power word of `g_k`. -/
def pwAdm (k h : SimsIdx c r) (x : ℕ) : Prop :=
  k.1 < h.1 ∨ (h.1 = k.1 ∧ h.2.val < k.2.val ∧ p ∣ x) ∨ x = 0

/-- The counted power word arrays. -/
def pwArrayOK (B : PWArray p c r a) : Prop := ∀ k h, pwAdm p k h (B k h).val

/-- The base-`p` logarithm of the number of choices of coordinate `h` in the word of `g_k`. -/
def pwExp (k h : SimsIdx c r) : ℕ :=
  (if k.1 < h.1 then a h else 0) + (if h.1 = k.1 ∧ h.2.val < k.2.val then a h - 1 else 0)

/-- `s_i = log_p |L_i| = Σ_v a(i, v)`. -/
def sL (i : Fin c) : ℕ := ∑ v : Fin (r i), a ⟨i, v⟩

/-- `m_{i+1} = Σ_{u > i} s_u`. -/
def mAbove (i : Fin c) : ℕ := ∑ u ∈ Finset.univ.filter (fun u => i < u), sL a u

/-- The first bound in (47): `Σ_i [ r_i m_{i+1} + Σ_v (r_i - v)(a(i,v) - 1) ]` (1-based `v`). -/
def pwBound1 : ℕ :=
  ∑ i : Fin c, (r i * mAbove a i + ∑ v : Fin (r i), (r i - 1 - v.val) * (a ⟨i, v⟩ - 1))

/-- The second bound in (47): `PW = Σ_i [ r_i m_{i+1} + (r_i - 1)(s_i - r_i) ]`. -/
def pwBound2 : ℕ :=
  ∑ i : Fin c, (r i * mAbove a i + (r i - 1) * (sL a i - r i))

lemma card_adm_le (k h : SimsIdx c r) :
    Nat.card {x : Fin (p ^ a h) // pwAdm p k h x.val} ≤ p ^ pwExp a k h := by
  unfold pwExp
  by_cases h1 : k.1 < h.1
  · have h2 : ¬ (h.1 = k.1 ∧ h.2.val < k.2.val) := by
      intro h'
      rw [h'.1] at h1
      exact lt_irrefl _ h1
    rw [if_pos h1, if_neg h2, add_zero]
    calc Nat.card {x : Fin (p ^ a h) // pwAdm p k h x.val} ≤ Nat.card (Fin (p ^ a h)) :=
          Finite.card_subtype_le _
      _ = p ^ a h := Nat.card_fin _
  · by_cases h2 : h.1 = k.1 ∧ h.2.val < k.2.val
    · rw [if_neg h1, if_pos h2, zero_add]
      have hdvd : ∀ x : {x : Fin (p ^ a h) // pwAdm p k h x.val}, p ∣ x.1.val := by
        intro x
        have hx := x.2
        unfold pwAdm at hx
        rcases hx with h' | ⟨_, _, hd⟩ | h0
        · exact absurd h' h1
        · exact hd
        · rw [h0]
          exact dvd_zero p
      have hlt : ∀ x : {x : Fin (p ^ a h) // pwAdm p k h x.val}, x.1.val / p < p ^ (a h - 1) := by
        intro x
        have hx : x.1.val < p ^ a h := x.1.isLt
        rcases Nat.eq_zero_or_pos (a h) with ha | ha
        · have hp1 : p ^ a h = 1 := by rw [ha, pow_zero]
          have hx0 : x.1.val = 0 := by omega
          have e : a h - 1 = 0 := by omega
          rw [e, hx0, Nat.zero_div, pow_zero]
          exact Nat.one_pos
        · obtain ⟨n, hn⟩ : ∃ n, a h = n + 1 := ⟨a h - 1, by omega⟩
          have hx' : x.1.val < p * p ^ n := by
            rw [← pow_succ', ← hn]
            exact hx
          have e : a h - 1 = n := by omega
          rw [e]
          exact Nat.div_lt_of_lt_mul hx'
      let f : {x : Fin (p ^ a h) // pwAdm p k h x.val} → Fin (p ^ (a h - 1)) :=
        fun x => ⟨x.1.val / p, hlt x⟩
      have hf : Function.Injective f := by
        intro x y hxy
        have e : x.1.val / p = y.1.val / p := congrArg Fin.val hxy
        apply Subtype.ext
        apply Fin.ext
        calc x.1.val = x.1.val / p * p := (Nat.div_mul_cancel (hdvd x)).symm
          _ = y.1.val / p * p := by rw [e]
          _ = y.1.val := Nat.div_mul_cancel (hdvd y)
      calc Nat.card {x : Fin (p ^ a h) // pwAdm p k h x.val} ≤ Nat.card (Fin (p ^ (a h - 1))) :=
            Nat.card_le_card_of_injective f hf
        _ = p ^ (a h - 1) := Nat.card_fin _
    · rw [if_neg h1, if_neg h2, add_zero, pow_zero]
      have h0 : ∀ x : {x : Fin (p ^ a h) // pwAdm p k h x.val}, x.1.val = 0 := by
        intro x
        have hx := x.2
        unfold pwAdm at hx
        rcases hx with h' | ⟨e1, e2, _⟩ | h0
        · exact absurd h' h1
        · exact (h2 ⟨e1, e2⟩).elim
        · exact h0
      have hf : Function.Injective (fun _ : {x : Fin (p ^ a h) // pwAdm p k h x.val} => ()) := by
        intro x y _
        apply Subtype.ext
        apply Fin.ext
        rw [h0 x, h0 y]
      calc Nat.card {x : Fin (p ^ a h) // pwAdm p k h x.val} ≤ Nat.card Unit :=
            Nat.card_le_card_of_injective _ hf
        _ = 1 := Nat.card_unique

/-- The counting core of Theorem 3.1: the admissible arrays number at most `p ^ Σ pwExp`. -/
theorem card_pwArrayOK_le :
    Nat.card {B : PWArray p c r a // pwArrayOK p a B} ≤ p ^ (∑ k, ∑ h, pwExp a k h) := by
  have e1 : {B : PWArray p c r a // pwArrayOK p a B} ≃
      ((k : SimsIdx c r) → {row : (h : SimsIdx c r) → Fin (p ^ a h) //
        ∀ h, pwAdm p k h (row h).val}) :=
    @Equiv.subtypePiEquivPi (SimsIdx c r) (fun _ => (h : SimsIdx c r) → Fin (p ^ a h))
      (fun k row => ∀ h, pwAdm p k h (row h).val)
  have e2 : ∀ k : SimsIdx c r, {row : (h : SimsIdx c r) → Fin (p ^ a h) //
      ∀ h, pwAdm p k h (row h).val} ≃
      ((h : SimsIdx c r) → {x : Fin (p ^ a h) // pwAdm p k h x.val}) :=
    fun k => @Equiv.subtypePiEquivPi (SimsIdx c r) (fun h => Fin (p ^ a h))
      (fun h x => pwAdm p k h x.val)
  rw [Nat.card_congr e1, Nat.card_pi]
  calc ∏ k, Nat.card {row : (h : SimsIdx c r) → Fin (p ^ a h) // ∀ h, pwAdm p k h (row h).val}
        = ∏ k, ∏ h, Nat.card {x : Fin (p ^ a h) // pwAdm p k h x.val} := by
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [Nat.card_congr (e2 k), Nat.card_pi]
    _ ≤ ∏ k, ∏ h, p ^ pwExp a k h :=
          Finset.prod_le_prod' fun k _ => Finset.prod_le_prod' fun h _ => card_adm_le p a k h
    _ = p ^ (∑ k, ∑ h, pwExp a k h) := by
          simp only [Finset.prod_pow_eq_pow_sum]

/-- The exponent sum equals the first bound in (47). -/
theorem sum_pwExp : ∑ k, ∑ h, pwExp a k h = pwBound1 a := by
  unfold pwBound1
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hA : ∑ h : SimsIdx c r, (if i < h.1 then a h else 0) = mAbove a i := by
    rw [Fintype.sum_sigma]
    unfold mAbove sL
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : i < u
    · simp [hu]
    · simp [hu]
  have hB : ∀ j : Fin (r i),
      ∑ h : SimsIdx c r, (if h.1 = i ∧ h.2.val < j.val then a h - 1 else 0) =
        ∑ v : Fin (r i), (if v.val < j.val then a ⟨i, v⟩ - 1 else 0) := by
    intro j
    rw [Fintype.sum_sigma, Fintype.sum_eq_single i]
    · simp
    · intro u hu
      simp [hu]
  have hrow : ∀ j : Fin (r i), ∑ h, pwExp a ⟨i, j⟩ h =
      mAbove a i + ∑ v : Fin (r i), (if v.val < j.val then a ⟨i, v⟩ - 1 else 0) := by
    intro j
    rw [← hA, ← hB j, ← Finset.sum_add_distrib]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hrow j, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [← Fin.card_Ioi (a := v)]
  congr 1
  ext j
  simp

/-- The second inequality of (47). -/
theorem pwBound1_le_pwBound2 (ha : ∀ k, 1 ≤ a k) : pwBound1 a ≤ pwBound2 a := by
  unfold pwBound1 pwBound2
  refine Finset.sum_le_sum fun i _ => ?_
  have hs : ∑ v : Fin (r i), (a ⟨i, v⟩ - 1) = sL a i - r i := by
    have h1 : ∑ v : Fin (r i), (a ⟨i, v⟩ - 1 + 1) = sL a i :=
      Finset.sum_congr rfl fun v _ => Nat.sub_add_cancel (ha _)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h1
    omega
  have h2 : ∑ v : Fin (r i), (r i - 1 - v.val) * (a ⟨i, v⟩ - 1) ≤
      ∑ v : Fin (r i), (r i - 1) * (a ⟨i, v⟩ - 1) :=
    Finset.sum_le_sum fun v _ => Nat.mul_le_mul (Nat.sub_le _ _) le_rfl
  rw [← Finset.mul_sum, hs] at h2
  exact Nat.add_le_add_left h2 _

/-- Counting core, first bound of (47). -/
theorem pw_count_bound1 :
    Nat.card {B : PWArray p c r a // pwArrayOK p a B} ≤ p ^ pwBound1 a := by
  rw [← sum_pwExp]
  exact card_pwArrayOK_le p a

/-- Counting core, second bound of (47). -/
theorem pw_count_bound2 (hp : 0 < p) (ha : ∀ k, 1 ≤ a k) :
    Nat.card {B : PWArray p c r a // pwArrayOK p a B} ≤ p ^ pwBound2 a :=
  (pw_count_bound1 p a).trans (Nat.pow_le_pow_right hp (pwBound1_le_pwBound2 a ha))

end PowerWordCount

section PowerWordGroup

variable {p : ℕ} [hp : Fact p.Prime]

/-- Burnside step: for an irredundant generating family of a finite p-group, an ordered product
`Π y_v ^ e_v` lying in the Frattini subgroup has all exponents divisible by `p`. -/
theorem dvd_of_prod_mem_frattini {Q : Type u} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    {n : ℕ} (y : Fin n → Q) (hgen : Subgroup.closure (Set.range y) = ⊤)
    (hirr : ∀ v, Subgroup.closure (y '' {w | w ≠ v}) ≠ ⊤) (e : Fin n → ℕ)
    (he : (List.ofFn fun v => y v ^ e v).prod ∈ frattini Q) (v : Fin n) : p ∣ e v := by
  by_contra hv
  have hker : (fratPi Q).ker = frattini Q := ker_fratPi hQ
  have hprod : ∏ w, (fratPi Q) (y w) ^ e w = 1 := by
    have h1 : (fratPi Q) (List.ofFn fun v => y v ^ e v).prod = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact he
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn] at h1
    simp only [Function.comp_def, map_pow] at h1
    exact h1
  have hM : (fratPi Q) (y v) ^ e v ∈ (Subgroup.closure (y '' {w | w ≠ v})).map (fratPi Q) := by
    have h2 : (fratPi Q) (y v) ^ e v *
        ∏ w ∈ Finset.univ.erase v, (fratPi Q) (y w) ^ e w = 1 := by
      rw [Finset.mul_prod_erase Finset.univ (fun w => (fratPi Q) (y w) ^ e w)
        (Finset.mem_univ v)]
      exact hprod
    have h3 : ∏ w ∈ Finset.univ.erase v, (fratPi Q) (y w) ^ e w ∈
        (Subgroup.closure (y '' {w | w ≠ v})).map (fratPi Q) := by
      refine prod_mem fun w hw => ?_
      have hmem : y w ∈ y '' {w | w ≠ v} := ⟨w, Finset.ne_of_mem_erase hw, rfl⟩
      exact pow_mem (Subgroup.mem_map_of_mem (fratPi Q) (Subgroup.subset_closure hmem)) _
    rw [eq_inv_of_mul_eq_one_left h2]
    exact inv_mem h3
  have hpow1 : (fratPi Q) (y v) ^ p = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, hker, frattini_eq_pPhi hQ]
    exact pow_mem_pPhi p (y v)
  have hcop : Nat.Coprime (e v) p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hv)
  have hyM : (fratPi Q) (y v) ∈ (Subgroup.closure (y '' {w | w ≠ v})).map (fratPi Q) := by
    have e1 : (fratPi Q) (y v) = ((fratPi Q) (y v) ^ (e v : ℤ)) ^ (Nat.gcdA (e v) p) *
        ((fratPi Q) (y v) ^ (p : ℤ)) ^ (Nat.gcdB (e v) p) := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop,
        Nat.cast_one, zpow_one]
    rw [e1]
    refine mul_mem (zpow_mem ?_ _) (zpow_mem ?_ _)
    · rw [zpow_natCast]
      exact hM
    · rw [zpow_natCast, hpow1]
      exact one_mem _
  obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hyM
  have hyK : y v ∈ Subgroup.closure (y '' {w | w ≠ v}) ⊔ frattini Q := by
    have hk : s⁻¹ * y v ∈ frattini Q := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hsy, inv_mul_cancel]
    have hsplit : y v = s * (s⁻¹ * y v) := by group
    rw [hsplit]
    exact Subgroup.mul_mem_sup hs hk
  have htop : Subgroup.closure (y '' {w | w ≠ v}) ⊔ frattini Q = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨w, rfl⟩
    by_cases hw : w = v
    · rw [hw]
      exact hyK
    · have hmem : y w ∈ y '' {w | w ≠ v} := ⟨w, hw, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.subset_closure hmem)
  exact hirr v (closure_eq_top_of_sup_frattini htop)

/-- The layer argument of Theorem 3.1: if the images of `x` generate the finite p-group `H ⧸ N`
irredundantly and `x_j ^ p ^ A = (Π_v x_v ^ b_v) * z` with `A ≥ 1` and `z ∈ N`, then every
`b_v` is divisible by `p`. -/
theorem dvd_of_power_relation {H : Type u} [Group H] (N : Subgroup H) [N.Normal]
    [Finite (H ⧸ N)] (hQ : IsPGroup p (H ⧸ N)) {n : ℕ} (x : Fin n → H)
    (hgen : Subgroup.closure (Set.range fun v => (x v : H ⧸ N)) = ⊤)
    (hirr : ∀ v, Subgroup.closure ((fun w => (x w : H ⧸ N)) '' {w | w ≠ v}) ≠ ⊤)
    (j : Fin n) (A : ℕ) (hA : 1 ≤ A) (b : Fin n → ℕ) (z : H) (hz : z ∈ N)
    (hrel : x j ^ p ^ A = (List.ofFn fun v => x v ^ b v).prod * z) (v : Fin n) : p ∣ b v := by
  refine dvd_of_prod_mem_frattini hQ (fun v => (x v : H ⧸ N)) hgen hirr b ?_ v
  show (List.ofFn fun v => (x v : H ⧸ N) ^ b v).prod ∈ frattini (H ⧸ N)
  have h1 : ((x j ^ p ^ A : H) : H ⧸ N) = (((List.ofFn fun v => x v ^ b v).prod : H) : H ⧸ N) := by
    rw [hrel, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  have h2 : (((List.ofFn fun v => x v ^ b v).prod : H) : H ⧸ N) =
      (List.ofFn fun v => (x v : H ⧸ N) ^ b v).prod := by
    rw [← QuotientGroup.mk'_apply, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, QuotientGroup.mk'_apply, QuotientGroup.mk_pow]
  rw [← h2, ← h1, QuotientGroup.mk_pow, frattini_eq_pPhi hQ]
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  rw [show p ^ (A' + 1) = p * p ^ A' from pow_succ' p A', pow_mul]
  exact pow_mem (pow_mem_pPhi p _) _

/-- The weight-`i` layer `γ_{i+1} / γ_{i+2}` (0-based `i`), as a quotient of `lcs G i`. -/
abbrev LayerQ (G : Type u) [Group G] (i : ℕ) : Type u :=
  ↥(lcs G i) ⧸ (lcs G (i + 1)).subgroupOf (lcs G i)

/-- Sims power data (equation (27) and the layer generation property of Section 2.1). -/
structure SimsPowerData (p : ℕ) {G : Type u} [Group G] {c : ℕ} {r : Fin c → ℕ}
    (a : SimsIdx c r → ℕ) (g : SimsIdx c r → G) (B : PWArray p c r a) : Prop where
  mem : ∀ k, g k ∈ lcs G k.1
  gen : ∀ i : Fin c, Subgroup.closure (Set.range fun v : Fin (r i) =>
      (QuotientGroup.mk (⟨g ⟨i, v⟩, mem ⟨i, v⟩⟩ : lcs G i) : LayerQ G i)) = ⊤
  irr : ∀ (i : Fin c) (v : Fin (r i)), Subgroup.closure ((fun w : Fin (r i) =>
      (QuotientGroup.mk (⟨g ⟨i, w⟩, mem ⟨i, w⟩⟩ : lcs G i) : LayerQ G i)) '' {w | w ≠ v}) ≠ ⊤
  pos : ∀ k, 1 ≤ a k
  supp : ∀ k h, ¬ k.1 < h.1 → ¬ (h.1 = k.1 ∧ h.2.val < k.2.val) → (B k h).val = 0
  pow : ∀ (i : Fin c) (j : Fin (r i)), g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩ =
      (List.ofFn fun v : Fin (r i) => g ⟨i, v⟩ ^ (B ⟨i, j⟩ ⟨i, v⟩).val).prod *
      (List.ofFn fun u : Fin c => if i < u then
        (List.ofFn fun v : Fin (r u) => g ⟨u, v⟩ ^ (B ⟨i, j⟩ ⟨u, v⟩).val).prod else 1).prod

/-- The deeper blocks of a power word lie in `γ_{i+2}`. -/
lemma deeper_mem {G : Type u} [Group G] {c : ℕ} {r : Fin c → ℕ} (g : SimsIdx c r → G)
    (hmem : ∀ k, g k ∈ lcs G k.1) (b : SimsIdx c r → ℕ) (i : Fin c) :
    (List.ofFn fun u : Fin c => if i < u then
      (List.ofFn fun v : Fin (r u) => g ⟨u, v⟩ ^ b ⟨u, v⟩).prod else 1).prod ∈
        lcs G ((i : ℕ) + 1) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn'] at hx
  obtain ⟨u, rfl⟩ := hx
  dsimp only
  split_ifs with hu
  · refine Subgroup.list_prod_mem _ fun y hy => ?_
    rw [List.mem_ofFn'] at hy
    obtain ⟨v, rfl⟩ := hy
    exact Subgroup.pow_mem _ (lcs_antitone (Nat.succ_le_of_lt (hu : (i : ℕ) < u))
      (hmem ⟨u, v⟩)) _
  · exact Subgroup.one_mem _

/-- Same-layer power coordinates are multiples of `p` (Sims, p.160; proof of Theorem 3.1). -/
theorem SimsPowerData.dvd_same_layer {G : Type u} [Group G] [Finite G] (hG : IsPGroup p G)
    {c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ} {g : SimsIdx c r → G} {B : PWArray p c r a}
    (hd : SimsPowerData p a g B) (i : Fin c) (j v : Fin (r i)) :
    p ∣ (B ⟨i, j⟩ ⟨i, v⟩).val := by
  have hQ : IsPGroup p (LayerQ G i) := (hG.to_subgroup _).to_quotient _
  have hdeep := deeper_mem g hd.mem (fun h => (B ⟨i, j⟩ h).val) i
  have htail : (List.ofFn fun u : Fin c => if i < u then
      (List.ofFn fun v : Fin (r u) => g ⟨u, v⟩ ^ (B ⟨i, j⟩ ⟨u, v⟩).val).prod else 1).prod ∈
        lcs G i := lcs_antitone (Nat.le_succ _) hdeep
  have hz : (⟨_, htail⟩ : lcs G i) ∈ (lcs G ((i : ℕ) + 1)).subgroupOf (lcs G i) :=
    Subgroup.mem_subgroupOf.mpr hdeep
  have hrel : (⟨g ⟨i, j⟩, hd.mem ⟨i, j⟩⟩ : lcs G i) ^ p ^ a ⟨i, j⟩ =
      (List.ofFn fun w : Fin (r i) =>
        (⟨g ⟨i, w⟩, hd.mem ⟨i, w⟩⟩ : lcs G i) ^ (B ⟨i, j⟩ ⟨i, w⟩).val).prod * ⟨_, htail⟩ := by
    apply (lcs G i).subtype_injective
    rw [map_mul, map_pow, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, map_pow, Subgroup.coe_subtype]
    exact hd.pow i j
  exact dvd_of_power_relation ((lcs G ((i : ℕ) + 1)).subgroupOf (lcs G i)) hQ
    (fun w => (⟨g ⟨i, w⟩, hd.mem ⟨i, w⟩⟩ : lcs G i)) (hd.gen i) (hd.irr i) j (a ⟨i, j⟩)
    (hd.pos _) (fun w => (B ⟨i, j⟩ ⟨i, w⟩).val) _ hz hrel v

/-- Group-theoretic reduction of Theorem 3.1: a realised power word array is admissible. -/
theorem SimsPowerData.arrayOK {G : Type u} [Group G] [Finite G] (hG : IsPGroup p G)
    {c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ} {g : SimsIdx c r → G} {B : PWArray p c r a}
    (hd : SimsPowerData p a g B) : pwArrayOK p a B := by
  rintro ⟨i, j⟩ ⟨u, v⟩
  by_cases h1 : i < u
  · exact Or.inl h1
  by_cases h2 : u = i ∧ v.val < j.val
  · obtain ⟨hu, hv⟩ := h2
    subst hu
    exact Or.inr (Or.inl ⟨rfl, hv, hd.dvd_same_layer hG _ _ _⟩)
  · exact Or.inr (Or.inr (hd.supp ⟨i, j⟩ ⟨u, v⟩ h1 h2))

/-- The power word arrays realised by finite p-groups with Sims power data. -/
def realizedPW (p c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ) : Set (PWArray p c r a) :=
  {B | ∃ (G : Type) (_ : Group G) (_ : Finite G) (g : SimsIdx c r → G),
    IsPGroup p G ∧ SimsPowerData p a g B}

/-- Li-Qiao Theorem 3.1, first bound of (47). -/
theorem liqiao_thm_3_1_bound1 (c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ) :
    (realizedPW p c r a).ncard ≤ p ^ pwBound1 a := by
  have hsub : realizedPW p c r a ⊆ {B | pwArrayOK p a B} := by
    rintro B ⟨G, _, _, g, hG, hd⟩
    exact hd.arrayOK hG
  calc (realizedPW p c r a).ncard ≤ {B | pwArrayOK p a B}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card {B : PWArray p c r a // pwArrayOK p a B} := (Nat.card_coe_set_eq _).symm
    _ ≤ p ^ pwBound1 a := pw_count_bound1 p a

/-- Li-Qiao Theorem 3.1: at most `p ^ Σ_i [ r_i m_{i+1} + (r_i - 1)(s_i - r_i) ]` power word
arrays are realised, for a fixed relative order array with all entries `≥ 1`. -/
theorem liqiao_thm_3_1 (c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ) (ha : ∀ k, 1 ≤ a k) :
    (realizedPW p c r a).ncard ≤ p ^ pwBound2 a :=
  (liqiao_thm_3_1_bound1 c r a).trans
    (Nat.pow_le_pow_right hp.out.pos (pwBound1_le_pwBound2 a ha))

/-! ### Bridge from a Sims generating set with normal forms (Section 2.1, (25)-(27))

`SimsGenSet p a g` records the data of a Sims generating set as in Section 2.1 of the paper:
generators in the right lower central term, layer images forming a minimum generating set of
`L_i`, positive relative orders with the relative order relation (25), and the Sims normal
form (26), stated as uniqueness of coordinates together with existence of normal forms supported
on the generators of each term `⟨g_{i,1}, ..., g_{i,j-1}, G_{i+1}⟩` of the Sims series.
From this the power word array `B k = coord (g_k ^ p ^ a k)` gives `SimsPowerData`. -/

/-- A minimum generating family of a group is irredundant. -/
theorem irredundant_of_minimum {Q : Type u} [Group Q] {n : ℕ} (y : Fin n → Q)
    (hmin : ∀ (m : ℕ) (z : Fin m → Q), Subgroup.closure (Set.range z) = ⊤ → n ≤ m)
    (v : Fin n) : Subgroup.closure (y '' {w | w ≠ v}) ≠ ⊤ := by
  intro htop
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := v.isLt; omega⟩
  have hr : Set.range (y ∘ v.succAbove) = y '' {w | w ≠ v} := by
    rw [Set.range_comp, Fin.range_succAbove]
    ext w
    simp
  have h := hmin m (y ∘ v.succAbove) (by rw [hr]; exact htop)
  omega

/-- Splitting an ordered product at the first nontrivial factor. -/
theorem list_prod_ofFn_split {M : Type*} [Monoid M] (n : ℕ) : ∀ (f : Fin n → M) (i : Fin n),
    (∀ u, u < i → f u = 1) →
    (List.ofFn f).prod = f i * (List.ofFn fun u => if i < u then f u else 1).prod := by
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i hf
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp [List.ofFn_succ, Fin.succ_pos]
    · have hf0 : f 0 = 1 := hf 0 (Fin.succ_pos i')
      have hrec := ih (fun u => f u.succ) i'
        (fun u hu => hf u.succ (Fin.succ_lt_succ_iff.mpr hu))
      rw [List.ofFn_succ, List.prod_cons, hf0, one_mul, hrec]
      conv_rhs => rw [List.ofFn_succ, List.prod_cons]
      simp [Fin.succ_lt_succ_iff, Fin.not_lt_zero]

section Bridge

variable {G : Type u} [Group G] {c : ℕ} {r : Fin c → ℕ}

/-- The weight-`u` block `Π_v g_{u,v} ^ e(u,v)` (increasing `v`). -/
def blockProd (g : SimsIdx c r → G) (e : SimsIdx c r → ℕ) (u : Fin c) : G :=
  (List.ofFn fun v : Fin (r u) => g ⟨u, v⟩ ^ e ⟨u, v⟩).prod

/-- The full Sims normal form product `Π_u Π_v g_{u,v} ^ e(u,v)` of (26). -/
def fullProd (g : SimsIdx c r → G) (e : SimsIdx c r → ℕ) : G :=
  (List.ofFn fun u : Fin c => blockProd g e u).prod

/-- The term `⟨g_{i,v} : v < j⟩ G_{i+1}` of the Sims series (0-based `i`, `v`). -/
def relSub (g : SimsIdx c r → G) (i : Fin c) (j : ℕ) : Subgroup G :=
  Subgroup.closure {x | ∃ v : Fin (r i), v.val < j ∧ g ⟨i, v⟩ = x} ⊔ lcs G ((i : ℕ) + 1)

/-- Coordinates supported on the generators of `relSub g i j`. -/
def SupportedIn (i : Fin c) (j : ℕ) (e : SimsIdx c r → ℕ) : Prop :=
  ∀ h : SimsIdx c r, (h.1 < i ∨ (h.1 = i ∧ j ≤ h.2.val)) → e h = 0

/-- Sims normal form (26): coordinates are unique, and every element of a term of the Sims
series has a normal form using only the generators of that term. -/
structure SimsNormalForm (p : ℕ) (a : SimsIdx c r → ℕ) (g : SimsIdx c r → G) where
  coord : G → (h : SimsIdx c r) → Fin (p ^ a h)
  uniq : ∀ e : (h : SimsIdx c r) → Fin (p ^ a h), coord (fullProd g fun h => (e h).val) = e
  sub : ∀ (i : Fin c) (j : ℕ) (x : G), x ∈ relSub g i j →
    ∃ e : (h : SimsIdx c r) → Fin (p ^ a h),
      SupportedIn i j (fun h => (e h).val) ∧ fullProd g (fun h => (e h).val) = x

/-- The normal form of an element of a Sims series term is supported on its generators. -/
theorem SimsNormalForm.coord_spec {p : ℕ} {a : SimsIdx c r → ℕ} {g : SimsIdx c r → G}
    (nf : SimsNormalForm p a g) (i : Fin c) (j : ℕ) (x : G) (hx : x ∈ relSub g i j) :
    SupportedIn i j (fun h => (nf.coord x h).val) ∧
      fullProd g (fun h => (nf.coord x h).val) = x := by
  obtain ⟨e, he, hprod⟩ := nf.sub i j x hx
  have hc : nf.coord x = e := by
    rw [← hprod]
    exact nf.uniq e
  rw [hc]
  exact ⟨he, hprod⟩

/-- A Sims generating set (Section 2.1): layer images form a minimum generating set of each
layer, relative orders are positive and satisfy (25), and normal forms (26) exist. -/
structure SimsGenSet (p : ℕ) (a : SimsIdx c r → ℕ) (g : SimsIdx c r → G) where
  mem : ∀ k, g k ∈ lcs G k.1
  gen : ∀ i : Fin c, Subgroup.closure (Set.range fun v : Fin (r i) =>
      (QuotientGroup.mk (⟨g ⟨i, v⟩, mem ⟨i, v⟩⟩ : lcs G i) : LayerQ G i)) = ⊤
  minimum : ∀ (i : Fin c) (n : ℕ) (y : Fin n → LayerQ G i),
    Subgroup.closure (Set.range y) = ⊤ → r i ≤ n
  pos : ∀ k, 1 ≤ a k
  rel : ∀ (i : Fin c) (j : Fin (r i)), g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩ ∈ relSub g i j.val
  nf : SimsNormalForm p a g

/-- The power word array (27) of a Sims generating set. -/
def SimsGenSet.powerWords {p : ℕ} {a : SimsIdx c r → ℕ} {g : SimsIdx c r → G}
    (S : SimsGenSet p a g) : PWArray p c r a :=
  fun k => S.nf.coord (g k ^ p ^ a k)

/-- Bridge: the normal form coordinates of `g_{ij} ^ p ^ a(i,j)` give Sims power data. -/
theorem SimsGenSet.powerData {p : ℕ} {a : SimsIdx c r → ℕ} {g : SimsIdx c r → G}
    (S : SimsGenSet p a g) : SimsPowerData p a g S.powerWords where
  mem := S.mem
  gen := S.gen
  irr := fun i v => irredundant_of_minimum _ (S.minimum i) v
  pos := S.pos
  supp := by
    rintro ⟨i, j⟩ ⟨u, v⟩ h1 h2
    have hs := (S.nf.coord_spec i j.val _ (S.rel i j)).1
    refine hs ⟨u, v⟩ ?_
    rcases lt_or_eq_of_le (not_lt.mp h1) with hu | hu
    · exact Or.inl hu
    · subst hu
      exact Or.inr ⟨rfl, not_lt.mp fun hv => h2 ⟨rfl, hv⟩⟩
  pow := by
    intro i j
    obtain ⟨hs, hprod⟩ := S.nf.coord_spec i j.val _ (S.rel i j)
    show g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩ =
      (List.ofFn fun v : Fin (r i) =>
        g ⟨i, v⟩ ^ (S.nf.coord (g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩) ⟨i, v⟩).val).prod *
      (List.ofFn fun u : Fin c => if i < u then
        (List.ofFn fun v : Fin (r u) =>
          g ⟨u, v⟩ ^ (S.nf.coord (g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩) ⟨u, v⟩).val).prod else 1).prod
    have hf : ∀ u, u < i →
        blockProd g (fun h => (S.nf.coord (g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩) h).val) u = 1 := by
      intro u hu
      refine List.prod_eq_one fun x hx => ?_
      rw [List.mem_ofFn'] at hx
      obtain ⟨v, rfl⟩ := hx
      dsimp only
      rw [hs ⟨u, v⟩ (Or.inl hu), pow_zero]
    have hsplit := list_prod_ofFn_split _
      (fun u => blockProd g (fun h => (S.nf.coord (g ⟨i, j⟩ ^ p ^ a ⟨i, j⟩) h).val) u) i hf
    conv_lhs => rw [← hprod]
    exact hsplit

end Bridge

/-- The power word array of any Sims generating set of a finite p-group is realised. -/
theorem SimsGenSet.mem_realizedPW {G : Type} [Group G] [Finite G] (hG : IsPGroup p G)
    {c : ℕ} {r : Fin c → ℕ} {a : SimsIdx c r → ℕ} {g : SimsIdx c r → G}
    (S : SimsGenSet p a g) : S.powerWords ∈ realizedPW p c r a :=
  ⟨G, inferInstance, inferInstance, g, hG, S.powerData⟩

/-- Theorem 3.1 for Sims generating sets: the power word arrays of Sims generating sets of finite
p-groups, with fixed relative order array, number at most `p ^ PW`. -/
theorem liqiao_thm_3_1_simsGenSet (c : ℕ) (r : Fin c → ℕ) (a : SimsIdx c r → ℕ)
    (ha : ∀ k, 1 ≤ a k) :
    {B : PWArray p c r a | ∃ (G : Type) (_ : Group G) (_ : Finite G) (g : SimsIdx c r → G)
      (S : SimsGenSet p a g), IsPGroup p G ∧ S.powerWords = B}.ncard ≤ p ^ pwBound2 a := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (liqiao_thm_3_1 c r a ha)
  rintro B ⟨G, _, _, g, S, hG, rfl⟩
  exact S.mem_realizedPW hG

end PowerWordGroup

end OMA.SimsLite

#print axioms OMA.SimsLite.liqiao_thm_3_1
#print axioms OMA.SimsLite.liqiao_thm_3_1_simsGenSet
