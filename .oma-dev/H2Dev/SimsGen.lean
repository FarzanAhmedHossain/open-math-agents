import H2Dev.Rigidity
import H2Dev.CoreFlag
import H2Dev.Burnside

/-! Li-Qiao, Section 2.1: Sims generating sets and their relation arrays, and Proposition 2.4
(rigidity, BNV Theorem 5.6).

Flattened encoding. The ordered Sims generating set `(g_{i,j})` of the paper, listed as
`g_{1,1}, ..., g_{1,r_1}, g_{2,1}, ..., g_{c,r_c}`, is a tuple `X : Fin n → G`; position `t`
has 0-based weight `lv t` (so `g_{i,j}` has `lv = i - 1`), and `lv` is monotone. The first `s`
positions are the Sims core generators `g_{1,1}, ..., g_{1,s}`. Every position of weight `≥ 2`
(`lv ≥ 1`) is a commutator `X t = ⁅X (df t).1, X (df t).2⁆` with `(df t).2` a core position and
`(df t).1` of weight one less: for weight 2 this is `g_{2,j} = [g_{1,f(j)}, g_{1,k}]` with
`f(j) < k ≤ s` (`(df t).2 = k` is the block of `j`, i.e. `d_{k-1} < j ≤ d_k`), for weight
`i ≥ 3` it is `[g_{i-1,a}, g_{1,b}]`, `b ≤ s` (the recorded index pairs of the paper).

The relation arrays:
* `a t` is the relative-order exponent `a(i,j)`;
* `b t` is the power word: `X t ^ (p ^ a t) = ∏ X u ^ (b t u)` (product in increasing order, the
  Sims normal form (26)/(27)); `b t u = 0` unless `u` has the same weight and comes earlier, or
  has larger weight;
* `c t k` is the commutator coefficient row of `⁅X t, X k⁆`, supported on larger weights. It is
  recorded on the index ranges of Proposition 2.4: weight-1 pairs `t < k`; weight-2 `t` against
  core `k` with `k ≤ (df t).2` (the condition `d_{k-1} < j`); weight `≥ 3` against all core `k`.

Commutator convention: Mathlib's `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`, as in `CommForm.lean` and the rest
of the Sims-lite library. The paper uses `[x, y] = x⁻¹ y⁻¹ x y`, so the generators `g_{i,j}` for
`i ≥ 2` and the commutator coefficients `c` here differ from the paper's by this change of
convention; rigidity and all counts are unaffected, and downstream modules must use the same
convention.

Main results:
* `prop_2_4` (Proposition 2.4) and `sims_rigidity`;
* `exists_sims_gen` (Section 2.1): the paper's Sims generating set. The core comes from
  `CoreFlag.core_flag` (strict flag, BNV Prop 5.2); layer 1 is the core completed greedily to a
  basis modulo `Φ(G)`; each later layer is selected greedily, as a minimum generating set
  modulo `γ_{i+1} γ_i^p`, from the commutators of the previous layer with the core (weight 2 in
  blocks sorted by the second index). The properties are collected in `SimsGen`: `r_i` entries
  in weight `i`, with `p ^ r_i |γ_{i+1} γ_i^p| = |γ_i|` and `r_1 = d(G)`; relative orders `≥ 1` and
  `n ≤ m`; the block structure `(d_k)`, `f` of weight 2; unique normal forms (26).
The weight-3 index restriction `a > d_{b-1}` (BNV 5.4) is enforced: layer 3 is selected only
from the `[g_{2,a}, g_{1,b}]` with `b ≤ co(a)` (`cVal`), these still span `γ_3` modulo
`γ_4 γ_3^p` by a Jacobi reduction (`sLay_span_two`), and the restriction is recorded as the field
`SimsGen.w3`. Proposition 2.4 only records `c(2, j, k, ·)` for `k ≤ (df j).2`, as in the
paper. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u v

section SProd

variable {D : Type u} [Group D]

/-- The ordered product `f 0 * f 1 * ... * f (n - 1)`. -/
def sprod : (n : ℕ) → (Fin n → D) → D
  | 0, _ => 1
  | n + 1, f => f 0 * sprod n (fun i => f i.succ)

lemma sprod_mem (K : Subgroup D) : ∀ (n : ℕ) (f : Fin n → D), (∀ i, f i ∈ K) → sprod n f ∈ K
  | 0, _, _ => by
    show (1 : D) ∈ K
    exact K.one_mem
  | n + 1, f, h => by
    show f 0 * sprod n (fun i => f i.succ) ∈ K
    exact K.mul_mem (h 0) (sprod_mem K n _ (fun i => h i.succ))

lemma map_sprod {E : Type v} [Group E] (φ : D →* E) : ∀ (n : ℕ) (f : Fin n → D),
    φ (sprod n f) = sprod n (fun i => φ (f i))
  | 0, _ => by
    show φ 1 = 1
    exact map_one φ
  | n + 1, f => by
    show φ (f 0 * sprod n (fun i => f i.succ)) = φ (f 0) * sprod n (fun i => φ (f i.succ))
    rw [map_mul, map_sprod φ n]

/-- The Sims normal-form word `∏_t X t ^ e t`, in increasing position order. -/
def nfw {n : ℕ} (X : Fin n → D) (e : Fin n → ℕ) : D := sprod n (fun t => X t ^ e t)

lemma map_nfw {E : Type v} [Group E] (φ : D →* E) {n : ℕ} (X : Fin n → D) (e : Fin n → ℕ) :
    φ (nfw X e) = nfw (fun t => φ (X t)) e := by
  unfold nfw
  rw [map_sprod]
  simp only [map_pow]

lemma nfw_mem {n : ℕ} (X : Fin n → D) (e : Fin n → ℕ) (T : Set (Fin n))
    (h : ∀ t, e t ≠ 0 → t ∈ T) : nfw X e ∈ Subgroup.closure (X '' T) := by
  unfold nfw
  apply sprod_mem
  intro t
  show X t ^ e t ∈ _
  by_cases ht : e t = 0
  · rw [ht, pow_zero]
    exact one_mem _
  · have hmem : X t ∈ Subgroup.closure (X '' T) := Subgroup.subset_closure ⟨t, h t ht, rfl⟩
    exact pow_mem hmem _

lemma sprod_one : ∀ (n : ℕ) (f : Fin n → D), (∀ i, f i = 1) → sprod n f = 1
  | 0, _, _ => rfl
  | n + 1, f, h => by
    show f 0 * sprod n (fun i => f i.succ) = 1
    rw [h 0, sprod_one n _ (fun i => h i.succ), one_mul]

lemma sprod_single : ∀ (n : ℕ) (f : Fin n → D) (t : Fin n), (∀ i, i ≠ t → f i = 1) →
    sprod n f = f t
  | 0, _, t, _ => t.elim0
  | n + 1, f, t, h => by
    show f 0 * sprod n (fun i => f i.succ) = f t
    by_cases ht : t = 0
    · rw [sprod_one n _ (fun i => h i.succ (by rw [ht]; exact Fin.succ_ne_zero i)), mul_one, ht]
    · obtain ⟨t', rfl⟩ := Fin.exists_succ_eq.mpr ht
      rw [h 0 (fun h0 => ht h0.symm), one_mul]
      exact sprod_single n _ t' (fun i hi => h i.succ (fun h' => hi (Fin.succ_injective _ h')))

lemma sprod_mul : ∀ (n : ℕ) (f g : Fin n → D), (∀ i j, f i ≠ 1 → g j ≠ 1 → i < j) →
    sprod n f * sprod n g = sprod n (fun i => f i * g i)
  | 0, _, _, _ => by
    show (1 : D) * 1 = 1
    rw [one_mul]
  | n + 1, f, g, h => by
    show f 0 * sprod n (fun i => f i.succ) * (g 0 * sprod n (fun i => g i.succ)) =
      f 0 * g 0 * sprod n (fun i => f i.succ * g i.succ)
    by_cases hg : g 0 = 1
    · rw [hg, one_mul, mul_one, mul_assoc]
      congr 1
      exact sprod_mul n _ _ (fun i j hi hj => Fin.succ_lt_succ_iff.mp (h _ _ hi hj))
    · have hf : ∀ i, f i = 1 := by
        intro i
        by_contra hi
        exact absurd (h i 0 hi hg) (Fin.not_lt_zero i)
      rw [sprod_one n _ (fun i => hf i.succ), hf 0]
      simp only [one_mul]
      congr 1
      congr 1
      funext i
      rw [hf i.succ, one_mul]

lemma nfw_mul {n : ℕ} (X : Fin n → D) (e1 e2 : Fin n → ℕ)
    (h : ∀ u v, e1 u ≠ 0 → e2 v ≠ 0 → u < v) : nfw X e1 * nfw X e2 = nfw X (e1 + e2) := by
  unfold nfw
  rw [sprod_mul]
  · congr 1
    funext i
    rw [Pi.add_apply, pow_add]
  · intro i j hi hj
    refine h i j (fun h0 => hi ?_) (fun h0 => hj ?_)
    · simp only [h0, pow_zero]
    · simp only [h0, pow_zero]

/-- The exponent vector with a single entry `k` at `t`. -/
def delta {n : ℕ} (t : Fin n) (k : ℕ) : Fin n → ℕ := fun u => if u = t then k else 0

lemma nfw_delta {n : ℕ} (X : Fin n → D) (t : Fin n) (k : ℕ) : nfw X (delta t k) = X t ^ k := by
  unfold nfw
  rw [sprod_single n _ t]
  · show X t ^ (if t = t then k else 0) = X t ^ k
    rw [if_pos rfl]
  · intro i hi
    show X i ^ (if i = t then k else 0) = 1
    rw [if_neg hi, pow_zero]

lemma nfw_zero {n : ℕ} (X : Fin n → D) : nfw X (fun _ => 0) = 1 := by
  unfold nfw
  exact sprod_one n _ (fun i => pow_zero _)

end SProd

section CardLe

variable {D : Type u} [Group D]

/-- One step of the collection: if `x` normalises `K` and `x ^ q ∈ K`, every element of the group
generated by `x` and `K` is `y * x ^ k` with `y ∈ K`. -/
lemma exists_mul_pow_of_mem (K : Subgroup D) (x : D) (q : ℕ) (hq : 0 < q)
    (hconj : ∀ y ∈ K, x * y * x⁻¹ ∈ K) (hpow : x ^ q ∈ K) (S : Set D)
    (hS : S ⊆ insert x (K : Set D)) :
    ∀ z ∈ Subgroup.closure S, ∃ y ∈ K, ∃ k : ℕ, z = y * x ^ k := by
  have hconjm : ∀ m : ℕ, ∀ y ∈ K, x ^ m * y * (x ^ m)⁻¹ ∈ K := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih =>
      intro y hy
      have := hconj _ (ih y hy)
      convert this using 1
      group
  intro z hz
  induction hz using Subgroup.closure_induction_left with
  | one => exact ⟨1, one_mem _, 0, by simp⟩
  | mul_left g hg z hz ih =>
    obtain ⟨y, hy, k, rfl⟩ := ih
    rcases Set.mem_insert_iff.mp (hS hg) with rfl | hg'
    · exact ⟨g * y * g⁻¹, hconj y hy, k + 1, by group⟩
    · exact ⟨g * y, mul_mem hg' hy, k, by group⟩
  | inv_mul_cancel g hg z hz ih =>
    obtain ⟨y, hy, k, rfl⟩ := ih
    rcases Set.mem_insert_iff.mp (hS hg) with rfl | hg'
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      refine ⟨g ^ q' * ((g ^ (q' + 1))⁻¹ * y) * (g ^ q')⁻¹,
        hconjm q' _ (mul_mem (inv_mem hpow) hy), q' + k, ?_⟩
      group
    · exact ⟨g⁻¹ * y, mul_mem (inv_mem hg') hy, k, by group⟩

/-- The cardinality step: `|⟨x, K⟩| ≤ q |K|`. -/
lemma card_closure_le_mul [Finite D] (K : Subgroup D) (x : D) (q : ℕ) (hq : 0 < q)
    (hconj : ∀ y ∈ K, x * y * x⁻¹ ∈ K) (hpow : x ^ q ∈ K) (S : Set D)
    (hS : S ⊆ insert x (K : Set D)) :
    Nat.card (Subgroup.closure S) ≤ Nat.card K * q := by
  have key : ∀ z ∈ Subgroup.closure S, ∃ yk : K × Fin q, z = (yk.1 : D) * x ^ (yk.2 : ℕ) := by
    intro z hz
    obtain ⟨y, hy, k, rfl⟩ := exists_mul_pow_of_mem K x q hq hconj hpow S hS z hz
    refine ⟨(⟨y * (x ^ q) ^ (k / q), mul_mem hy (pow_mem hpow _)⟩, ⟨k % q, Nat.mod_lt _ hq⟩), ?_⟩
    show y * x ^ k = y * (x ^ q) ^ (k / q) * x ^ (k % q)
    rw [mul_assoc, ← pow_mul, ← pow_add, Nat.div_add_mod]
  choose F hF using key
  have hinj : Function.Injective (fun z : Subgroup.closure S => F z.1 z.2) := by
    intro z z' h
    have h' : F z.1 z.2 = F z'.1 z'.2 := h
    apply Subtype.ext
    calc z.1 = ((F z.1 z.2).1 : D) * x ^ ((F z.1 z.2).2 : ℕ) := hF _ _
      _ = ((F z'.1 z'.2).1 : D) * x ^ ((F z'.1 z'.2).2 : ℕ) := by rw [h']
      _ = z'.1 := (hF _ _).symm
  have hc := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_fin] at hc

/-- An element normalising the generators of a subgroup normalises the subgroup. -/
lemma conj_mem_of_gen (T : Set D) (x : D) (h : ∀ z ∈ T, x * z * x⁻¹ ∈ Subgroup.closure T) :
    ∀ y ∈ Subgroup.closure T, x * y * x⁻¹ ∈ Subgroup.closure T := by
  intro y hy
  have hle : Subgroup.closure T ≤ (Subgroup.closure T).comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro z hz
    exact h z hz
  simpa using hle hy

/-- Collection along a well-ordered relation: if every generator `X t` has `X t ^ q t` in the
subgroup generated by its successors, and normalises it, then `|⟨X⟩| ≤ ∏ q t`. -/
theorem card_le_of_prec [Finite D] {n : ℕ} (X : Fin n → D) (q : Fin n → ℕ)
    (hq : ∀ t, 0 < q t) (prec : Fin n → Fin n → Prop)
    (hirr : ∀ t, ¬ prec t t) (hasymm : ∀ t u, prec t u → ¬ prec u t)
    (hmin : ∀ S : Finset (Fin n), S.Nonempty → ∃ t ∈ S, ∀ u ∈ S, u ≠ t → prec t u)
    (hpow : ∀ t, X t ^ q t ∈ Subgroup.closure (X '' {u | prec t u}))
    (hconj : ∀ t u, prec t u → X t * X u * (X t)⁻¹ ∈ Subgroup.closure (X '' {u | prec t u})) :
    ∀ S : Finset (Fin n), (∀ t ∈ S, ∀ u, prec t u → u ∈ S) →
      Nat.card (Subgroup.closure (X '' (S : Set (Fin n)))) ≤ ∏ t ∈ S, q t := by
  suffices h : ∀ k, ∀ S : Finset (Fin n), S.card = k → (∀ t ∈ S, ∀ u, prec t u → u ∈ S) →
      Nat.card (Subgroup.closure (X '' (S : Set (Fin n)))) ≤ ∏ t ∈ S, q t from
    fun S hS => h _ S rfl hS
  intro k
  induction k with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro S hS hup
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t, htS, htmin⟩ := hmin S hne
    have hup' : ∀ t' ∈ S.erase t, ∀ u, prec t' u → u ∈ S.erase t := by
      intro t' ht' u hu
      have ht'S := Finset.mem_of_mem_erase ht'
      have ht't := Finset.ne_of_mem_erase ht'
      refine Finset.mem_erase.mpr ⟨?_, hup t' ht'S u hu⟩
      rintro rfl
      exact hasymm _ _ (htmin t' ht'S ht't) hu
    have hcard : (S.erase t).card = k := by
      rw [Finset.card_erase_of_mem htS]
      omega
    have hK := ih (S.erase t) hcard hup'
    have hsucc : Subgroup.closure (X '' {u | prec t u}) ≤
        Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) := by
      apply Subgroup.closure_mono
      rintro _ ⟨u, hu, rfl⟩
      have hu' : prec t u := hu
      refine ⟨u, ?_, rfl⟩
      rw [Finset.mem_coe]
      refine Finset.mem_erase.mpr ⟨?_, hup t htS u hu'⟩
      rintro rfl
      exact hirr _ hu'
    have hconjK := conj_mem_of_gen (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) (X t) (by
      rintro _ ⟨u, hu, rfl⟩
      rw [Finset.mem_coe] at hu
      have hut := Finset.ne_of_mem_erase hu
      have huS := Finset.mem_of_mem_erase hu
      exact hsucc (hconj t u (htmin u huS hut)))
    have hS' : X '' (S : Set (Fin n)) ⊆
        insert (X t) ((Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) :
          Subgroup D) : Set D) := by
      rintro _ ⟨u, hu, rfl⟩
      rw [Finset.mem_coe] at hu
      by_cases hut : u = t
      · rw [hut]
        exact Set.mem_insert _ _
      · refine Set.mem_insert_of_mem _ (Subgroup.subset_closure ⟨u, ?_, rfl⟩)
        rw [Finset.mem_coe]
        exact Finset.mem_erase.mpr ⟨hut, hu⟩
    have hstep := card_closure_le_mul _ (X t) (q t) (hq t) hconjK (hsucc (hpow t)) _ hS'
    calc Nat.card (Subgroup.closure (X '' (S : Set (Fin n))))
        ≤ Nat.card (Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n)))) * q t :=
          hstep
      _ ≤ (∏ u ∈ S.erase t, q u) * q t := Nat.mul_le_mul_right _ hK
      _ = ∏ u ∈ S, q u := by rw [mul_comm, Finset.mul_prod_erase S q htS]

/-- The lower bound matching `card_le_of_prec`: if no power `X t ^ k` with `0 < k < q t` lies in
the subgroup generated by the successors of `t`, then `|⟨X⟩| ≥ ∏ q t`. -/
theorem card_ge_of_prec [Finite D] {n : ℕ} (X : Fin n → D) (q : Fin n → ℕ)
    (prec : Fin n → Fin n → Prop) (hasymm : ∀ t u, prec t u → ¬ prec u t)
    (hmin : ∀ S : Finset (Fin n), S.Nonempty → ∃ t ∈ S, ∀ u ∈ S, u ≠ t → prec t u)
    (hnot : ∀ t k, 0 < k → k < q t → X t ^ k ∉ Subgroup.closure (X '' {u | prec t u})) :
    ∀ S : Finset (Fin n), (∀ t ∈ S, ∀ u, prec t u → u ∈ S) →
      ∏ t ∈ S, q t ≤ Nat.card (Subgroup.closure (X '' (S : Set (Fin n)))) := by
  suffices h : ∀ k, ∀ S : Finset (Fin n), S.card = k → (∀ t ∈ S, ∀ u, prec t u → u ∈ S) →
      ∏ t ∈ S, q t ≤ Nat.card (Subgroup.closure (X '' (S : Set (Fin n)))) from
    fun S hS => h _ S rfl hS
  intro k
  induction k with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro S hS hup
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t, htS, htmin⟩ := hmin S hne
    have hup' : ∀ t' ∈ S.erase t, ∀ u, prec t' u → u ∈ S.erase t := by
      intro t' ht' u hu
      have ht'S := Finset.mem_of_mem_erase ht'
      have ht't := Finset.ne_of_mem_erase ht'
      refine Finset.mem_erase.mpr ⟨?_, hup t' ht'S u hu⟩
      rintro rfl
      exact hasymm _ _ (htmin t' ht'S ht't) hu
    have hcard : (S.erase t).card = k := by
      rw [Finset.card_erase_of_mem htS]
      omega
    have hK := ih (S.erase t) hcard hup'
    have hKL : Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) ≤
        Subgroup.closure (X '' (S : Set (Fin n))) := by
      apply Subgroup.closure_mono
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu)), rfl⟩
    have hKs : Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) ≤
        Subgroup.closure (X '' {u | prec t u}) := by
      apply Subgroup.closure_mono
      rintro _ ⟨u, hu, rfl⟩
      have hu' := Finset.mem_coe.mp hu
      exact ⟨u, htmin u (Finset.mem_of_mem_erase hu') (Finset.ne_of_mem_erase hu'), rfl⟩
    have hxL : X t ∈ Subgroup.closure (X '' (S : Set (Fin n))) :=
      Subgroup.subset_closure ⟨t, Finset.mem_coe.mpr htS, rfl⟩
    have hinj : Function.Injective
        (fun yk : Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) ×
            Fin (q t) =>
          (⟨(yk.1 : D) * X t ^ (yk.2 : ℕ), mul_mem (hKL yk.1.2) (pow_mem hxL _)⟩ :
            Subgroup.closure (X '' (S : Set (Fin n))))) := by
      intro a b h
      have heq : (a.1 : D) * X t ^ (a.2 : ℕ) = (b.1 : D) * X t ^ (b.2 : ℕ) :=
        congrArg Subtype.val h
      have hkk : (a.2 : ℕ) = b.2 := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have e1 : X t ^ ((b.2 : ℕ) - a.2) = (b.1 : D)⁻¹ * a.1 := by
            rw [pow_sub _ hlt.le, eq_mul_inv_of_mul_eq heq]
            group
          have hmem : X t ^ ((b.2 : ℕ) - a.2) ∈
              Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) := by
            rw [e1]
            exact mul_mem (inv_mem b.1.2) a.1.2
          have hb2 := b.2.isLt
          exact hnot t _ (by omega) (by omega) (hKs hmem)
        · have e1 : X t ^ ((a.2 : ℕ) - b.2) = (a.1 : D)⁻¹ * b.1 := by
            rw [pow_sub _ hlt.le, eq_mul_inv_of_mul_eq heq.symm]
            group
          have hmem : X t ^ ((a.2 : ℕ) - b.2) ∈
              Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n))) := by
            rw [e1]
            exact mul_mem (inv_mem a.1.2) b.1.2
          have ha2 := a.2.isLt
          exact hnot t _ (by omega) (by omega) (hKs hmem)
      have hy : (a.1 : D) = b.1 := by
        rw [hkk] at heq
        exact mul_right_cancel heq
      exact Prod.ext (Subtype.ext hy) (Fin.ext hkk)
    have hc := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_fin] at hc
    calc ∏ u ∈ S, q u = (∏ u ∈ S.erase t, q u) * q t := by
          rw [mul_comm, Finset.mul_prod_erase S q htS]
      _ ≤ Nat.card (Subgroup.closure (X '' ((S.erase t : Finset (Fin n)) : Set (Fin n)))) * q t :=
          Nat.mul_le_mul_right _ hK
      _ ≤ _ := hc

end CardLe

section Data

/-- The data of an ordered Sims generating set, flattened (see the module docstring): the
number `n` of generators, the Sims rank `s`, the 0-based weights `lv`, the commutator definitions
`df` of the positions of weight `≥ 2`, and the relation arrays `a`, `b`, `c`. -/
structure SimsData where
  n : ℕ
  s : ℕ
  lv : Fin n → ℕ
  df : Fin n → Fin n × Fin n
  a : Fin n → ℕ
  b : Fin n → Fin n → ℕ
  c : Fin n → Fin n → Fin n → ℕ

namespace SimsData

/-- `u` comes after `t` in the collection order: larger weight, or the same weight and an
earlier position. The power word of `X t` lives on the successors of `t`. -/
def prec (d : SimsData) (t u : Fin d.n) : Prop :=
  d.lv t < d.lv u ∨ (d.lv t = d.lv u ∧ u.val < t.val)

/-- The index ranges of the commutator coefficient array in Proposition 2.4. -/
def Rec (d : SimsData) (t k : Fin d.n) : Prop :=
  (d.lv t = 0 ∧ d.lv k = 0 ∧ t < k) ∨ (d.lv t = 1 ∧ k.val ≤ (d.df t).2.val) ∨
    (2 ≤ d.lv t ∧ k.val < d.s)

/-- Structural validity of Sims data (the shape of a Sims generating set). -/
structure Struct (d : SimsData) : Prop where
  mono : ∀ t u : Fin d.n, t ≤ u → d.lv t ≤ d.lv u
  s_le : d.s ≤ d.n
  core : ∀ t : Fin d.n, t.val < d.s → d.lv t = 0
  df_lv : ∀ t, 1 ≤ d.lv t → d.lv (d.df t).1 + 1 = d.lv t
  df_core : ∀ t, 1 ≤ d.lv t → (d.df t).2.val < d.s
  df_one : ∀ t, d.lv t = 1 → (d.df t).1 < (d.df t).2

/-- Validity of Sims data: the shape, and the zero patterns of the power word and commutator
coefficient arrays. -/
structure Valid (d : SimsData) : Prop extends Struct d where
  b_supp : ∀ t u, d.b t u ≠ 0 → d.prec t u
  c_supp : ∀ t k u, d.c t k u ≠ 0 → d.lv t < d.lv u

/-- The ranges `0 ≤ b(·, u) < p ^ a(u)` and `0 ≤ c(·, u) < p ^ a(u)` of the arrays. -/
def Bounded (p : ℕ) (d : SimsData) : Prop :=
  (∀ t u, d.b t u < p ^ d.a u) ∧ (∀ t k u, d.c t k u < p ^ d.a u)

lemma prec_irrefl (d : SimsData) (t : Fin d.n) : ¬ d.prec t t := by
  unfold prec
  omega

lemma prec_asymm (d : SimsData) (t u : Fin d.n) (h : d.prec t u) : ¬ d.prec u t := by
  unfold prec at *
  omega

lemma prec_min (d : SimsData) (S : Finset (Fin d.n)) (hS : S.Nonempty) :
    ∃ t ∈ S, ∀ u ∈ S, u ≠ t → d.prec t u := by
  obtain ⟨t0, ht0, hmin0⟩ := Finset.exists_min_image S d.lv hS
  have hT : (S.filter (fun u => d.lv u = d.lv t0)).Nonempty :=
    ⟨t0, Finset.mem_filter.mpr ⟨ht0, rfl⟩⟩
  obtain ⟨t, htT, hmax⟩ := Finset.exists_max_image _ (fun u : Fin d.n => u.val) hT
  obtain ⟨htS, htl⟩ := Finset.mem_filter.mp htT
  refine ⟨t, htS, fun u huS hut => ?_⟩
  have h1 := hmin0 u huS
  unfold prec
  by_cases hl : d.lv u = d.lv t0
  · have h2 := hmax u (Finset.mem_filter.mpr ⟨huS, hl⟩)
    have h3 : u.val ≠ t.val := fun h => hut (Fin.ext h)
    right
    constructor
    · omega
    · have h2' : u.val ≤ t.val := h2
      omega
  · left
    omega

end SimsData

/-- `(G, X)` realises the Sims data `d` at the prime `p`: `|G| = p ^ (∑ a)`, `X` generates `G`,
the commutator definitions hold, and the power and (recorded) commutator relations hold with the
arrays of `d` as Sims normal-form coordinates. -/
structure SimsRealizes (p : ℕ) (d : SimsData) {G : Type u} [Group G] (X : Fin d.n → G) : Prop where
  card : Nat.card G = p ^ (∑ t, d.a t)
  gen : Subgroup.closure (Set.range X) = ⊤
  dfeq : ∀ t, 1 ≤ d.lv t → X t = ⁅X (d.df t).1, X (d.df t).2⁆
  pow : ∀ t, X t ^ (p ^ d.a t) = nfw X (d.b t)
  comm0 : ∀ t k, d.lv t = 0 → d.lv k = 0 → t < k → ⁅X t, X k⁆ = nfw X (d.c t k)
  comm1 : ∀ t k : Fin d.n, d.lv t = 1 → k.val ≤ (d.df t).2.val → ⁅X t, X k⁆ = nfw X (d.c t k)
  comm2 : ∀ t k : Fin d.n, 2 ≤ d.lv t → k.val < d.s → ⁅X t, X k⁆ = nfw X (d.c t k)

end Data

section CardData

variable {D : Type u} [Group D]

/-- The weight-`v` generators. -/
abbrev levSet (d : SimsData) (Z : Fin d.n → D) (v : ℕ) : Set D := Z '' {t | d.lv t = v}

/-- The core generators, indexed by `ℕ` (junk `1` out of range). -/
def simsU (d : SimsData) (Z : Fin d.n → D) (k : ℕ) : D := if h : k < d.n then Z ⟨k, h⟩ else 1

lemma simsU_of_lt (d : SimsData) (Z : Fin d.n → D) {k : ℕ} (h : k < d.n) :
    simsU d Z k = Z ⟨k, h⟩ := by
  unfold simsU
  rw [dif_pos h]

lemma simsU_val (d : SimsData) (Z : Fin d.n → D) (k : Fin d.n) : simsU d Z k.val = Z k :=
  simsU_of_lt d Z k.isLt

/-- The pairs of core indices defining the weight-2 generators. -/
def simsP (d : SimsData) : Set (ℕ × ℕ) :=
  {ab | ∃ t, d.lv t = 1 ∧ ab = ((d.df t).1.val, (d.df t).2.val)}

lemma mem_simsP (d : SimsData) {ab : ℕ × ℕ} :
    ab ∈ simsP d ↔ ∃ t, d.lv t = 1 ∧ ab = ((d.df t).1.val, (d.df t).2.val) := Iff.rfl

/-- The first factor of a commutator definition comes earlier. -/
lemma df_fst_lt (d : SimsData) (hd : d.Struct) (t : Fin d.n) (ht : 1 ≤ d.lv t) :
    (d.df t).1.val < t.val := by
  have h1 := hd.df_lv t ht
  by_contra hcon
  have h2 := hd.mono t (d.df t).1 (Fin.le_def.mpr (by omega))
  omega

/-- Every generator lies in the term of the lower central series given by its weight. -/
lemma lv_mem_lcs (d : SimsData) (hd : d.Struct) (Z : Fin d.n → D)
    (hdf : ∀ t, 1 ≤ d.lv t → Z t = ⁅Z (d.df t).1, Z (d.df t).2⁆) :
    ∀ t, Z t ∈ lcs D (d.lv t) := by
  refine fin_strong_ind ?_
  intro t ih
  by_cases h0 : d.lv t = 0
  · rw [h0, lcs_zero]
    exact Subgroup.mem_top _
  · have h1 : 1 ≤ d.lv t := by omega
    have hprev := ih (d.df t).1 (df_fst_lt d hd t h1)
    rw [← hd.df_lv t h1, hdf t h1]
    exact commElem_mem_lcs_succ hprev _

/-- The Lie lemma for Sims data: if the weight-`≥ 1` generators are commutator-defined and the
recorded commutators lie in the next weight modulo the next term, then each `lcs D w` (`w ≥ 1`)
is generated by the generators of weight `≥ w`. -/
theorem sims_lcs_tail (d : SimsData) (hd : d.Struct) (Z : Fin d.n → D)
    (hgen : Subgroup.closure (Set.range Z) = ⊤) (hN : ∃ N, lcs D N = ⊥)
    (hdf : ∀ t, 1 ≤ d.lv t → Z t = ⁅Z (d.df t).1, Z (d.df t).2⁆)
    (hH1' : ∀ i k, d.lv i = 0 → d.lv k = 0 →
      ⁅Z i, Z k⁆ ∈ Subgroup.closure (levSet d Z 1) ⊔ lcs D 2)
    (hH2' : ∀ t k : Fin d.n, d.lv t = 1 → k.val ≤ (d.df t).2.val →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (levSet d Z 2) ⊔ lcs D 3)
    (hH3' : ∀ t k : Fin d.n, 2 ≤ d.lv t → k.val < d.s →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (levSet d Z (d.lv t + 1)) ⊔ lcs D (d.lv t + 2)) :
    ∀ w, 1 ≤ w → lcs D w ≤ Subgroup.closure (Z '' {u | w ≤ d.lv u}) := by
  have hlv := lv_mem_lcs d hd Z hdf
  -- the data of the Lie lemma
  have hu : ∀ k : Fin d.n, simsU d Z k.val = Z k := simsU_val d Z
  have hP : ∀ ab ∈ simsP d, ab.1 < ab.2 ∧ ab.2 < d.s := by
    intro ab hab
    obtain ⟨t, ht, rfl⟩ := (mem_simsP d).mp hab
    exact ⟨Fin.lt_def.mp (hd.df_one t ht), hd.df_core t (by omega)⟩
  have hE1 : levSet d Z 1 = (fun ab : ℕ × ℕ => ⁅simsU d Z ab.1, simsU d Z ab.2⁆) '' simsP d := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : d.lv t = 1 := ht
      refine ⟨((d.df t).1.val, (d.df t).2.val), (mem_simsP d).mpr ⟨t, ht', rfl⟩, ?_⟩
      show ⁅simsU d Z (d.df t).1.val, simsU d Z (d.df t).2.val⁆ = Z t
      rw [hu, hu, hdf t (by omega)]
    · rintro ⟨ab, hab, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (mem_simsP d).mp hab
      refine ⟨t, ht, ?_⟩
      show Z t = ⁅simsU d Z (d.df t).1.val, simsU d Z (d.df t).2.val⁆
      rw [hu, hu]
      exact hdf t (by omega)
  have hL2 : ∀ w, 1 ≤ w → ∀ x ∈ levSet d Z (w + 1), ∃ y ∈ Subgroup.closure (levSet d Z w),
      ∃ b < d.s, x = ⁅y, simsU d Z b⁆ := by
    intro w hw x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have ht' : d.lv t = w + 1 := ht
    have h1 : 1 ≤ d.lv t := by omega
    have ha : d.lv (d.df t).1 = w := by have := hd.df_lv t h1; omega
    refine ⟨Z (d.df t).1, Subgroup.subset_closure ⟨(d.df t).1, ha, rfl⟩, (d.df t).2.val,
      hd.df_core t h1, ?_⟩
    rw [hu]
    exact hdf t h1
  have hL0 : Subgroup.closure (levSet d Z 0) ⊔ lcs D 1 = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    by_cases h0 : d.lv t = 0
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, h0, rfl⟩)
    · exact Subgroup.mem_sup_right (lcs_antitone (D := D) (show 1 ≤ d.lv t by omega) (hlv t))
  have hH1 : ∀ x ∈ levSet d Z 0, ∀ y ∈ levSet d Z 0,
      ⁅x, y⁆ ∈ Subgroup.closure (levSet d Z 1) ⊔ lcs D 2 := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨k, hk, rfl⟩
    exact hH1' i k hi hk
  have hH2 : ∀ ab ∈ simsP d, ∀ k ≤ ab.2, ⁅⁅simsU d Z ab.1, simsU d Z ab.2⁆, simsU d Z k⁆ ∈
      Subgroup.closure (levSet d Z 2) ⊔ lcs D 3 := by
    intro ab hab k hk
    obtain ⟨t, ht, rfl⟩ := (mem_simsP d).mp hab
    have hk' : k ≤ (d.df t).2.val := hk
    have hks : k < d.n := by
      have := hd.df_core t (by omega)
      have := hd.s_le
      omega
    show ⁅⁅simsU d Z (d.df t).1.val, simsU d Z (d.df t).2.val⁆, simsU d Z k⁆ ∈ _
    rw [hu, hu, ← hdf t (by omega), simsU_of_lt d Z hks]
    exact hH2' t ⟨k, hks⟩ ht hk'
  have hH3 : ∀ w, 2 ≤ w → ∀ x ∈ levSet d Z w, ∀ k < d.s,
      ⁅x, simsU d Z k⁆ ∈ Subgroup.closure (levSet d Z (w + 1)) ⊔ lcs D (w + 2) := by
    rintro w hw _ ⟨t, ht, rfl⟩ k hk
    have ht' : d.lv t = w := ht
    have hks : k < d.n := lt_of_lt_of_le hk hd.s_le
    rw [simsU_of_lt d Z hks]
    have hres := hH3' t ⟨k, hks⟩ (by omega) hk
    rwa [ht'] at hres
  obtain ⟨N, hN⟩ := hN
  have htail := lie_lemma_tail d.s (simsU d Z) (levSet d Z 0) (simsP d) (levSet d Z) hP hE1 hL2 hL0 hH1 hH2 hH3 N hN
  intro w hw
  refine le_trans (htail w hw) ?_
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_Ici, exists_prop] at hx
  obtain ⟨v, hv, t, ht, rfl⟩ := hx
  have ht' : d.lv t = v := ht
  exact Subgroup.subset_closure ⟨t, (show w ≤ d.lv t by omega), rfl⟩

/-- The counting core of Proposition 2.4: a nilpotent group generated by a tuple satisfying the
relations of valid Sims data has at most `p ^ (∑ a)` elements. -/
theorem card_le_of_sims [Finite D] {p : ℕ} (hp : 0 < p) (d : SimsData) (hd : d.Valid)
    (Z : Fin d.n → D) (hgen : Subgroup.closure (Set.range Z) = ⊤) (hN : ∃ N, lcs D N = ⊥)
    (hdf : ∀ t, 1 ≤ d.lv t → Z t = ⁅Z (d.df t).1, Z (d.df t).2⁆)
    (hpow : ∀ t, Z t ^ (p ^ d.a t) ∈ Subgroup.closure (Z '' {u | d.prec t u}))
    (hc0 : ∀ t k, d.lv t = 0 → d.lv k = 0 → t < k →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (Z '' {u | d.lv t < d.lv u}))
    (hc1 : ∀ t k : Fin d.n, d.lv t = 1 → k.val ≤ (d.df t).2.val →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (Z '' {u | d.lv t < d.lv u}))
    (hc2 : ∀ t k : Fin d.n, 2 ≤ d.lv t → k.val < d.s →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (Z '' {u | d.lv t < d.lv u})) :
    Nat.card D ≤ p ^ (∑ t, d.a t) := by
  have hlv := lv_mem_lcs d hd.toStruct Z hdf
  have hmono : ∀ (P Q : Fin d.n → Prop), (∀ u, P u → Q u) →
      Subgroup.closure (Z '' {u | P u}) ≤ Subgroup.closure (Z '' {u | Q u}) :=
    fun P Q h => Subgroup.closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact ⟨u, h u hu, rfl⟩)
  -- the tail from weight `w` lies in the weight-`w` generators modulo the next term
  have hdrop : ∀ w, 1 ≤ w → Subgroup.closure (Z '' {u | w ≤ d.lv u}) ≤
      Subgroup.closure (levSet d Z w) ⊔ lcs D (w + 1) := by
    intro w hw
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : w ≤ d.lv t := ht
    rcases Nat.lt_or_ge w (d.lv t) with hlt' | hge
    · exact Subgroup.mem_sup_right (lcs_antitone (D := D) (show w + 1 ≤ d.lv t by omega) (hlv t))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, le_antisymm hge ht', rfl⟩)
  have hH1' : ∀ i k, d.lv i = 0 → d.lv k = 0 →
      ⁅Z i, Z k⁆ ∈ Subgroup.closure (levSet d Z 1) ⊔ lcs D 2 := by
    intro i k hi' hk'
    rcases lt_trichotomy i k with hik | rfl | hki
    · exact hdrop 1 le_rfl (hmono _ _ (fun u hu => by omega) (hc0 i k hi' hk' hik))
    · rw [commutatorElement_self]
      exact one_mem _
    · rw [← commutatorElement_inv]
      exact inv_mem (hdrop 1 le_rfl (hmono _ _ (fun u hu => by omega) (hc0 k i hk' hi' hki)))
  have hH2' : ∀ t k : Fin d.n, d.lv t = 1 → k.val ≤ (d.df t).2.val →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (levSet d Z 2) ⊔ lcs D 3 := fun t k ht hk =>
    hdrop 2 (by omega) (hmono _ _ (fun u hu => by omega) (hc1 t k ht hk))
  have hH3' : ∀ t k : Fin d.n, 2 ≤ d.lv t → k.val < d.s →
      ⁅Z t, Z k⁆ ∈ Subgroup.closure (levSet d Z (d.lv t + 1)) ⊔ lcs D (d.lv t + 2) := by
    intro t k ht hk
    have hres := hdrop (d.lv t + 1) (by omega)
      (hmono _ _ (fun u hu => by omega) (hc2 t k ht hk))
    rwa [show d.lv t + 1 + 1 = d.lv t + 2 by omega] at hres
  have hdeep := sims_lcs_tail d hd.toStruct Z hgen hN hdf hH1' hH2' hH3'
  -- collection
  have hconj : ∀ t u, d.prec t u →
      Z t * Z u * (Z t)⁻¹ ∈ Subgroup.closure (Z '' {u | d.prec t u}) := by
    intro t u htu
    have he : Z t * Z u * (Z t)⁻¹ = ⁅Z t, Z u⁆ * Z u := by
      simp only [commutatorElement_def]
      group
    rw [he]
    refine mul_mem ?_ (Subgroup.subset_closure ⟨u, htu, rfl⟩)
    have h1 := hdeep (d.lv u + 1) (by omega) (commElem_mem_lcs_succ' (Z t) (hlv u))
    refine hmono _ _ (fun u' hu' => ?_) h1
    have hu'' : d.lv u + 1 ≤ d.lv u' := hu'
    have htu' : d.lv t < d.lv u ∨ (d.lv t = d.lv u ∧ u.val < t.val) := htu
    exact Or.inl (by omega)
  have hcard := card_le_of_prec Z (fun t => p ^ d.a t) (fun t => pow_pos hp _) d.prec
    d.prec_irrefl d.prec_asymm d.prec_min hpow hconj Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
  have hprod : ∏ t ∈ (Finset.univ : Finset (Fin d.n)), (fun t => p ^ d.a t) t =
      p ^ (∑ t, d.a t) := Finset.prod_pow_eq_pow_sum _ _ _
  rw [Finset.coe_univ, Set.image_univ, hgen, Subgroup.card_top] at hcard
  exact hcard.trans (le_of_eq hprod)

end CardData

section Rigid

variable {G G' : Type u} [Group G] [Group G']

/-- The paired subgroup of two realisations of the same Sims data has at most `p ^ (∑ a)`
elements. -/
theorem diag_card_le_sims [Finite G] [Finite G'] [Group.IsNilpotent G] [Group.IsNilpotent G']
    {p : ℕ} (hp : 0 < p) (d : SimsData) (hd : d.Valid) (X : Fin d.n → G) (X' : Fin d.n → G')
    (h : SimsRealizes p d X) (h' : SimsRealizes p d X') :
    Nat.card (diagSub X X') ≤ p ^ (∑ t, d.a t) := by
  have hF : ∀ e, diagFst X X' (nfw (diagGen X X') e) = nfw X e := fun e => map_nfw _ _ _
  have hS : ∀ e, diagSnd X X' (nfw (diagGen X X') e) = nfw X' e := fun e => map_nfw _ _ _
  have hrel : ∀ (x : diagSub X X') (e : Fin d.n → ℕ), diagFst X X' x = nfw X e →
      diagSnd X X' x = nfw X' e → x = nfw (diagGen X X') e := by
    intro x e h1 h2
    apply diag_ext X X'
    · rw [h1, hF]
    · rw [h2, hS]
  refine card_le_of_sims hp d hd (diagGen X X') (diagGen_closure X X') ?_ ?_ ?_ ?_ ?_ ?_
  · exact Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
  · intro t ht
    apply diag_ext X X'
    · simp only [map_commutatorElement, diagFst_gen]
      exact h.dfeq t ht
    · simp only [map_commutatorElement, diagSnd_gen]
      exact h'.dfeq t ht
  · intro t
    rw [hrel (diagGen X X' t ^ (p ^ d.a t)) (d.b t) (by simp only [map_pow, diagFst_gen]; exact h.pow t)
      (by simp only [map_pow, diagSnd_gen]; exact h'.pow t)]
    exact nfw_mem _ _ _ (fun u hu => hd.b_supp t u hu)
  · intro t k ht hk htk
    rw [hrel ⁅diagGen X X' t, diagGen X X' k⁆ (d.c t k) (by simp only [map_commutatorElement, diagFst_gen]; exact h.comm0 t k ht hk htk)
      (by simp only [map_commutatorElement, diagSnd_gen]; exact h'.comm0 t k ht hk htk)]
    exact nfw_mem _ _ _ (fun u hu => hd.c_supp t k u hu)
  · intro t k ht hk
    rw [hrel ⁅diagGen X X' t, diagGen X X' k⁆ (d.c t k) (by simp only [map_commutatorElement, diagFst_gen]; exact h.comm1 t k ht hk)
      (by simp only [map_commutatorElement, diagSnd_gen]; exact h'.comm1 t k ht hk)]
    exact nfw_mem _ _ _ (fun u hu => hd.c_supp t k u hu)
  · intro t k ht hk
    rw [hrel ⁅diagGen X X' t, diagGen X X' k⁆ (d.c t k) (by simp only [map_commutatorElement, diagFst_gen]; exact h.comm2 t k ht hk)
      (by simp only [map_commutatorElement, diagSnd_gen]; exact h'.comm2 t k ht hk)]
    exact nfw_mem _ _ _ (fun u hu => hd.c_supp t k u hu)

/-- Rigidity for Sims data: two finite groups realising the same valid Sims data are
isomorphic. -/
theorem sims_rigidity {p : ℕ} (hp : p.Prime) [Finite G] [Finite G'] (d : SimsData)
    (hd : d.Valid) (X : Fin d.n → G) (X' : Fin d.n → G') (h : SimsRealizes p d X)
    (h' : SimsRealizes p d X') : Nonempty (G ≃* G') := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent G := (IsPGroup.of_card h.card).isNilpotent
  have : Group.IsNilpotent G' := (IsPGroup.of_card h'.card).isNilpotent
  have hK := diag_card_le_sims hp.pos d hd X X' h h'
  have hb1 : Function.Bijective (diagFst X X') :=
    (diagFst_surj X X' h.gen).bijective_of_nat_card_le (by rw [h.card]; exact hK)
  have hb2 : Function.Bijective (diagSnd X X') :=
    (diagSnd_surj X X' h'.gen).bijective_of_nat_card_le (by rw [h'.card]; exact hK)
  exact ⟨(MulEquiv.ofBijective (diagFst X X') hb1).symm.trans
    (MulEquiv.ofBijective (diagSnd X X') hb2)⟩

/-- Realising data only reads the commutator coefficients on the recorded index ranges. -/
lemma SimsRealizes.of_rec {p : ℕ} (d : SimsData) (c' : Fin d.n → Fin d.n → Fin d.n → ℕ)
    (hc : ∀ t k u, d.Rec t k → c' t k u = d.c t k u) (X : Fin d.n → G)
    (h : SimsRealizes p { d with c := c' } X) : SimsRealizes p d X where
  card := h.card
  gen := h.gen
  dfeq := h.dfeq
  pow := h.pow
  comm0 := by
    intro t k ht hk htk
    rw [h.comm0 t k ht hk htk]
    congr 1
    funext u
    exact hc t k u (Or.inl ⟨ht, hk, htk⟩)
  comm1 := by
    intro t k ht hk
    rw [h.comm1 t k ht hk]
    congr 1
    funext u
    exact hc t k u (Or.inr (Or.inl ⟨ht, hk⟩))
  comm2 := by
    intro t k ht hk
    rw [h.comm2 t k ht hk]
    congr 1
    funext u
    exact hc t k u (Or.inr (Or.inr ⟨ht, hk⟩))

/-- Proposition 2.4 (BNV Theorem 5.6). Let `G`, `G'` be finite groups with ordered Sims
generating sets `X`, `X'` sharing the integers `p, c, s, (r_i), (d_k)` and the recorded
generator definitions (all encoded in `d`), the relative order array `a`, the power word array
`b`, and the commutator coefficient array on the index ranges of Proposition 2.4 (`d.c` and `c'`
agree wherever `d.Rec` holds). Then `G ≅ G'`. The generator definitions `d.df` (the function
`f` and the higher index pairs) are part of the input data, as in the recorded Sims presentation
data of the paper; `Bounded` is not needed. -/
theorem prop_2_4 {p : ℕ} (hp : p.Prime) [Finite G] [Finite G'] (d : SimsData) (hd : d.Valid)
    (c' : Fin d.n → Fin d.n → Fin d.n → ℕ) (hc : ∀ t k u, d.Rec t k → c' t k u = d.c t k u)
    (X : Fin d.n → G) (X' : Fin d.n → G') (h : SimsRealizes p d X)
    (h' : SimsRealizes p { d with c := c' } X') : Nonempty (G ≃* G') :=
  sims_rigidity hp d hd X X' h (SimsRealizes.of_rec d c' hc X' h')

end Rigid

section Layers

/-! Existence of the relation arrays. Given the shape `d` of a Sims-type generating tuple `X` of a
finite `p`-group (commutator definitions, and each `lcs G w` generated by the positions of weight
`≥ w`), the relative orders `relOrd` are the exponents `a(i, j)` of (25), `|G| = p ^ (∑ a)`, and
every element of the tail subgroups has a Sims normal form (26) with `0 ≤ e < p ^ a`. -/

variable {G : Type u} [Group G]

/-- Positions of weight `> w`, or of weight `w` and index `< j`. For `w = lv t`, `j = t` these are
the successors of `t` in collection order. -/
def lset (d : SimsData) (w j : ℕ) : Set (Fin d.n) :=
  {u | w < d.lv u ∨ (w = d.lv u ∧ u.val < j)}

lemma mem_lset (d : SimsData) {w j : ℕ} {u : Fin d.n} :
    u ∈ lset d w j ↔ w < d.lv u ∨ (w = d.lv u ∧ u.val < j) := Iff.rfl

/-- The relative-order exponent (25) of position `t`. -/
noncomputable def relOrd (p : ℕ) (d : SimsData) (X : Fin d.n → G) (t : Fin d.n) : ℕ :=
  sInf {a : ℕ | X t ^ (p ^ a) ∈ Subgroup.closure (X '' lset d (d.lv t) t.val)}

/-- Normal forms with relative-order bounds exist in the tail subgroup of `(w, j)`. -/
def NFP (p : ℕ) (d : SimsData) (X : Fin d.n → G) (w j : ℕ) : Prop :=
  ∀ z ∈ Subgroup.closure (X '' lset d w j), ∃ e : Fin d.n → ℕ,
    (∀ u, e u ≠ 0 → u ∈ lset d w j) ∧ (∀ u, e u < p ^ relOrd p d X u) ∧ z = nfw X e

variable {p m : ℕ} (d : SimsData) (X : Fin d.n → G)

lemma relOrd_spec [Finite G] (hG : Nat.card G = p ^ m) (t : Fin d.n) :
    X t ^ (p ^ relOrd p d X t) ∈ Subgroup.closure (X '' lset d (d.lv t) t.val) := by
  have hne : {a : ℕ | X t ^ (p ^ a) ∈ Subgroup.closure (X '' lset d (d.lv t) t.val)}.Nonempty := by
    refine ⟨m, ?_⟩
    show X t ^ (p ^ m) ∈ Subgroup.closure (X '' lset d (d.lv t) t.val)
    rw [← hG, pow_card_eq_one']
    exact one_mem _
  exact Nat.sInf_mem hne

lemma relOrd_not [Finite G] (hp : p.Prime) (hG : Nat.card G = p ^ m) (t : Fin d.n) (k : ℕ)
    (hk0 : 0 < k) (hk : k < p ^ relOrd p d X t) :
    X t ^ k ∉ Subgroup.closure (X '' lset d (d.lv t) t.val) := by
  intro hmem
  have h2 : X t ^ (p ^ m) ∈ Subgroup.closure (X '' lset d (d.lv t) t.val) := by
    rw [← hG, pow_card_eq_one']
    exact one_mem _
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right k (p ^ m))
  have h3 : X t ^ (Nat.gcd k (p ^ m)) ∈ Subgroup.closure (X '' lset d (d.lv t) t.val) := by
    have h4 : X t ^ ((Nat.gcd k (p ^ m) : ℕ) : ℤ) ∈
        Subgroup.closure (X '' lset d (d.lv t) t.val) := by
      rw [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      exact mul_mem (zpow_mem hmem _) (zpow_mem h2 _)
    rwa [zpow_natCast] at h4
  rw [he] at h3
  have hle : relOrd p d X t ≤ e := Nat.sInf_le h3
  have hdvd : p ^ e ∣ k := by
    rw [← he]
    exact Nat.gcd_dvd_left k (p ^ m)
  have h5 : p ^ e ≤ k := Nat.le_of_dvd hk0 hdvd
  have h6 : p ^ relOrd p d X t ≤ p ^ e := Nat.pow_le_pow_right hp.pos hle
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h5 hk) h6) (lt_irrefl _)

lemma lset_normal (hlv : ∀ t, X t ∈ lcs G (d.lv t))
    (hdeep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {u | w ≤ d.lv u})) (w j : ℕ) :
    (Subgroup.closure (X '' lset d w j)).Normal := by
  refine normal_of_sandwich (n := w) ?_ ?_
  · refine (hdeep (w + 1) (by omega)).trans (Subgroup.closure_mono ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, Or.inl hu, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' := (mem_lset d).mp hu
    exact lcs_antitone (D := G) (show w ≤ d.lv u by omega) (hlv u)

lemma NFP_of_eq {w j w' j' : ℕ} (h : lset d w j = lset d w' j') (H : NFP p d X w' j') :
    NFP p d X w j := by
  unfold NFP at *
  rw [h]
  exact H

lemma NFP_empty (hp : 0 < p) {w : ℕ} (j : ℕ) (h : ∀ u : Fin d.n, d.lv u < w) :
    NFP p d X w j := by
  intro z hz
  have hempty : lset d w j = ∅ := by
    ext u
    simp only [mem_lset, Set.mem_empty_iff_false, iff_false]
    have := h u
    omega
  rw [hempty, Set.image_empty, Subgroup.closure_empty, Subgroup.mem_bot] at hz
  refine ⟨fun _ => 0, fun u hu => (hu rfl).elim, fun u => pow_pos hp _, ?_⟩
  rw [hz, nfw_zero]

lemma NFP_zero {w : ℕ} (H : NFP p d X (w + 1) d.n) : NFP p d X w 0 := by
  refine NFP_of_eq d X ?_ H
  ext u
  simp only [mem_lset]
  have := u.isLt
  constructor
  · intro h
    omega
  · intro h
    omega

lemma NFP_succ [Finite G] (hp : p.Prime) (hG : Nat.card G = p ^ m) (hd : d.Struct)
    (hlv : ∀ t, X t ∈ lcs G (d.lv t))
    (hdeep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {u | w ≤ d.lv u})) {w j : ℕ}
    (hj : NFP p d X w j) (h0 : NFP p d X w 0) : NFP p d X w (j + 1) := by
  have hlt : ∀ u v : Fin d.n, d.lv u < d.lv v → u < v := by
    intro u v h
    by_contra hc
    have := hd.mono v u (not_lt.mp hc)
    omega
  by_cases hex : ∃ t : Fin d.n, t.val = j ∧ d.lv t = w
  swap
  · refine NFP_of_eq d X ?_ hj
    ext u
    simp only [mem_lset]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1, ?_⟩
        rcases Nat.lt_or_ge u.val j with h3 | h3
        · exact h3
        · exact absurd ⟨u, by omega, h1.symm⟩ hex
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
  obtain ⟨t, rfl, rfl⟩ := hex
  intro z hz
  have hq : 0 < p ^ relOrd p d X t := pow_pos hp.pos _
  have hK := lset_normal d X hlv hdeep (d.lv t) t.val
  have hS : X '' lset d (d.lv t) (t.val + 1) ⊆
      insert (X t) ((Subgroup.closure (X '' lset d (d.lv t) t.val) : Subgroup G) : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    by_cases hut : u = t
    · rw [hut]
      exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ (Subgroup.subset_closure ⟨u, ?_, rfl⟩)
      have hu' := (mem_lset d).mp hu
      have hne : u.val ≠ t.val := fun h => hut (Fin.ext h)
      exact (mem_lset d).mpr (by omega)
  obtain ⟨y, hy, k, rfl⟩ := exists_mul_pow_of_mem _ (X t) _ hq (fun y hy => hK.conj_mem y hy (X t))
    (relOrd_spec d X hG t) _ hS z hz
  obtain ⟨y', hy', k', hk', hyk⟩ : ∃ y' ∈ Subgroup.closure (X '' lset d (d.lv t) t.val),
      ∃ k' < p ^ relOrd p d X t, y * X t ^ k = y' * X t ^ k' :=
    ⟨y * (X t ^ (p ^ relOrd p d X t)) ^ (k / p ^ relOrd p d X t),
      mul_mem hy (pow_mem (relOrd_spec d X hG t) _), k % p ^ relOrd p d X t, Nat.mod_lt _ hq,
      by rw [mul_assoc, ← pow_mul, ← pow_add, Nat.div_add_mod]⟩
  rw [hyk]
  obtain ⟨e', he'S, he'b, rfl⟩ := hj y' hy'
  have hsplit : nfw X e' = nfw X (fun u => if d.lv u = d.lv t then e' u else 0) *
      nfw X (fun u => if d.lv u = d.lv t then 0 else e' u) := by
    rw [nfw_mul]
    · congr 1
      funext u
      simp only [Pi.add_apply]
      split_ifs <;> simp
    · intro u v hu hv
      apply hlt
      have hu1 : d.lv u = d.lv t := by
        by_contra hc
        apply hu
        show (if d.lv u = d.lv t then e' u else 0) = 0
        rw [if_neg hc]
      have hv1 : d.lv v ≠ d.lv t ∧ e' v ≠ 0 := by
        by_cases hc : d.lv v = d.lv t
        · exfalso
          apply hv
          show (if d.lv v = d.lv t then 0 else e' v) = 0
          rw [if_pos hc]
        · refine ⟨hc, fun h0 => hv ?_⟩
          show (if d.lv v = d.lv t then 0 else e' v) = 0
          rw [if_neg hc, h0]
      have := (mem_lset d).mp (he'S v hv1.2)
      omega
  have hHmem : nfw X (fun u => if d.lv u = d.lv t then 0 else e' u) ∈
      Subgroup.closure (X '' lset d (d.lv t) 0) := by
    refine nfw_mem X _ _ (fun v hv => ?_)
    have hv1 : d.lv v ≠ d.lv t ∧ e' v ≠ 0 := by
      by_cases hc : d.lv v = d.lv t
      · exfalso
        apply hv
        show (if d.lv v = d.lv t then 0 else e' v) = 0
        rw [if_pos hc]
      · refine ⟨hc, fun h0 => hv ?_⟩
        show (if d.lv v = d.lv t then 0 else e' v) = 0
        rw [if_neg hc, h0]
    have := (mem_lset d).mp (he'S v hv1.2)
    exact (mem_lset d).mpr (by omega)
  have hh : (X t ^ k')⁻¹ * nfw X (fun u => if d.lv u = d.lv t then 0 else e' u) * X t ^ k' ∈
      Subgroup.closure (X '' lset d (d.lv t) 0) := by
    have := (lset_normal d X hlv hdeep (d.lv t) 0).conj_mem _ hHmem (X t ^ k')⁻¹
    rwa [inv_inv] at this
  obtain ⟨eH, hHS, hHb, hH⟩ := h0 _ hh
  have h1 : ∀ u v, (fun u => if d.lv u = d.lv t then e' u else 0) u ≠ 0 → delta t k' v ≠ 0 →
      u < v := by
    intro u v hu hv
    have hvt : v = t := by
      by_contra hc
      apply hv
      show (if v = t then k' else 0) = 0
      rw [if_neg hc]
    have hu1 : d.lv u = d.lv t ∧ e' u ≠ 0 := by
      by_cases hc : d.lv u = d.lv t
      · refine ⟨hc, fun h0 => hu ?_⟩
        show (if d.lv u = d.lv t then e' u else 0) = 0
        rw [if_pos hc, h0]
      · exfalso
        apply hu
        show (if d.lv u = d.lv t then e' u else 0) = 0
        rw [if_neg hc]
    have := (mem_lset d).mp (he'S u hu1.2)
    rw [hvt, Fin.lt_def]
    omega
  have h2 : ∀ u v, ((fun u => if d.lv u = d.lv t then e' u else 0) + delta t k') u ≠ 0 →
      eH v ≠ 0 → u < v := by
    intro u v hu hv
    apply hlt
    have hv' := (mem_lset d).mp (hHS v hv)
    have hu' : d.lv u = d.lv t := by
      by_contra hc
      have hut : u ≠ t := fun h => hc (by rw [h])
      apply hu
      simp only [Pi.add_apply, delta, if_neg hc, if_neg hut, add_zero]
    omega
  refine ⟨(fun u => if d.lv u = d.lv t then e' u else 0) + delta t k' + eH, ?_, ?_, ?_⟩
  · intro u hu
    rw [mem_lset]
    by_cases h3 : eH u = 0
    · by_cases hut : u = t
      · right
        rw [hut]
        exact ⟨rfl, by omega⟩
      · have hL : (if d.lv u = d.lv t then e' u else 0) ≠ 0 := by
          intro h0
          apply hu
          simp only [Pi.add_apply, delta, if_neg hut, h3, add_zero, h0]
        by_cases hc : d.lv u = d.lv t
        · rw [if_pos hc] at hL
          have := (mem_lset d).mp (he'S u hL)
          omega
        · rw [if_neg hc] at hL
          exact absurd rfl hL
    · have := (mem_lset d).mp (hHS u h3)
      omega
  · intro u
    show (if d.lv u = d.lv t then e' u else 0) + delta t k' u + eH u < p ^ relOrd p d X u
    by_cases hc : d.lv u = d.lv t
    · have hH0 : eH u = 0 := by
        by_contra hne
        have := (mem_lset d).mp (hHS u hne)
        omega
      by_cases hut : u = t
      · have he0 : e' u = 0 := by
          by_contra hne
          have := (mem_lset d).mp (he'S u hne)
          rw [hut] at this
          omega
        rw [if_pos hc, he0, hH0, hut]
        simpa [delta] using hk'
      · rw [if_pos hc, hH0]
        simpa [delta, hut] using he'b u
    · have hut : u ≠ t := fun h => hc (by rw [h])
      rw [if_neg hc]
      simpa [delta, hut] using hHb u
  · rw [← nfw_mul X _ eH h2, ← nfw_mul X _ (delta t k') h1, nfw_delta, ← hH, hsplit]
    group

/-- Normal forms exist in every tail subgroup. -/
theorem nfp_all [Finite G] (hp : p.Prime) (hG : Nat.card G = p ^ m) (hd : d.Struct)
    (hlv : ∀ t, X t ∈ lcs G (d.lv t))
    (hdeep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {u | w ≤ d.lv u})) :
    ∀ w j, NFP p d X w j := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ u : Fin d.n, d.lv u < M :=
    ⟨Finset.univ.sup d.lv + 1, fun u => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ u))⟩
  have key : ∀ k w, M ≤ w + k → ∀ j, NFP p d X w j := by
    intro k
    induction k with
    | zero =>
      intro w hw j
      exact NFP_empty d X hp.pos j (fun u => lt_of_lt_of_le (hM u) (by omega))
    | succ k ih =>
      intro w hw
      have h0 : NFP p d X w 0 := NFP_zero d X (ih (w + 1) (by omega) d.n)
      intro j
      induction j with
      | zero => exact h0
      | succ j ihj => exact NFP_succ d X hp hG hd hlv hdeep ihj h0
  exact fun w j => key M w (by omega) j

/-- `|G| = p ^ (∑ a)` for the relative orders of a layered generating tuple. -/
theorem card_eq_relOrd [Finite G] (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (hgen : Subgroup.closure (Set.range X) = ⊤) (hlv : ∀ t, X t ∈ lcs G (d.lv t))
    (hdeep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {u | w ≤ d.lv u})) :
    Nat.card G = p ^ (∑ t, relOrd p d X t) := by
  have hprod : ∏ t ∈ (Finset.univ : Finset (Fin d.n)), (fun t => p ^ relOrd p d X t) t =
      p ^ (∑ t, relOrd p d X t) := Finset.prod_pow_eq_pow_sum _ _ _
  have hconj : ∀ t u, d.prec t u →
      X t * X u * (X t)⁻¹ ∈ Subgroup.closure (X '' {u | d.prec t u}) := by
    intro t u htu
    have he : X t * X u * (X t)⁻¹ = ⁅X t, X u⁆ * X u := by
      simp only [commutatorElement_def]
      group
    rw [he]
    refine mul_mem ?_ (Subgroup.subset_closure ⟨u, htu, rfl⟩)
    have h1 := hdeep (d.lv u + 1) (by omega) (commElem_mem_lcs_succ' (X t) (hlv u))
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨u', hu', rfl⟩
    refine ⟨u', ?_, rfl⟩
    have hu'' : d.lv u + 1 ≤ d.lv u' := hu'
    have htu' : d.lv t < d.lv u ∨ (d.lv t = d.lv u ∧ u.val < t.val) := htu
    exact Or.inl (by omega)
  have hle := card_le_of_prec X (fun t => p ^ relOrd p d X t) (fun t => pow_pos hp.pos _) d.prec
    d.prec_irrefl d.prec_asymm d.prec_min (fun t => relOrd_spec d X hG t) hconj Finset.univ
    (fun _ _ _ _ => Finset.mem_univ _)
  have hge := card_ge_of_prec X (fun t => p ^ relOrd p d X t) d.prec d.prec_asymm d.prec_min
    (fun t k hk0 hk => relOrd_not d X hp hG t k hk0 hk) Finset.univ
    (fun _ _ _ _ => Finset.mem_univ _)
  rw [Finset.coe_univ, Set.image_univ, hgen, Subgroup.card_top] at hle hge
  rw [← hprod]
  exact le_antisymm hle hge

/-- Existence of the relation arrays: a layered Sims-type generating tuple of a group of order
`p ^ m` realises Sims data with its relative orders, normal-form power words and commutator
coefficients, and these data are valid and bounded. -/
theorem exists_arrays [Finite G] (hp : p.Prime) (hG : Nat.card G = p ^ m) (hd : d.Struct)
    (hgen : Subgroup.closure (Set.range X) = ⊤)
    (hdf : ∀ t, 1 ≤ d.lv t → X t = ⁅X (d.df t).1, X (d.df t).2⁆)
    (hdeep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {u | w ≤ d.lv u})) :
    ∃ (b : Fin d.n → Fin d.n → ℕ) (c : Fin d.n → Fin d.n → Fin d.n → ℕ),
      ({ d with a := relOrd p d X, b := b, c := c } : SimsData).Valid ∧
      ({ d with a := relOrd p d X, b := b, c := c } : SimsData).Bounded p ∧
      SimsRealizes p ({ d with a := relOrd p d X, b := b, c := c } : SimsData) X := by
  have hlv := lv_mem_lcs d hd X hdf
  have hnf := nfp_all d X hp hG hd hlv hdeep
  have hb : ∀ t, ∃ e : Fin d.n → ℕ, (∀ u, e u ≠ 0 → d.prec t u) ∧
      (∀ u, e u < p ^ relOrd p d X u) ∧ X t ^ (p ^ relOrd p d X t) = nfw X e :=
    fun t => hnf (d.lv t) t.val _ (relOrd_spec d X hG t)
  have hc : ∀ t k, ∃ e : Fin d.n → ℕ, (∀ u, e u ≠ 0 → d.lv t < d.lv u) ∧
      (∀ u, e u < p ^ relOrd p d X u) ∧ ⁅X t, X k⁆ = nfw X e := by
    intro t k
    have hmem : ⁅X t, X k⁆ ∈ Subgroup.closure (X '' lset d (d.lv t) 0) := by
      have h1 := hdeep (d.lv t + 1) (by omega) (commElem_mem_lcs_succ (hlv t) (X k))
      refine Subgroup.closure_mono ?_ h1
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, Or.inl hu, rfl⟩
    obtain ⟨e, he1, he2, he3⟩ := hnf _ _ _ hmem
    refine ⟨e, fun u hu => ?_, he2, he3⟩
    have := (mem_lset d).mp (he1 u hu)
    omega
  choose b hb using hb
  choose c hc using hc
  refine ⟨b, c, ?_, ⟨fun t u => (hb t).2.1 u, fun t k u => (hc t k).2.1 u⟩, ?_⟩
  · exact ⟨⟨hd.mono, hd.s_le, hd.core, hd.df_lv, hd.df_core, hd.df_one⟩,
      fun t u h => (hb t).1 u h, fun t k u h => (hc t k).1 u h⟩
  · exact ⟨card_eq_relOrd d X hp hG hgen hlv hdeep, hgen, hdf, fun t => (hb t).2.2,
      fun t k _ _ _ => (hc t k).2.2, fun t k _ _ => (hc t k).2.2, fun t k _ _ => (hc t k).2.2⟩

end Layers


section Frattini

/-! The Frattini argument for an abelian section, and the Frattini subgroups `layK p G w` of the
layers: `layK p G 0 = Φ(G) = G^p γ_2` and `layK p G w = γ_{w+2} γ_{w+1}^p` (0-based weights), so
that `lcs G w / layK p G w = L_{w+1} / p L_{w+1}`. -/

variable {G : Type u} [Group G]

/-- The `p`-th powers of the image of `A` in `G ⧸ B`; a subgroup when the image is abelian. -/
def powImg (A B : Subgroup G) [B.Normal] (p : ℕ)
    (hc : ∀ x ∈ A, ∀ y ∈ A, QuotientGroup.mk' B x * QuotientGroup.mk' B y =
      QuotientGroup.mk' B y * QuotientGroup.mk' B x) : Subgroup (G ⧸ B) where
  carrier := {z | ∃ a ∈ A, z = QuotientGroup.mk' B a ^ p}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    show ∃ c ∈ A, QuotientGroup.mk' B a ^ p * QuotientGroup.mk' B b ^ p =
      QuotientGroup.mk' B c ^ p
    refine ⟨a * b, A.mul_mem ha hb, ?_⟩
    rw [map_mul, Commute.mul_pow (hc a ha b hb) p]
  one_mem' := by
    show ∃ c ∈ A, (1 : G ⧸ B) = QuotientGroup.mk' B c ^ p
    exact ⟨1, A.one_mem, by rw [map_one, one_pow]⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    show ∃ c ∈ A, (QuotientGroup.mk' B a ^ p)⁻¹ = QuotientGroup.mk' B c ^ p
    exact ⟨a⁻¹, A.inv_mem ha, by rw [map_inv, inv_pow]⟩

/-- The Frattini argument for an abelian section `A / B` of a finite `p`-group: if
`A ≤ B A^p`, then `A ≤ B`. -/
theorem frat_section [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (A B : Subgroup G) [B.Normal] (hAB : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ B)
    (h : A ≤ B ⊔ Subgroup.closure (Set.range (fun g : A => (g : G) ^ p))) : A ≤ B := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (G ⧸ B) := Finite.of_surjective _ (QuotientGroup.mk'_surjective B)
  have hker : ∀ g : G, QuotientGroup.mk' B g = 1 ↔ g ∈ B := fun g => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have hc : ∀ x ∈ A, ∀ y ∈ A, QuotientGroup.mk' B x * QuotientGroup.mk' B y =
      QuotientGroup.mk' B y * QuotientGroup.mk' B x := by
    intro x hx y hy
    have h1 : QuotientGroup.mk' B ⁅x, y⁆ = 1 := (hker _).mpr (hAB x hx y hy)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hle : A ≤ (powImg A B p hc).comap (QuotientGroup.mk' B) := by
    refine h.trans (sup_le ?_ ?_)
    · intro b hb
      show ∃ a' ∈ A, QuotientGroup.mk' B b = QuotientGroup.mk' B a' ^ p
      exact ⟨1, A.one_mem, by rw [map_one, one_pow, (hker b).mpr hb]⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show ∃ a' ∈ A, QuotientGroup.mk' B ((g : G) ^ p) = QuotientGroup.mk' B a' ^ p
      exact ⟨g, g.2, by rw [map_pow]⟩
  have hAQ : ∀ a ∈ A, ∃ a' ∈ A, QuotientGroup.mk' B a = QuotientGroup.mk' B a' ^ p :=
    fun a ha => hle ha
  have hsurj : Function.Surjective (fun z : A.map (QuotientGroup.mk' B) =>
      (⟨(z : G ⧸ B) ^ p, pow_mem z.2 p⟩ : A.map (QuotientGroup.mk' B))) := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨a', ha', he⟩ := hAQ a ha
    exact ⟨⟨QuotientGroup.mk' B a', Subgroup.mem_map_of_mem _ ha'⟩, Subtype.ext he.symm⟩
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  intro a ha
  rw [← hker]
  by_contra hne
  obtain ⟨k, hk⟩ := (IsPGroup.of_card hG).to_quotient B (QuotientGroup.mk' B a)
  have hex : ∃ k, QuotientGroup.mk' B a ^ p ^ k = 1 := ⟨k, hk⟩
  obtain ⟨k0, hspec, hmin⟩ : ∃ k0, QuotientGroup.mk' B a ^ p ^ k0 = 1 ∧
      ∀ j < k0, QuotientGroup.mk' B a ^ p ^ j ≠ 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hk0 : k0 ≠ 0 := by
    rintro rfl
    rw [pow_zero, pow_one] at hspec
    exact hne hspec
  have hz : (QuotientGroup.mk' B a ^ p ^ (k0 - 1)) ^ p = 1 := by
    rw [← pow_mul, ← pow_succ, show k0 - 1 + 1 = k0 by omega, hspec]
  have hzA : QuotientGroup.mk' B a ^ p ^ (k0 - 1) ∈ A.map (QuotientGroup.mk' B) :=
    pow_mem (Subgroup.mem_map_of_mem _ ha) _
  have heq : (⟨_, hzA⟩ : A.map (QuotientGroup.mk' B)) = ⟨1, one_mem _⟩ := by
    apply hinj
    apply Subtype.ext
    show (QuotientGroup.mk' B a ^ p ^ (k0 - 1)) ^ p = (1 : G ⧸ B) ^ p
    rw [hz, one_pow]
  exact hmin (k0 - 1) (by omega) (congrArg Subtype.val heq)

/-- The Frattini subgroup of the layer of 0-based weight `w`. -/
def layK (p : ℕ) (G : Type u) [Group G] : ℕ → Subgroup G
  | 0 => pPhi p G
  | w + 1 => lcs G (w + 2) ⊔ Subgroup.closure (Set.range (fun g : lcs G (w + 1) => (g : G) ^ p))

lemma layK_one (p : ℕ) : layK p G 1 = pN p G := rfl

lemma lcs_succ_le_layK (p : ℕ) : ∀ w, lcs G (w + 1) ≤ layK p G w
  | 0 => by
    show lcs G 1 ≤ pPhi p G
    rw [← commutator_eq_lcs_one]
    exact le_sup_right
  | _ + 1 => le_sup_left

lemma layK_le_lcs (p : ℕ) (w : ℕ) : layK p G (w + 1) ≤ lcs G (w + 1) := by
  show lcs G (w + 2) ⊔ Subgroup.closure (Set.range (fun g : lcs G (w + 1) => (g : G) ^ p)) ≤
    lcs G (w + 1)
  refine sup_le (lcs_antitone (by omega)) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  exact pow_mem g.2 p

lemma pow_mem_layK (p : ℕ) : ∀ (w : ℕ) (x : G), x ∈ lcs G w → x ^ p ∈ layK p G w
  | 0, x, _ => pow_mem_pPhi p x
  | w + 1, x, hx => Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩)

lemma layK_normal_sup (p : ℕ) (w : ℕ) (T : Set G) (hT : T ⊆ lcs G w) :
    (Subgroup.closure T ⊔ layK p G w).Normal := by
  rcases w with _ | w
  · exact normal_of_lcs_one_le ((lcs_succ_le_layK p 0).trans le_sup_right)
  · exact normal_of_sandwich (n := w + 1) ((lcs_succ_le_layK p (w + 1)).trans le_sup_right)
      (sup_le ((Subgroup.closure_le _).mpr hT) (layK_le_lcs p w))

/-- The Frattini argument for a layer. -/
lemma frat_layer [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) (w : ℕ)
    (T : Set G) (hT : T ⊆ lcs G (w + 1))
    (h : lcs G (w + 1) ≤ Subgroup.closure T ⊔ layK p G (w + 1)) :
    lcs G (w + 1) ≤ Subgroup.closure T ⊔ lcs G (w + 2) := by
  have hN : (Subgroup.closure T ⊔ lcs G (w + 2)).Normal :=
    normal_of_sandwich (n := w + 1) le_sup_right
      (sup_le ((Subgroup.closure_le _).mpr hT) (lcs_antitone (by omega)))
  refine frat_section hp hG (lcs G (w + 1)) _ ?_ ?_
  · intro x hx y hy
    have h1 := commElem_mem_lcs_add hx hy
    exact Subgroup.mem_sup_right
      (lcs_antitone (D := G) (show w + 2 ≤ w + 1 + (w + 1) + 1 by omega) h1)
  · rw [sup_assoc]
    exact h

/-- `|⟨x_0, ..., x_{j-1}⟩ M| ≤ p ^ j |M|` when each `⟨x_0, ..., x_{j-1}⟩ M` is normal and
`x_j ^ p ∈ M`. -/
lemma card_closure_sup_le_of [Finite G] {p : ℕ} (hp : 0 < p) (M : Subgroup G) (x : ℕ → G)
    (hN : ∀ j, (Subgroup.closure (x '' Set.Iio j) ⊔ M).Normal) (hMp : ∀ j, x j ^ p ∈ M) :
    ∀ j, Nat.card (Subgroup.closure (x '' Set.Iio j) ⊔ M : Subgroup G) ≤ p ^ j * Nat.card M := by
  intro j
  induction j with
  | zero =>
    have hle : Subgroup.closure (x '' Set.Iio 0) ⊔ M ≤ M := by
      refine sup_le ?_ le_rfl
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (Set.mem_Iio.mp hi) (Nat.not_lt_zero i)
    rw [pow_zero, one_mul]
    exact Subgroup.card_le_of_le hle
  | succ j ih =>
    have := hN j
    have hle : Subgroup.closure (x '' Set.Iio (j + 1)) ⊔ M ≤
        (Subgroup.closure (x '' Set.Iio j) ⊔ M) ⊔ Subgroup.zpowers (x j) := by
      refine sup_le ?_ (le_sup_right.trans le_sup_left)
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < j + 1 := Set.mem_Iio.mp hi
      by_cases hij : i < j
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.subset_closure ⟨i, Set.mem_Iio.mpr hij, rfl⟩))
      · rw [show i = j by omega]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (x j))
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_sup_zpowers_le (K := Subgroup.closure (x '' Set.Iio j) ⊔ M) hp
      (Subgroup.mem_sup_right (hMp j))
    have h3 : p * Nat.card (Subgroup.closure (x '' Set.Iio j) ⊔ M : Subgroup G) ≤
        p * (p ^ j * Nat.card M) := Nat.mul_le_mul le_rfl ih
    have e : p * (p ^ j * Nat.card M) = p ^ (j + 1) * Nat.card M := by
      rw [pow_succ]
      ring
    rw [← e]
    exact h1.trans (h2.trans h3)

end Frattini

section Greedy

/-! Greedy selection of a minimal generating sublist modulo a subgroup `K`, in the given order:
`c j` is kept iff it is not in the subgroup generated by the kept earlier entries and `K`. -/

variable {G : Type u} [Group G]

open Classical in
/-- The indices `< j` kept by the greedy selection. -/
noncomputable def gsel (c : ℕ → G) (K : Subgroup G) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => if c j ∈ Subgroup.closure (c '' (gsel c K j : Set ℕ)) ⊔ K then gsel c K j
      else insert j (gsel c K j)

lemma gsel_cases (c : ℕ → G) (K : Subgroup G) (j : ℕ) :
    (gsel c K (j + 1) = gsel c K j ∧
      c j ∈ Subgroup.closure (c '' (gsel c K j : Set ℕ)) ⊔ K) ∨
    (gsel c K (j + 1) = insert j (gsel c K j) ∧
      c j ∉ Subgroup.closure (c '' (gsel c K j : Set ℕ)) ⊔ K) := by
  by_cases h : c j ∈ Subgroup.closure (c '' (gsel c K j : Set ℕ)) ⊔ K
  · left
    refine ⟨?_, h⟩
    simp only [gsel, if_pos h]
  · right
    refine ⟨?_, h⟩
    simp only [gsel, if_neg h]

lemma gsel_sub (c : ℕ → G) (K : Subgroup G) : ∀ j, ∀ i ∈ gsel c K j, i < j
  | 0, i, hi => by simp [gsel] at hi
  | j + 1, i, hi => by
    rcases gsel_cases c K j with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at hi
      exact Nat.lt_succ_of_lt (gsel_sub c K j i hi)
    · rw [h, Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (gsel_sub c K j i hi)

lemma gsel_mem_iff (c : ℕ → G) (K : Subgroup G) :
    ∀ d j i, i < j → (i ∈ gsel c K (j + d) ↔ i ∈ gsel c K j)
  | 0, _, _, _ => Iff.rfl
  | d + 1, j, i, hij => by
    rw [← gsel_mem_iff c K d j i hij, show j + (d + 1) = j + d + 1 by omega]
    rcases gsel_cases c K (j + d) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, Finset.mem_insert]
      constructor
      · rintro (h' | h')
        · exact absurd h' (by omega)
        · exact h'
      · exact Or.inr

lemma gsel_span (c : ℕ → G) (K : Subgroup G) :
    ∀ j, ∀ i < j, c i ∈ Subgroup.closure (c '' (gsel c K j : Set ℕ)) ⊔ K
  | 0, i, hi => absurd hi (Nat.not_lt_zero i)
  | j + 1, i, hi => by
    have hmono : Subgroup.closure (c '' (gsel c K j : Set ℕ)) ⊔ K ≤
        Subgroup.closure (c '' (gsel c K (j + 1) : Set ℕ)) ⊔ K := by
      refine sup_le_sup_right (Subgroup.closure_mono (Set.image_mono ?_)) K
      intro x hx
      rcases gsel_cases c K j with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        exact hx
      · rw [h, Finset.coe_insert]
        exact Set.mem_insert_of_mem _ hx
    by_cases hij : i < j
    · exact hmono (gsel_span c K j i hij)
    · have hij' : i = j := by omega
      subst hij'
      rcases gsel_cases c K i with ⟨-, h'⟩ | ⟨h, -⟩
      · exact hmono h'
      · refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, ?_, rfl⟩)
        rw [h, Finset.coe_insert]
        exact Set.mem_insert _ _

lemma gsel_indep (c : ℕ → G) (K : Subgroup G) {j i : ℕ} (hi : i ∈ gsel c K j) :
    c i ∉ Subgroup.closure (c '' (gsel c K i : Set ℕ)) ⊔ K := by
  have hij := gsel_sub c K j i hi
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
  have h1 : i ∈ gsel c K (i + 1) :=
    (gsel_mem_iff c K d (i + 1) i (Nat.lt_succ_self i)).mp hi
  rcases gsel_cases c K i with ⟨h, -⟩ | ⟨-, h'⟩
  · rw [h] at h1
    exact absurd (gsel_sub c K i i h1) (lt_irrefl i)
  · exact h'

/-- The `i`-th element of `S` in increasing order (junk `0` out of range). -/
noncomputable def genum (S : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < S.card then S.orderEmbOfFin rfl ⟨i, h⟩ else 0

lemma genum_mem (S : Finset ℕ) {i : ℕ} (h : i < S.card) : genum S i ∈ S := by
  unfold genum
  rw [dif_pos h]
  exact Finset.orderEmbOfFin_mem S rfl _

lemma genum_lt (S : Finset ℕ) {i j : ℕ} (hij : i < j) (hj : j < S.card) :
    genum S i < genum S j := by
  unfold genum
  rw [dif_pos (lt_trans hij hj), dif_pos hj]
  exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)

lemma genum_le (S : Finset ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < S.card) :
    genum S i ≤ genum S j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact (genum_lt S h hj).le
  · have hij' : i = j := by omega
    subst hij'
    exact le_rfl

lemma genum_inj (S : Finset ℕ) {i j : ℕ} (hi : i < S.card) (hj : j < S.card)
    (h : genum S i = genum S j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd h (genum_lt S h' hj).ne
  · exact h'
  · exact absurd h (genum_lt S h' hi).ne'

lemma genum_surj (S : Finset ℕ) {x : ℕ} (hx : x ∈ S) : ∃ i < S.card, genum S i = x := by
  have hr : x ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  obtain ⟨⟨i, hi⟩, rfl⟩ := hr
  refine ⟨i, hi, ?_⟩
  unfold genum
  rw [dif_pos hi]

/-- A layer: `r` entries `x 0, ..., x (r - 1)` (junk `1` beyond), with the parent index `par` and
core index `cor` of each entry (for weights `≥ 2`). -/
structure SLay (G : Type u) where
  r : ℕ
  x : ℕ → G
  par : ℕ → ℕ
  cor : ℕ → ℕ

/-- The greedy layer selected from the candidates `c 0, ..., c (N - 1)` modulo `K`. -/
noncomputable def gLay (c : ℕ → G) (K : Subgroup G) (N : ℕ) (pa co : ℕ → ℕ) : SLay G where
  r := (gsel c K N).card
  x := fun i => if i < (gsel c K N).card then c (genum (gsel c K N) i) else 1
  par := fun i => pa (genum (gsel c K N) i)
  cor := fun i => co (genum (gsel c K N) i)

variable (c : ℕ → G) (K : Subgroup G) (N : ℕ) (pa co : ℕ → ℕ)

lemma gLay_x {i : ℕ} (hi : i < (gsel c K N).card) :
    (gLay c K N pa co).x i = c (genum (gsel c K N) i) := if_pos hi

lemma gLay_x_cases (i : ℕ) :
    (gLay c K N pa co).x i = c (genum (gsel c K N) i) ∨ (gLay c K N pa co).x i = 1 := by
  by_cases hi : i < (gsel c K N).card
  · exact Or.inl (if_pos hi)
  · exact Or.inr (if_neg hi)

lemma gsel_genum_earlier {i i' : ℕ} (hi : i < (gsel c K N).card) (hi' : i' < i) :
    genum (gsel c K N) i' ∈ gsel c K (genum (gsel c K N) i) := by
  have h1 := genum_lt (gsel c K N) hi' hi
  have h2 := gsel_sub c K N _ (genum_mem _ hi)
  have h3 := genum_mem (gsel c K N) (lt_trans hi' hi)
  have h4 := gsel_mem_iff c K (N - genum (gsel c K N) i) (genum (gsel c K N) i) _ h1
  rw [show genum (gsel c K N) i + (N - genum (gsel c K N) i) = N by omega] at h4
  exact h4.mp h3

/-- Independence of a greedy layer modulo `K`. -/
lemma gLay_indep {i : ℕ} (hi : i < (gLay c K N pa co).r) :
    (gLay c K N pa co).x i ∉ Subgroup.closure ((gLay c K N pa co).x '' Set.Iio i) ⊔ K := by
  intro hmem
  have hi' : i < (gsel c K N).card := hi
  rw [gLay_x c K N pa co hi'] at hmem
  apply gsel_indep c K (genum_mem (gsel c K N) hi')
  refine (sup_le_sup_right (Subgroup.closure_mono ?_) K) hmem
  rintro _ ⟨i', hi'', rfl⟩
  have hi''' : i' < i := hi''
  refine ⟨genum (gsel c K N) i', gsel_genum_earlier c K N hi' hi''', ?_⟩
  exact (gLay_x c K N pa co (lt_trans hi''' hi')).symm

/-- Prefix spanning of a greedy layer: the first `J` candidates are generated modulo `K` by the
kept entries among them. -/
lemma gLay_span {J : ℕ} (hJ : J ≤ N) {j : ℕ} (hj : j < J) :
    c j ∈ Subgroup.closure ((gLay c K N pa co).x ''
      {i | i < (gsel c K N).card ∧ genum (gsel c K N) i < J}) ⊔ K := by
  refine (sup_le_sup_right (Subgroup.closure_mono ?_) K) (gsel_span c K J j hj)
  rintro _ ⟨y, hy, rfl⟩
  have hyJ : y < J := gsel_sub c K J y hy
  have hyS : y ∈ gsel c K N := by
    have h1 := gsel_mem_iff c K (N - J) J y hyJ
    rw [show J + (N - J) = N by omega] at h1
    exact h1.mpr hy
  obtain ⟨i, hi, rfl⟩ := genum_surj _ hyS
  exact ⟨i, ⟨hi, hyJ⟩, gLay_x c K N pa co hi⟩

lemma gLay_span_all {j : ℕ} (hj : j < N) :
    c j ∈ Subgroup.closure ((gLay c K N pa co).x '' Set.Iio (gLay c K N pa co).r) ⊔ K := by
  refine (sup_le_sup_right (Subgroup.closure_mono ?_) K) (gLay_span c K N pa co le_rfl hj)
  rintro _ ⟨i, ⟨hi, -⟩, rfl⟩
  exact ⟨i, hi, rfl⟩

end Greedy

section TheoremL

/-! Theorem L (BNV Prop 3.8 / LQ Lemma 2.2, eq (34)) for a core `u_0, ..., u_{s-1}`: with
`E_1 = {[u_a, u_b] : a < b < s}` and `E_{w+1} = {[y, u_b] : y ∈ ⟨E_w⟩, b < s}`, each `γ_{w+1}` is
generated by `E_w` modulo `γ_{w+2}`, provided `γ_2 ≤ ⟨E_1⟩ γ_3`. -/

variable {G : Type u} [Group G]

/-- The candidate sets of Theorem L. -/
def lieE (s : ℕ) (u : ℕ → G) : ℕ → Set G
  | 0 => ∅
  | 1 => (fun ab : ℕ × ℕ => ⁅u ab.1, u ab.2⁆) '' {ab | ab.1 < ab.2 ∧ ab.2 < s}
  | w + 2 => {x | ∃ y ∈ Subgroup.closure (lieE s u (w + 1)), ∃ b < s, x = ⁅y, u b⁆}

lemma lieE_sub (s : ℕ) (u : ℕ → G) : ∀ w, lieE s u (w + 1) ⊆ (lcs G (w + 1) : Set G)
  | 0 => by
    rintro _ ⟨ab, -, rfl⟩
    exact commElem_mem_lcs_one _ _
  | w + 1 => by
    rintro _ ⟨y, hy, b, -, rfl⟩
    have hy' : y ∈ lcs G (w + 1) := (Subgroup.closure_le _).mpr (lieE_sub s u w) hy
    exact commElem_mem_lcs_succ hy' _

theorem theoremL (s : ℕ) (u : ℕ → G) (H1 : Set G)
    (hL0 : Subgroup.closure H1 ⊔ lcs G 1 = ⊤)
    (hcore : lcs G 1 ≤ Subgroup.closure (lieE s u 1) ⊔ lcs G 2) :
    ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (lieE s u w) ⊔ lcs G (w + 1) := by
  refine lie_lemma s u H1 {ab | ab.1 < ab.2 ∧ ab.2 < s} (lieE s u) (fun ab hab => hab) rfl
    ?_ hL0 ?_ ?_ ?_
  · intro w hw x hx
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    exact hx
  · intro x _ y _
    exact hcore (commElem_mem_lcs_one x y)
  · intro ab hab k hk
    have hk' : k < s := lt_of_le_of_lt hk hab.2
    refine Subgroup.mem_sup_left (Subgroup.subset_closure ?_)
    show ⁅⁅u ab.1, u ab.2⁆, u k⁆ ∈ lieE s u (0 + 2)
    exact ⟨⁅u ab.1, u ab.2⁆, Subgroup.subset_closure ⟨ab, hab, rfl⟩, k, hk', rfl⟩
  · intro w hw x hx k hk
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    refine Subgroup.mem_sup_left (Subgroup.subset_closure ?_)
    show ⁅x, u k⁆ ∈ lieE s u (w' + 2)
    exact ⟨x, Subgroup.subset_closure hx, k, hk, rfl⟩

end TheoremL

section Layers2

/-! The layers of the Sims generating set. Layer `0` (weight 1) is the core `u_0, ..., u_{s-1}`
followed by a greedy completion to a basis modulo `Φ(G)`; layer `1` (weight 2) is the greedy
selection modulo `γ_3 γ_2^p` from the core commutators `[u_a, u_b]` (`a < b`), listed in the
order `b`-major (blocks by `b`, as in (23)/(24)); layer `w + 1 ≥ 2` is the greedy selection
modulo `γ_{w+3} γ_{w+2}^p` from the commutators `[x, u_b]` of the layer-`w` entries `x` with the
core (index `a * s + b`). -/

variable {G : Type u} [Group G]

/-- Parent index of candidate `j` of layer `w + 1`. -/
def cPar (s w j : ℕ) : ℕ := if w = 0 then j % s else j / s

/-- Core index of candidate `j` of layer `w + 1`. -/
def cCor (s w j : ℕ) : ℕ := if w = 0 then j / s else j % s

/-- Candidate `j` of layer `w + 1` built from layer `w` (junk `1` for the pairs `a ≥ b` of
layer 1, and for the pairs `(a, b)` of layer 2 with `co(a) < b`, i.e. `a ≤ d_{b-1}` in the
paper's 1-based indexing: the weight-3 candidates are `[g_{2,a}, g_{1,b}]` with `d_{b-1} < a`). -/
def cVal (s : ℕ) (u : ℕ → G) (w : ℕ) (L : SLay G) (j : ℕ) : G :=
  if (w = 0 ∧ ¬ cPar s w j < cCor s w j) ∨ (w = 1 ∧ L.cor (cPar s w j) < cCor s w j) then 1
  else ⁅L.x (cPar s w j), u (cCor s w j)⁆

/-- Number of candidates of layer `w + 1`. -/
def cN (s w : ℕ) (L : SLay G) : ℕ := if w = 0 then s * s else L.r * s

lemma cPar_zero {s j : ℕ} : cPar s 0 j = j % s := if_pos rfl
lemma cCor_zero {s j : ℕ} : cCor s 0 j = j / s := if_pos rfl
lemma cN_zero {s : ℕ} {L : SLay G} : cN s 0 L = s * s := if_pos rfl
lemma cPar_ne {s w j : ℕ} (hw : w ≠ 0) : cPar s w j = j / s := if_neg hw
lemma cCor_ne {s w j : ℕ} (hw : w ≠ 0) : cCor s w j = j % s := if_neg hw
lemma cN_ne {s w : ℕ} {L : SLay G} (hw : w ≠ 0) : cN s w L = L.r * s := if_neg hw

lemma cVal_succ (s : ℕ) (u : ℕ → G) (w : ℕ) (L : SLay G) (j : ℕ)
    (h : ¬ (w = 0 ∧ L.cor (j / s) < j % s)) :
    cVal s u (w + 1) L j = ⁅L.x (j / s), u (j % s)⁆ := by
  unfold cVal
  have hn : ¬ ((w + 1 = 0 ∧ ¬ cPar s (w + 1) j < cCor s (w + 1) j) ∨
      (w + 1 = 1 ∧ L.cor (cPar s (w + 1) j) < cCor s (w + 1) j)) := by
    rintro (h' | h')
    · exact absurd h'.1 (by omega)
    · rw [cPar_ne (show w + 1 ≠ 0 by omega), cCor_ne (show w + 1 ≠ 0 by omega)] at h'
      obtain ⟨h1', h2'⟩ := h'
      exact h ⟨by omega, h2'⟩
  rw [if_neg hn, cPar_ne (show w + 1 ≠ 0 by omega), cCor_ne (show w + 1 ≠ 0 by omega)]

lemma cVal_zero_of_lt (s : ℕ) (u : ℕ → G) (L : SLay G) {j : ℕ} (h : j % s < j / s) :
    cVal s u 0 L j = ⁅L.x (j % s), u (j / s)⁆ := by
  unfold cVal
  have hn : ¬ (((0 : ℕ) = 0 ∧ ¬ cPar s 0 j < cCor s 0 j) ∨
      ((0 : ℕ) = 1 ∧ L.cor (cPar s 0 j) < cCor s 0 j)) := by
    rintro (h' | h')
    · exact h'.2 (by rw [cPar_zero, cCor_zero]; exact h)
    · exact Nat.zero_ne_one h'.1
  rw [if_neg hn, cPar_zero, cCor_zero]

lemma slot_lt {s A a b : ℕ} (ha : a < A) (hb : b < s) : a * s + b < A * s :=
  lt_of_lt_of_le (Nat.add_lt_add_left hb _)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ha)

lemma slot_div {s a b : ℕ} (hb : b < s) : (a * s + b) / s = a := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < s), Nat.div_eq_of_lt hb, zero_add]

lemma slot_mod {s a b : ℕ} (hb : b < s) : (a * s + b) % s = b := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- The genuine form of the entries of a candidate-built greedy layer. -/
lemma gLay_cVal_gen (s : ℕ) (u : ℕ → G) (hs : 0 < s) (w : ℕ) (L : SLay G)
    (hr : w = 0 → s ≤ L.r) (K : Subgroup G) {i : ℕ}
    (hi : i < (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).r) :
    (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).par i < L.r ∧
    (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).cor i < s ∧
    (w = 0 → (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).par i <
      (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).cor i) ∧
    (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).x i =
      ⁅L.x ((gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).par i),
        u ((gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).cor i)⁆ := by
  have hind := gLay_indep (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w) hi
  have hi' : i < (gsel (cVal s u w L) K (cN s w L)).card := hi
  have hj := gsel_sub (cVal s u w L) K (cN s w L) _ (genum_mem _ hi')
  have hx := gLay_x (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w) hi'
  have hne : cVal s u w L (genum (gsel (cVal s u w L) K (cN s w L)) i) ≠ 1 := by
    intro h1
    apply hind
    rw [hx, h1]
    exact one_mem _
  have e1 : (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).par i =
      cPar s w (genum (gsel (cVal s u w L) K (cN s w L)) i) := rfl
  have e2 : (gLay (cVal s u w L) K (cN s w L) (cPar s w) (cCor s w)).cor i =
      cCor s w (genum (gsel (cVal s u w L) K (cN s w L)) i) := rfl
  rw [e1, e2, hx]
  generalize genum (gsel (cVal s u w L) K (cN s w L)) i = j at hj hne ⊢
  have hcv2 : ¬ ((w = 0 ∧ ¬ cPar s w j < cCor s w j) ∨
      (w = 1 ∧ L.cor (cPar s w j) < cCor s w j)) := by
    intro hc
    apply hne
    unfold cVal
    rw [if_pos hc]
  have hcv : ¬ (w = 0 ∧ ¬ cPar s w j < cCor s w j) := fun hc => hcv2 (Or.inl hc)
  have hval : cVal s u w L j = ⁅L.x (cPar s w j), u (cCor s w j)⁆ := by
    unfold cVal
    rw [if_neg hcv2]
  refine ⟨?_, ?_, ?_, hval⟩
  · by_cases hw : w = 0
    · subst hw
      rw [cPar_zero]
      have h1 : j % s < s := Nat.mod_lt _ hs
      have h2 := hr rfl
      omega
    · rw [cN_ne hw] at hj
      rw [cPar_ne hw]
      exact (Nat.div_lt_iff_lt_mul hs).mpr hj
  · by_cases hw : w = 0
    · subst hw
      rw [cN_zero] at hj
      rw [cCor_zero]
      exact (Nat.div_lt_iff_lt_mul hs).mpr hj
    · rw [cCor_ne hw]
      exact Nat.mod_lt _ hs
  · intro hw
    by_contra hc
    exact hcv ⟨hw, hc⟩

/-- The weight-3 index restriction of a candidate-built greedy layer from layer `1`. -/
lemma gLay_cVal_w3 (s : ℕ) (u : ℕ → G) (L : SLay G) (K : Subgroup G) {i : ℕ}
    (hi : i < (gLay (cVal s u 1 L) K (cN s 1 L) (cPar s 1) (cCor s 1)).r) :
    ¬ L.cor ((gLay (cVal s u 1 L) K (cN s 1 L) (cPar s 1) (cCor s 1)).par i) <
      (gLay (cVal s u 1 L) K (cN s 1 L) (cPar s 1) (cCor s 1)).cor i := by
  have hind := gLay_indep (cVal s u 1 L) K (cN s 1 L) (cPar s 1) (cCor s 1) hi
  have hi' : i < (gsel (cVal s u 1 L) K (cN s 1 L)).card := hi
  have hx := gLay_x (cVal s u 1 L) K (cN s 1 L) (cPar s 1) (cCor s 1) hi'
  intro hlt
  apply hind
  rw [hx]
  have hc : ((1 : ℕ) = 0 ∧ ¬ cPar s 1 (genum (gsel (cVal s u 1 L) K (cN s 1 L)) i) <
      cCor s 1 (genum (gsel (cVal s u 1 L) K (cN s 1 L)) i)) ∨
      ((1 : ℕ) = 1 ∧ L.cor (cPar s 1 (genum (gsel (cVal s u 1 L) K (cN s 1 L)) i)) <
        cCor s 1 (genum (gsel (cVal s u 1 L) K (cN s 1 L)) i)) := Or.inr ⟨rfl, hlt⟩
  have h1 : cVal s u 1 L (genum (gsel (cVal s u 1 L) K (cN s 1 L)) i) = 1 := if_pos hc
  rw [h1]
  exact one_mem _

/-- Modulo `γ_4`, `⁅g ^ n, y⁆ = ⁅g, y⁆ ^ n` for `g ∈ γ_2`. -/
lemma commElem_pow_left_mem3 (g y : G) (hg : g ∈ lcs G 1) (n : ℕ) :
    ⁅g ^ n, y⁆ * (⁅g, y⁆ ^ n)⁻¹ ∈ lcs G 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ⁅g, ⁅g ^ n, y⁆⁆ ∈ lcs G 3 :=
      lcs_antitone (show 3 ≤ 1 + (1 + 1) + 1 by omega)
        (commElem_mem_lcs_add hg (commElem_mem_lcs_succ (pow_mem hg n) y))
    have e : ⁅g ^ (n + 1), y⁆ * (⁅g, y⁆ ^ (n + 1))⁻¹ =
        ⁅g, ⁅g ^ n, y⁆⁆ * (⁅g ^ n, y⁆ * (⁅g, y⁆ ^ n)⁻¹) := by
      rw [pow_succ' g n, commElem_mul_left, pow_succ]
      group
    rw [e]
    exact Subgroup.mul_mem _ hc ih

/-- `⁅K_1, G⁆ ≤ K_2` for the Frattini subgroups `K_1 = γ_3 γ_2^p`, `K_2 = γ_4 γ_3^p`. -/
lemma comm_layK_one (p : ℕ) (z : G) (hz : z ∈ layK p G 1) (g : G) : ⁅z, g⁆ ∈ layK p G 2 := by
  haveI : (layK p G 2).Normal :=
    normal_of_sandwich (n := 2) (lcs_succ_le_layK p 2) (layK_le_lcs p 1)
  have hle : layK p G 1 ≤ zn (layK p G 2) g := by
    show lcs G 2 ⊔ Subgroup.closure (Set.range (fun y : lcs G 1 => (y : G) ^ p)) ≤ _
    refine sup_le ?_ ?_
    · intro x hx
      exact mem_zn.mpr (lcs_succ_le_layK p 2 (commElem_mem_lcs_succ' g hx))
    · rw [Subgroup.closure_le]
      rintro _ ⟨y, rfl⟩
      apply mem_zn.mpr
      apply commElem_mem_symm
      have h1 := commElem_pow_left_mem3 (y : G) g y.2 p
      have h2 : ⁅(y : G), g⁆ ^ p ∈ layK p G 2 :=
        pow_mem_layK p 2 _ (commElem_mem_lcs_succ y.2 g)
      have e : ⁅(y : G) ^ p, g⁆ = ⁅(y : G) ^ p, g⁆ * (⁅(y : G), g⁆ ^ p)⁻¹ * ⁅(y : G), g⁆ ^ p := by
        group
      rw [e]
      exact Subgroup.mul_mem _ (lcs_succ_le_layK p 2 h1) h2
  exact commElem_mem_symm (mem_zn.mp (hle hz))

/-- The layers after layer `0`. -/
noncomputable def sLay (p s : ℕ) (u : ℕ → G) (L0 : SLay G) : ℕ → SLay G
  | 0 => L0
  | w + 1 => gLay (cVal s u w (sLay p s u L0 w)) (layK p G (w + 1)) (cN s w (sLay p s u L0 w))
      (cPar s w) (cCor s w)

variable (p s : ℕ) (u : ℕ → G) (L0 : SLay G)

lemma sLay_zero : sLay p s u L0 0 = L0 := rfl

lemma sLay_succ (w : ℕ) :
    sLay p s u L0 (w + 1) = gLay (cVal s u w (sLay p s u L0 w)) (layK p G (w + 1))
      (cN s w (sLay p s u L0 w)) (cPar s w) (cCor s w) := rfl

lemma sLay_one :
    sLay p s u L0 1 = gLay (cVal s u 0 L0) (layK p G 1) (cN s 0 L0) (cPar s 0) (cCor s 0) := rfl

lemma sLay_mem : ∀ w i, (sLay p s u L0 w).x i ∈ lcs G w
  | 0, i => by
    rw [lcs_zero]
    exact Subgroup.mem_top _
  | w + 1, i => by
    rw [sLay_succ]
    rcases gLay_x_cases (cVal s u w (sLay p s u L0 w)) (layK p G (w + 1))
        (cN s w (sLay p s u L0 w)) (cPar s w) (cCor s w) i with h | h
    · rw [h]
      unfold cVal
      split_ifs
      · exact one_mem _
      · exact commElem_mem_lcs_succ (sLay_mem w _) _
    · rw [h]
      exact one_mem _

lemma sLay_indep (w : ℕ) {i : ℕ} (hi : i < (sLay p s u L0 (w + 1)).r) :
    (sLay p s u L0 (w + 1)).x i ∉
      Subgroup.closure ((sLay p s u L0 (w + 1)).x '' Set.Iio i) ⊔ layK p G (w + 1) := by
  rw [sLay_succ] at hi ⊢
  exact gLay_indep _ _ _ _ _ hi

lemma sLay_gen (hs : 0 < s) (hr0 : s ≤ L0.r) (w : ℕ) {i : ℕ}
    (hi : i < (sLay p s u L0 (w + 1)).r) :
    (sLay p s u L0 (w + 1)).par i < (sLay p s u L0 w).r ∧ (sLay p s u L0 (w + 1)).cor i < s ∧
    (w = 0 → (sLay p s u L0 (w + 1)).par i < (sLay p s u L0 (w + 1)).cor i) ∧
    (sLay p s u L0 (w + 1)).x i = ⁅(sLay p s u L0 w).x ((sLay p s u L0 (w + 1)).par i),
      u ((sLay p s u L0 (w + 1)).cor i)⁆ := by
  rw [sLay_succ] at hi ⊢
  exact gLay_cVal_gen s u hs w (sLay p s u L0 w) (fun hw => by subst hw; exact hr0) _ hi

/-- Spanning for the layers of weight `≥ 3`. -/
lemma sLay_span_succ (hs : 0 < s) (w : ℕ) {a b : ℕ} (ha : a < (sLay p s u L0 (w + 1)).r)
    (hb : b < s) (hw : ¬ (w = 0 ∧ (sLay p s u L0 (w + 1)).cor a < b)) :
    ⁅(sLay p s u L0 (w + 1)).x a, u b⁆ ∈ Subgroup.closure ((sLay p s u L0 (w + 1 + 1)).x ''
      Set.Iio (sLay p s u L0 (w + 1 + 1)).r) ⊔ layK p G (w + 1 + 1) := by
  have hj : a * s + b < cN s (w + 1) (sLay p s u L0 (w + 1)) := by
    rw [cN_ne (show w + 1 ≠ 0 by omega)]
    exact slot_lt ha hb
  have hv : cVal s u (w + 1) (sLay p s u L0 (w + 1)) (a * s + b) =
      ⁅(sLay p s u L0 (w + 1)).x a, u b⁆ := by
    have hw' : ¬ (w = 0 ∧ (sLay p s u L0 (w + 1)).cor ((a * s + b) / s) < (a * s + b) % s) := by
      rw [slot_div hb, slot_mod hb]
      exact hw
    rw [cVal_succ s u w _ _ hw', slot_div hb, slot_mod hb]
  rw [← hv, sLay_succ p s u L0 (w + 1)]
  exact gLay_span_all _ _ _ _ _ hj

/-- The weight-3 restriction of layer `2`. -/
lemma sLay_w3 {i : ℕ} (hi : i < (sLay p s u L0 2).r) :
    (sLay p s u L0 2).cor i ≤ (sLay p s u L0 1).cor ((sLay p s u L0 2).par i) :=
  not_lt.mp (gLay_cVal_w3 s u (sLay p s u L0 1) (layK p G 2) (i := i) hi)

/-- Prefix spanning for layer `1` (the subspaces `W_k` of BNV Prop 5.2). -/
lemma sLay_span_one (hs : 0 < s) (hx0 : ∀ a < s, L0.x a = u a) {k : ℕ} (hk : k ≤ s)
    {a b : ℕ} (hab : a < b) (hb : b < k) :
    ⁅u a, u b⁆ ∈ Subgroup.closure ((sLay p s u L0 1).x ''
      {i | i < (sLay p s u L0 1).r ∧ (sLay p s u L0 1).cor i < k}) ⊔ layK p G 1 := by
  have hbs : b < s := lt_of_lt_of_le hb hk
  have has : a < s := lt_trans hab hbs
  have hJ : k * s ≤ cN s 0 L0 := by
    rw [cN_zero]
    exact Nat.mul_le_mul_right s hk
  have hj : b * s + a < k * s := slot_lt hb has
  have hv : cVal s u 0 L0 (b * s + a) = ⁅u a, u b⁆ := by
    rw [cVal_zero_of_lt s u L0 (j := b * s + a) (by rw [slot_mod has, slot_div has]; exact hab),
      slot_mod has,
      slot_div has, hx0 a has]
  rw [← hv, sLay_one]
  refine (sup_le_sup_right (Subgroup.closure_mono ?_) _)
    (gLay_span (cVal s u 0 L0) (layK p G 1) (cN s 0 L0) (cPar s 0) (cCor s 0) hJ hj)
  rintro _ ⟨i, ⟨hi, hik⟩, rfl⟩
  refine ⟨i, ⟨hi, ?_⟩, rfl⟩
  show cCor s 0 (genum _ i) < k
  rw [cCor_zero]
  exact (Nat.div_lt_iff_lt_mul hs).mpr hik

/-- Weight-3 reduction (BNV Section 5.4, a Jacobi argument): every `[g_{2,a}, g_{1,b}]` lies in
the span of the restricted weight-3 candidates modulo `γ_4 γ_3^p`. By strong induction on `b`:
for `co(a) = k < b` and `g_{2,a} = [u_f, u_k]` (`f < k`), the three subgroup lemma reduces
`[[u_f, u_k], u_b]` to commutators of `[u_k, u_b], [u_f, u_b] ∈ W_{b+1}` with `u_f`, `u_k`. -/
lemma sLay_span_two (hs : 0 < s) (hr0 : s ≤ L0.r) (hx0 : ∀ a < s, L0.x a = u a) :
    ∀ b, b < s → ∀ a, a < (sLay p s u L0 1).r → ⁅(sLay p s u L0 1).x a, u b⁆ ∈
      Subgroup.closure ((sLay p s u L0 2).x '' Set.Iio (sLay p s u L0 2).r) ⊔ layK p G 2 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb a ha
    have hN : (Subgroup.closure ((sLay p s u L0 2).x '' Set.Iio (sLay p s u L0 2).r) ⊔
        layK p G 2).Normal :=
      layK_normal_sup p 2 _ (by rintro _ ⟨i, -, rfl⟩; exact sLay_mem p s u L0 2 i)
    by_cases hab : (sLay p s u L0 1).cor a < b
    · have hg := sLay_gen p s u L0 hs hr0 0 ha
      have hk : (sLay p s u L0 1).cor a < s := hg.2.1
      have hfk : (sLay p s u L0 1).par a < (sLay p s u L0 1).cor a := hg.2.2.1 rfl
      have hxa : (sLay p s u L0 1).x a =
          ⁅L0.x ((sLay p s u L0 1).par a), u ((sLay p s u L0 1).cor a)⁆ := hg.2.2.2
      rw [hx0 ((sLay p s u L0 1).par a) (by omega)] at hxa
      rw [hxa]
      have hKn : (Subgroup.closure ((sLay p s u L0 1).x '' {i | i < (sLay p s u L0 1).r ∧
          (sLay p s u L0 1).cor i < b + 1}) ⊔ layK p G 1).Normal :=
        layK_normal_sup p 1 _ (by rintro _ ⟨i, -, rfl⟩; exact sLay_mem p s u L0 1 i)
      have hKM : ∀ c, c < b → ∀ z ∈ Subgroup.closure ((sLay p s u L0 1).x '' {i |
          i < (sLay p s u L0 1).r ∧ (sLay p s u L0 1).cor i < b + 1}) ⊔ layK p G 1,
          ⁅z, u c⁆ ∈ Subgroup.closure ((sLay p s u L0 2).x '' Set.Iio (sLay p s u L0 2).r) ⊔
            layK p G 2 := by
        intro c hc
        haveI := hN
        refine lie_sup_comm ?_ ?_
        · rintro _ ⟨i, ⟨hi, -⟩, rfl⟩
          exact ih c hc (by omega) i hi
        · intro z hz
          exact Subgroup.mem_sup_right (comm_layK_one p z hz (u c))
      haveI := hN
      haveI := hKn
      exact lie_three _ _ _
        (sLay_span_one p s u L0 hs hx0 (show b + 1 ≤ s by omega) hab (Nat.lt_succ_self b))
        (hKM _ (by omega))
        (commElem_mem_symm (sLay_span_one p s u L0 hs hx0 (show b + 1 ≤ s by omega)
          (show (sLay p s u L0 1).par a < b by omega) (Nat.lt_succ_self b)))
        (hKM _ hab)
    · exact sLay_span_succ p s u L0 hs 0 ha hb (fun h => hab h.2)

/-- The layers generate the lower central series: `γ_{w+2} ≤ ⟨layer w + 1⟩ γ_{w+3}`. -/
theorem sLay_lcs [Finite G] {m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) (hs : 0 < s)
    (hx0 : ∀ a < s, L0.x a = u a)
    (hL0 : Subgroup.closure (L0.x '' Set.Iio L0.r) ⊔ lcs G 1 = ⊤)
    (hcore : lcs G 1 ≤ Subgroup.closure (lieE s u 1) ⊔ lcs G 2) (hr0 : s ≤ L0.r) :
    ∀ w, lcs G (w + 1) ≤ Subgroup.closure ((sLay p s u L0 (w + 1)).x ''
      Set.Iio (sLay p s u L0 (w + 1)).r) ⊔ lcs G (w + 2) := by
  have hT := theoremL s u (L0.x '' Set.Iio L0.r) hL0 hcore
  have hsub : ∀ w, (sLay p s u L0 (w + 1)).x '' Set.Iio (sLay p s u L0 (w + 1)).r ⊆
      (lcs G (w + 1) : Set G) := by
    rintro w _ ⟨i, -, rfl⟩
    exact sLay_mem p s u L0 (w + 1) i
  intro w
  induction w with
  | zero =>
    apply frat_layer hp hG 0 _ (hsub 0)
    refine (hT 1 le_rfl).trans (sup_le ?_ ((lcs_succ_le_layK p 1).trans le_sup_right))
    rw [Subgroup.closure_le]
    rintro _ ⟨ab, hab, rfl⟩
    have h1 := sLay_span_one p s u L0 hs hx0 le_rfl hab.1 hab.2
    exact (sup_le_sup_right (Subgroup.closure_mono (Set.image_mono (fun i hi => hi.1))) _) h1
  | succ w ih =>
    apply frat_layer hp hG (w + 1) _ (hsub (w + 1))
    have hN := layK_normal_sup p (w + 1 + 1)
      ((sLay p s u L0 (w + 1 + 1)).x '' Set.Iio (sLay p s u L0 (w + 1 + 1)).r) (hsub (w + 1))
    refine (hT (w + 1 + 1) (by omega)).trans
      (sup_le ?_ ((lcs_succ_le_layK p (w + 1 + 1)).trans le_sup_right))
    rw [Subgroup.closure_le]
    rintro _ ⟨y, hy, b, hb, rfl⟩
    have hy1 := ih ((Subgroup.closure_le _).mpr (lieE_sub s u w) hy)
    have hle : Subgroup.closure ((sLay p s u L0 (w + 1)).x '' Set.Iio (sLay p s u L0 (w + 1)).r) ⊔
        lcs G (w + 2) ≤ zn (Subgroup.closure ((sLay p s u L0 (w + 1 + 1)).x ''
          Set.Iio (sLay p s u L0 (w + 1 + 1)).r) ⊔ layK p G (w + 1 + 1)) (u b) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨a, ha, rfl⟩
        have hspan : ⁅(sLay p s u L0 (w + 1)).x a, u b⁆ ∈ Subgroup.closure
            ((sLay p s u L0 (w + 1 + 1)).x '' Set.Iio (sLay p s u L0 (w + 1 + 1)).r) ⊔
              layK p G (w + 1 + 1) := by
          rcases Nat.eq_zero_or_pos w with hw | hw
          · subst hw
            exact sLay_span_two p s u L0 hs hr0 hx0 b hb a ha
          · exact sLay_span_succ p s u L0 hs w ha hb (fun h => by omega)
        exact mem_zn.mpr (commElem_mem_symm hspan)
      · intro g hg
        exact mem_zn.mpr (Subgroup.mem_sup_right
          ((lcs_succ_le_layK p (w + 1 + 1)) (commElem_mem_lcs_succ' (u b) hg)))
    exact commElem_mem_symm (mem_zn.mp (hle hy1))

end Layers2

section Layer0

/-- An enumeration of all elements of `G` (junk `1` beyond `|G|`). -/
noncomputable def allElt (G : Type u) [Group G] [Finite G] (j : ℕ) : G :=
  if h : j < Nat.card G then (Finite.equivFin G).symm ⟨j, h⟩ else 1

variable {G : Type u} [Group G] [Finite G]

lemma allElt_surj (g : G) : ∃ j < Nat.card G, allElt G j = g := by
  refine ⟨(Finite.equivFin G g).val, (Finite.equivFin G g).isLt, ?_⟩
  unfold allElt
  rw [dif_pos (Finite.equivFin G g).isLt]
  simp

/-- The greedy completion of the core to a basis modulo `Φ(G)`. -/
noncomputable abbrev lay0E (p s : ℕ) (u : ℕ → G) : SLay G :=
  gLay (allElt G) (Subgroup.closure (u '' Set.Iio s) ⊔ pPhi p G) (Nat.card G) id id

/-- Layer `0` (weight 1): the core `u_0, ..., u_{s-1}` followed by its greedy completion. -/
noncomputable def lay0 (p s : ℕ) (u : ℕ → G) : SLay G where
  r := s + (lay0E p s u).r
  x := fun i => if i < s then u i else (lay0E p s u).x (i - s)
  par := id
  cor := id

variable (p s : ℕ) (u : ℕ → G)

lemma lay0_x_lt {i : ℕ} (h : i < s) : (lay0 p s u).x i = u i := if_pos h

lemma lay0_x_ge {i : ℕ} (h : ¬ i < s) : (lay0 p s u).x i = (lay0E p s u).x (i - s) := if_neg h

lemma lay0_indep (hu : ∀ k < s, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ pPhi p G) {i : ℕ}
    (hi : i < (lay0 p s u).r) :
    (lay0 p s u).x i ∉ Subgroup.closure ((lay0 p s u).x '' Set.Iio i) ⊔ pPhi p G := by
  by_cases his : i < s
  · rw [lay0_x_lt p s u his]
    intro hmem
    apply hu i his
    refine (sup_le_sup_right (Subgroup.closure_mono ?_) _) hmem
    rintro _ ⟨i', hi', rfl⟩
    have hi'' : i' < i := hi'
    exact ⟨i', hi', (lay0_x_lt p s u (lt_trans hi'' his)).symm⟩
  · rw [lay0_x_ge p s u his]
    intro hmem
    have hi' : i - s < (lay0E p s u).r := by
      have h1 : i < s + (lay0E p s u).r := hi
      omega
    apply gLay_indep _ _ _ _ _ hi'
    refine (sup_le ?_ ?_ : _ ≤ Subgroup.closure ((lay0E p s u).x '' Set.Iio (i - s)) ⊔
      (Subgroup.closure (u '' Set.Iio s) ⊔ pPhi p G)) hmem
    · rw [Subgroup.closure_le]
      rintro _ ⟨i', hi'', rfl⟩
      have hi''' : i' < i := hi''
      by_cases h' : i' < s
      · rw [lay0_x_lt p s u h']
        exact Subgroup.mem_sup_right
          (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i', h', rfl⟩))
      · rw [lay0_x_ge p s u h']
        exact Subgroup.mem_sup_left
          (Subgroup.subset_closure ⟨i' - s, show i' - s < i - s by omega, rfl⟩)
    · exact le_sup_right.trans le_sup_right

lemma lay0_span (g : G) :
    g ∈ Subgroup.closure ((lay0 p s u).x '' Set.Iio (lay0 p s u).r) ⊔ pPhi p G := by
  obtain ⟨j, hj, rfl⟩ := allElt_surj g
  have h1 := gLay_span (allElt G) (Subgroup.closure (u '' Set.Iio s) ⊔ pPhi p G) (Nat.card G)
    id id le_rfl hj
  refine (sup_le ?_ ?_ : _ ≤ Subgroup.closure ((lay0 p s u).x '' Set.Iio (lay0 p s u).r) ⊔
    pPhi p G) h1
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, ⟨hi, -⟩, rfl⟩
    have hi' : i < (lay0E p s u).r := hi
    refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨s + i, ?_, ?_⟩)
    · show s + i < s + (lay0E p s u).r
      omega
    · rw [lay0_x_ge p s u (by omega), show s + i - s = i by omega]
  · refine sup_le ?_ le_sup_right
    refine (Subgroup.closure_mono ?_).trans le_sup_left
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < s := hk
    exact ⟨k, show k < s + (lay0E p s u).r by omega, lay0_x_lt p s u hk'⟩

end Layer0

section Flat

/-! Flattening the layers into a tuple `X : Fin n → G`: layer `w` occupies the positions
`fOff r w, ..., fOff r w + r w - 1`. -/

variable {G : Type u} [Group G]

/-- Offsets of the layers. -/
def fOff (ℓ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => fOff ℓ w + ℓ w

lemma fOff_succ (ℓ : ℕ → ℕ) (w : ℕ) : fOff ℓ (w + 1) = fOff ℓ w + ℓ w := rfl

lemma fOff_mono (ℓ : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : fOff ℓ a ≤ fOff ℓ b := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · rw [fOff_succ]
      exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · obtain rfl : a = b + 1 := by omega
      exact le_rfl

/-- The layer of position `t`. -/
def fLv (ℓ : ℕ → ℕ) (L t : ℕ) : ℕ := Nat.findGreatest (fun w => fOff ℓ w ≤ t) L

lemma fLv_eq {ℓ : ℕ → ℕ} {L t w : ℕ} (hw : w ≤ L) (h1 : fOff ℓ w ≤ t) (h2 : t < fOff ℓ (w + 1)) :
    fLv ℓ L t = w := by
  unfold fLv
  have hle := Nat.le_findGreatest (P := fun w => fOff ℓ w ≤ t) hw h1
  have hspec : fOff ℓ (Nat.findGreatest (fun w => fOff ℓ w ≤ t) L) ≤ t :=
    Nat.findGreatest_spec (P := fun w => fOff ℓ w ≤ t) hw h1
  by_contra hne
  have hgt : w + 1 ≤ Nat.findGreatest (fun w => fOff ℓ w ≤ t) L := by omega
  have := fOff_mono ℓ hgt
  omega

lemma fLv_spec {ℓ : ℕ → ℕ} {L t : ℕ} (ht : t < fOff ℓ (L + 1)) :
    fOff ℓ (fLv ℓ L t) ≤ t ∧ t < fOff ℓ (fLv ℓ L t + 1) ∧ fLv ℓ L t ≤ L := by
  have h1 : fOff ℓ (fLv ℓ L t) ≤ t :=
    Nat.findGreatest_spec (P := fun w => fOff ℓ w ≤ t) (Nat.zero_le L) (Nat.zero_le t)
  have h3 : fLv ℓ L t ≤ L := Nat.findGreatest_le L
  refine ⟨h1, ?_, h3⟩
  by_cases hL : fLv ℓ L t = L
  · rw [hL]
    exact ht
  · have h4 := Nat.findGreatest_is_greatest (P := fun w => fOff ℓ w ≤ t)
      (n := L) (k := fLv ℓ L t + 1) (by unfold fLv; omega) (by omega)
    exact not_le.mp h4

lemma fLv_mono {ℓ : ℕ → ℕ} {L t t' : ℕ} (ht' : t' < fOff ℓ (L + 1)) (h : t ≤ t') :
    fLv ℓ L t ≤ fLv ℓ L t' := by
  have ht : t < fOff ℓ (L + 1) := lt_of_le_of_lt h ht'
  obtain ⟨h1, -, -⟩ := fLv_spec ht
  obtain ⟨-, h2', -⟩ := fLv_spec ht'
  by_contra hc
  have := fOff_mono ℓ (show fLv ℓ L t' + 1 ≤ fLv ℓ L t by omega)
  omega

/-- `k` as an element of `Fin n` (junk `dflt` out of range). -/
def bFin (n k : ℕ) (dflt : Fin n) : Fin n := if h : k < n then ⟨k, h⟩ else dflt

lemma bFin_val {n k : ℕ} (dflt : Fin n) (h : k < n) : (bFin n k dflt).val = k := by
  unfold bFin
  rw [dif_pos h]

/-- The layer lengths, truncated after layer `L`. -/
def fLen (L : ℕ) (r : ℕ → ℕ) (w : ℕ) : ℕ := if w ≤ L then r w else 0

lemma fLen_of_le {L : ℕ} {r : ℕ → ℕ} {w : ℕ} (h : w ≤ L) : fLen L r w = r w := if_pos h

lemma fLen_of_gt {L : ℕ} {r : ℕ → ℕ} {w : ℕ} (h : ¬ w ≤ L) : fLen L r w = 0 := if_neg h

lemma fOff_one (L : ℕ) (r : ℕ → ℕ) : fOff (fLen L r) 1 = r 0 := by
  show fOff (fLen L r) 0 + fLen L r 0 = r 0
  rw [fLen_of_le (Nat.zero_le L)]
  show 0 + r 0 = r 0
  omega

lemma fpos_lt {L : ℕ} {r : ℕ → ℕ} {w i : ℕ} (hw : w ≤ L) (hi : i < r w) :
    fOff (fLen L r) w + i < fOff (fLen L r) (L + 1) := by
  have h1 : fOff (fLen L r) (w + 1) = fOff (fLen L r) w + r w := by
    rw [fOff_succ, fLen_of_le hw]
  have h2 := fOff_mono (fLen L r) (show w + 1 ≤ L + 1 by omega)
  omega

lemma fpos_lv {L : ℕ} {r : ℕ → ℕ} {w i : ℕ} (hw : w ≤ L) (hi : i < r w) :
    fLv (fLen L r) L (fOff (fLen L r) w + i) = w := by
  apply fLv_eq hw (Nat.le_add_right _ _)
  rw [fOff_succ, fLen_of_le hw]
  omega

lemma fLv_inv {L : ℕ} {r : ℕ → ℕ} {t : ℕ} (ht : t < fOff (fLen L r) (L + 1)) :
    fLv (fLen L r) L t ≤ L ∧ fOff (fLen L r) (fLv (fLen L r) L t) ≤ t ∧
      t - fOff (fLen L r) (fLv (fLen L r) L t) < r (fLv (fLen L r) L t) := by
  obtain ⟨h1, h2, h3⟩ := fLv_spec ht
  refine ⟨h3, h1, ?_⟩
  rw [fOff_succ, fLen_of_le h3] at h2
  omega

/-- The commutator definitions of the flattened tuple. -/
def fDf (L : ℕ) (r : ℕ → ℕ) (pa co : ℕ → ℕ → ℕ) (t : Fin (fOff (fLen L r) (L + 1))) :
    Fin (fOff (fLen L r) (L + 1)) × Fin (fOff (fLen L r) (L + 1)) :=
  match fLv (fLen L r) L t.val with
  | 0 => (t, t)
  | w + 1 => (bFin _ (fOff (fLen L r) w + pa (w + 1) (t.val - fOff (fLen L r) (w + 1))) t,
      bFin _ (co (w + 1) (t.val - fOff (fLen L r) (w + 1))) t)

lemma fDf_succ (L : ℕ) (r : ℕ → ℕ) (pa co : ℕ → ℕ → ℕ) (t : Fin (fOff (fLen L r) (L + 1)))
    {w : ℕ} (h : fLv (fLen L r) L t.val = w + 1) :
    fDf L r pa co t = (bFin _ (fOff (fLen L r) w + pa (w + 1) (t.val - fOff (fLen L r) (w + 1))) t,
      bFin _ (co (w + 1) (t.val - fOff (fLen L r) (w + 1))) t) := by
  unfold fDf
  rw [h]

/-- The flattened tuple. -/
def fX (L : ℕ) (r : ℕ → ℕ) (xs : ℕ → ℕ → G) (t : Fin (fOff (fLen L r) (L + 1))) : G :=
  xs (fLv (fLen L r) L t.val) (t.val - fOff (fLen L r) (fLv (fLen L r) L t.val))

lemma fX_eq (L : ℕ) (r : ℕ → ℕ) (xs : ℕ → ℕ → G) (t : Fin (fOff (fLen L r) (L + 1))) {w : ℕ}
    (h : fLv (fLen L r) L t.val = w) : fX L r xs t = xs w (t.val - fOff (fLen L r) w) := by
  unfold fX
  rw [h]

lemma fX_pos {L : ℕ} {r : ℕ → ℕ} (xs : ℕ → ℕ → G) {w i : ℕ} (hw : w ≤ L) (hi : i < r w) :
    fX L r xs ⟨fOff (fLen L r) w + i, fpos_lt hw hi⟩ = xs w i := by
  rw [fX_eq L r xs ⟨fOff (fLen L r) w + i, fpos_lt hw hi⟩ (fpos_lv hw hi)]
  show xs w (fOff (fLen L r) w + i - fOff (fLen L r) w) = xs w i
  rw [Nat.add_sub_cancel_left]

/-- The shape of the flattened tuple (the arrays are filled in by `exists_arrays`). -/
def fData (s L : ℕ) (r : ℕ → ℕ) (pa co : ℕ → ℕ → ℕ) : SimsData where
  n := fOff (fLen L r) (L + 1)
  s := s
  lv := fun t => fLv (fLen L r) L t.val
  df := fDf L r pa co
  a := fun _ => 0
  b := fun _ _ => 0
  c := fun _ _ _ => 0

variable {s L : ℕ} {r : ℕ → ℕ} {xs : ℕ → ℕ → G} {pa co : ℕ → ℕ → ℕ}

lemma fData_s_le (H0 : s ≤ r 0) : s ≤ fOff (fLen L r) (L + 1) := by
  have h1 := fOff_one L r
  have h2 := fOff_mono (fLen L r) (show 1 ≤ L + 1 by omega)
  omega

lemma fDf_vals (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (t : Fin (fOff (fLen L r) (L + 1))) {w : ℕ} (hw : fLv (fLen L r) L t.val = w + 1) :
    w + 1 ≤ L ∧ t.val - fOff (fLen L r) (w + 1) < r (w + 1) ∧
    ((fDf L r pa co t).1).val =
      fOff (fLen L r) w + pa (w + 1) (t.val - fOff (fLen L r) (w + 1)) ∧
    ((fDf L r pa co t).2).val = co (w + 1) (t.val - fOff (fLen L r) (w + 1)) := by
  obtain ⟨hL, -, hi⟩ := fLv_inv (r := r) t.isLt
  rw [hw] at hL hi
  have hp := Hpa w _ hi
  have hc := Hco w _ hi
  refine ⟨hL, hi, ?_, ?_⟩
  · rw [fDf_succ L r pa co t hw]
    exact bFin_val t (fpos_lt (show w ≤ L by omega) hp)
  · rw [fDf_succ L r pa co t hw]
    exact bFin_val t (lt_of_lt_of_le hc (fData_s_le (L := L) H0))

lemma fData_struct (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (H1 : ∀ i, i < r 1 → pa 1 i < co 1 i) : (fData s L r pa co).Struct := by
  refine ⟨?_, fData_s_le H0, ?_, ?_, ?_, ?_⟩
  · intro t v htv
    exact fLv_mono v.isLt (Fin.le_def.mp htv)
  · intro t ht
    have ht' : t.val < fOff (fLen L r) (0 + 1) := by
      have h1 : fOff (fLen L r) (0 + 1) = r 0 := fOff_one L r
      have h2 : t.val < s := ht
      omega
    exact fLv_eq (Nat.zero_le L) (Nat.zero_le _) ht'
  · intro t ht
    obtain ⟨w, hw⟩ : ∃ w, fLv (fLen L r) L t.val = w + 1 :=
      ⟨fLv (fLen L r) L t.val - 1, by have : 1 ≤ fLv (fLen L r) L t.val := ht; omega⟩
    obtain ⟨hL, hi, h1, -⟩ := fDf_vals (pa := pa) (co := co) H0 Hpa Hco t hw
    show fLv (fLen L r) L ((fDf L r pa co t).1).val + 1 = fLv (fLen L r) L t.val
    rw [h1, hw, fpos_lv (show w ≤ L by omega) (Hpa w _ hi)]
  · intro t ht
    obtain ⟨w, hw⟩ : ∃ w, fLv (fLen L r) L t.val = w + 1 :=
      ⟨fLv (fLen L r) L t.val - 1, by have : 1 ≤ fLv (fLen L r) L t.val := ht; omega⟩
    obtain ⟨-, hi, -, h2⟩ := fDf_vals (pa := pa) (co := co) H0 Hpa Hco t hw
    show ((fDf L r pa co t).2).val < s
    rw [h2]
    exact Hco w _ hi
  · intro t ht
    have hw : fLv (fLen L r) L t.val = 0 + 1 := ht
    obtain ⟨-, hi, h1, h2⟩ := fDf_vals (pa := pa) (co := co) H0 Hpa Hco t hw
    show (fDf L r pa co t).1 < (fDf L r pa co t).2
    rw [Fin.lt_def, h1, h2]
    have h3 : pa 1 (t.val - fOff (fLen L r) (0 + 1)) < co 1 (t.val - fOff (fLen L r) (0 + 1)) :=
      H1 _ hi
    show 0 + pa 1 (t.val - fOff (fLen L r) (0 + 1)) < co 1 (t.val - fOff (fLen L r) (0 + 1))
    omega

lemma fX_df (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (Hx : ∀ w i, i < r (w + 1) → xs (w + 1) i = ⁅xs w (pa (w + 1) i), xs 0 (co (w + 1) i)⁆)
    (t : Fin (fOff (fLen L r) (L + 1))) (ht : 1 ≤ fLv (fLen L r) L t.val) :
    fX L r xs t = ⁅fX L r xs (fDf L r pa co t).1, fX L r xs (fDf L r pa co t).2⁆ := by
  obtain ⟨w, hw⟩ : ∃ w, fLv (fLen L r) L t.val = w + 1 := ⟨fLv (fLen L r) L t.val - 1, by omega⟩
  obtain ⟨hL, hi, h1, h2⟩ := fDf_vals (pa := pa) (co := co) H0 Hpa Hco t hw
  have hp := Hpa w _ hi
  have hc := Hco w _ hi
  have e1 : fLv (fLen L r) L ((fDf L r pa co t).1).val = w := by
    rw [h1]
    exact fpos_lv (show w ≤ L by omega) hp
  have e2 : fLv (fLen L r) L ((fDf L r pa co t).2).val = 0 := by
    rw [h2]
    have h3 : fOff (fLen L r) (0 + 1) = r 0 := fOff_one L r
    exact fLv_eq (Nat.zero_le L) (Nat.zero_le _) (by omega)
  have e0 : fOff (fLen L r) 0 = 0 := rfl
  rw [fX_eq L r xs t hw, fX_eq L r xs _ e1, fX_eq L r xs _ e2, Hx w _ hi, h1, h2,
    Nat.add_sub_cancel_left, e0, Nat.sub_zero]

lemma flat_gen (h0 : Subgroup.closure (xs 0 '' Set.Iio (r 0)) = ⊤) :
    Subgroup.closure (Set.range (fX L r xs)) = ⊤ := by
  rw [eq_top_iff, ← h0, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact Subgroup.subset_closure ⟨⟨_, fpos_lt (Nat.zero_le L) hi⟩, fX_pos xs (Nat.zero_le L) hi⟩

lemma flat_lev
    (HU : ∀ w, w + 1 ≤ L → lcs G (w + 1) ≤
      Subgroup.closure (xs (w + 1) '' Set.Iio (r (w + 1))) ⊔ lcs G (w + 2))
    (HL : lcs G (L + 1) = ⊥) (w : ℕ) :
    lcs G (w + 1) ≤ Subgroup.closure (levSet (fData s L r pa co) (fX L r xs) (w + 1)) ⊔
      lcs G (w + 2) := by
  by_cases hw : w + 1 ≤ L
  · refine (HU w hw).trans (sup_le_sup_right (Subgroup.closure_mono ?_) _)
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨⟨_, fpos_lt hw hi⟩, fpos_lv hw hi, fX_pos xs hw hi⟩
  · exact ((lcs_antitone (D := G) (show L + 1 ≤ w + 1 by omega)).trans (le_of_eq HL)).trans
      bot_le

lemma flat_deep (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (H1 : ∀ i, i < r 1 → pa 1 i < co 1 i)
    (Hx : ∀ w i, i < r (w + 1) → xs (w + 1) i = ⁅xs w (pa (w + 1) i), xs 0 (co (w + 1) i)⁆)
    (h0 : Subgroup.closure (xs 0 '' Set.Iio (r 0)) = ⊤)
    (HU : ∀ w, w + 1 ≤ L → lcs G (w + 1) ≤
      Subgroup.closure (xs (w + 1) '' Set.Iio (r (w + 1))) ⊔ lcs G (w + 2))
    (HL : lcs G (L + 1) = ⊥) :
    ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (fX L r xs '' {v | w ≤ (fData s L r pa co).lv v}) := by
  have hd := fData_struct (L := L) H0 Hpa Hco H1
  have hdf : ∀ t, 1 ≤ (fData s L r pa co).lv t → fX L r xs t =
      ⁅fX L r xs ((fData s L r pa co).df t).1, fX L r xs ((fData s L r pa co).df t).2⁆ :=
    fun t ht => fX_df H0 Hpa Hco Hx t ht
  have hlv := lv_mem_lcs (fData s L r pa co) hd (fX L r xs) hdf
  refine sims_lcs_tail (fData s L r pa co) hd (fX L r xs) (flat_gen h0) ⟨L + 1, HL⟩ hdf ?_ ?_ ?_
  · intro i k _ _
    exact flat_lev HU HL 0 (commElem_mem_lcs_one _ _)
  · intro t k ht _
    have h1 := commElem_mem_lcs_succ (hlv t) (fX L r xs k)
    rw [ht] at h1
    exact flat_lev HU HL 1 h1
  · intro t k _ _
    exact flat_lev HU HL ((fData s L r pa co).lv t) (commElem_mem_lcs_succ (hlv t) _)

lemma flat_indep (p : ℕ)
    (Hind : ∀ w i, i < r w → xs w i ∉ Subgroup.closure (xs w '' Set.Iio i) ⊔ layK p G w)
    (t : Fin (fOff (fLen L r) (L + 1))) :
    fX L r xs t ∉ Subgroup.closure (fX L r xs '' {v | (fData s L r pa co).lv v =
      (fData s L r pa co).lv t ∧ v < t}) ⊔ layK p G ((fData s L r pa co).lv t) := by
  obtain ⟨-, -, hi⟩ := fLv_inv (r := r) t.isLt
  intro hmem
  apply Hind _ _ hi
  rw [← fX_eq L r xs t rfl]
  refine (sup_le_sup_right (Subgroup.closure_mono ?_) _) hmem
  rintro _ ⟨v, ⟨hv1, hv2⟩, rfl⟩
  have hv1' : fLv (fLen L r) L v.val = fLv (fLen L r) L t.val := hv1
  obtain ⟨-, hv3, -⟩ := fLv_inv (r := r) v.isLt
  rw [hv1'] at hv3
  have hv2' : v.val < t.val := hv2
  refine ⟨v.val - fOff (fLen L r) (fLv (fLen L r) L t.val), ?_, (fX_eq L r xs v hv1').symm⟩
  show v.val - fOff (fLen L r) (fLv (fLen L r) L t.val) <
    t.val - fOff (fLen L r) (fLv (fLen L r) L t.val)
  omega

lemma flat_core (u : ℕ → G) (H0 : s ≤ r 0) (Hc0 : ∀ i < s, xs 0 i = u i)
    (t : Fin (fOff (fLen L r) (L + 1))) (ht : t.val < s) : fX L r xs t = u t.val := by
  have h1 : fOff (fLen L r) (0 + 1) = r 0 := fOff_one L r
  have h0 : fLv (fLen L r) L t.val = 0 :=
    fLv_eq (Nat.zero_le L) (Nat.zero_le _) (by omega)
  rw [fX_eq L r xs t h0]
  show xs 0 (t.val - 0) = u t.val
  rw [Nat.sub_zero]
  exact Hc0 _ ht

lemma flat_one (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (t : Fin (fOff (fLen L r) (L + 1))) (ht : fLv (fLen L r) L t.val = 1) :
    1 ≤ L ∧ r 0 ≤ t.val ∧ t.val - r 0 < r 1 ∧
      ((fDf L r pa co t).1).val = pa 1 (t.val - r 0) ∧
      ((fDf L r pa co t).2).val = co 1 (t.val - r 0) := by
  have hw : fLv (fLen L r) L t.val = 0 + 1 := ht
  obtain ⟨hL, hi, h1, h2⟩ := fDf_vals (pa := pa) (co := co) H0 Hpa Hco t hw
  obtain ⟨-, h3, -⟩ := fLv_inv (r := r) t.isLt
  rw [hw] at h3
  have e : fOff (fLen L r) (0 + 1) = r 0 := fOff_one L r
  rw [e] at hi h1 h2 h3
  refine ⟨hL, h3, hi, ?_, h2⟩
  rw [h1]
  show 0 + pa 1 (t.val - r 0) = pa 1 (t.val - r 0)
  omega

lemma flat_mono (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (Hmono : ∀ i i', i ≤ i' → i' < r 1 → co 1 i ≤ co 1 i')
    (t t' : Fin (fOff (fLen L r) (L + 1))) (ht : fLv (fLen L r) L t.val = 1)
    (ht' : fLv (fLen L r) L t'.val = 1) (htt : t ≤ t') :
    (fDf L r pa co t).2 ≤ (fDf L r pa co t').2 := by
  obtain ⟨-, h3, -, -, h2⟩ := flat_one (pa := pa) (co := co) H0 Hpa Hco t ht
  obtain ⟨-, h3', hi', -, h2'⟩ := flat_one (pa := pa) (co := co) H0 Hpa Hco t' ht'
  rw [Fin.le_def, h2, h2']
  have h4 : t.val ≤ t'.val := Fin.le_def.mp htt
  exact Hmono _ _ (by omega) hi'

lemma flat_inj (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s)
    (Hinj : ∀ i i', i < r 1 → i' < r 1 → pa 1 i = pa 1 i' → co 1 i = co 1 i' → i = i')
    (t t' : Fin (fOff (fLen L r) (L + 1))) (ht : fLv (fLen L r) L t.val = 1)
    (ht' : fLv (fLen L r) L t'.val = 1) (h1 : (fDf L r pa co t).1 = (fDf L r pa co t').1)
    (h2 : (fDf L r pa co t).2 = (fDf L r pa co t').2) : t = t' := by
  obtain ⟨-, h3, hi, e1, e2⟩ := flat_one (pa := pa) (co := co) H0 Hpa Hco t ht
  obtain ⟨-, h3', hi', e1', e2'⟩ := flat_one (pa := pa) (co := co) H0 Hpa Hco t' ht'
  have hp : pa 1 (t.val - r 0) = pa 1 (t'.val - r 0) := by rw [← e1, ← e1', h1]
  have hc : co 1 (t.val - r 0) = co 1 (t'.val - r 0) := by rw [← e2, ← e2', h2]
  have h4 := Hinj _ _ hi hi' hp hc
  exact Fin.ext (by omega)

lemma flat_Wk (p : ℕ) (u : ℕ → G) (H0 : s ≤ r 0)
    (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s) (H1 : ∀ i, i < r 1 → pa 1 i < co 1 i)
    (Hx : ∀ w i, i < r (w + 1) → xs (w + 1) i = ⁅xs w (pa (w + 1) i), xs 0 (co (w + 1) i)⁆)
    (Hc0 : ∀ i < s, xs 0 i = u i) (hL1 : 1 ≤ L)
    (HS1 : ∀ k ≤ s, ∀ a b, a < b → b < k →
      ⁅u a, u b⁆ ∈ Subgroup.closure (xs 1 '' {i | i < r 1 ∧ co 1 i < k}) ⊔ pN p G)
    {k : ℕ} (hk : k ≤ s) :
    WkN (pN p G) u k = Subgroup.closure (fX L r xs '' {t | (fData s L r pa co).lv t = 1 ∧
      ((fData s L r pa co).df t).2.val < k}) ⊔ pN p G := by
  apply le_antisymm
  · refine WkN_le (pN p G) le_sup_right ?_
    intro a b hab hb
    refine (sup_le_sup_right (Subgroup.closure_mono ?_) _) (HS1 k hk a b hab hb)
    rintro _ ⟨i, ⟨hi, hik⟩, rfl⟩
    have hpos := fpos_lt (L := L) hL1 hi
    have hlv := fpos_lv (L := L) hL1 hi
    refine ⟨⟨_, hpos⟩, ⟨hlv, ?_⟩, fX_pos xs hL1 hi⟩
    obtain ⟨-, -, -, -, h2⟩ := flat_one (pa := pa) (co := co) H0 Hpa Hco ⟨_, hpos⟩ hlv
    show ((fDf L r pa co ⟨_, hpos⟩).2).val < k
    rw [h2]
    show co 1 (fOff (fLen L r) 1 + i - r 0) < k
    have e : fOff (fLen L r) 1 + i - r 0 = i := by
      rw [fOff_one]
      omega
    rw [e]
    exact hik
  · refine sup_le ?_ (le_WkN _ u k)
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ⟨ht1, htk⟩, rfl⟩
    have ht1' : fLv (fLen L r) L t.val = 1 := ht1
    have hd := fData_struct (L := L) H0 Hpa Hco H1
    have hlt : ((fDf L r pa co t).1).val < ((fDf L r pa co t).2).val :=
      Fin.lt_def.mp (hd.df_one t ht1)
    have hcs : ((fDf L r pa co t).2).val < s :=
      hd.df_core t (show 1 ≤ fLv (fLen L r) L t.val by omega)
    rw [fX_df H0 Hpa Hco Hx t (by omega), flat_core u H0 Hc0 _ (lt_trans hlt hcs),
      flat_core u H0 Hc0 _ hcs]
    exact comm_mem_WkN _ u hlt htk

lemma flat_blocks (p : ℕ) (u : ℕ → G) (hstrict : StrictChainN (pN p G) u s)
    (hWk : ∀ k ≤ s, WkN (pN p G) u k = Subgroup.closure (fX L r xs '' {t |
      (fData s L r pa co).lv t = 1 ∧ ((fData s L r pa co).df t).2.val < k}) ⊔ pN p G)
    {k : ℕ} (hk1 : 1 ≤ k) (hks : k < s) :
    ∃ t, (fData s L r pa co).lv t = 1 ∧ ((fData s L r pa co).df t).2.val = k := by
  by_contra hno
  push_neg at hno
  have hset : {t : Fin (fOff (fLen L r) (L + 1)) | (fData s L r pa co).lv t = 1 ∧
      ((fData s L r pa co).df t).2.val < k} = {t | (fData s L r pa co).lv t = 1 ∧
      ((fData s L r pa co).df t).2.val < k + 1} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      have h3 := hno t h1
      exact ⟨h1, by omega⟩
  apply hstrict (k + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel, hWk k (by omega), hWk (k + 1) (by omega), hset]
  rfl

end Flat

section NormalForm

variable {G : Type u} [Group G]

/-- Existence of Sims normal forms with `0 ≤ e < p ^ a` for the whole group. -/
theorem nf_exists_of [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (d : SimsData) (hd : d.Struct) (X : Fin d.n → G)
    (hgen : Subgroup.closure (Set.range X) = ⊤) (hlv : ∀ t, X t ∈ lcs G (d.lv t))
    (hdeep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {u | w ≤ d.lv u})) :
    ∀ g : G, ∃ e : Fin d.n → ℕ, (∀ t, e t < p ^ relOrd p d X t) ∧ g = nfw X e := by
  intro g
  have hnf := nfp_all d X hp hG hd hlv hdeep 0 d.n
  have hmem : g ∈ Subgroup.closure (X '' lset d 0 d.n) := by
    have hle : Subgroup.closure (Set.range X) ≤ Subgroup.closure (X '' lset d 0 d.n) := by
      apply Subgroup.closure_mono
      rintro _ ⟨v, rfl⟩
      refine ⟨v, ?_, rfl⟩
      rw [mem_lset]
      rcases Nat.eq_zero_or_pos (d.lv v) with h | h
      · exact Or.inr ⟨h.symm, v.isLt⟩
      · exact Or.inl h
    rw [hgen] at hle
    exact hle (Subgroup.mem_top g)
  obtain ⟨e, -, he, rfl⟩ := hnf g hmem
  exact ⟨e, he, rfl⟩

/-- Uniqueness of Sims normal forms (26): a counting argument, since
`|G| = p ^ (∑ a) = #{e : 0 ≤ e < p ^ a}`. -/
theorem nfw_unique [Finite G] {p : ℕ} (d : SimsData) (X : Fin d.n → G)
    (hcard : Nat.card G = p ^ (∑ t, d.a t))
    (hex : ∀ g : G, ∃ e : Fin d.n → ℕ, (∀ t, e t < p ^ d.a t) ∧ g = nfw X e)
    (e e' : Fin d.n → ℕ) (he : ∀ t, e t < p ^ d.a t) (he' : ∀ t, e' t < p ^ d.a t)
    (h : nfw X e = nfw X e') : e = e' := by
  have hsurj : Function.Surjective
      (fun f : (t : Fin d.n) → Fin (p ^ d.a t) => nfw X (fun t => (f t : ℕ))) := by
    intro g
    obtain ⟨e0, he0, rfl⟩ := hex g
    exact ⟨fun t => ⟨e0 t, he0 t⟩, rfl⟩
  have hc : Nat.card ((t : Fin d.n) → Fin (p ^ d.a t)) = Nat.card G := by
    rw [Nat.card_pi, hcard]
    simp only [Nat.card_fin]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  have hinj := (hsurj.bijective_of_nat_card_le (le_of_eq hc)).1
  have h2 := @hinj (fun t => ⟨e t, he t⟩) (fun t => ⟨e' t, he' t⟩) h
  funext t
  exact congrArg (fun f : (t : Fin d.n) → Fin (p ^ d.a t) => ((f t : Fin _) : ℕ)) h2

end NormalForm

section SimsCore

variable {G : Type u} [Group G]

/-- The Sims rank (17)/(20): the least number of generators of a subgroup `H` with
`γ₂ = [H, H] γ₃` (the inclusion `⊇` is automatic). -/
noncomputable def simsRank (G : Type u) [Group G] : ℕ :=
  sInf {k | ∃ u : Fin k → G,
    lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔ lcs G 2}

/-- A `Fin k`-tuple as a sequence (junk `1` beyond `k`). -/
def extF {k : ℕ} (x : Fin k → G) (i : ℕ) : G := if h : i < k then x ⟨i, h⟩ else 1

lemma extF_lt {k : ℕ} (x : Fin k → G) {i : ℕ} (h : i < k) : extF x i = x ⟨i, h⟩ := dif_pos h

lemma range_extF {k : ℕ} (x : Fin k → G) : Set.range x = extF x '' Set.Iio k := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, extF_lt x i.isLt⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, (extF_lt x hi).symm⟩

/-- The characterisation (20) of the Sims rank: no `t < s(G)` elements generate `γ₂` modulo
`γ₃ γ₂^p` by their commutators. -/
lemma core_min [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) {t : ℕ}
    (ht : t < simsRank G) (v : ℕ → G) :
    ¬ lcs G 1 ≤ ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔
      pN p G := by
  intro h
  have hB : (⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔
      lcs G 2).Normal := by
    refine normal_of_sandwich (n := 1) le_sup_right (sup_le ?_ (lcs_antitone (by omega)))
    exact Subgroup.commutator_le.mpr (fun x _ y _ => commElem_mem_lcs_one x y)
  have h2 : lcs G 1 ≤ ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔
      lcs G 2 := by
    refine frat_section hp hG (lcs G 1) _ ?_ ?_
    · intro x hx y hy
      exact Subgroup.mem_sup_right
        (lcs_antitone (D := G) (show 2 ≤ 1 + 1 + 1 by omega) (commElem_mem_lcs_add hx hy))
    · rw [sup_assoc]
      exact h
  have hle : simsRank G ≤ t := by
    apply Nat.sInf_le
    refine ⟨fun i => v i, ?_⟩
    have e : Set.range (fun i : Fin t => v i) = v '' Set.Iio t := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.isLt, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [e]
    exact h2
  omega

/-- A core whose commutators span `γ₂` modulo `γ₃ γ₂^p` spans it modulo `γ₃`. -/
lemma core_lieE [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) {s : ℕ}
    {u : ℕ → G} (hW : WkN (pN p G) u s = lcs G 1) :
    lcs G 1 ≤ Subgroup.closure (lieE s u 1) ⊔ lcs G 2 := by
  apply frat_layer hp hG 0 (lieE s u 1) (lieE_sub s u 0)
  refine (le_of_eq hW.symm).trans ?_
  refine WkN_le (pN p G) le_sup_right ?_
  intro a b hab hb
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(a, b), ⟨hab, hb⟩, rfl⟩)

/-- A Sims core with the strict flag of BNV Prop 5.2 (via `CoreFlag.core_flag`, with
`N = γ₃ γ₂^p` and `M = Φ(G)`). -/
theorem exists_core [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (hna : lcs G 1 ≠ ⊥) :
    2 ≤ simsRank G ∧ ∃ u : ℕ → G, StrictChainN (pN p G) u (simsRank G) ∧
      WkN (pN p G) u (simsRank G) = lcs G 1 ∧
      (∀ k < simsRank G, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ pPhi p G) ∧
      lcs G 1 ≤ ⁅Subgroup.closure (u '' Set.Iio (simsRank G)),
        Subgroup.closure (u '' Set.Iio (simsRank G))⁆ ⊔ lcs G 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent G := (IsPGroup.of_card hG).isNilpotent
  obtain ⟨N, hN⟩ : ∃ N, lcs G N = ⊥ := Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
  let e : Fin (Nat.card G) → G := (Finite.equivFin G).symm
  have he : Set.range e = Set.univ := Equiv.range_eq_univ _
  have hne : {k | ∃ u : Fin k → G,
      lcs G 1 ≤ ⁅Subgroup.closure (Set.range u), Subgroup.closure (Set.range u)⁆ ⊔
        lcs G 2}.Nonempty := by
    refine ⟨Nat.card G, e, ?_⟩
    rw [he, Subgroup.closure_univ]
    exact le_sup_left
  obtain ⟨x, hx⟩ : ∃ x : Fin (simsRank G) → G,
      lcs G 1 ≤ ⁅Subgroup.closure (Set.range x), Subgroup.closure (Set.range x)⁆ ⊔ lcs G 2 :=
    Nat.sInf_mem hne
  have hs : 2 ≤ simsRank G := by
    by_contra hlt
    have hk : simsRank G ≤ 1 := by omega
    have hHH : ⁅Subgroup.closure (Set.range x), Subgroup.closure (Set.range x)⁆ ≤ ⊥ := by
      refine commutator_closure_le ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
      rw [hij, commutatorElement_self]
      exact one_mem _
    have h12 : lcs G 1 ≤ lcs G 2 := le_trans hx (sup_le (le_trans hHH bot_le) le_rfl)
    have hall : ∀ n, lcs G 1 ≤ lcs G (n + 1) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        refine le_trans h12 ?_
        rw [lcs_succ 1, lcs_succ (n + 1)]
        exact Subgroup.commutator_mono ih le_rfl
    have hbot : lcs G 1 ≤ ⊥ := by
      rw [← hN]
      exact le_trans (hall N) (lcs_antitone (by omega))
    exact hna (le_bot_iff.mp hbot)
  have hcore0 : lcs G 1 ≤ ⁅Subgroup.closure (extF x '' Set.Iio (simsRank G)),
      Subgroup.closure (extF x '' Set.Iio (simsRank G))⁆ ⊔ pN p G := by
    rw [← range_extF]
    exact hx.trans (sup_le_sup_left (lcs_two_le_pN p) _)
  obtain ⟨u, -, hstrict, hW, hind, -, -⟩ := core_flag hp hG (pN p G) (pPhi p G)
    (lcs_two_le_pN p) (pN_le_lcs_one p) (lcs_succ_le_layK p 0) (pow_mem_pPhi p)
    (fun g m hm => commElem_mem_symm (commElem_pPhi_mem p hm g)) (simsRank G) (extF x) hcore0
    (fun t ht v _ => core_min hp hG ht v)
  have hcore := core_lieE hp hG hW
  have hcomm : Subgroup.closure (lieE (simsRank G) u 1) ≤
      ⁅Subgroup.closure (u '' Set.Iio (simsRank G)),
        Subgroup.closure (u '' Set.Iio (simsRank G))⁆ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨ab, hab, rfl⟩
    exact Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure ⟨ab.1, lt_trans hab.1 hab.2, rfl⟩)
      (Subgroup.subset_closure ⟨ab.2, hab.2, rfl⟩)
  exact ⟨hs, u, hstrict, hW, hind, hcore.trans (sup_le_sup_right hcomm _)⟩

end SimsCore

section SimsGenSet

variable {G : Type u} [Group G]

/-- The properties of the paper's Sims generating set `X` (Section 2.1), with flattened Sims
data `d`, core sequence `u` and layer lengths `r` (`r w = r_{w+1}` of the paper):
* the first `s` entries are the core, `d` is valid, bounded and realised by `X`, every relative
  order is `≥ 1` (so `n ≤ m`);
* the positions of weight `w + 1` are the interval `[fOff r w, fOff r w + r w)`, and
  `p ^ r_w |γ_{w+2} γ_{w+1}^p| = |γ_{w+1}|` (for `w = 0`: `|Φ(G)|`), i.e.
  `r_{w+1} = dim L_{w+1} / p L_{w+1} = d(G_{w+1}/G_{w+2})`;
* each layer is independent modulo its Frattini subgroup (so a minimum generating set of
  `G_i / G_{i+1}`) and generates `G_i` modulo `G_{i+1}`;
* weight 2 (`lv = 1`): `g_{2,j} = [g_{1,f(j)}, g_{1,k}]` with blocks sorted by `k`
  (`block_mono`), `f` injective on each block (`block_inj`), the flag
  `W_k = ⟨[u_a, u_b] : a < b < k⟩ γ₃ γ₂^p` spanned by the blocks `< k` (`flag`), and every block
  `k = 1, ..., s - 1` (0-based) nonempty (`block_ne`, the strictness `d_{k-1} < d_k`);
* unique Sims normal forms (26);
* `deep`: each `γ_{w+1}`, `w ≥ 1`, is generated by the generators of weight `≥ w + 1`;
  `nf_sub`: every element of a tail subgroup `⟨X u : u ∈ lset d w j⟩` has a bounded normal form
  supported on `lset d w j`; `n_eq`: the positions are exactly the layers `0, ..., c - 1` for
  some `c`;
* `w3`: the weight-3 index restriction of Section 2.1: a weight-3 generator
  `[g_{2,a}, g_{1,b}]` (0-based `a = (df t).1`, `b = (df t).2`) has `b ≤ co(a)`, the core index
  of `g_{2,a}`; in the paper's 1-based indexing this is `d_{b-1} < a ≤ r_2`. -/
structure SimsGen (p : ℕ) (u : ℕ → G) (d : SimsData) (X : Fin d.n → G) (r : ℕ → ℕ) : Prop where
  core : ∀ t : Fin d.n, t.val < d.s → X t = u t.val
  valid : d.Valid
  bounded : d.Bounded p
  realizes : SimsRealizes p d X
  a_pos : ∀ t, 1 ≤ d.a t
  n_le_sum : d.n ≤ ∑ t, d.a t
  layer_iff : ∀ (t : Fin d.n) (w : ℕ), d.lv t = w ↔ fOff r w ≤ t.val ∧ t.val < fOff r w + r w
  layer_card : ∀ w, p ^ r w * Nat.card (layK p G w) = Nat.card (lcs G w)
  layer_indep : ∀ t, X t ∉ Subgroup.closure (X '' {v | d.lv v = d.lv t ∧ v < t}) ⊔
    layK p G (d.lv t)
  layer_gen : ∀ w, lcs G w ≤ Subgroup.closure (X '' {t | d.lv t = w}) ⊔ lcs G (w + 1)
  block_mono : ∀ t t', d.lv t = 1 → d.lv t' = 1 → t ≤ t' → (d.df t).2 ≤ (d.df t').2
  block_inj : ∀ t t', d.lv t = 1 → d.lv t' = 1 → (d.df t).1 = (d.df t').1 →
    (d.df t).2 = (d.df t').2 → t = t'
  flag : ∀ k ≤ d.s, WkN (pN p G) u k =
    Subgroup.closure (X '' {t | d.lv t = 1 ∧ (d.df t).2.val < k}) ⊔ pN p G
  block_ne : ∀ k, 1 ≤ k → k < d.s → ∃ t, d.lv t = 1 ∧ (d.df t).2.val = k
  nf_exists : ∀ g : G, ∃ e : Fin d.n → ℕ, (∀ t, e t < p ^ d.a t) ∧ g = nfw X e
  nf_unique : ∀ e e' : Fin d.n → ℕ, (∀ t, e t < p ^ d.a t) → (∀ t, e' t < p ^ d.a t) →
    nfw X e = nfw X e' → e = e'
  deep : ∀ w, 1 ≤ w → lcs G w ≤ Subgroup.closure (X '' {t | w ≤ d.lv t})
  nf_sub : ∀ (w j : ℕ), ∀ z ∈ Subgroup.closure (X '' lset d w j), ∃ e : Fin d.n → ℕ,
    (∀ t, e t ≠ 0 → t ∈ lset d w j) ∧ (∀ t, e t < p ^ d.a t) ∧ z = nfw X e
  n_eq : ∃ c, d.n = fOff r c
  w3 : ∀ t, d.lv t = 2 → (d.df t).2.val ≤ (d.df (d.df t).1).2.val

/-- Assembly: the flattened layers form a Sims generating set. -/
theorem flat_final [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) {s L : ℕ}
    {r : ℕ → ℕ} {xs : ℕ → ℕ → G} {pa co : ℕ → ℕ → ℕ} (u : ℕ → G)
    (H0 : s ≤ r 0) (Hpa : ∀ w i, i < r (w + 1) → pa (w + 1) i < r w)
    (Hco : ∀ w i, i < r (w + 1) → co (w + 1) i < s) (H1 : ∀ i, i < r 1 → pa 1 i < co 1 i)
    (Hx : ∀ w i, i < r (w + 1) → xs (w + 1) i = ⁅xs w (pa (w + 1) i), xs 0 (co (w + 1) i)⁆)
    (Hc0 : ∀ i < s, xs 0 i = u i) (h0 : Subgroup.closure (xs 0 '' Set.Iio (r 0)) = ⊤)
    (HU : ∀ w, w + 1 ≤ L → lcs G (w + 1) ≤
      Subgroup.closure (xs (w + 1) '' Set.Iio (r (w + 1))) ⊔ lcs G (w + 2))
    (HL : lcs G (L + 1) = ⊥) (hL1 : 1 ≤ L)
    (Hind : ∀ w i, i < r w → xs w i ∉ Subgroup.closure (xs w '' Set.Iio i) ⊔ layK p G w)
    (Hcard : ∀ w ≤ L, p ^ r w * Nat.card (layK p G w) = Nat.card (lcs G w))
    (HS1 : ∀ k ≤ s, ∀ a b, a < b → b < k →
      ⁅u a, u b⁆ ∈ Subgroup.closure (xs 1 '' {i | i < r 1 ∧ co 1 i < k}) ⊔ pN p G)
    (Hmono : ∀ i i', i ≤ i' → i' < r 1 → co 1 i ≤ co 1 i')
    (Hinj : ∀ i i', i < r 1 → i' < r 1 → pa 1 i = pa 1 i' → co 1 i = co 1 i' → i = i')
    (hstrict : StrictChainN (pN p G) u s) (Hw3 : ∀ i, i < r 2 → co 2 i ≤ co 1 (pa 2 i)) :
    ∃ (d : SimsData) (X : Fin d.n → G), d.s = s ∧ SimsGen p u d X (fLen L r) := by
  have hd := fData_struct (s := s) (L := L) H0 Hpa Hco H1
  have hdf : ∀ t, 1 ≤ (fData s L r pa co).lv t → fX L r xs t =
      ⁅fX L r xs ((fData s L r pa co).df t).1, fX L r xs ((fData s L r pa co).df t).2⁆ :=
    fun t ht => fX_df H0 Hpa Hco Hx t ht
  have hgen := flat_gen (L := L) h0
  have hdeep := flat_deep (s := s) (pa := pa) (co := co) H0 Hpa Hco H1 Hx h0 HU HL
  have hlv := lv_mem_lcs (fData s L r pa co) hd (fX L r xs) hdf
  obtain ⟨b, c, hv, hb, hr⟩ :=
    exists_arrays (fData s L r pa co) (fX L r xs) hp hG hd hgen hdf hdeep
  have hind := flat_indep (s := s) (L := L) (pa := pa) (co := co) p Hind
  have ha1 : ∀ t, 1 ≤ relOrd p (fData s L r pa co) (fX L r xs) t := by
    intro t
    by_contra h0'
    have hz : relOrd p (fData s L r pa co) (fX L r xs) t = 0 := by omega
    have hmem := relOrd_spec (fData s L r pa co) (fX L r xs) hG t
    rw [hz, pow_zero, pow_one] at hmem
    apply hind t
    refine (Subgroup.closure_le _).mpr ?_ hmem
    rintro _ ⟨v, hv', rfl⟩
    rcases (mem_lset (fData s L r pa co)).mp hv' with h | ⟨h1, h2⟩
    · exact Subgroup.mem_sup_right (lcs_succ_le_layK p _
        (lcs_antitone (D := G) (show (fData s L r pa co).lv t + 1 ≤ (fData s L r pa co).lv v
          from h) (hlv v)))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨v, ⟨h1.symm, Fin.lt_def.mpr h2⟩, rfl⟩)
  have hWk : ∀ k ≤ s, WkN (pN p G) u k = Subgroup.closure (fX L r xs '' {t |
      (fData s L r pa co).lv t = 1 ∧ ((fData s L r pa co).df t).2.val < k}) ⊔ pN p G :=
    fun k hk => flat_Wk p u H0 Hpa Hco H1 Hx Hc0 hL1 HS1 hk
  have hex := nf_exists_of hp hG (fData s L r pa co) hd (fX L r xs) hgen hlv hdeep
  have hnfp := nfp_all (fData s L r pa co) (fX L r xs) hp hG hd hlv hdeep
  have hw3 : ∀ t : Fin (fData s L r pa co).n, (fData s L r pa co).lv t = 2 →
      ((fData s L r pa co).df t).2.val ≤
        ((fData s L r pa co).df ((fData s L r pa co).df t).1).2.val := by
    intro t ht
    have ht' : fLv (fLen L r) L t.val = 1 + 1 := ht
    obtain ⟨-, hi, h1, h2⟩ := fDf_vals (L := L) (pa := pa) (co := co) H0 Hpa Hco t ht'
    have hl1 : (fData s L r pa co).lv ((fData s L r pa co).df t).1 + 1 =
        (fData s L r pa co).lv t := hd.df_lv t (by omega)
    have ht1 : fLv (fLen L r) L ((fDf L r pa co t).1).val = 0 + 1 := by
      have e : (fData s L r pa co).lv ((fData s L r pa co).df t).1 = 1 := by omega
      exact e
    obtain ⟨-, -, -, h4⟩ := fDf_vals (L := L) (pa := pa) (co := co) H0 Hpa Hco _ ht1
    have h5 : ((fDf L r pa co t).1).val - fOff (fLen L r) (0 + 1) =
        pa (1 + 1) (t.val - fOff (fLen L r) (1 + 1)) := by
      rw [h1]
      exact Nat.add_sub_cancel_left _ _
    show ((fDf L r pa co t).2).val ≤ ((fDf L r pa co (fDf L r pa co t).1).2).val
    rw [h4, h2, h5]
    exact Hw3 _ hi
  refine ⟨⟨(fData s L r pa co).n, (fData s L r pa co).s, (fData s L r pa co).lv,
    (fData s L r pa co).df, relOrd p (fData s L r pa co) (fX L r xs), b, c⟩, fX L r xs, rfl, ?_⟩
  refine
    { core := fun t ht => flat_core u H0 Hc0 t ht
      valid := hv
      bounded := hb
      realizes := hr
      a_pos := ha1
      n_le_sum := ?_
      layer_iff := ?_
      layer_card := ?_
      layer_indep := hind
      layer_gen := ?_
      block_mono := fun t t' ht ht' htt => flat_mono H0 Hpa Hco Hmono t t' ht ht' htt
      block_inj := fun t t' ht ht' h1 h2 => flat_inj H0 Hpa Hco Hinj t t' ht ht' h1 h2
      flag := hWk
      block_ne := fun k hk1 hks => flat_blocks p u hstrict hWk hk1 hks
      nf_exists := hex
      nf_unique := fun e e' he he' h => nfw_unique _ (fX L r xs) hr.card hex e e' he he' h
      deep := hdeep
      nf_sub := fun w j => hnfp w j
      n_eq := ⟨L + 1, rfl⟩
      w3 := hw3 }
  · calc fOff (fLen L r) (L + 1) = ∑ _t : Fin (fOff (fLen L r) (L + 1)), 1 := by simp
      _ ≤ ∑ t, relOrd p (fData s L r pa co) (fX L r xs) t :=
        Finset.sum_le_sum (fun t _ => ha1 t)
  · intro t w
    constructor
    · intro h
      have h' : fLv (fLen L r) L t.val = w := h
      obtain ⟨h1, h2, -⟩ := fLv_spec (ℓ := fLen L r) t.isLt
      rw [h'] at h1 h2
      rw [fOff_succ] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hw : w ≤ L
      · exact fLv_eq hw h1 (lt_of_lt_of_eq h2 (fOff_succ (fLen L r) w).symm)
      · exfalso
        have h3 := fOff_mono (fLen L r) (show L + 1 ≤ w by omega)
        have h4 : t.val < fOff (fLen L r) (L + 1) := t.isLt
        omega
  · intro w
    by_cases hw : w ≤ L
    · rw [fLen_of_le hw]
      exact Hcard w hw
    · rw [fLen_of_gt hw, pow_zero, one_mul]
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      have h1 : lcs G (w' + 1) = ⊥ := le_bot_iff.mp
        ((lcs_antitone (D := G) (show L + 1 ≤ w' + 1 by omega)).trans (le_of_eq HL))
      have h2 : layK p G (w' + 1) = ⊥ := le_bot_iff.mp ((layK_le_lcs p w').trans (le_of_eq h1))
      rw [h1, h2]
  · intro w
    rcases w with _ | w
    · rw [lcs_zero, ← h0]
      refine le_sup_of_le_left (Subgroup.closure_mono ?_)
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨⟨_, fpos_lt (Nat.zero_le L) hi⟩, fpos_lv (Nat.zero_le L) hi,
        fX_pos xs (Nat.zero_le L) hi⟩
    · exact flat_lev (s := s) (pa := pa) (co := co) HU HL w

/-- The layer data of the construction. -/
noncomputable def gR [Finite G] (p s : ℕ) (u : ℕ → G) (w : ℕ) : ℕ :=
  (sLay p s u (lay0 p s u) w).r

/-- The entries of the layers. -/
noncomputable def gXs [Finite G] (p s : ℕ) (u : ℕ → G) (w i : ℕ) : G :=
  (sLay p s u (lay0 p s u) w).x i

/-- The parent indices of the layers. -/
noncomputable def gPa [Finite G] (p s : ℕ) (u : ℕ → G) (w i : ℕ) : ℕ :=
  (sLay p s u (lay0 p s u) w).par i

/-- The core indices of the layers. -/
noncomputable def gCo [Finite G] (p s : ℕ) (u : ℕ → G) (w i : ℕ) : ℕ :=
  (sLay p s u (lay0 p s u) w).cor i

lemma sLay_one_cor (p s : ℕ) (u : ℕ → G) (L0 : SLay G) (i : ℕ) :
    (sLay p s u L0 1).cor i = genum (gsel (cVal s u 0 L0) (layK p G 1) (cN s 0 L0)) i / s := by
  rw [sLay_one]
  exact cCor_zero

lemma sLay_one_par (p s : ℕ) (u : ℕ → G) (L0 : SLay G) (i : ℕ) :
    (sLay p s u L0 1).par i = genum (gsel (cVal s u 0 L0) (layK p G 1) (cN s 0 L0)) i % s := by
  rw [sLay_one]
  exact cPar_zero

lemma sLay_one_cor_mono (p s : ℕ) (u : ℕ → G) (L0 : SLay G) {i i' : ℕ} (h : i ≤ i')
    (hi' : i' < (sLay p s u L0 1).r) : (sLay p s u L0 1).cor i ≤ (sLay p s u L0 1).cor i' := by
  rw [sLay_one_cor, sLay_one_cor]
  have h1 : i' < (gsel (cVal s u 0 L0) (layK p G 1) (cN s 0 L0)).card := hi'
  exact Nat.div_le_div_right (genum_le _ h h1)

lemma sLay_one_inj (p s : ℕ) (u : ℕ → G) (L0 : SLay G) {i i' : ℕ}
    (hi : i < (sLay p s u L0 1).r) (hi' : i' < (sLay p s u L0 1).r)
    (hp : (sLay p s u L0 1).par i = (sLay p s u L0 1).par i')
    (hc : (sLay p s u L0 1).cor i = (sLay p s u L0 1).cor i') : i = i' := by
  rw [sLay_one_par, sLay_one_par] at hp
  rw [sLay_one_cor, sLay_one_cor] at hc
  have h1 := Nat.div_add_mod (genum (gsel (cVal s u 0 L0) (layK p G 1) (cN s 0 L0)) i) s
  have h2 := Nat.div_add_mod (genum (gsel (cVal s u 0 L0) (layK p G 1) (cN s 0 L0)) i') s
  rw [hp, hc] at h1
  exact genum_inj _ hi hi' (h1.symm.trans h2)

/-- The construction from a core with the strict flag. -/
theorem sims_gen_of_core [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) {s : ℕ}
    (hs : 2 ≤ s) (u : ℕ → G) (hstrict : StrictChainN (pN p G) u s)
    (hW : WkN (pN p G) u s = lcs G 1)
    (hind : ∀ k < s, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ pPhi p G) :
    ∃ (d : SimsData) (X : Fin d.n → G) (r : ℕ → ℕ), d.s = s ∧ d.n ≤ m ∧
      r 0 = Group.rank G ∧ SimsGen p u d X r := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G := IsPGroup.of_card hG
  have : Group.IsNilpotent G := hpg.isNilpotent
  have hs0 : 0 < s := by omega
  have hx0 : ∀ a < s, (lay0 p s u).x a = u a := fun a ha => lay0_x_lt p s u ha
  have hr0 : s ≤ (lay0 p s u).r := Nat.le_add_right s _
  have hgen0 : Subgroup.closure ((lay0 p s u).x '' Set.Iio (lay0 p s u).r) = ⊤ := by
    apply closure_eq_top_of_sup_frattini
    rw [frattini_eq_pPhi hpg, eq_top_iff]
    intro g _
    exact lay0_span p s u g
  have hcore := core_lieE hp hG hW
  have hU := sLay_lcs p s u (lay0 p s u) hp hG hs0 hx0 (by rw [hgen0, top_sup_eq]) hcore hr0
  obtain ⟨N, hN⟩ : ∃ N, lcs G N = ⊥ := Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
  have hL : lcs G (N + 1 + 1) = ⊥ :=
    le_bot_iff.mp (hN ▸ lcs_antitone (D := G) (show N ≤ N + 1 + 1 by omega))
  have Hind : ∀ w i, i < gR p s u w →
      gXs p s u w i ∉ Subgroup.closure (gXs p s u w '' Set.Iio i) ⊔ layK p G w := by
    intro w i hi
    rcases w with _ | w
    · exact lay0_indep p s u hind hi
    · exact sLay_indep p s u (lay0 p s u) w hi
  have Heq : ∀ w, Subgroup.closure (gXs p s u w '' Set.Iio (gR p s u w)) ⊔ layK p G w =
      lcs G w := by
    intro w
    rcases w with _ | w
    · show Subgroup.closure ((lay0 p s u).x '' Set.Iio (lay0 p s u).r) ⊔ pPhi p G = lcs G 0
      rw [hgen0, top_sup_eq, lcs_zero]
    · apply le_antisymm
      · refine sup_le ?_ (layK_le_lcs p w)
        rw [Subgroup.closure_le]
        rintro _ ⟨i, -, rfl⟩
        exact sLay_mem p s u (lay0 p s u) (w + 1) i
      · exact (hU w).trans (sup_le_sup_left (lcs_succ_le_layK p (w + 1)) _)
  have Hcard : ∀ w, p ^ gR p s u w * Nat.card (layK p G w) = Nat.card (lcs G w) := by
    intro w
    have hmem : ∀ i, gXs p s u w i ∈ lcs G w := fun i => sLay_mem p s u (lay0 p s u) w i
    have hN' : ∀ j, (Subgroup.closure (gXs p s u w '' Set.Iio j) ⊔ layK p G w).Normal :=
      fun j => layK_normal_sup p w _ (by rintro _ ⟨i, -, rfl⟩; exact hmem i)
    have h1 := card_growth hp hG (layK p G w) (v := gXs p s u w) (gR p s u w)
      (fun k hk => Hind w k hk)
    have h2 := card_closure_sup_le_of hp.pos (layK p G w) (gXs p s u w) hN'
      (fun j => pow_mem_layK p w _ (hmem j)) (gR p s u w)
    rw [Heq w] at h1 h2
    exact le_antisymm h1 h2
  have Hrank : gR p s u 0 = Group.rank G := by
    have h1 : p ^ gR p s u 0 * Nat.card (pPhi p G) = Nat.card (lcs G 0) := Hcard 0
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini G)
    rw [card_quot_frattini hpg, frattini_eq_pPhi hpg] at h2
    have h3 : Nat.card (lcs G 0) = Nat.card G := by rw [lcs_zero, Subgroup.card_top]
    have h4 : 0 < Nat.card (pPhi p G) := Nat.card_pos
    have h6 : p ^ gR p s u 0 * Nat.card (pPhi p G) = p ^ Group.rank G * Nat.card (pPhi p G) := by
      rw [← h2, ← h3, h1]
    exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_right h4 h6)
  have Hpa : ∀ w i, i < gR p s u (w + 1) → gPa p s u (w + 1) i < gR p s u w :=
    fun w i hi => (sLay_gen p s u (lay0 p s u) hs0 hr0 w hi).1
  have Hco : ∀ w i, i < gR p s u (w + 1) → gCo p s u (w + 1) i < s :=
    fun w i hi => (sLay_gen p s u (lay0 p s u) hs0 hr0 w hi).2.1
  have H1 : ∀ i, i < gR p s u 1 → gPa p s u 1 i < gCo p s u 1 i :=
    fun i hi => (sLay_gen p s u (lay0 p s u) hs0 hr0 0 hi).2.2.1 rfl
  have Hx : ∀ w i, i < gR p s u (w + 1) → gXs p s u (w + 1) i =
      ⁅gXs p s u w (gPa p s u (w + 1) i), gXs p s u 0 (gCo p s u (w + 1) i)⁆ := by
    intro w i hi
    obtain ⟨-, hc, -, he⟩ := sLay_gen p s u (lay0 p s u) hs0 hr0 w hi
    have e0 : gXs p s u 0 (gCo p s u (w + 1) i) = u (gCo p s u (w + 1) i) := lay0_x_lt p s u hc
    rw [e0]
    exact he
  have HS1 : ∀ k ≤ s, ∀ a b, a < b → b < k → ⁅u a, u b⁆ ∈
      Subgroup.closure (gXs p s u 1 '' {i | i < gR p s u 1 ∧ gCo p s u 1 i < k}) ⊔ pN p G :=
    fun k hk a b hab hb => sLay_span_one p s u (lay0 p s u) hs0 hx0 hk hab hb
  have Hmono : ∀ i i', i ≤ i' → i' < gR p s u 1 → gCo p s u 1 i ≤ gCo p s u 1 i' :=
    fun i i' h hi' => sLay_one_cor_mono p s u (lay0 p s u) h hi'
  have Hinj : ∀ i i', i < gR p s u 1 → i' < gR p s u 1 → gPa p s u 1 i = gPa p s u 1 i' →
      gCo p s u 1 i = gCo p s u 1 i' → i = i' :=
    fun i i' hi hi' hp' hc => sLay_one_inj p s u (lay0 p s u) hi hi' hp' hc
  have Hw3 : ∀ i, i < gR p s u 2 → gCo p s u 2 i ≤ gCo p s u 1 (gPa p s u 2 i) :=
    fun i hi => sLay_w3 p s u (lay0 p s u) hi
  obtain ⟨d, X, hds, hspec⟩ := flat_final (L := N + 1) (r := gR p s u) (xs := gXs p s u)
    (pa := gPa p s u) (co := gCo p s u) hp hG u hr0 Hpa Hco H1 Hx hx0 hgen0 (fun w _ => hU w) hL
    (by omega) Hind (fun w _ => Hcard w) HS1 Hmono Hinj hstrict Hw3
  refine ⟨d, X, fLen (N + 1) (gR p s u), hds, ?_, ?_, hspec⟩
  · have h1 := hspec.realizes.card
    rw [hG] at h1
    have h2 := Nat.pow_right_injective hp.two_le h1
    rw [h2]
    exact hspec.n_le_sum
  · rw [fLen_of_le (Nat.zero_le _)]
    exact Hrank

/-- Section 2.1 (existence of the Sims generating set). Every nonabelian group `G` of order
`p ^ m` has a Sims core `u_0, ..., u_{s-1}` (`s = s(G) ≥ 2`) carrying the strict flag of BNV
Prop 5.2, and an ordered generating tuple `X` with flattened Sims data `d` and layer lengths
`r` (`r 0 = r_1 = d(G)`) satisfying all the properties of `SimsGen`: minimum generating sets
of the layers, the block structure `(d_k, f)` of weight 2, relative orders `≥ 1` (so `n ≤ m`),
valid bounded relation arrays realised by `X`, and unique normal forms. -/
theorem exists_sims_gen [Finite G] {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m)
    (hna : lcs G 1 ≠ ⊥) :
    ∃ (u : ℕ → G) (d : SimsData) (X : Fin d.n → G) (r : ℕ → ℕ),
      2 ≤ simsRank G ∧ d.s = simsRank G ∧
      lcs G 1 ≤ ⁅Subgroup.closure (u '' Set.Iio d.s), Subgroup.closure (u '' Set.Iio d.s)⁆ ⊔
        lcs G 2 ∧
      StrictChainN (pN p G) u d.s ∧ WkN (pN p G) u d.s = lcs G 1 ∧
      (∀ k < d.s, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ pPhi p G) ∧
      d.n ≤ m ∧ r 0 = Group.rank G ∧ SimsGen p u d X r := by
  obtain ⟨hs2, u, hstrict, hW, hind, hcore⟩ := exists_core hp hG hna
  obtain ⟨d, X, r, hds, hnm, hrank, hspec⟩ := sims_gen_of_core hp hG hs2 u hstrict hW hind
  refine ⟨u, d, X, r, hs2, hds, ?_, ?_, ?_, ?_, hnm, hrank, hspec⟩
  · rw [hds]
    exact hcore
  · rw [hds]
    exact hstrict
  · rw [hds]
    exact hW
  · rw [hds]
    exact hind

end SimsGenSet

end OMA.SimsLite
