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

Commutators are Mathlib's `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`. -/

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
agree wherever `d.Rec` holds). Then `G ≅ G'`. -/
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
    rw [map_mul, (hc a ha b hb : Commute _ _).mul_pow]
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
layer 1). -/
def cVal (s : ℕ) (u : ℕ → G) (w : ℕ) (L : SLay G) (j : ℕ) : G :=
  if w = 0 ∧ ¬ cPar s w j < cCor s w j then 1 else ⁅L.x (cPar s w j), u (cCor s w j)⁆

/-- Number of candidates of layer `w + 1`. -/
def cN (s w : ℕ) (L : SLay G) : ℕ := if w = 0 then s * s else L.r * s

lemma cPar_zero {s j : ℕ} : cPar s 0 j = j % s := if_pos rfl
lemma cCor_zero {s j : ℕ} : cCor s 0 j = j / s := if_pos rfl
lemma cN_zero {s : ℕ} {L : SLay G} : cN s 0 L = s * s := if_pos rfl
lemma cPar_ne {s w j : ℕ} (hw : w ≠ 0) : cPar s w j = j / s := if_neg hw
lemma cCor_ne {s w j : ℕ} (hw : w ≠ 0) : cCor s w j = j % s := if_neg hw
lemma cN_ne {s w : ℕ} {L : SLay G} (hw : w ≠ 0) : cN s w L = L.r * s := if_neg hw

lemma cVal_succ (s : ℕ) (u : ℕ → G) (w : ℕ) (L : SLay G) (j : ℕ) :
    cVal s u (w + 1) L j = ⁅L.x (j / s), u (j % s)⁆ := by
  unfold cVal
  rw [if_neg (show ¬ (w + 1 = 0 ∧ ¬ cPar s (w + 1) j < cCor s (w + 1) j) from
    fun h => absurd h.1 (by omega)), cPar_ne (show w + 1 ≠ 0 by omega),
    cCor_ne (show w + 1 ≠ 0 by omega)]

lemma cVal_zero_of_lt (s : ℕ) (u : ℕ → G) (L : SLay G) {j : ℕ} (h : j % s < j / s) :
    cVal s u 0 L j = ⁅L.x (j % s), u (j / s)⁆ := by
  unfold cVal
  rw [if_neg (show ¬ ((0 : ℕ) = 0 ∧ ¬ cPar s 0 j < cCor s 0 j) from
    fun h' => h'.2 (by rw [cPar_zero, cCor_zero]; exact h)), cPar_zero, cCor_zero]

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
  have hcv : ¬ (w = 0 ∧ ¬ cPar s w j < cCor s w j) := by
    intro hc
    apply hne
    unfold cVal
    rw [if_pos hc]
  have hval : cVal s u w L j = ⁅L.x (cPar s w j), u (cCor s w j)⁆ := by
    unfold cVal
    rw [if_neg hcv]
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
    (hb : b < s) :
    ⁅(sLay p s u L0 (w + 1)).x a, u b⁆ ∈ Subgroup.closure ((sLay p s u L0 (w + 1 + 1)).x ''
      Set.Iio (sLay p s u L0 (w + 1 + 1)).r) ⊔ layK p G (w + 1 + 1) := by
  have hj : a * s + b < cN s (w + 1) (sLay p s u L0 (w + 1)) := by
    rw [cN_ne (show w + 1 ≠ 0 by omega)]
    exact slot_lt ha hb
  have hv : cVal s u (w + 1) (sLay p s u L0 (w + 1)) (a * s + b) =
      ⁅(sLay p s u L0 (w + 1)).x a, u b⁆ := by
    rw [cVal_succ, slot_div hb, slot_mod hb]
  rw [← hv, sLay_succ p s u L0 (w + 1)]
  exact gLay_span_all _ _ _ _ _ hj

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
    (gLay_span _ _ _ _ _ hJ hj)
  rintro _ ⟨i, ⟨hi, hik⟩, rfl⟩
  refine ⟨i, ⟨hi, ?_⟩, rfl⟩
  show cCor s 0 (genum _ i) < k
  rw [cCor_zero]
  exact (Nat.div_lt_iff_lt_mul hs).mpr hik

/-- The layers generate the lower central series: `γ_{w+2} ≤ ⟨layer w + 1⟩ γ_{w+3}`. -/
theorem sLay_lcs [Finite G] {m : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ m) (hs : 0 < s)
    (hx0 : ∀ a < s, L0.x a = u a)
    (hL0 : Subgroup.closure (L0.x '' Set.Iio L0.r) ⊔ lcs G 1 = ⊤)
    (hcore : lcs G 1 ≤ Subgroup.closure (lieE s u 1) ⊔ lcs G 2) :
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
        exact mem_zn.mpr (commElem_mem_symm (sLay_span_succ p s u L0 hs w ha hb))
      · intro g hg
        exact mem_zn.mpr (Subgroup.mem_sup_right
          ((lcs_succ_le_layK p (w + 1 + 1)) (commElem_mem_lcs_succ' (u b) hg)))
    exact commElem_mem_symm (mem_zn.mp (hle hy1))

end Layers2

end OMA.SimsLite
