import H2Dev.Strict

/-! BNV Prop 5.2 (strict flag of a minimal core), group-level form.

Setting: `G` a group of order `p ^ n`, two subgroups `N` and `M` with
* `γ_3 ≤ N ≤ γ_2` (in the application `N = γ_3 γ_2^p`, so that `γ_2 / N = W`);
* `γ_2 ≤ M`, `g ^ p ∈ M` for all `g`, and `⁅g, m⁆ ∈ N` for `m ∈ M`
  (in the application `M = G^p γ_2 = Φ(G)`, so that `G / M = V`).
A core is `H = ⟨x_0, ..., x_{s-1}⟩` with `γ_2 ≤ ⁅H, H⁆ N`; it is minimal when no subgroup
`⟨v_0, ..., v_{t-1}⟩ ≤ H` with `t < s` is a core.

Main result `core_flag`: a minimal core has elements `u_0, ..., u_{s-1}` in `H` with
* the strict flag `N = W_1 < W_2 < ... < W_s = γ_2`, `W_k = ⟨⁅u_a, u_b⁆ : a < b < k⟩ N`;
* `u_k ∉ ⟨u_0, ..., u_{k-1}⟩ M` (independence in `V`), and `⟨u_0, ..., u_{s-1}⟩ M = H M`;
* `p ^ (k - 1) |N| ≤ |W_k|` (so `d_k ≥ k - 1`, Lemma 2.3 / BNV Cor 5.3).
The proof is the exchange argument of the library's S1, run inside `H`, plus a counting
bound showing that strict chains in `H` have length at most `s`. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section CoreFlag

variable {G : Type u} [Group G]

/-! Strict chains relative to a base subgroup `N`. -/

/-- `W_k(u) = ⟨⁅u a, u b⁆ : a < b < k⟩ N`. -/
def WkN (N : Subgroup G) (u : ℕ → G) (k : ℕ) : Subgroup G :=
  Subgroup.closure {x | ∃ a b, a < b ∧ b < k ∧ x = ⁅u a, u b⁆} ⊔ N

/-- `u` is strict of length `t` relative to `N`. -/
def StrictChainN (N : Subgroup G) (u : ℕ → G) (t : ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ t → WkN N u (k - 1) ≠ WkN N u k

lemma Wk_eq_WkN (u : ℕ → G) (k : ℕ) : Wk u k = WkN (lcs G 2) u k := rfl

lemma strictChain_iff_N (u : ℕ → G) (t : ℕ) : StrictChain u t ↔ StrictChainN (lcs G 2) u t :=
  Iff.rfl

lemma le_WkN (N : Subgroup G) (u : ℕ → G) (k : ℕ) : N ≤ WkN N u k := by
  unfold WkN
  exact le_sup_right

lemma comm_mem_WkN (N : Subgroup G) (u : ℕ → G) {a b k : ℕ} (hab : a < b) (hbk : b < k) :
    ⁅u a, u b⁆ ∈ WkN N u k := by
  unfold WkN
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, b, hab, hbk, rfl⟩)

lemma WkN_le (N : Subgroup G) {u : ℕ → G} {k : ℕ} {H : Subgroup G} (h3 : N ≤ H)
    (h : ∀ a b, a < b → b < k → ⁅u a, u b⁆ ∈ H) : WkN N u k ≤ H := by
  unfold WkN
  refine sup_le ?_ h3
  rw [Subgroup.closure_le]
  rintro _ ⟨a, b, hab, hbk, rfl⟩
  exact h a b hab hbk

lemma WkN_mono (N : Subgroup G) (u : ℕ → G) {k l : ℕ} (hkl : k ≤ l) :
    WkN N u k ≤ WkN N u l :=
  WkN_le N (le_WkN N u l) fun a b hab hbk => comm_mem_WkN N u hab (by omega)

lemma WkN_le_lcs_one (N : Subgroup G) (hN2 : N ≤ lcs G 1) (u : ℕ → G) (k : ℕ) :
    WkN N u k ≤ lcs G 1 :=
  WkN_le N hN2 fun a b _ _ => commElem_mem_lcs_succ (n := 0) (Subgroup.mem_top (u a)) (u b)

lemma WkN_normal (N : Subgroup G) (hN3 : lcs G 2 ≤ N) (hN2 : N ≤ lcs G 1) (u : ℕ → G)
    (k : ℕ) : (WkN N u k).Normal :=
  normal_of_sandwich (n := 1) (hN3.trans (le_WkN N u k)) (WkN_le_lcs_one N hN2 u k)

lemma WkN_congr_le (N : Subgroup G) {u v : ℕ → G} {k : ℕ} (h : ∀ i < k, u i = v i) :
    WkN N u k ≤ WkN N v k :=
  WkN_le N (le_WkN N v k) fun a b hab hbk => by
    rw [h a (by omega), h b hbk]
    exact comm_mem_WkN N v hab hbk

lemma WkN_congr (N : Subgroup G) {u v : ℕ → G} {k : ℕ} (h : ∀ i < k, u i = v i) :
    WkN N u k = WkN N v k :=
  le_antisymm (WkN_congr_le N h) (WkN_congr_le N fun i hi => (h i hi).symm)

lemma WkN_succ_le (N : Subgroup G) {u : ℕ → G} {k : ℕ} (h : ∀ a < k, ⁅u a, u k⁆ ∈ WkN N u k) :
    WkN N u (k + 1) ≤ WkN N u k := by
  refine WkN_le N (le_WkN N u k) ?_
  intro a b hab hbk
  by_cases hb : b < k
  · exact comm_mem_WkN N u hab hb
  · rw [show b = k by omega]
    exact h a (by omega)

lemma WkN_exists_not_mem_of_ne (N : Subgroup G) {u : ℕ → G} {k : ℕ}
    (h : WkN N u k ≠ WkN N u (k + 1)) : ∃ a < k, ⁅u a, u k⁆ ∉ WkN N u k := by
  by_contra hc
  apply h
  refine le_antisymm (WkN_mono N u (show k ≤ k + 1 by omega)) (WkN_succ_le N ?_)
  intro a ha
  by_contra hn
  exact hc ⟨a, ha, hn⟩

lemma WkN_le_core (N : Subgroup G) (v : ℕ → G) (t : ℕ) :
    WkN N v t ≤ ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔ N :=
  WkN_le N le_sup_right fun a b hab hbt =>
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure ⟨a, Set.mem_Iio.mpr (by omega), rfl⟩)
      (Subgroup.subset_closure ⟨b, Set.mem_Iio.mpr hbt, rfl⟩))

lemma strictChainN_of (N : Subgroup G) {u : ℕ → G} {t : ℕ}
    (h : ∀ k, 1 ≤ k → k + 1 ≤ t → WkN N u k ≠ WkN N u (k + 1)) : StrictChainN N u t := by
  intro k hk hkt
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact h j (by omega) hkt

lemma StrictChainN.ne_succ {N : Subgroup G} {u : ℕ → G} {t : ℕ} (h : StrictChainN N u t) {k : ℕ}
    (hk : 1 ≤ k) (hkt : k + 1 ≤ t) : WkN N u k ≠ WkN N u (k + 1) := by
  have := h (k + 1) (by omega) hkt
  rw [Nat.add_sub_cancel] at this
  exact this

lemma strictChainN_zero (N : Subgroup G) (u : ℕ → G) : StrictChainN N u 0 := by
  intro k hk hkt
  omega

lemma WkN_ne_of_mem {A B : Subgroup G} {z : G} (hB : z ∈ B) (hA : z ∉ A) : A ≠ B := by
  rintro rfl
  exact hA hB

/-- The chain `(x, y)` is strict of length 2 when `⁅x, y⁆ ∉ N`. -/
lemma strictN_two (N : Subgroup G) {u : ℕ → G} {x y : G} (e0 : u 0 = x) (e1 : u 1 = y)
    (hxy : ⁅x, y⁆ ∉ N) : StrictChainN N u 2 := by
  apply strictChainN_of
  intro k hk hkt
  rw [show k = 1 by omega]
  have hm : ⁅u 0, u 1⁆ ∈ WkN N u (1 + 1) := comm_mem_WkN N u (by norm_num) (by norm_num)
  have h1 : WkN N u 1 ≤ N := WkN_le N le_rfl fun a b hab hb => by
    exfalso
    omega
  rw [e0, e1] at hm
  exact WkN_ne_of_mem hm fun h => hxy (h1 h)

/-- Appending `v` with `⁅u a, v⁆ ∉ W_t`. -/
lemma strictN_append (N : Subgroup G) {u u' : ℕ → G} {t a : ℕ} {v : G}
    (hu : StrictChainN N u t) (ha : a < t)
    (e1 : ∀ i < t, u' i = u i) (e2 : u' t = v) (hv : ⁅u a, v⁆ ∉ WkN N u t) :
    StrictChainN N u' (t + 1) := by
  have hW : ∀ k ≤ t, WkN N u' k = WkN N u k := fun k hk =>
    WkN_congr N fun i hi => e1 i (by omega)
  apply strictChainN_of
  intro k hk hkt
  rcases Nat.lt_or_ge k t with hkt' | hkt'
  · rw [hW k (by omega), hW (k + 1) (by omega)]
    exact hu.ne_succ hk (by omega)
  · rw [show k = t by omega, hW t le_rfl]
    have hm : ⁅u' a, u' t⁆ ∈ WkN N u' (t + 1) := comm_mem_WkN N u' ha (by omega)
    rw [e1 a ha, e2] at hm
    exact WkN_ne_of_mem hm hv

/-- The exchange `u' = (u_0, ..., u_{s-1}, w, y)`. -/
lemma strictN_exchange (N : Subgroup G) {u u' : ℕ → G} {s : ℕ} {w y : G}
    (hu : StrictChainN N u (s + 1))
    (hcw : ∀ a < s, ⁅u a, w⁆ ∈ WkN N u (s + 1))
    (e1 : ∀ i < s, u' i = u i) (e2 : u' s = w) (e3 : u' (s + 1) = y)
    (hw1 : ∃ a < s, ⁅u a, w⁆ ∉ WkN N u s) (hw2 : ⁅w, y⁆ ∉ WkN N u (s + 1)) :
    StrictChainN N u' (s + 1 + 1) := by
  have hW : ∀ k ≤ s, WkN N u' k = WkN N u k := fun k hk =>
    WkN_congr N fun i hi => e1 i (by omega)
  have hle : WkN N u' (s + 1) ≤ WkN N u (s + 1) := by
    refine WkN_le N (le_WkN N u (s + 1)) ?_
    intro a b hab hb
    by_cases hbs : b < s
    · rw [e1 a (by omega), e1 b hbs]
      exact comm_mem_WkN N u hab (by omega)
    · rw [show b = s by omega, e1 a (by omega), e2]
      exact hcw a (by omega)
  apply strictChainN_of
  intro k hk hkt
  by_cases hks : k < s
  · rw [hW k (by omega), hW (k + 1) (by omega)]
    exact hu.ne_succ hk (by omega)
  · by_cases hk' : k = s
    · rw [hk']
      obtain ⟨a, ha, hna⟩ := hw1
      have hm : ⁅u' a, u' s⁆ ∈ WkN N u' (s + 1) := comm_mem_WkN N u' ha (by omega)
      rw [e1 a ha, e2] at hm
      rw [hW s le_rfl]
      exact WkN_ne_of_mem hm hna
    · rw [show k = s + 1 by omega]
      have hm : ⁅u' s, u' (s + 1)⁆ ∈ WkN N u' (s + 1 + 1) :=
        comm_mem_WkN N u' (by omega) (by omega)
      rw [e2, e3] at hm
      exact WkN_ne_of_mem hm fun h => hw2 (hle h)

/-- Extension inside a subgroup `H`: a strict chain in `H` of length `t ≥ 2` with
`⁅x, y⁆ ∉ W_t` for some `x, y ∈ H` extends to a strict chain in `H` of length `t + 1`. -/
lemma strictN_extend (N : Subgroup G) (hN : lcs G 2 ≤ N) {H : Subgroup G} {u : ℕ → G} {t : ℕ}
    (ht : 2 ≤ t) (hu : StrictChainN N u t) (huH : ∀ i < t, u i ∈ H) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hxy : ⁅x, y⁆ ∉ WkN N u t) :
    ∃ u' : ℕ → G, StrictChainN N u' (t + 1) ∧ ∀ i < t + 1, u' i ∈ H := by
  by_cases hc : ∃ a < t, ∃ v ∈ H, ⁅u a, v⁆ ∉ WkN N u t
  · obtain ⟨a, ha, v, hv, hav⟩ := hc
    refine ⟨fun i => if i < t then u i else v, ?_, ?_⟩
    · refine strictN_append N (u' := fun i => if i < t then u i else v) hu ha ?_ ?_ hav
      · intro i hi
        exact if_pos hi
      · show (if t < t then u t else v) = v
        exact if_neg (lt_irrefl t)
    · intro i hi
      show (if i < t then u i else v) ∈ H
      by_cases h : i < t
      · rw [if_pos h]
        exact huH i h
      · rw [if_neg h]
        exact hv
  · have hc' : ∀ a < t, ∀ v ∈ H, ⁅u a, v⁆ ∈ WkN N u t := fun a ha v hv => by
      by_contra hn
      exact hc ⟨a, ha, v, hv, hn⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    obtain ⟨a0, ha0, hna0⟩ :=
      WkN_exists_not_mem_of_ne N (hu.ne_succ (k := s) (by omega) le_rfl)
    have hw : ∃ w ∈ H, (∃ a < s, ⁅u a, w⁆ ∉ WkN N u s) ∧ ⁅w, y⁆ ∉ WkN N u (s + 1) := by
      by_cases hx' : ∃ a < s, ⁅u a, x⁆ ∉ WkN N u s
      · exact ⟨x, hx, hx', hxy⟩
      · refine ⟨u s * x, H.mul_mem (huH s (by omega)) hx, ⟨a0, ha0, ?_⟩, ?_⟩
        · have hax : ⁅u a0, x⁆ ∈ WkN N u s := by
            by_contra hn
            exact hx' ⟨a0, ha0, hn⟩
          rw [comm_mul_right_mem_iff' (hN.trans (le_WkN N u s)) hax]
          exact hna0
        · rw [comm_mul_left_mem_iff (hN.trans (le_WkN N u (s + 1))) (hc' s (by omega) y hy)]
          exact hxy
    obtain ⟨w, hwH, hw1, hw2⟩ := hw
    refine ⟨fun i => if i < s then u i else if i = s then w else y, ?_, ?_⟩
    · refine strictN_exchange N (u' := fun i => if i < s then u i else if i = s then w else y)
        hu (fun a ha => hc' a (by omega) w hwH) ?_ ?_ ?_ hw1 hw2
      · intro i hi
        exact if_pos hi
      · show (if s < s then u s else if s = s then w else y) = w
        rw [if_neg (lt_irrefl s), if_pos rfl]
      · show (if s + 1 < s then u (s + 1) else if s + 1 = s then w else y) = y
        rw [if_neg (show ¬ (s + 1 < s) by omega), if_neg (show ¬ (s + 1 = s) by omega)]
    · intro i hi
      show (if i < s then u i else if i = s then w else y) ∈ H
      by_cases h1 : i < s
      · rw [if_pos h1]
        exact huH i (by omega)
      · rw [if_neg h1]
        by_cases h2 : i = s
        · rw [if_pos h2]
          exact hwH
        · rw [if_neg h2]
          exact hy

/-- Generalised S2: the entries of a strict chain are independent modulo any `M` with
`⁅G, M⁆ ≤ N`. -/
theorem strictN_indep (N M : Subgroup G) (hN3 : lcs G 2 ≤ N) (hN2 : N ≤ lcs G 1)
    (hMN : ∀ g m : G, m ∈ M → ⁅g, m⁆ ∈ N) (u : ℕ → G) (t : ℕ) (h : StrictChainN N u t)
    (ht : 2 ≤ t) : ∀ k < t, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ M := by
  intro k hk hmem
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    have hle : Subgroup.closure (u '' Set.Iio 0) ⊔ M ≤ M := by
      refine sup_le ?_ le_rfl
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (Set.mem_Iio.mp hi) (Nat.not_lt_zero i)
    have h0 : u 0 ∈ M := hle hmem
    refine h.ne_succ (k := 1) le_rfl (by omega)
      (le_antisymm (WkN_mono N u (show 1 ≤ 1 + 1 by omega)) (WkN_succ_le N ?_))
    intro a ha
    obtain rfl : a = 0 := by omega
    exact le_WkN N u 1 (commElem_mem_symm (hMN (u 1) (u 0) h0))
  · haveI := WkN_normal N hN3 hN2 u k
    refine h.ne_succ (k := k) (by omega) (by omega)
      (le_antisymm (WkN_mono N u (show k ≤ k + 1 by omega)) (WkN_succ_le N ?_))
    intro a ha
    have hle : Subgroup.closure (u '' Set.Iio k) ⊔ M ≤ zn (WkN N u k) (u a) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨b, hb, rfl⟩
        rw [SetLike.mem_coe, mem_zn]
        rcases lt_trichotomy a b with hab | hab | hab
        · exact comm_mem_WkN N u hab (Set.mem_Iio.mp hb)
        · rw [hab, commutatorElement_self]
          exact (WkN N u k).one_mem
        · exact commElem_mem_symm (comm_mem_WkN N u hab ha)
      · intro z hz
        exact mem_zn.mpr (le_WkN N u k (hMN (u a) z hz))
    exact mem_zn.mp (hle hmem)

/-! Counting in a group of order `p ^ n`. -/

lemma powK_aux_mul (a b k k' : G) : a * k * (b * k') = a * b * (b⁻¹ * k * b⁻¹⁻¹ * k') := by
  group

lemma powK_aux_inv (a k : G) : (a * k)⁻¹ = a⁻¹ * (a * k⁻¹ * a⁻¹) := by
  group

/-- `x ^ e * k` with `e : ℤ` and `k ∈ K`: a subgroup when `K` is normal. -/
def powK (K : Subgroup G) [hK : K.Normal] (x : G) : Subgroup G where
  carrier := {g | ∃ e : ℤ, ∃ k ∈ K, g = x ^ e * k}
  one_mem' := by
    show ∃ e : ℤ, ∃ k ∈ K, (1 : G) = x ^ e * k
    exact ⟨0, 1, K.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨e, k, hk, rfl⟩ ⟨f, k', hk', rfl⟩
    show ∃ e' : ℤ, ∃ k'' ∈ K, x ^ e * k * (x ^ f * k') = x ^ e' * k''
    refine ⟨e + f, (x ^ f)⁻¹ * k * (x ^ f)⁻¹⁻¹ * k',
      K.mul_mem (hK.conj_mem k hk _) hk', ?_⟩
    rw [zpow_add]
    exact powK_aux_mul _ _ _ _
  inv_mem' := by
    rintro _ ⟨e, k, hk, rfl⟩
    show ∃ e' : ℤ, ∃ k'' ∈ K, (x ^ e * k)⁻¹ = x ^ e' * k''
    refine ⟨-e, x ^ e * k⁻¹ * (x ^ e)⁻¹, hK.conj_mem _ (K.inv_mem hk) _, ?_⟩
    rw [zpow_neg]
    exact powK_aux_inv _ _

lemma mem_powK {K : Subgroup G} [K.Normal] {x g : G} :
    g ∈ powK K x ↔ ∃ e : ℤ, ∃ k ∈ K, g = x ^ e * k := Iff.rfl

lemma mem_sup_zpowers_decomp {K : Subgroup G} [K.Normal] {x : G} {p : ℕ} (hp : 0 < p)
    (hx : x ^ p ∈ K) {g : G} (hg : g ∈ K ⊔ Subgroup.zpowers x) :
    ∃ e : ℕ, e < p ∧ ∃ k ∈ K, g = x ^ e * k := by
  have hle : K ⊔ Subgroup.zpowers x ≤ powK K x := by
    refine sup_le (fun k hk => mem_powK.mpr ⟨0, k, hk, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact mem_powK.mpr ⟨1, 1, K.one_mem, by simp⟩
  obtain ⟨e, k, hk, rfl⟩ := mem_powK.mp (hle hg)
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg e hp'.ne')
  have hrp : r < p := by
    have := Int.emod_lt_of_pos e hp'
    rw [hr] at this
    exact_mod_cast this
  refine ⟨r, hrp, (x ^ p) ^ (e / (p : ℤ)) * k, K.mul_mem (zpow_mem hx _) hk, ?_⟩
  have he : e = (r : ℤ) + (p : ℤ) * (e / (p : ℤ)) := by
    rw [← hr]
    have := Int.emod_add_mul_ediv e (p : ℤ)
    linarith
  calc x ^ e * k = x ^ ((r : ℤ) + (p : ℤ) * (e / (p : ℤ))) * k := by rw [← he]
    _ = x ^ r * ((x ^ p) ^ (e / (p : ℤ)) * k) := by
      rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, mul_assoc]

variable [Finite G]

lemma card_sup_zpowers_le {K : Subgroup G} [K.Normal] {x : G} {p : ℕ} (hp : 0 < p)
    (hx : x ^ p ∈ K) : Nat.card (K ⊔ Subgroup.zpowers x : Subgroup G) ≤ p * Nat.card K := by
  have hmem : ∀ q : Fin p × K, x ^ (q.1 : ℕ) * (q.2 : G) ∈ K ⊔ Subgroup.zpowers x :=
    fun q => mul_mem (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) _)
      (Subgroup.mem_sup_left q.2.2)
  let f : Fin p × K → (K ⊔ Subgroup.zpowers x : Subgroup G) := fun q => ⟨_, hmem q⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he, k, hk, rfl⟩ := mem_sup_zpowers_decomp hp hx hg
    exact ⟨(⟨e, he⟩, ⟨k, hk⟩), rfl⟩
  have h := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, (Nat.card_eq_fintype_card : Nat.card (Fin p) = Fintype.card (Fin p)),
    Fintype.card_fin] at h

variable {p n : ℕ}

/-- In a group of order `p ^ n`, a proper inclusion of subgroups multiplies the order by `p`. -/
lemma p_mul_card_le (hp : p.Prime) (hG : Nat.card G = p ^ n) {K L : Subgroup G} (hle : K ≤ L)
    (hne : K ≠ L) : p * Nat.card K ≤ Nat.card L := by
  have h2 : Nat.card L ∣ p ^ n := by
    rw [← hG]
    exact Subgroup.card_subgroup_dvd_card L
  have h1 : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hle
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp h2
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp (h1.trans h2)
  have hab : a ≤ b := by
    rw [ha, hb] at h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
  have hab' : a ≠ b := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [ha, hb]))
  rw [ha, hb, ← pow_succ']
  exact Nat.pow_le_pow_right hp.pos (by omega)

/-- `|⟨x_0, ..., x_{j-1}⟩ M| ≤ p ^ j |M|` when `M ≥ γ_2` contains all `p`-th powers. -/
lemma card_closure_sup_le (hp : 0 < p) {M : Subgroup G} (hM2 : lcs G 1 ≤ M)
    (hMp : ∀ g : G, g ^ p ∈ M) (x : ℕ → G) :
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
    have : (Subgroup.closure (x '' Set.Iio j) ⊔ M).Normal :=
      normal_of_lcs_one_le (hM2.trans le_sup_right)
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
      (Subgroup.mem_sup_right (hMp (x j)))
    have h3 : p * Nat.card (Subgroup.closure (x '' Set.Iio j) ⊔ M : Subgroup G) ≤
        p * (p ^ j * Nat.card M) := Nat.mul_le_mul le_rfl ih
    have e : p * (p ^ j * Nat.card M) = p ^ (j + 1) * Nat.card M := by
      rw [pow_succ]
      ring
    rw [← e]
    exact h1.trans (h2.trans h3)

/-- An independent sequence modulo `M` grows `⟨v_0, ..., v_{t-1}⟩ M` by a factor `p` each step. -/
lemma card_growth (hp : p.Prime) (hG : Nat.card G = p ^ n) (M : Subgroup G) {v : ℕ → G} :
    ∀ t, (∀ k < t, v k ∉ Subgroup.closure (v '' Set.Iio k) ⊔ M) →
      p ^ t * Nat.card M ≤ Nat.card (Subgroup.closure (v '' Set.Iio t) ⊔ M : Subgroup G) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [pow_zero, one_mul]
    exact Subgroup.card_le_of_le le_sup_right
  | succ t ih =>
    intro hind
    have h1 := ih fun k hk => hind k (by omega)
    have hle : Subgroup.closure (v '' Set.Iio t) ⊔ M ≤ Subgroup.closure (v '' Set.Iio (t + 1)) ⊔ M :=
      sup_le_sup_right (Subgroup.closure_mono
        (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ t)))) M
    have hne : Subgroup.closure (v '' Set.Iio t) ⊔ M ≠
        Subgroup.closure (v '' Set.Iio (t + 1)) ⊔ M := by
      intro h
      apply hind t (Nat.lt_succ_self t)
      rw [h]
      exact Subgroup.mem_sup_left
        (Subgroup.subset_closure ⟨t, Set.mem_Iio.mpr (Nat.lt_succ_self t), rfl⟩)
    have h2 := p_mul_card_le hp hG hle hne
    have h3 : p * (p ^ t * Nat.card M) ≤
        p * Nat.card (Subgroup.closure (v '' Set.Iio t) ⊔ M : Subgroup G) := Nat.mul_le_mul le_rfl h1
    have e : p * (p ^ t * Nat.card M) = p ^ (t + 1) * Nat.card M := by
      rw [pow_succ]
      ring
    rw [← e]
    exact h3.trans h2

/-- Strict chains inside `⟨x_0, ..., x_{s-1}⟩` that are independent modulo `M` have length
at most `s`. -/
lemma indep_length_le (hp : p.Prime) (hG : Nat.card G = p ^ n) {M : Subgroup G}
    (hM2 : lcs G 1 ≤ M) (hMp : ∀ g : G, g ^ p ∈ M) (x : ℕ → G) (s : ℕ) {v : ℕ → G} {t : ℕ}
    (hind : ∀ k < t, v k ∉ Subgroup.closure (v '' Set.Iio k) ⊔ M)
    (hvH : ∀ i < t, v i ∈ Subgroup.closure (x '' Set.Iio s)) : t ≤ s := by
  have h1 := card_growth hp hG M t hind
  have h2 : Nat.card (Subgroup.closure (v '' Set.Iio t) ⊔ M : Subgroup G) ≤
      Nat.card (Subgroup.closure (x '' Set.Iio s) ⊔ M : Subgroup G) := by
    refine Subgroup.card_le_of_le (sup_le ?_ le_sup_right)
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Subgroup.mem_sup_left (hvH i (Set.mem_Iio.mp hi))
  have h3 := card_closure_sup_le hp.pos hM2 hMp x s
  have hc : 0 < Nat.card M := Nat.card_pos
  by_contra hts
  have h4 : p ^ (s + 1) ≤ p ^ t := Nat.pow_le_pow_right hp.pos (by omega)
  have h6 : 0 < p ^ s := pow_pos hp.pos s
  rw [pow_succ] at h4
  have h7 : p ^ s * p * Nat.card M ≤ p ^ t * Nat.card M := Nat.mul_le_mul h4 le_rfl
  have h8 : p ^ s * 2 * Nat.card M ≤ p ^ s * p * Nat.card M :=
    Nat.mul_le_mul (Nat.mul_le_mul le_rfl hp.two_le) le_rfl
  have h9 : 0 < p ^ s * Nat.card M := Nat.mul_pos h6 hc
  linarith

/-- `d_k ≥ k - 1`: along a strict chain, `p ^ (k - 1) |N| ≤ |W_k|`. -/
lemma WkN_card_growth (hp : p.Prime) (hG : Nat.card G = p ^ n) (N : Subgroup G) {u : ℕ → G}
    {t : ℕ} (hu : StrictChainN N u t) :
    ∀ k, 1 ≤ k → k ≤ t → p ^ (k - 1) * Nat.card N ≤ Nat.card (WkN N u k) := by
  intro k
  induction k with
  | zero => intro hk _; omega
  | succ j ih =>
    intro _ hkt
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [show 0 + 1 - 1 = 0 by omega, pow_zero, one_mul]
      exact Subgroup.card_le_of_le (le_WkN N u 1)
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h1 := ih (by omega) (by omega)
      rw [show i + 1 - 1 = i by omega] at h1
      have h2 := p_mul_card_le hp hG (WkN_mono N u (show i + 1 ≤ i + 1 + 1 by omega))
        (hu.ne_succ (k := i + 1) (by omega) hkt)
      rw [show i + 1 + 1 - 1 = i + 1 by omega, pow_succ']
      have h3 : p * (p ^ i * Nat.card N) ≤ p * Nat.card (WkN N u (i + 1)) :=
        Nat.mul_le_mul le_rfl h1
      rw [mul_assoc]
      exact h3.trans h2

omit [Finite G] in
lemma exists_comm_not_mem {N H W : Subgroup G} (hcore : lcs G 1 ≤ ⁅H, H⁆ ⊔ N) (hNW : N ≤ W)
    (hW : ¬ lcs G 1 ≤ W) : ∃ x ∈ H, ∃ y ∈ H, ⁅x, y⁆ ∉ W := by
  by_contra hc
  apply hW
  refine hcore.trans (sup_le ?_ hNW)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  by_contra hn
  exact hc ⟨x, hx, y, hy, hn⟩

/-- BNV Prop 5.2, group-level: the strict flag of a minimal core. -/
theorem core_flag (hp : p.Prime) (hG : Nat.card G = p ^ n) (N M : Subgroup G)
    (hN3 : lcs G 2 ≤ N) (hN2 : N ≤ lcs G 1) (hM2 : lcs G 1 ≤ M) (hMp : ∀ g : G, g ^ p ∈ M)
    (hMN : ∀ g m : G, m ∈ M → ⁅g, m⁆ ∈ N) (s : ℕ) (x : ℕ → G)
    (hcore : lcs G 1 ≤
      ⁅Subgroup.closure (x '' Set.Iio s), Subgroup.closure (x '' Set.Iio s)⁆ ⊔ N)
    (hmin : ∀ t < s, ∀ v : ℕ → G, (∀ i < t, v i ∈ Subgroup.closure (x '' Set.Iio s)) →
      ¬ lcs G 1 ≤ ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔ N) :
    ∃ u : ℕ → G, (∀ i < s, u i ∈ Subgroup.closure (x '' Set.Iio s)) ∧
      StrictChainN N u s ∧ WkN N u s = lcs G 1 ∧
      (∀ k < s, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ M) ∧
      Subgroup.closure (u '' Set.Iio s) ⊔ M = Subgroup.closure (x '' Set.Iio s) ⊔ M ∧
      (∀ k, 1 ≤ k → k ≤ s → p ^ (k - 1) * Nat.card N ≤ Nat.card (WkN N u k)) := by
  have hHH : s ≤ 1 →
      ⁅Subgroup.closure (x '' Set.Iio s), Subgroup.closure (x '' Set.Iio s)⁆ ≤ N := by
    intro hs1
    have := normal_of_sandwich (n := 1) hN3 hN2
    apply commutator_closure_le
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    have hi' : i < s := Set.mem_Iio.mp hi
    have hj' : j < s := Set.mem_Iio.mp hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    rw [commutatorElement_self]
    exact N.one_mem
  rcases (show s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with hs | hs | hs
  · subst hs
    refine ⟨x, fun i hi => absurd hi (Nat.not_lt_zero i), strictChainN_zero N x, ?_,
      fun k hk => absurd hk (Nat.not_lt_zero k), rfl, fun k hk hks => absurd hks (by omega)⟩
    exact le_antisymm (WkN_le_lcs_one N hN2 x 0)
      (hcore.trans (sup_le ((hHH (by omega)).trans (le_WkN N x 0)) (le_WkN N x 0)))
  · subst hs
    exfalso
    exact hmin 0 (by omega) x (fun i hi => absurd hi (Nat.not_lt_zero i))
      ((hcore.trans (sup_le (hHH le_rfl) le_rfl)).trans le_sup_right)
  · have stepA : ∀ j, j + 2 ≤ s → ∃ u : ℕ → G, StrictChainN N u (j + 2) ∧
        ∀ i < j + 2, u i ∈ Subgroup.closure (x '' Set.Iio s) := by
      intro j
      induction j with
      | zero =>
        intro hs2
        have h0 : ¬ lcs G 1 ≤ N := fun h =>
          hmin 0 (by omega) x (fun i hi => absurd hi (Nat.not_lt_zero i)) (h.trans le_sup_right)
        obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_not_mem hcore le_rfl h0
        refine ⟨fun i => if i = 0 then a else b, ?_, ?_⟩
        · refine strictN_two N (u := fun i => if i = 0 then a else b) ?_ ?_ hab
          · show (if (0 : ℕ) = 0 then a else b) = a
            exact if_pos rfl
          · show (if (1 : ℕ) = 0 then a else b) = b
            exact if_neg (by norm_num)
        · intro i hi
          show (if i = 0 then a else b) ∈ Subgroup.closure (x '' Set.Iio s)
          by_cases h : i = 0
          · rw [if_pos h]
            exact ha
          · rw [if_neg h]
            exact hb
      | succ j ih =>
        intro hs2
        obtain ⟨u, hu, huH⟩ := ih (by omega)
        have hnc : ¬ lcs G 1 ≤ WkN N u (j + 2) := fun h =>
          hmin (j + 2) (by omega) u huH (h.trans (WkN_le_core N u (j + 2)))
        obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_not_mem hcore (le_WkN N u _) hnc
        obtain ⟨u', hu', hu'H⟩ := strictN_extend N hN3 (by omega) hu huH ha hb hab
        rw [show j + 1 + 2 = j + 2 + 1 by omega]
        exact ⟨u', hu', hu'H⟩
    obtain ⟨u, hu, huH⟩ := stepA (s - 2) (by omega)
    rw [show s - 2 + 2 = s by omega] at hu huH
    have hge : lcs G 1 ≤ WkN N u s := by
      by_contra hc
      obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_not_mem hcore (le_WkN N u s) hc
      obtain ⟨u', hu', hu'H⟩ := strictN_extend N hN3 (by omega) hu huH ha hb hab
      have := indep_length_le hp hG hM2 hMp x s
        (strictN_indep N M hN3 hN2 hMN u' (s + 1) hu' (by omega)) hu'H
      omega
    have hind := strictN_indep N M hN3 hN2 hMN u s hu (by omega)
    refine ⟨u, huH, hu, le_antisymm (WkN_le_lcs_one N hN2 u s) hge, hind, ?_,
      WkN_card_growth hp hG N hu⟩
    have hle : Subgroup.closure (u '' Set.Iio s) ⊔ M ≤ Subgroup.closure (x '' Set.Iio s) ⊔ M := by
      refine sup_le ?_ le_sup_right
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact Subgroup.mem_sup_left (huH i (Set.mem_Iio.mp hi))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    exact (card_closure_sup_le hp.pos hM2 hMp x s).trans (card_growth hp hG M s hind)

/-- Consequences (BNV Cor 5.3 / LQ Lemma 2.3, lower half): for a minimal core of size
`s ≥ 1`, `p ^ (s - 1) |N| ≤ |γ_2|` (so `s - 1 ≤ r_2`) and `p ^ s |M| ≤ |G|` (so `s ≤ r_1`). -/
theorem core_flag_card (hp : p.Prime) (hG : Nat.card G = p ^ n) (N M : Subgroup G)
    (hN3 : lcs G 2 ≤ N) (hN2 : N ≤ lcs G 1) (hM2 : lcs G 1 ≤ M) (hMp : ∀ g : G, g ^ p ∈ M)
    (hMN : ∀ g m : G, m ∈ M → ⁅g, m⁆ ∈ N) (s : ℕ) (x : ℕ → G)
    (hcore : lcs G 1 ≤
      ⁅Subgroup.closure (x '' Set.Iio s), Subgroup.closure (x '' Set.Iio s)⁆ ⊔ N)
    (hmin : ∀ t < s, ∀ v : ℕ → G, (∀ i < t, v i ∈ Subgroup.closure (x '' Set.Iio s)) →
      ¬ lcs G 1 ≤ ⁅Subgroup.closure (v '' Set.Iio t), Subgroup.closure (v '' Set.Iio t)⁆ ⊔ N) :
    (1 ≤ s → p ^ (s - 1) * Nat.card N ≤ Nat.card (lcs G 1)) ∧
      p ^ s * Nat.card M ≤ Nat.card G := by
  obtain ⟨u, -, -, hW, hind, -, hcard⟩ :=
    core_flag hp hG N M hN3 hN2 hM2 hMp hMN s x hcore hmin
  refine ⟨fun hs => ?_, ?_⟩
  · have := hcard s hs le_rfl
    rwa [hW] at this
  · exact (card_growth hp hG M s hind).trans (Subgroup.card_le_card_group _)

end CoreFlag

end OMA.SimsLite
