import H2Dev.Comm

/-! Theorem S of the blueprint (section 3): strict chains.
S1 (`exists_strict_chain`) by maximality, S2 (`strict_chain_indep`) via `zn`. -/

namespace OMA.SimsLite

open scoped commutatorElement

universe u

section StrictStmt

variable {G : Type u} [Group G]

/-- `W_k(u) = ⟨⁅u a, u b⁆ : a < b < k⟩ γ_3`. -/
def Wk (u : ℕ → G) (k : ℕ) : Subgroup G :=
  Subgroup.closure {x | ∃ a b, a < b ∧ b < k ∧ x = ⁅u a, u b⁆} ⊔ lcs G 2

/-- `u` is strict of length `t`: each new core element enlarges `W`. -/
def StrictChain (u : ℕ → G) (t : ℕ) : Prop := ∀ k, 2 ≤ k → k ≤ t → Wk u (k - 1) ≠ Wk u k

/-! Basic facts about `Wk`. -/

lemma lcs_two_le_Wk (u : ℕ → G) (k : ℕ) : lcs G 2 ≤ Wk u k := by
  unfold Wk
  exact le_sup_right

lemma comm_mem_Wk (u : ℕ → G) {a b k : ℕ} (hab : a < b) (hbk : b < k) :
    ⁅u a, u b⁆ ∈ Wk u k := by
  unfold Wk
  exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨a, b, hab, hbk, rfl⟩)

lemma Wk_le {u : ℕ → G} {k : ℕ} {H : Subgroup G} (h3 : lcs G 2 ≤ H)
    (h : ∀ a b, a < b → b < k → ⁅u a, u b⁆ ∈ H) : Wk u k ≤ H := by
  unfold Wk
  refine sup_le ?_ h3
  rw [Subgroup.closure_le]
  rintro _ ⟨a, b, hab, hbk, rfl⟩
  exact h a b hab hbk

lemma Wk_mono (u : ℕ → G) {k l : ℕ} (hkl : k ≤ l) : Wk u k ≤ Wk u l :=
  Wk_le (lcs_two_le_Wk u l) fun a b hab hbk => comm_mem_Wk u hab (by omega)

lemma Wk_le_lcs_one (u : ℕ → G) (k : ℕ) : Wk u k ≤ lcs G 1 :=
  Wk_le (lcs_antitone (by norm_num)) fun a b _ _ =>
    commElem_mem_lcs_succ (n := 0) (Subgroup.mem_top (u a)) (u b)

lemma Wk_normal (u : ℕ → G) (k : ℕ) : (Wk u k).Normal :=
  normal_of_sandwich (n := 1) (lcs_two_le_Wk u k) (Wk_le_lcs_one u k)

lemma Wk_congr_le {u v : ℕ → G} {k : ℕ} (h : ∀ i < k, u i = v i) : Wk u k ≤ Wk v k :=
  Wk_le (lcs_two_le_Wk v k) fun a b hab hbk => by
    rw [h a (by omega), h b hbk]
    exact comm_mem_Wk v hab hbk

lemma Wk_congr {u v : ℕ → G} {k : ℕ} (h : ∀ i < k, u i = v i) : Wk u k = Wk v k :=
  le_antisymm (Wk_congr_le h) (Wk_congr_le fun i hi => (h i hi).symm)

lemma Wk_succ_le {u : ℕ → G} {k : ℕ} (h : ∀ a < k, ⁅u a, u k⁆ ∈ Wk u k) :
    Wk u (k + 1) ≤ Wk u k := by
  refine Wk_le (lcs_two_le_Wk u k) ?_
  intro a b hab hbk
  by_cases hb : b < k
  · exact comm_mem_Wk u hab hb
  · rw [show b = k by omega]
    exact h a (by omega)

lemma Wk_exists_not_mem_of_ne {u : ℕ → G} {k : ℕ} (h : Wk u k ≠ Wk u (k + 1)) :
    ∃ a < k, ⁅u a, u k⁆ ∉ Wk u k := by
  by_contra hc
  apply h
  refine le_antisymm (Wk_mono u (show k ≤ k + 1 by omega)) (Wk_succ_le ?_)
  intro a ha
  by_contra hn
  exact hc ⟨a, ha, hn⟩

lemma Wk_ne_of_mem {A B : Subgroup G} {z : G} (hB : z ∈ B) (hA : z ∉ A) : A ≠ B := by
  rintro rfl
  exact hA hB

lemma Wk_exists_comm {W : Subgroup G} (h : ¬ lcs G 1 ≤ W) : ∃ x y : G, ⁅x, y⁆ ∉ W := by
  by_contra hc
  apply h
  have e : lcs G 1 = ⁅(⊤ : Subgroup G), ⊤⁆ := rfl
  rw [e, Subgroup.commutator_le]
  intro x _ y _
  by_contra hxy
  exact hc ⟨x, y, hxy⟩

/-! Basic facts about strict chains. -/

lemma strictChain_of {u : ℕ → G} {t : ℕ}
    (h : ∀ k, 1 ≤ k → k + 1 ≤ t → Wk u k ≠ Wk u (k + 1)) : StrictChain u t := by
  intro k hk hkt
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact h j (by omega) hkt

lemma StrictChain.ne_succ {u : ℕ → G} {t : ℕ} (h : StrictChain u t) {k : ℕ} (hk : 1 ≤ k)
    (hkt : k + 1 ≤ t) : Wk u k ≠ Wk u (k + 1) := by
  have := h (k + 1) (by omega) hkt
  rw [Nat.add_sub_cancel] at this
  exact this

lemma strictChain_zero (u : ℕ → G) : StrictChain u 0 := by
  intro k hk hkt
  omega

/-- A strict chain has length at most `Nat.card G`: the orders of the `Wk u k` increase. -/
lemma StrictChain.le_card [Finite G] {u : ℕ → G} {t : ℕ} (h : StrictChain u t) :
    t ≤ Nat.card G := by
  have key : ∀ k, 1 ≤ k → k ≤ t → k ≤ Nat.card (Wk u k) := by
    intro k
    induction k with
    | zero => intro hk _; omega
    | succ j ih =>
      intro hk hkt
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        show 1 ≤ Nat.card (Wk u 1)
        have hpos : 0 < Nat.card (Wk u 1) := Nat.card_pos
        omega
      · have h1 := ih (by omega) (by omega)
        have hne := h.ne_succ (k := j) (by omega) hkt
        have hle := Wk_mono u (show j ≤ j + 1 by omega)
        have hlt : Nat.card (Wk u j) < Nat.card (Wk u (j + 1)) := by
          by_contra hc
          exact hne (Subgroup.eq_of_le_of_card_ge hle (by omega))
        omega
  rcases Nat.eq_zero_or_pos t with ht | ht
  · omega
  · exact (key t (by omega) le_rfl).trans (Subgroup.card_le_card_group _)

/-- The chain `(x, y)` is strict of length 2 when `⁅x, y⁆ ∉ γ_3`. -/
lemma strict_two {u : ℕ → G} {x y : G} (e0 : u 0 = x) (e1 : u 1 = y)
    (hxy : ⁅x, y⁆ ∉ lcs G 2) : StrictChain u 2 := by
  apply strictChain_of
  intro k hk hkt
  rw [show k = 1 by omega]
  have hm : ⁅u 0, u 1⁆ ∈ Wk u (1 + 1) := comm_mem_Wk u (by norm_num) (by norm_num)
  have h1 : Wk u 1 ≤ lcs G 2 := Wk_le le_rfl fun a b hab hb => by
    exfalso
    omega
  rw [e0, e1] at hm
  exact Wk_ne_of_mem hm fun h => hxy (h1 h)

/-- Case 1 of S1: appending `v` with `⁅u a, v⁆ ∉ W_t`. -/
lemma strict_append {u u' : ℕ → G} {t a : ℕ} {v : G} (hu : StrictChain u t) (ha : a < t)
    (e1 : ∀ i < t, u' i = u i) (e2 : u' t = v) (hv : ⁅u a, v⁆ ∉ Wk u t) :
    StrictChain u' (t + 1) := by
  have hW : ∀ k ≤ t, Wk u' k = Wk u k := fun k hk => Wk_congr fun i hi => e1 i (by omega)
  apply strictChain_of
  intro k hk hkt
  rcases Nat.lt_or_ge k t with hkt' | hkt'
  · rw [hW k (by omega), hW (k + 1) (by omega)]
    exact hu.ne_succ hk (by omega)
  · rw [show k = t by omega, hW t le_rfl]
    have hm : ⁅u' a, u' t⁆ ∈ Wk u' (t + 1) := comm_mem_Wk u' ha (by omega)
    rw [e1 a ha, e2] at hm
    exact Wk_ne_of_mem hm hv

/-- Case 2 of S1: the exchange `u' = (u_0, ..., u_{s-1}, w, y)`. -/
lemma strict_exchange {u u' : ℕ → G} {s : ℕ} {w y : G} (hu : StrictChain u (s + 1))
    (hc : ∀ a < s + 1, ∀ v, ⁅u a, v⁆ ∈ Wk u (s + 1))
    (e1 : ∀ i < s, u' i = u i) (e2 : u' s = w) (e3 : u' (s + 1) = y)
    (hw1 : ∃ a < s, ⁅u a, w⁆ ∉ Wk u s) (hw2 : ⁅w, y⁆ ∉ Wk u (s + 1)) :
    StrictChain u' (s + 1 + 1) := by
  have hW : ∀ k ≤ s, Wk u' k = Wk u k := fun k hk => Wk_congr fun i hi => e1 i (by omega)
  have hle : Wk u' (s + 1) ≤ Wk u (s + 1) := by
    refine Wk_le (lcs_two_le_Wk u (s + 1)) ?_
    intro a b hab hb
    by_cases hbs : b < s
    · rw [e1 a (by omega), e1 b hbs]
      exact comm_mem_Wk u hab (by omega)
    · rw [show b = s by omega, e1 a (by omega), e2]
      exact hc a (by omega) w
  apply strictChain_of
  intro k hk hkt
  by_cases hks : k < s
  · rw [hW k (by omega), hW (k + 1) (by omega)]
    exact hu.ne_succ hk (by omega)
  · by_cases hk' : k = s
    · rw [hk']
      obtain ⟨a, ha, hna⟩ := hw1
      have hm : ⁅u' a, u' s⁆ ∈ Wk u' (s + 1) := comm_mem_Wk u' ha (by omega)
      rw [e1 a ha, e2] at hm
      rw [hW s le_rfl]
      exact Wk_ne_of_mem hm hna
    · rw [show k = s + 1 by omega]
      have hm : ⁅u' s, u' (s + 1)⁆ ∈ Wk u' (s + 1 + 1) :=
        comm_mem_Wk u' (by omega) (by omega)
      rw [e2, e3] at hm
      exact Wk_ne_of_mem hm fun h => hw2 (hle h)

/-- The extension step of S1: a strict chain of length `t ≥ 2` with `γ_2 ≰ W_t` extends. -/
lemma strict_extend {u : ℕ → G} {t : ℕ} (ht : 2 ≤ t) (hu : StrictChain u t) {x y : G}
    (hxy : ⁅x, y⁆ ∉ Wk u t) : ∃ u' : ℕ → G, StrictChain u' (t + 1) := by
  by_cases hc : ∃ a < t, ∃ v, ⁅u a, v⁆ ∉ Wk u t
  · obtain ⟨a, ha, v, hv⟩ := hc
    refine ⟨fun i => if i < t then u i else v, ?_⟩
    refine strict_append (u' := fun i => if i < t then u i else v) hu ha ?_ ?_ hv
    · intro i hi
      exact if_pos hi
    · show (if t < t then u t else v) = v
      exact if_neg (lt_irrefl t)
  · have hc' : ∀ a < t, ∀ v, ⁅u a, v⁆ ∈ Wk u t := fun a ha v => by
      by_contra hn
      exact hc ⟨a, ha, v, hn⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    obtain ⟨a0, ha0, hna0⟩ := Wk_exists_not_mem_of_ne (hu.ne_succ (k := s) (by omega) le_rfl)
    have hw : ∃ w : G, (∃ a < s, ⁅u a, w⁆ ∉ Wk u s) ∧ ⁅w, y⁆ ∉ Wk u (s + 1) := by
      by_cases hx : ∃ a < s, ⁅u a, x⁆ ∉ Wk u s
      · exact ⟨x, hx, hxy⟩
      · refine ⟨u s * x, ⟨a0, ha0, ?_⟩, ?_⟩
        · have hax : ⁅u a0, x⁆ ∈ Wk u s := by
            by_contra hn
            exact hx ⟨a0, ha0, hn⟩
          rw [comm_mul_right_mem_iff' (lcs_two_le_Wk u s) hax]
          exact hna0
        · rw [comm_mul_left_mem_iff (lcs_two_le_Wk u (s + 1)) (hc' s (by omega) y)]
          exact hxy
    obtain ⟨w, hw1, hw2⟩ := hw
    refine ⟨fun i => if i < s then u i else if i = s then w else y, ?_⟩
    refine strict_exchange (u' := fun i => if i < s then u i else if i = s then w else y)
      hu hc' ?_ ?_ ?_ hw1 hw2
    · intro i hi
      exact if_pos hi
    · show (if s < s then u s else if s = s then w else y) = w
      rw [if_neg (lt_irrefl s), if_pos rfl]
    · show (if s + 1 < s then u (s + 1) else if s + 1 = s then w else y) = y
      rw [if_neg (show ¬ (s + 1 < s) by omega), if_neg (show ¬ (s + 1 = s) by omega)]

/-- S1: a strict chain whose commutators generate `γ_2` modulo `γ_3`. -/
theorem exists_strict_chain [Finite G] :
    ∃ (t : ℕ) (u : ℕ → G), t ≠ 1 ∧ StrictChain u t ∧ lcs G 1 ≤ Wk u t := by
  by_contra H
  have H' : ∀ (t : ℕ) (u : ℕ → G), t ≠ 1 → StrictChain u t → ¬ lcs G 1 ≤ Wk u t :=
    fun t u h1 h2 h3 => H ⟨t, u, h1, h2, h3⟩
  have key : ∀ n : ℕ, ∃ u : ℕ → G, StrictChain u (n + 2) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨x, y, hxy⟩ :=
        Wk_exists_comm (H' 0 (fun _ => 1) (by norm_num) (strictChain_zero _))
      refine ⟨fun i => if i = 0 then x else y, ?_⟩
      refine strict_two (u := fun i => if i = 0 then x else y) (x := x) (y := y) ?_ ?_ ?_
      · show (if (0 : ℕ) = 0 then x else y) = x
        exact if_pos rfl
      · show (if (1 : ℕ) = 0 then x else y) = y
        exact if_neg (by norm_num)
      · exact fun h => hxy (lcs_two_le_Wk (fun _ : ℕ => (1 : G)) 0 h)
    | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨x, y, hxy⟩ := Wk_exists_comm (H' (n + 2) u (by omega) hu)
      obtain ⟨u', hu'⟩ := strict_extend (by omega) hu hxy
      refine ⟨u', ?_⟩
      show StrictChain u' (n + 1 + 2)
      rw [show n + 1 + 2 = n + 2 + 1 by omega]
      exact hu'
  obtain ⟨u, hu⟩ := key (Nat.card G)
  have := hu.le_card
  omega

/-- S2: the elements of a strict chain are independent modulo `γ_2`. -/
theorem strict_chain_indep (u : ℕ → G) (t : ℕ) (h : StrictChain u t) (ht : 2 ≤ t) :
    ∀ k < t, u k ∉ Subgroup.closure (u '' Set.Iio k) ⊔ lcs G 1 := by
  intro k hk hmem
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    have hle : Subgroup.closure (u '' Set.Iio 0) ⊔ lcs G 1 ≤ lcs G 1 := by
      refine sup_le ?_ le_rfl
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (Set.mem_Iio.mp hi) (Nat.not_lt_zero i)
    have h0 : u 0 ∈ lcs G 1 := hle hmem
    refine h.ne_succ (k := 1) le_rfl (by omega)
      (le_antisymm (Wk_mono u (show 1 ≤ 1 + 1 by omega)) (Wk_succ_le ?_))
    intro a ha
    obtain rfl : a = 0 := by omega
    exact lcs_two_le_Wk u 1 (commElem_mem_lcs_succ (n := 1) h0 (u 1))
  · haveI := Wk_normal u k
    refine h.ne_succ (k := k) (by omega) (by omega)
      (le_antisymm (Wk_mono u (show k ≤ k + 1 by omega)) (Wk_succ_le ?_))
    intro a ha
    have hle : Subgroup.closure (u '' Set.Iio k) ⊔ lcs G 1 ≤ zn (Wk u k) (u a) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨b, hb, rfl⟩
        rw [SetLike.mem_coe, mem_zn]
        rcases lt_trichotomy a b with hab | hab | hab
        · exact comm_mem_Wk u hab (Set.mem_Iio.mp hb)
        · rw [hab, commutatorElement_self]
          exact (Wk u k).one_mem
        · exact commElem_mem_symm (comm_mem_Wk u hab ha)
      · intro z hz
        exact mem_zn.mpr (lcs_two_le_Wk u k (commElem_mem_lcs_succ' (n := 1) (u a) hz))
    exact mem_zn.mp (hle hmem)

end StrictStmt

end OMA.SimsLite
