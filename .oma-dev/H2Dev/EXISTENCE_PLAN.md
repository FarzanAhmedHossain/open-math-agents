# Existence (Theorem E) plan

Module: `.oma-dev/H2Dev/Existence.lean` (imports `H2Dev.Code`, `H2Dev.Stmt`, `Mathlib.Data.List.GetD`).
Namespace `OMA.SimsLite`, `open scoped commutatorElement`. Levels are 0-based: the blueprint weight
`w` is the Lean level `w - 1`, `lcs G 0 = ⊤`.

Main theorem (fully proved from the helpers below):

    theorem existence {p : ℕ} (hp : p.Prime) (m : ℕ) (G : Type u) [Group G] [Finite G]
        (hG : Nat.card G = p ^ m) : ∃ (X : Fin m → G) (c : Code p m), Realizes X c

## Architecture

The proof never flattens lists and recovers positions afterwards. Every position is a record

    structure Ent (G) where g : G; lv : ℕ; df : Option (Option (ℕ × ℕ)); ci : Option ℕ; st : ℕ

(element, level, definition, core index, step) and lists of records are read with the total
accessor `ent L i := L.getD i Ent.dft`. Three layers of the argument:

1. Greedy layer (Lemma G). `layer p N C` folds a candidate list `C` from the left:
   `layer p N (c :: C) = chainE p (clen p (cl (C.map Ent.g) ⊔ N) c.g) c ++ layer p N C`, where
   `clen p K x = Nat.log p (K.relIndex (K ⊔ zpowers x))` and `chainE p n c` is the chain
   `c, c^p, ..., c^(p^(n-1))` whose non-initial records are power records (`df = some none`,
   `ci = none`, same `lv` and `st`). The chain of a candidate is taken over the closure of the LATER
   candidates, so the list is built left to right and positions never move.
2. Construction (`Dat`, `Dat.Hyp`). Data `d = ⟨p, t, u, en⟩` with `u` the strict core from
   `exists_strict_chain` and `en` an enumeration of `G`.
   * `cand0 = en (free records) ++ [coreE (t-1), ..., coreE 0]`, `Y0 = layer p (lcs G 1) cand0`,
     `pos κ = Y0.findIdx (ci = some κ)` (position of the head of the chain of `u κ`).
   * `cand1 = blocks t-1, ..., 0`, block `β = [⁅u a, u β⁆ : a < β]` with `df = comm (pos a, pos β)`,
     `st = β`; layer 1 is `layer p (lcs G 2) cand1`.
   * `cands (w+2) = commC (w+2) (off (w+1)) (Y (w+1))`: for each entry `y` of layer `w+1` (at
     absolute position `off (w+1) + r`) and each `b < t`, the record `⁅y.g, u b⁆` with
     `df = comm (off (w+1) + r, pos b)`.
   * `lay`, `Y w`, `off w`, `cands w`, `full n = Y 0 ++ ... ++ Y (n-1)`; the final list is `full m`.
3. Encoding. `LGood p t pos L` collects list-level V1 to V6, R1, membership, span and power
   facts; `realizes_of_good` turns a good list of length `m` into `(X, c)` with `Realizes X c`
   through `shapeOf` (clamped read-off of the shape), `Xof`, and `realizes_of_layout`
   (exponents from `nf_surj` + `suffix_hyps`, packed by `codeOf`).

Glue (fully proved): `existence`, `realizes_of_good`, `Dat.good_full` (structure instance whose
fields are the `good_*` lemmas).

## Helpers

Status at the time of writing: every helper below has a proof in the file; the column `deps`
lists what each proof uses, so that a broken proof can be repaired in isolation. Sizes are the
sizes of the current proofs.

### Generic list and closure lemmas (about 60 lines, no dependencies)
`ent_eq`, `ent_append_left`, `ent_append_right`, `ent_mem`, `exists_ent_of_mem`, `cl_append`,
`cl_cons`, `cl_nil`, `cl_le_of_forall`, `chainE_zero`, `length_chainE`, `ent_chainE`,
`g_ent_chainE`, `head_mem_chainE`, `cl_chainE`.
Math: list bookkeeping; `cl (l ++ l') = cl l ⊔ cl l'` by `Subgroup.closure_union`; the closure of
a nonempty chain of `c` is `zpowers c`.

### layer_append (10 lines)
`∃ P, layer p N (A ++ C) = P ++ layer p N C`. Induction on `A`.

### layer_src (25 lines)
Every `e ∈ layer p N C` has a source `c ∈ C` with `e.g = c.g ^ k`, same `lv` and `st`, and either
`e = c` or (`e.df = some none` and `e.ci = none`). Induction on `C`, case split on the chain index.

### layer_pow (50 lines)
If no candidate has `df = some none`, then every power record at index `r` of the layer has
`0 < r`, the record at `r - 1` has the same `lv` and `st`, and `g r = (g (r - 1)) ^ p`.
Induction on `C`; inside a chain the previous record is the previous chain index
(`c^(p^r) = (c^(p^(r-1)))^p`), outside it the induction hypothesis shifted by the chain length.

### normal_K (8 lines)
`(cl (C.map Ent.g) ⊔ lcs G (w+1)).Normal` when all candidates lie in `lcs G w`
(`normal_of_sandwich`).

### clen_spec (G1, 15 lines)
For `K` normal, `|G| = p^m`: `p ^ clen p K x = K.relIndex (K ⊔ zpowers x)`,
`x ^ (p ^ clen p K x) ∈ K`, and `clen p K x = 0 → x ∈ K`.
Math: the relative index divides `|K ⊔ ⟨x⟩|`, which divides `p^m`, so it is `p^a`
(`Nat.dvd_prime_pow`) and `Nat.log p (p^a) = a`; `Subgroup.pow_relIndex_mem`; index 1 means
`K ⊔ ⟨x⟩ ≤ K`.

### layer_sup (Y3), layer_card (Y4), layer_powrel (Y2) (25 + 20 + 45 lines)
Hypotheses `p.Prime`, `|G| = p^m`, all candidates in `lcs G w`, `N = lcs G (w+1)`.
* `cl (layer.map g) ⊔ N = cl (C.map g) ⊔ N`: induction; a chain of positive length generates
  `zpowers c`, a chain of length 0 has `c ∈ K`.
* `p ^ |layer| = N.relIndex (cl (C.map g) ⊔ N)`: induction, `Subgroup.relIndex_mul_relIndex`
  for `N ≤ K ≤ K ⊔ zpowers c`.
* `(ent layer r).g ^ p ∈ cl ((layer.map g).drop (r+1)) ⊔ N`: inside a chain the next record; at
  the end of a chain `c^(p^a) ∈ K = cl (layer C) ⊔ N` by Y3; after the chain the induction
  hypothesis.

### layer_mem_head, layer_head_of_ne (Y5, 15 + 25 lines)
* If `c.g ∉ cl (C.map g) ⊔ N` then `c ∈ layer p N (A ++ c :: C)`: the chain of `c` has positive
  length (`clen_spec`) and `layer_append`.
* If `cl ((B ++ C).map g) ⊔ N ≠ cl (C.map g) ⊔ N` then some `c ∈ B` lies in
  `layer p N (B ++ C)`: induction on `B`; an empty chain does not change the closure.

### lcs_eq_bot_of_card (Lemma K, 60 lines)
`p.Prime → Nat.card G = p^m → lcs G m = ⊥`. Math: `G` is nilpotent (`IsPGroup.isNilpotent`), so a
stationary step forces `⊥`; otherwise each step has index at least `p`; by induction
`lcs G w = ⊥ ∨ |lcs G w| * p^w ≤ p^m`.

### Shape.start_le, Shape.lt_start_iff (40 lines)
For a monotone shape, `i < s.start w ↔ s.lv i < w` (injections into `Fin i` and from
`Fin (i+1)`).

### realizes_of_layout (110 lines)
Valid shape, tuple `X`, R1 definitions, `X i ∈ lcs G (s.lv i)`,
`lcs G w ≤ cl ((List.ofFn X).drop (s.start w))` and `X i ^ p ∈ cl (drop (i+1))` give a code.
Math: the hypotheses give the `nf_surj` hypotheses (h2 directly, h3 because
`⁅g, X j⁆ ∈ lcs G (lv j + 1) ≤ cl (drop (start (lv j + 1))) ≤ cl (drop (j+1))`); `suffix_hyps`
and `nf_surj` give exponents for every element of every suffix closure (`nfE`); `codeOf` stores
`nfE` of the relation's suffix at column `j - offset`; `codeOf_ex` and `nf_congr` give R2 to R5
(the columns of each relation's suffix are exactly the index set, by `Shape.lt_start_iff`).

### LGood.t_le, shapeOf_lv, shapeOf_df_none, shapeOf_df_pow, shapeOf_df_comm, shapeOf_st,
### shapeOf_cidx_pos, shapeOf_cidx_some, shapeOf_ncore, shapeOf_valid (220 lines)
`shapeOf` clamps every value into range; for good lists of length `m` the clamps are inactive
(`lv < m`, positions `< i < m`, core indices `< t ≤ m`). `cidx i = some κ` exactly when
`ent L i` has `ci = some κ` and `i = pos κ`, so `cidx` is injective by construction and
`ncore = t` through the bijection `κ ↦ pos κ`. V1 to V6 then transcribe the `LGood` fields.

### Xof_pow, Xof_comm, Xof_mem, Xof_span, Xof_powrel, ofFn_Xof (45 lines)
Fin-level transcriptions of the `LGood` fields; `Xof_span` uses `Shape.lt_start_iff` to identify
`s.start w` with a level cut.

### Candidate lemmas (about 120 lines; no hypotheses)
`mem_commC`, `mem_cand1`, `cands_lv`, `cands_df`, `cands_ci`, `cands_st`, `cl_blocks`,
`cands_mem`.
* `c ∈ commC w o Y ↔ ∃ r < |Y|, ∃ b < t, c = ⟨⁅(ent Y r).g, u b⁆, w, comm (o + r, pos b), none, 0⟩`.
* `c ∈ cand1 ↔ ∃ a b, a < b ∧ b < t ∧ c = ⟨⁅u a, u b⁆, 1, comm (pos a, pos b), none, b⟩`.
* levels are `w`, only layer-0 candidates are free, only core records have `ci = some κ`
  (then `κ < t`, `g = u κ`, free), steps of layer 1 are in `[1, t)`.
* `cl ((blocks k-1..0).map g) = closure {⁅u a, u b⁆ : a < b < k}` (so `⊔ lcs G 2` is `Wk u k`).
* candidates of level `w` lie in `lcs G w` (strong induction).

### Layer and list lemmas (about 120 lines; no hypotheses)
`Y_src`, `Y_lv`, `Y_ci`, `Y_mem_of`, `Y_mem`, `off_mono`, `full_append`, `full_prefix`,
`ent_full`, `locate`, `full_cut`: every position `i < |full n|` is `off w + r` with `w < n`,
`r < |Y w|`, and `ent (full n) (off w + r) = ent (Y w) r`; levels are constant on layers, so
`i < off v ↔ lv i < v`.

### Generic good fields (about 80 lines)
`good_mono`, `good_free`, `good_pow`, `good_ci`, `good_st`, `good_mem` for `full n`, by `locate`
and the layer lemmas.

### Facts needing `Dat.Hyp` (about 300 lines)
* `core_Y0`: for `κ < t`, `pos κ < |Y0|` and the record there has `ci = some κ`. Math: `t ≥ 2`
  (as `t ≠ 1`), S2 (`strict_chain_indep`) gives `u κ ∉ closure (u '' Iio κ) ⊔ lcs G 1`; split
  `cand0 = A ++ coreE κ :: [coreE (κ-1), ..., coreE 0]` and use `layer_mem_head`; then `findIdx`.
* `Y_nil`: `m ≤ w → Y w = []` (Lemma K and `layer_card`).
* `steps_Y1`: for `1 ≤ β < t` some record of layer 1 has `lv = 1`, `st = β`. Math: split
  `cand1 = A ++ (block β ++ blocks (β-1..0))`; `cl ⊔ lcs G 2` of the two tails are
  `Wk u (β+1) ≠ Wk u β` (strictness at `k = β + 1`); `layer_head_of_ne` and `layer_append`.
* `lie_app`: `lcs G w ≤ cl ((Y w).map g) ⊔ lcs G (w+1)`. Math: `w = 0` from the enumeration;
  `w ≥ 1` from `lie_lemma` with `H1 = univ`, `P = {a < b < t}`, `E v = set (cands v)`;
  (L2) from `mem_commC` and `Y_src`; (H1) from `lcs G 1 ≤ Wk u t`; (H2), (H3) from one lemma:
  `x ∈ cl (Y v) ⊔ lcs G (v+1)` (Y3) and `zn M (u k)` contains the entries of `Y v` (their
  commutators with `u k` are candidates of level `v+1`) and `lcs G (v+1)`.
* `cands_sup`: `cl (cands v) ⊔ lcs G (v+1) = lcs G v`.
* `span_drop`: `lcs G v = cl ((full m).map g).drop (off v)` for `v ≤ m`, downward induction.
* `card_drop`: `|lcs G v| = p ^ (|full m| - off v)`, downward induction with `layer_card`.
* `full_length_eq`: `|full m| = m` (`card_drop` at `v = 0`).
* `good_lv_lt`, `good_comm`, `good_core`, `good_steps`, `good_span`, `good_powrel`.

## Notes for the integrator
* The only external dependencies are the Stmt stubs `lie_lemma`, `exists_strict_chain`,
  `strict_chain_indep` (no others) and the NF/Comm base lemmas.
* `existence` needs `[Finite G]` only to enumerate `G` and for the index lemmas.
