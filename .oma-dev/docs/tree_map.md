**Erdos1160.erdos_1160.variants.sum: reduction tree, wall analysis and team note**

The live desk API (fetched 2026-11-27) lists 37 steps. 8 are solved, 19 are open leaves and 10 are open internal nodes. Two differences from the snapshot in the task:
- R3.H1.R1.H2.R1.H1 is marked SOLVED on the desk but is missing from the task's solved list.
- Reduction R2.H2.R1 (PR #5909) has no local file in `C:\Users\monir\open-math-agents\reductions\`. I used the desk statements for it.

Saved desk JSON: `C:\Users\monir\AppData\Local\Temp\claude\b596c85084d8d676\f9cebc68-e947-4ea6-b1ff-fe6711c31c1b\scratchpad\tree\desk.json`.

**Legend**
- SOLVED: marked solved on the desk.
- ELEM: elementary, given the solved steps and Mathlib.
- GLUE: follows from another open node by short bookkeeping; CFSG-free.
- LIB: known from refereed pre-2026 results; CFSG/FT-free; needs a big Lean library.
- OPEN: true only through the 2026 preprints (Li-Qiao, Su-Xia); classically open; CFSG/FT-free.
- WALL: every known route needs CFSG or Feit-Thompson (FT).

The verifier corrections are applied throughout.

## Tree

```
ROOT  sum_{n<2^m} g(n) <= g(2^m) eventually   [OPEN + WALL on every branch]
|
+- R1  (H1 & H2 => root; Li-Qiao 15.5/15.7)
|  +- R1.H1  sum_{n<2^m} g <= 2*sum_{k<m} g(2^k)                    [WALL]
|  |  +- R1.H1.R1
|  |     +- H1  abelian classes                                    [SOLVED]
|  |     +- H2  2(S-A) <= 3P                                       [WALL]
|  |        +- R1.H1.R1.H2.R1
|  |           +- H1  large deficit: 4*sum_{2^(m-r) does not divide n} g(n) <= g(2^(m-1))   [WALL]
|  |           |      needs Higman + sharp 2-group bound + Pyber/CFSG (Sims NOT needed).
|  |           |      Can be re-reduced to the three hypotheses of R3.H1.R1.
|  |           +- H2  bounded deficit: 2^(r+2) g(2^k q) <= g(2^(k+r-1))   [OPEN, CFSG-free]
|  |                  Li-Qiao 15.2-15.5 a(N)-weighted count (W_h bound, Lemma 15.5).
|  |                  Su-Xia's version uses Maroti, so it is CFSG-type.
|  |                  Strictly stronger than R3.H2 (one fewer (2/9)k^2 of slack).
|  +- R1.H2  3 g(2^m) < g(2^(m+1))                     [OPEN, CFSG/FT-free, 2-groups only]
|     +- R1.H2.R1  (arithmetic for m >= 64)
|        +- H1  2^(2m^3) <= g(2^m)^27 * 2^(13m^2)  (Higman-type)    [SOLVED]
|        +- H2  log2 g(2^m) <= (2/27)m^3 - m^2/3   = the 2-GROUP FRONTIER   [OPEN]
|           |   BLQR25 and Sims' theorem are not needed; the exceptional input needed is weaker than Li-Qiao Thm 1.4.
|           +- R1.H2.R1.H2.R1  (split on Frattini class 2 = FC2)
|           |  +- H1  FC2                                          [SOLVED, sorry-free, coefficient -10/27]
|           |  +- H2  non-FC2                                      [OPEN]
|           |     +- ...R1.H2.R1
|           |        +- H1  class <= 2                             [SOLVED]
|           |        +- H2  class >= 3, |gamma3| <= 2              [SOLVED]
|           |        +- H3  class >= 3, |gamma3| >= 4              [OPEN]  (cite Li-Qiao Thm 1.4, eps = 1/1024; m=11 is undetermined)
|           |           +- H3.R1
|           |           |  +- H1  class 3, gamma3 central, k <~ sqrt(m)/10^4   [SOLVED]
|           |           |  +- H2  the rest: class >= 4, or class 3 with larger k   [OPEN]
|           |           |         Li-Qiao Thm 1.4 / Su-Xia Prop 6.2
|           |           +- H3.R2  (rank <= m/7 proved inside the file)
|           |              +- H1  class 3, rank > m/7              [OPEN]
|           |              +- H2  class >= 4, rank > m/7           [OPEN]
|           +- R1.H2.R1.H2.R2  (Su-Xia's four populations; alternative split)
|              +- H1  K = bottom (= FC2), factor 4                 [ELEM]
|              |      corollary of the solved FC2 file: per-rank 10m^2 bound + frattini_eq_squareCore
|              +- H2  bounded width |Phi/P3| <= 2^192000           [OPEN]
|              +- H3  central strip |3d - 2m| <= 2d/1000           [OPEN, hardest; Su-Xia s.4-6]
|              +- H4  off-strip                                    [LIB]
|                     Sims/Newman-Seeley count with rank tracking (BNV Ch.5; Su-Xia Prop 3.5);
|                     cubic saving about 1e-7 m^3, works eventually.
|
+- R2  (H1 & H2 & H3 => root)
|  +- R2.H1  2*sum_{k<m} g(2^k) <= g(2^m)                         [GLUE from R1.H2 via R1's sum_le_of_eventual_growth]
|  +- R2.H2  g(n) <= 2^(m-1) g(2^(m-2)) for every non-2-power n < 2^m   [WALL + beyond the preprints]
|  |  |  Tight at n = 3*2^(m-2): needs g(3*2^k) <= 2^(k+1) g(2^k).
|  |  |  Heuristically g(3*2^k)/g(2^k) is about 2^(2k/3) (OEIS data: 8.7, 19.4, 38.9 for k = 7, 8, 9),
|  |  |  but Li-Qiao (error O(k^1.5)) and Su-Xia 8.9 (O(k), unspecified constant) do not give it.
|  |  +- R2.H2.R1
|  |     +- H1  nilpotent, 11 v2(n) <= 7m                         [ELEM]
|  |     |      #nilp(n) = prod over p of g(p^(a_p)) (Mathlib isNilpotent_of_finite_tfae);
|  |     |      solved PC bound + 2^19 <= 3^12 gives log2 #nilp <= 0.0671 m^3 < (2/27)m^3;
|  |     |      solved Higman-type lower bound at m-2.
|  |     +- H2  nilpotent, 7m < 11 v2(n), n not a 2-power         [GLUE on the frontier]
|  |     |      needs an m^2 coefficient < -7/27 at m-3; -1/3 suffices.
|  |     +- H3  non-nilpotent, all non-2-power orders              [WALL]
|  |            odd orders: FT; A5-type orders: CFSG.
|  |            At 3*2^k the trivial bound on C3 x| Q already uses (2^k - 1) g(2^k),
|  |            leaving g(2^k) for the rest; that needs a linear-precision a(N) count.
|  +- R2.H3  2^(2m) g(2^(m-2)) <= g(2^m)                           [GLUE: solved R1.H2.R1.H1 + frontier; margin (8/27)m^2]
|
+- R3  (H1 & H2 => root; Su-Xia 8.7)
   +- R3.H1  large deficit                                          [WALL]
   |  +- R3.H1.R1
   |     +- H1  dyadic comparison, O(m^2) slack                     [GLUE: frontier + solved lower bound, via the file's dyadic_comparison]
   |     +- H2  odd q: g(q)^27 <= 2^(r^3+D)                         [WALL]
   |     |      classical with CFSG: Pyber's general bound gives 0.0295 r^3.
   |     |  +- R3.H1.R1.H2.R1
   |     |     +- H1  g(p^a)^6 * p^a <= p^(a^3)  (PC bound)         [SOLVED]
   |     |     +- H2  g(3^a)^12 <= 3^(a^3+B(a+1)^2)                 [LIB: Sims 1965]
   |     |     +- H3  odd prescribed-Sylow                          [WALL]
   |     |            FT + Pyber's soluble case (Hall/Sylow systems), or CFSG. Classical.
   |     +- H3  mixed prescribed-Sylow g(2^a q) <= g(2^a) g(q) 2^(O(m^2))   [WALL]
   |            Pyber 1993 (n^(75mu+16)) / BNV 16.20 + the nilpotent injection. Classical.
   +- R3.H2  bounded deficit, fixed q                               [OPEN, CFSG-free]
      +- R3.H2.R1
         +- H1  extension encoding                                  [SOLVED]
         +- H2  template-weight bound                               [OPEN]
                Li-Qiao Lemmas 15.4/15.5: a matching decomposition. Needs the a(N)-weighted
                W_h bound; crude |Aut N| counts lose about (2/9)k^2 too much.
```

## (1) Is there a branch whose remaining leaves are all CFSG-free and FT-free?

No.
- **R1** is blocked by R1.H1.R1.H2.R1.H1.
- **R2** is blocked by R2.H2.R1.H3.
- **R3** is blocked by R3.H1.R1.H3 and R3.H1.R1.H2.R1.H3.

This comes from the root statement itself, not from how it was split. The root sums g(n) over every odd n < 2^m. Bounding those needs a log-count of at most (2/27 − δ)m^3. The only known ways are FT plus a soluble count, or CFSG. The root also covers orders with a large odd part where non-solvable groups exist, and there Pyber's prescribed-Sylow theorem (CFSG) is the only known tool. Only orders with a bounded odd part are CFSG-free, because G/O_2(G) embeds in Sym(b).

What is achievable is isolating the walls, and R3 does this cleanly:
- Its two wall leaves are classical refereed theorems (Pyber 1993 / BNV 16.20). They can be carried as named hypotheses.
- All of R3's preprint-dependent pieces are CFSG-free: the 2-group frontier and the bounded-deficit count.
- The R1.H2 subtree is entirely CFSG/FT-free, but it is only half of R1.

## (2) Realistic formalizability of the open leaves, by effort

1. **R1.H2.R1.H2.R2.H1** (small, a few hundred lines). The proof is in `C:\Users\monir\AppData\Local\Temp\claude\b596c85084d8d676\f9cebc68-e947-4ea6-b1ff-fe6711c31c1b\scratchpad\dl\Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H1.lean`. Reuse its `frattini_eq_squareCore` and the per-rank bound `f^27 * 2^(10m^2) <= 2^(2m^3)`, then redo `sum_over_ranks` with factor 4. It only helps closing if the R2 split of R1.H2.R1.H2 is pursued.
2. **R2.H2.R1.H1** (about 1k lines, elementary). Uses the solved PC bound, the solved Higman-type bound and Mathlib's Sylow product. It has no closing value while R2.H2.R1.H3 stays a wall.
3. **Glue leaves R2.H1, R2.H3, R3.H1.R1.H1, R2.H2.R1.H2** (short each). They become provable as soon as R1.H2.R1.H2 is closed.
4. **R1.H2.R1.H2.R2.H4 and R3.H1.R1.H2.R1.H2** (classical; one shared Sims-counting library, probably 5–20k lines). The p=2 version needs rank tracking; the p=3 version needs only the leading coefficient.
5. **2-group frontier leaves** (very large, preprint-level). The most tractable is H3.R2.H1 (class 3, high rank): it is a single Jacobi layer, the rank of Λ³V → W⊗V. Next come H3.R2.H2 and H3.R1.H2 (class ≥ 4), then R1.H2.R1.H2.R2.H2. R1.H2.R1.H2.R2.H3 is hardest (Su-Xia uses LHS spectral sequences and Waterhouse/Sergeichuk pencils, none of which Mathlib has).
   - Suggested next reduction: split H3.R1.H2 using the rank ≤ m/7 lemma already proved in the H3.R2 file. That leaves only the high-rank cases.
6. **R3.H2.R1.H2, then R1.H1.R1.H2.R1.H2** (very large). CFSG-free, but they need Li-Qiao's a(N)-weighted W_h bound, which goes beyond the −1/3 frontier.
7. **Not formalizable now:** R3.H1.R1.H3, R3.H1.R1.H2.R1.H3 and R1.H1.R1.H2.R1.H1 (CFSG/FT; usable as axioms). R2.H2.R1.H3 is a wall and also needs precision beyond what the preprints prove.

## (3) Leaf R3.H1.R1.H2.R1.H2: g(3^a)^12 <= 3^(a^3+B(a+1)^2)

**It is true classically.** Sims 1965 gives log_3 f(3^a) ≤ (2/27)a³ + O(a^{8/3}). Since 12·(2/27) = 8/9 < 1, this leaves (1/9)a³ of slack, and B absorbs small a. The weaker bounds do not reach it: the solved PC bound gives 12/6 = 2 > 1, and Higman's 1960 upper bound gives 12·(2/15) = 1.6 > 1. So it needs a Sims-quality argument. It is CFSG-free and FT-free.

**Its branch cannot close without FT or CFSG.**
- Its sibling R3.H1.R1.H2.R1.H3 (prescribed-Sylow for all odd orders) needs FT plus Hall/Sylow-system theory, or CFSG.
- R3.H1 also needs R3.H1.R1.H3 (Pyber/CFSG).

**What a proof would contribute:**
- It would leave R3.H1.R1.H2 depending only on one classical black box (H3).
- It does nothing for closure unless Pyber is accepted as an axiom.
- It can be avoided. R3.H1.R1's cubic budget only needs an odd-order coefficient c < 2/27, while H2 asks for 1/27. A re-split of R3.H1 with g(q)^14 ≤ 2^(r³+D) lets the solved PC bound handle p = 3: 14·(1/6)(12/19)² ≈ 0.93 < 1, and 27/14 < 2 in the budget. That removes this leaf.
- Its main value elsewhere is the Sims library it would create, which R1.H2.R1.H2.R2.H4 also needs (at p=2, with rank tracking).

## (4) Team note (1,282 characters)

Erdos1160 sum variant, desk status 2026-11-27: 8 of 37 steps solved, all of them 2-group or elementary pieces. No branch avoids CFSG and Feit-Thompson, and with known mathematics none can, because the root sums over odd orders (FT plus soluble-group counting, or CFSG) and over orders with large odd part that admit non-solvable groups (Pyber's prescribed-Sylow theorem, CFSG). Best route: R3. Its only CFSG/FT leaves, R3.H1.R1.H3 and R3.H1.R1.H2.R1.H3, are classical refereed results (Pyber 1993, BNV 16.20) and can be carried as named hypotheses. The rest of R3 is CFSG-free:
(a) the 2-group frontier log2 g(2^m) <= (2/27)m^3 - m^2/3 (R1.H2.R1.H2; open core: class >= 3, |gamma3| >= 4, rank > m/7). Short glue from it gives R1.H2, R2.H1, R2.H3 and R3.H1.R1.H1.
(b) the bounded-deficit count R3.H2.R1.H2 (Li-Qiao Sec. 15, a(N)-weighted).
(c) Sims at p=3 (R3.H1.R1.H2.R1.H2). Classical, but it can be dropped by re-splitting R3.H1 with odd exponent 1/14 instead of 1/27; the solved PC bound then covers p=3.
R2 is dominated: R2.H2.R1.H3 is a CFSG wall, and at n=3*2^(m-2) it needs a linear-precision count that neither preprint gives. Quick wins with little closing value: R1.H2.R1.H2.R2.H1 and R2.H2.R1.H1. Main effort belongs on the high-rank class-3 and class>=4 2-group leaves.

Saved copy: `C:\Users\monir\AppData\Local\Temp\claude\b596c85084d8d676\f9cebc68-e947-4ea6-b1ff-fe6711c31c1b\scratchpad\tree\summary.txt`

## Per-step classifications

### Erdos1160.erdos_1160.variants.sum.R1.H1
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, higman_lower_bound, pyber_prescribed_sylow, cfsg, hall_sylow_basis, feit_thompson
- formalizable: not_foreseeable
- meaning: For every large enough m, count the groups of every order n with 1 <= n < 2^m (up to isomorphism). That total is at most twice the number of 2-groups below 2^m, meaning groups of order 1, 2, 4, ..., 2^(m-1). Put another way: write F(x) for the number of groups of order at most x and F_2(x) for the number of 2-groups of order at most x. The claim is F(2^m - 1) <= 2 F_2(2^m - 1) eventually. So below 2^m, the groups whose order is not a power of 2 are eventually no more numerous than the 2-groups. This is a weak form of the 'almost all groups are 2-groups' statement (Pyber's 2-group domination question), taken at the cutoffs x = 2^m - 1. It does not follow from the parent theorem, and it does not need R1.H2.
- verifier agrees: True
- correction: I could not refute the classification. It stands as given: truth = true_conditional_on_preprint, formalizable_now = not_foreseeable, and the needs list is right for the only known route. Three small inaccuracies in the justification should be fixed. None changes the verdict.

1. The claim that the single-order comparison g(3*2^(m-2)) <= g(2^(m-1)) is "an instance of BNV Question 22.16" is wrong. Q22.16 says n <= 2^m implies g(n) <= g(2^m). For n = 3*2^(m-2) that gives only g(3*2^(m-2)) <= g(2^m). The comparison with g(2^(m-1)) looks downward, to the power of 2 below n, so it is strictly stronger. It implies the 22.16 instance, because G -> G x C_2 gives g(2^(m-1)) <= g(2^m). Its classical openness therefore follows, but it is not an instance. The data also shows the downward comparison fails at small sizes: g(24) = 15 > g(16) = 14 and g(48) = 52 > g(32) = 51.

2. "No CFSG-free bound of the needed quality, n^{(2/27)mu^2 + o(...)}" misstates what is needed. Even with CFSG, the general Pyber/BNV bound n^{(2/27)mu^2 + O(mu^{3/2} or mu^{5/3})} is not enough. What is needed is the prescribed-Sylow form f(n) <= n^{O(mu)} * prod f(p^{a_p}) (Pyber 1993 p.204, or BNV Thm 16.20), combined with Li-Qiao's uniform bound f(p^a) <= p^{2a^3/27 + Ca}.
   - Useful refinement: with CFSG, the published bound BNV Cor 16.21, log2 f(n) <= log2 n * ((2/27)mu^2 + C mu^{3/2}), together with Higman's lower bound, already handles every order 2^a*b with log2 b >> sqrt(m).
   - Only orders with odd part be

### Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, pyber_prescribed_sylow, cfsg, higman_lower_bound, sims_upper_bound, hall_sylow_basis, other
- formalizable: not_foreseeable
- meaning: Let S(m) be the number of groups of every order 1 <= n < 2^m, A(m) the number of abelian ones among them, and P(m) = g(1)+g(2)+g(4)+...+g(2^(m-1)), the number of groups of 2-power order below 2^m. The step says that for all large m, the number of nonabelian groups of order below 2^m is at most 3/2 times P(m): 2(S - A) <= 3P. A(m) is only O(2^m), so it hardly matters. P(m) = g(2^(m-1))(1 + 2^(-Omega(m^2))). So the step amounts to F(2^m - 1) <= (3/2 + o(1)) F_2(2^m - 1). In words: all groups of order below 2^m, other than those of order 2^(m-1), add up to at most about half of g(2^(m-1)). In particular g(3*2^(m-2)), g(5*2^(m-3)), g(7*2^(m-3)) and so on are each at most about (1/2) g(2^(m-1)).
- verifier agrees: True
- correction: I could not refute the classification. The truth label (true_conditional_on_preprint), the needs list and formalizable_now = not_foreseeable all hold up. The errors I found are minor and do not change the verdict.

What I checked independently:
- Small cases. I recomputed the OEIS b-files (A000001 through 2047, with g(1024) = 49,487,367,289, and A000688). The step holds for m = 1..4, fails for m = 5..9 (m = 9: 183,548 > 176,283) and holds for m = 10 (23,515,524 <= 31,658,922) and m = 11 (99,821,068,220 <= 148,493,760,789). S/P is 1.1144 at m = 10 and 1.0083 at m = 11.
- Li-Qiao. In lq.txt, Corollaries 15.10 and 15.11 say what the analyst says. Proposition 15.9 uses Pyber [Pyb93, p.204] with a threshold of 2^342. Proposition 15.7 and Corollary 15.8 handle bounded odd parts without CFSG (Lemma 15.4 needs only Schur-Zassenhaus for a normal 2-subgroup and a cyclic quotient).
- Su-Xia. Theorem 1.1 is as described.
- The child hypotheses. Both H1 and H2 of R1.H1.R1.H2.R1 follow from Corollaries 15.10 and 15.11, so H1 even holds with r = 1.

Is CFSG necessary? I found no route without it. A bounded-quotient extension count only works when the odd part b is bounded, because factor-set data grows like |Gamma|^2 and Gamma can be any subgroup of Sym(b). Crude bounds of the form n^{C mu^2} or 2^{O(Omega^3)} lose at the cubic level, and the intermediate range 342 <= log2 b = o(m) needs a per-order loss of O(m^2) relative to f(2^a). Even odd orders defeat crude bounds: for odd n near 2^m y

### Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2.R1.H1
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, li_qiao_or_su_xia, pyber_prescribed_sylow, cfsg, hall_sylow_basis, sims_upper_bound
- formalizable: not_foreseeable
- meaning: There is a fixed r ≥ 1 with the following property. For every large m, take all orders n < 2^m whose 2-part is at least r+1 powers of two short of 2^m, meaning v_2(n) ≤ m−r−1, i.e. n is not a multiple of 2^(m−r). Together these orders carry at most a quarter as many isomorphism classes of groups as the single order 2^(m−1). The sum includes every odd n < 2^m, the 2-powers 2^a with a ≤ m−r−1, and every mixed order 2^a·b (b odd > 1, a ≤ m−r−1), including orders where non-solvable groups exist. It leaves out only 2^(m−1) and the bounded-deficit orders 2^(m−r)·q with q < 2^r, which the sibling H2 handles. One immediate consequence comes from the term n = 2^(m−r−1): 4·g(2^(m−r−1)) ≤ g(2^(m−1)) for all large m.
- verifier agrees: False
- correction: Most of the classification holds up. The error is that sims_upper_bound should be removed from "needs".

What holds up:
- The truth value (true_conditional_on_preprint) and formalizable_now (not_foreseeable) are right.
- The plain meaning is right.
- Both routes work: r = 1 via Li-Qiao Cor. 15.11, and large r via Pyber, with r ≥ 340 using 75μ+16, or r ≥ 112 using BNV 16.20.
- I recomputed the whole small-case table from OEIS b000001 (scratchpad\lit1160\b000001.txt). Every number matches, including g(1024) = 49487367289.
- The CFSG dependence is real. I found no CFSG-free way to handle orders where non-solvable groups occur. Crude extension counting of R by Q = G/R loses about d(Q)·log2|Aut R| ≈ t·m² bits, against a saving of only about (2/9)·t·m². Bounded d(Q) and Out-type control come from CFSG. Even "non-solvable implies even order" is Feit-Thompson. So Pyber/CFSG is needed on every known route, as claimed. Hall/Sylow-system theory and Feit-Thompson are only internal to Pyber.

The error: Sims (1965) is not needed on any route.
1. At p = 2, Sims' bound (2/27)a³ + O(a^{8/3}) is too weak anyway, as the analyst says.
2. At odd primes, Li-Qiao already gives a bound uniform in p. Their Thm 14.4, a restatement of Thm 1.1, says "There is an absolute constant C such that, for every prime p and every integer m ≥ 1": log_p f(p^m) ≤ 2m³/27 − 4m²/9 + Cm. Li-Qiao's own Prop. 15.9, the same computation as route (b), uses (160) for the odd primes, not Sims.
3. Independently of the preprin

### Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2.R1.H2
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, higman_lower_bound, pc_presentation_count, sims_upper_bound, elementary, other
- formalizable: only_with_major_library
- meaning: Fix r ≥ 1 and a q < 2^r that is not a power of 2. Then, once k is large enough (the threshold may depend on r and q), the order n = 2^k·q has at most a 2^-(r+2) share as many groups as the order 2^(k+r-1).

q = 0 is allowed and trivial, because g(0) = 0. For r = 1 only q = 0 is possible. Write q = 2^a·s with s odd and s ≥ 3, and let K = k + a. Since 2^(k+r-1) ≤ 2^k·q < 2^(k+r) exactly when q ≥ 2^(r-1), the hardest cases compare g(2^K·s) with g(2^(K+⌊log2 s⌋)), where 2^(K+⌊log2 s⌋) is the largest power of 2 not above n. The easiest hard case is r=2, q=3: 16·g(3·2^k) ≤ g(2^(k+1)). Up to the monotonicity g(2^j) ≤ g(2^(j+1)), the step is equivalent to this: for every fixed odd s ≥ 3, g(2^K·s)/g(2^(K+⌊log2 s⌋)) → 0 as K → ∞.

This is stronger than the Higman–Erdős comparison g(n) ≤ g(2^m) for n ≤ 2^m, restricted to fixed odd part, because it compares with the power of 2 below n, not above it.
- verifier agrees: True
- correction: I found no substantive error. I checked the classification against the preprints' HTML and the OEIS data, and it holds.

Checks:
(1) The step matches the parent file Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2.R1.lean. Its main theorem applies H2 only at the fixed r from H1 and each q < 2^r. g 0 = 0 is the theorem Erdos1160.g_zero.
(2) The equivalence claim is right. The step implies that for each odd s ≥ 3, g(2^K s)/g(2^(K+L)) → 0, where L = ⌊log2 s⌋. The proof takes q = 2^a s and r = a+L+1, and needs no monotonicity. The converse needs monotonicity of g(2^j).
(3) All small-case numbers check against the b-file: 15/14, 52/51, 0.865, 0.663, 0.36, 0.104 and 0.00826. At k=9, 16·g(1536) ≤ g(1024) holds. The pairs (r,q) = (5,24), (6,48) and (7,96) still fail at the last available k.
(4) Li–Qiao v3 §15 matches the analyst's description:
- Lemma 15.3: the kernel J_N is a 2-group with |J_N| dividing 2^(r1(n−r1)).
- Lemma 15.4: the extension count is at most a(N)^(h+1)·2^(h·r1(n−r1) + n|Γ|^2).
- Lemma 15.5: W_h(n) ≤ 2^((2/27)n^3 + ((2h−4)/9)n^2 + O(n^(3/2))).
- Propositions 15.6 and 15.7 then give, via h ≤ v−1, the bound 2^(Q(m) − (2/9)m^2 + O_Γ(m^(3/2))).
- Pyber appears only in Corollary 14.6 and Proposition 15.9, never in the bounded-odd-part chain.
(5) Su–Xia's Theorem 1.1 and Proposition 8.9 read as quoted, so both routes to truth are valid.

Is there a cheaper route? I found none. The step forces g(2^(K+1))/g(2^K) → ∞. To see this, take q = 3·2^(r−2) and note g(3·2^K) ≥ g(2^K

### Erdos1160.erdos_1160.variants.sum.R1.H2
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count
- formalizable: yes_large
- meaning: For every large enough m, there are more than three times as many groups of order 2^(m+1) as groups of order 2^m, counted up to isomorphism. This is only about 2-groups. In R1 it gives the geometric tail bound sum_{k<m} g(2^k) <= g(2^m)/2. Combined with R1.H1 (non-2-power orders are at most the 2-power count), that closes the parent.
- verifier agrees: False
- correction: The core verdict holds. R1.H2 is true conditional on the October 2026 preprints. Li-Qiao 2610.14509v3 Thm 14.4, and the computation at the end of the proof of Cor 15.11, give it. Su-Xia 2610.11092v1 Thm 1.2 gives it with p fixed at 2, and so do Thm 1.3 and Cor 8.10. Only 2-groups appear, so CFSG, Feit-Thompson, Pyber and Hall theory are not needed. In Li-Qiao, Pyber is used only for Cor 1.2/14.6 and Section 15, never in 14.3/14.4. In Su-Xia, Pyber and Liebeck-Pyber appear only in Section 8. I checked the small cases against OEIS A000679: the inequality fails for m=0..3 and holds for m=4..10, using a(11) >= 1774274800863737. The R1.H2.R1 arithmetic is also right: 2m^2-20m-65 > 0, and the Lean witness 2k^2+236k+6846 matches. There is no cheaper classical route. A ratio argument still needs an upper bound on the non-Frattini-class-2 count at the m^2 level, and lower bounds alone only give the "frequently" version. The local Higman proof in fact proves exactly that, as frequently_sharp_jump_two_power.

The classification is wrong where it says what is needed and how hard the pieces are:

(1) It says the step "needs the new upper bound with quadratic coefficient -4/9", built from "Sims framework + BLQR25 + Li-Qiao concentration". That is false, and it contradicts the analyst's own earlier remark that only -(2/9+eps)m^2 is needed. R1.H2.R1 asks for -(1/3)m^2. That leaves (1/9)m^2 of slack against the full |GL_d(2)| saving of about 2^{(4/9)m^2}. So BLQR25, which pins the Frattini-cl

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2
- truth: true_conditional_on_preprint
- needs: pc_presentation_count, sims_upper_bound, li_qiao_or_su_xia, other
- formalizable: yes_large
- meaning: For every large enough m, the number of groups of order 2^m (up to isomorphism) is at most 2^((2/27)m^3 - (1/3)m^2). Taking log base 2 of g(2^m)^27 * 2^(9m^2) <= 2^(2m^3) gives 27*log2 g(2^m) + 9m^2 <= 2m^3, so this is an upper bound on log2 f(2^m) whose second-order term is -(1/3)m^2. It only concerns 2-groups, i.e. groups of prime-power order. In the parent reduction R1.H2.R1, this upper bound at m is paired with the lower bound H1 (2^(2m^3) <= g(2^m)^27 * 2^(13m^2), already solved) at m+1 to get 3*g(2^m) < g(2^(m+1)) for m >= 64.
- verifier agrees: True
- correction: I agree with the classification: true_conditional_on_preprint, formalizable yes_large, and none of CFSG, Feit-Thompson, Pyber or Hall theory is needed. I found no substantive error, only the minor imprecisions below.

What I checked and confirmed:
- The step is equivalent to log2 g(2^m) <= (2/27)m^3 - (1/3)m^2, since 9/27 = 1/3.
- Higman's bound (2/27)m^2(m-6) has quadratic coefficient -12/27 = -4/9.
- The data margins for m = 1..11 are correct: negative for m <= 7, positive for m = 8..11.
- The parent reduction R1.H2.R1 pairs H2 at m with H1 at m+1, with threshold m >= 64.
- Li-Qiao arXiv:2610.14509 v3 (12 Nov 2026): Thm 1.1 is f(p^m) <= p^{(2/27)m^3-(4/9)m^2+O(m)}. Thm 1.4 has absolute eps and m0 "for every prime p". Pyber's prescribed-Sylow theorem is cited only for Thm 1.3 and Section 15. The paper does not mention CFSG.
- Su-Xia arXiv:2610.11092 v1 (8 Oct 2026): Thm 1.3 is P_p <= (1+p^{-m^2/300}) R_p, for any fixed prime p.
- Sims' conjecture (error O(m^2)) does not imply the step, so the step was open before these preprints.

Minor corrections:

(1) The Su-Xia main term is misquoted. M_p(m) = p^{(2/27)m^3-(4/9)m^2+m/3-c}/g_p^2 holds only for m ≢ 2 (mod 3), with c = 2 for m ≡ 0 and c = 26/27 for m ≡ 1. For m ≡ 2 (mod 3) it is (1+p^{-3}) p^{(2/27)m^3-(4/9)m^2+2m/9-7/27}/g_p^2, so the linear term is 2m/9, not m/3. Here g_p = ∏(1-p^{-i}). The predicted margin is therefore 3m^2-9m-O(1) for m ≢ 2 (mod 3) and 3m^2-6m-O(1) for m ≡ 2 (mod 3). The m=10 check (35.58 vs 35.53) is s

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count, other
- formalizable: yes_large
- meaning: Let N_m be the number of isomorphism classes of groups of order 2^m whose Frattini subgroup is not both central and of exponent at most 2. For 2-groups Phi(G) = G^2, so these are exactly the 2-groups that are not of Frattini class 2: their lower exponent-2 central series has length at least 3, i.e. they lie outside the family h_2 = {Phi(G) <= Z(G), Phi(G)^2 = 1}. The step says that for all large m, 27*log2(2*N_m) + 9m^2 <= 2m^3. Equivalently, log2 N_m <= (2/27)m^3 - (1/3)m^2 - 1. In context, the parent step is the second-order upper bound log2 g(2^m) <= (2/27)m^3 - m^2/3. The parent reduction splits the 2-groups of order 2^m into the Frattini-class-2 groups (sibling H1, already proved in Lean) and the rest (this step).
- verifier agrees: True
- correction: I found no material error, and the classification stands.

**Statement.** The meaning and the arithmetic check out.
- For 2-groups, Phi(G) = G^2, and the Lean predicate "Phi central and of exponent at most 2" is exactly Frattini class 2.
- (2N)^27 * 2^(9m^2) <= 2^(2m^3) is equivalent to log2 N <= (2/27)m^3 - m^2/3 - 1.
- The parent R1.H2.R1.H2 has coefficient -1/3, and the reduction file splits it into the Frattini-class-2 groups and the rest.
- The small-m values recompute correctly: m=8 gives 1028.9 > 1024, m=9 gives 1385.7 <= 1458, m=10 gives 1886.2 <= 2000.
- The tree status matches the live API: R1.H1 solved; R1.H2.R1.H1 and .H2 solved, .H3 open; H3.R1.H1 solved; everything under H3.R2 and R2 open.
- In the sub-reduction, Subgroup.lowerCentralSeries ⊤ 2 = gamma_3, as the analyst says.

**Literature.** It checks out against the arXiv pages.
- Li-Qiao 2610.14509 v3 (12 Nov 2026), Theorem 1.4: f(p^m) - f_H(p^m) <= p^{(2/27)m^3 - (4/9)m^2 - eps*m^2}, with absolute eps and m0, uniform in p. Here H is the family with Phi <= Z and Phi^p = 1.
- That bound beats the needed -1/3 coefficient for every m >= max(m0, 3), as the analyst says.
- Su-Xia 2610.11092 v1, Theorem 1.3: R_p <= Q_p <= P_p <= (1 + p^{-m^2/300}) R_p, for fixed p.

**Was the step open before 2026?** Yes. Together with the already-proved sibling H1, the step gives log2 f(2^m) <= (2/27)m^3 - m^2/3. That implies Sims's O(m^2) conjecture at p = 2, which was open until these preprints. So "true_conditional_on_preprint"

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3
- truth: true_conditional_on_preprint
- needs: sims_upper_bound, pc_presentation_count, li_qiao_or_su_xia, other
- formalizable: yes_large
- meaning: Let N_m be the number of isomorphism classes of groups G of order 2^m whose third lower central term γ_3(G) = [[G,G],G] has order greater than 2 (so at least 4, because G is a 2-group). In Mathlib, `(⊤ : Subgroup G).lowerCentralSeries 2` is ⁅⁅⊤,⊤⁆,⊤⁆ = γ_3. The other condition, ¬(G' ≤ Z(G)), says the class is at least 3, so it adds nothing. The step claims that for all large m, (8·N_m)^27 · 2^(9m^2) ≤ 2^(2m^3). This is exactly log2 N_m ≤ (2/27)m^3 − m^2/3 − 3. Put simply: 2-groups with a large γ_3 number at most 2^{(2/27)m^3 − m^2/3 − O(1)}. The cubic term matches the count of all groups, so the bound has to be correct in its m^2 term.
- verifier agrees: True
- correction: The classification holds: true_conditional_on_preprint; needs Sims-style pc-presentation counting plus Li–Qiao or Su–Xia; no CFSG, Feit–Thompson, Pyber or Hall theory; formalizable_now yes_large. I found no cheaper route. Five peripheral items need fixing.

WHAT I RE-CHECKED AND CONFIRM
- The inequality is equivalent to log2 N_m ≤ (2/27)m^3 − m^2/3 − 3.
- Lean semantics: Mathlib/GroupTheory/Nilpotent.lean:395 defines lowerCentralSeries S 0 = S and (n+1) = ⁅S_n, S⁆, so index 2 is γ_3, and ¬(G' ≤ Z) is redundant.
- The parent R1.H2.R1.H2 is g(2^m)^27·2^(9m^2) ≤ 2^(2m^3). Siblings H1 and H2 are solved and H3 is open. Children R1.H1 is solved; R1.H2, R2.H1 and R2.H2 are open.
- The H×D_32 lower bound with Krull–Schmidt gives an m^2 coefficient of −14/9, so precision at the m^2 level is unavoidable.
- Small-case thresholds for m = 5..10 are correct.
- Li–Qiao v3 (12 Nov 2026) states Theorems 1.1 and 1.4 as quoted, uniformly in p, and its Theorem 7.1 treats p = 2 explicitly. Su–Xia Theorem 1.3 gives P_p(m) ≤ (1 + p^(−m^2/300)) R_p(m) for fixed p.

CORRECTIONS
1. The m=11 claim is a logical error. f(2048) is unknown. Only the lower bound 1,774,274,116,992,170 (the count with 2-class 2) is known, and a lower bound cannot verify an upper-bound inequality. The threshold for m=11 is N_11 ≤ about 4.31e16. Status: undetermined, heuristically expected to hold. m = 9 and 10 do hold.

2. Cite Theorem 1.4 (restated as Theorem 14.3), not Theorem 1.1.
   - Theorem 1.1 needs the further unrefere

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R1.H2
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count, other
- formalizable: yes_large
- meaning: Indexing first. In this Mathlib, (⊤ : Subgroup G).lowerCentralSeries n is defined with 0 = G and n+1 = ⁅previous, G⁆ (Mathlib/GroupTheory/Nilpotent.lean:395-419). So lowerCentralSeries 2 is gamma_3 = [[G,G],G], not the derived subgroup.

- X is the set of isomorphism classes of groups of order 2^m with nilpotency class at least 3 (commutator not central) and |gamma_3| >= 4.
- C is the set of class-3 groups (gamma_3 central and nontrivial) with |gamma_3| = 2^k, where 1 <= k and 10^8(k+5)^2 + 10^7 <= m, so k <= K(m) ≈ sqrt(m)/10^4 - 5.
- X \ C is therefore every group of order 2^m of class at least 4, plus the class-3 groups with |gamma_3| = 2^k for k >= max(2, K(m)+1). For m < 3.61*10^9 the set C is empty and X \ C = X.

Since (16N)^27 * 2^(9m^2) <= 2^(2m^3) is equivalent to log2 N <= (2/27)m^3 - (1/3)m^2 - 4, the step says: for all large m, the number of these higher-class groups of order 2^m is at most 2^((2/27)m^3 - m^2/3 - 4). This is one leaf of the chain that reduces log2 g(2^m) <= (2/27)m^3 - (1/3)m^2 (step R1.H2.R1.H2) to pieces, each carrying a constant-factor margin.
- verifier agrees: True
- correction: I could not refute the classification; its core holds up when re-derived.

**What checks out**
- **Indexing.** Mathlib/GroupTheory/Nilpotent.lean:395-397 has S.lowerCentralSeries 0 = S and (n+1) = ⁅previous, S⁆, so the series at index 2 is gamma_3.
- **What X \ C is.** It is the class ≥ 4 groups plus the class-3 groups with |gamma_3| = 2^k, k ≥ max(2, K(m)+1). C is empty for m < 3.61e9.
- **The inequality.** It is equivalent to log2 N ≤ (2/27)m^3 − m^2/3 − 4.
- **Membership in H_2.** X \ C lies outside H_2 = {Phi(G) ≤ Z(G), Phi(G)^2 = 1}, because members of H_2 have class ≤ 2.
- **Li-Qiao.** Theorem 14.3 in lq.txt (lines 5676ff) gives f − f_H ≤ p^((2/27)m^3 − (4/9)m^2 − m^2/1024) uniformly in p. The arithmetic gives 2m^3 − (3 + 27/1024)m^2 + 108. Theorem 1.1 needs BLQR25 (eq. 13).
- **Lower-bound family.** H x D_32 has class 4 and gamma_3 ≅ C4, which is not central (Z(D_32) = <r^8>). Combined with Krull-Schmidt cancellation this gives (2/27)m^3 − (14/9)m^2 + O(m).
- **Small cases.** Burrell's count 49,487,367,289 is the one Li-Qiao cite. The m = 10, 11 and 8 checks are right.
- **No CFSG, Feit-Thompson, Hall or Pyber.** Only 2-groups are involved.

**Why no classical shortcut exists (cleaner than the analyst's argument)**
The siblings are all marked solved in Lean: R1.H2.R1.H2.R1.H1, ...R1.H2.R1.H2.R1.H2.R1.H1, ...H2, and ...H3.R1.H1. This step plus those siblings closes R1.H2.R1.H2, which says log2 f(2^m) ≤ (2/27)m^3 − m^2/3 for all large m. That is Sims' conjecture for p = 

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.H1
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count, other
- formalizable: yes_large
- meaning: Let N_m be the number of isomorphism classes of groups G of order 2^m that satisfy three conditions. First, G has nilpotency class exactly 3: gamma_3(G) = [[G,G],G] is nontrivial and central. In Mathlib, (⊤).lowerCentralSeries 2 is gamma_3, and the hypothesis that G' is not central is implied by the next condition, so it adds nothing. Second, |gamma_3(G)| > 2, which for a 2-group means |gamma_3(G)| >= 4. Third, G needs more than floor(m/7) generators (Group.rank G = d(G) = dim G/Phi(G)). The claim is that for all large m, (24 N_m)^27 * 2^(9m^2) <= 2^(2m^3). Equivalently, log2 N_m <= (2/27)m^3 - (1/3)m^2 - log2 24. This is a second-order upper bound. Higman's family alone gives about (2/27)m^3 - (4/9)m^2, so the claim says this class-3 subfamily is at most 2^(m^2/9) times bigger than Higman's family. It is one piece of the tree's target log2 f(2^m) <= (2/27)m^3 - m^2/3 (R1.H2.R1.H2), which drives the growth step 3 g(2^m) < g(2^(m+1)).
- verifier agrees: True
- correction: No real error found. I checked every load-bearing claim against the local reduction files, the desk API, Mathlib source, and the cached preprint texts (scratchpad\dl\lq.txt, sx.txt).

What checks out:
- (⊤).lowerCentralSeries 2 is γ3: Mathlib defines Subgroup.lowerCentralSeries with 0 => S and n+1 => ⁅·,S⁆.
- ¬(G' ≤ Z(G)) is redundant given |γ3| > 2, and m/7 is floor division.
- The 27-power arithmetic is right, including the m=9 and m=10 checks. The value 49,487,367,289 is the figure Li-Qiao quote for groups of order 1024.
- The sibling solved flags and the line counts of their proof files (5,445, 9,899, 11,633) are as stated.
- Only 2-groups occur, so no CFSG, Feit-Thompson, Pyber or Hall theory is needed. In Li-Qiao, Pyber is used only for Theorem 1.3 (2-group domination).
- The claim that the step is conditional on the preprints is right. The nearest classical result is Blackburn's thesis: class at most 3, p odd only, bound p^{(2/27)m^3+O(m^2)}. That does not cover p=2 and has no second-order term, so classical results are indeed insufficient.

Refinements (the classification stands, but these sharpen it):

1. The step needs less than the routes the analyst cites. Every group in the set has G' ≤ Φ(G) with G' not central, so Φ(G) is not central. Either of these results alone then closes the step:
   - Li-Qiao Theorem 1.4 (restated as Theorem 14.3): f(p^m) - f_H(p^m) ≤ p^{(2/27)m^3 - (4/9)m^2 - m^2/1024} for large m, uniformly in p.
   - Su-Xia Proposition 6.2: the number o

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.H2
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count
- formalizable: yes_large
- meaning: Let N_m be the number of isomorphism classes of groups G of order 2^m with three properties: G has nilpotency class at least 4, so gamma_4(G) = [gamma_3(G),G] is nontrivial (that is what "not gamma_3 <= Z(G)" says; in Mathlib, (⊤).lowerCentralSeries 2 is gamma_3); G is not of class at most 2; |gamma_3(G)| > 2; and G needs more than floor(m/7) generators (Group.rank G > m/7). The step claims that for all large m, (24 N_m)^27 * 2^(9m^2) <= 2^(2m^3). Equivalently, log2 N_m <= (2/27)m^3 - (1/3)m^2 - log2 24.

Two of the conditions are redundant. Class at least 4 already gives "not class at most 2". It also gives |gamma_3| >= 4: in a nilpotent group gamma_3 = gamma_4 would force gamma_3 = 1, so gamma_4 < gamma_3 and both are nontrivial. So the set is exactly the 2-groups of order 2^m with class at least 4 and rank above floor(m/7).

In the parent reduction (file ...R1.H2.R1.H2.R1.H2.R1.H3.R2.lean), this step is H2. H1 covers class exactly 3 with rank above m/7. The low-rank case, rank at most m/7, is already proved there (low_rank_bound, which uses a count of marked central-lift presentations of at most 2^((d+1)m(m+1)/2)). Further up, R1.H2.R1.H2 is the m^2-level upper bound g(2^m)^27 * 2^(9m^2) <= 2^(2m^3), which says log2 g(2^m) <= (2/27)m^3 - m^2/3.
- verifier agrees: True
- correction: I agree with the classification. I found no error that would change truth, needs, or formalizability. What I checked:

1. **The statement.** In Mathlib, `(⊤ : Subgroup G).lowerCentralSeries 2` is defined as ⁅⁅⊤,⊤⁆,⊤⁆, which is gamma_3 (Nilpotent.lean:395). The condition ¬(gamma_3 ≤ Z) is the same as gamma_4 ≠ 1. That already implies class ≥ 3, and it also implies |gamma_3| ≥ 2|gamma_4| ≥ 4. So two of the conditions are redundant, as claimed. The step H2 slots into `main` of ...R1.H3.R2.lean exactly as described, alongside H1 and the proved `low_rank_bound`.

2. **Literature.** I read the arXiv v3 HTML of Li-Qiao 2610.14509. Theorem 1.4 says: there are absolute ε > 0 and m₀ such that, for every prime p (so p = 2 is included) and every m ≥ m₀, f(p^m) − f_𝔥(p^m) ≤ p^((2/27)m³ − (4/9)m² − εm²). Here 𝔥 is the family with Φ ≤ Z and Φ^p = 1. Theorem 1.1 is f(p^m) ≤ p^((2/27)m³ − (4/9)m² + O(m)). CFSG does not appear. Pyber is used only for Theorem 1.3, the domination result. Either theorem gives the step, with margin about m²/9.

3. **Why there is no cheaper route.** The analyst understates this point. The map H ↦ H×D32 makes the step imply Sims' conjecture for p = 2:
   - The map sends any group of order 2^n with d(H) > (n+5)/7 − 2 into the set counted by N_{n+5}.
   - It is injective on isomorphism classes, by Krull-Schmidt cancellation.
   - The remaining low-rank groups number at most 2^(n³/14 + O(n²)), which is below 2^((2/27)n³).
   - Together these give log₂ f(2^n) ≤ (2/27)n³

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.H1
- truth: true_known
- needs: elementary
- formalizable: yes_small
- meaning: Fix a large m and look at the groups of order 2^m. For a group G of that order, F = <x^2 : x in G> is its Frattini subgroup Phi(G), because for 2-groups Phi(G) = G^2. K = F^2[F,G] is the next term of the lower exponent-2 central series. So K = 1 says Phi(G) is elementary abelian and central. These are the 2-groups of "Frattini class <= 2" (2-class <= 2), elementary abelian groups included. C is the set of isomorphism classes of such groups. Which representative `choose` picks does not matter: the condition is invariant under isomorphism, and the bridge argument below only uses the chosen representative anyway. The inequality (4|C|)^27 * 2^(9m^2) <= 2^(2m^3) is equivalent to log2|C| <= (2/27)m^3 - (1/3)m^2 - 2. In words: there are at most 2^((2/27)m^3 - m^2/3 - 2) groups of order 2^m of Frattini class 2. That is Higman's cubic term with a quadratic saving of m^2/3. The true saving is (4/9)m^2.
- verifier agrees: True
- correction: No substantive error found. I re-derived each claim and checked the sources.

(1) What the statement means. F = <x^2> = G^2, and for 2-groups this is Phi(G), because [x,y] = (xy)^2 (y^-1 x^-1 y)^2 (y^-2) under Mathlib's convention [x,y] = x y x^-1 y^-1; I checked the identity by hand. K = F^2[F,G] = lambda_3. So K = 1 means exactly that Phi(G) is elementary abelian and central.

(2) The arithmetic. (4|C|)^27 * 2^(9m^2) <= 2^(2m^3) is equivalent to log2|C| <= (2/27)m^3 - m^2/3 - 2. Plain Gaussian-binomial counting does not get there. Its exponent is max over s of s((m-s)(m-s+1)/2 - s), which comes to (2/27)m^3 + m/8 + O(1), so it has no quadratic saving. A GL-orbit saving of (3/4)d^2 near d = 2m/3 is genuinely needed, as the analyst says.

(3) The literature. arXiv:2503.07299 (Blaser, Li, Qiao, Rogovskyy) Theorem 1.3 gives f_{H_p}(p^l) <= p^((2/27)l^3 - (4/9)l^2 + O(l)) with no restriction on p. H_p is defined as Phi central and elementary abelian. The p = 2 case is only sketched: it relies on Fact 4.6 and says the rest is proved "in the same way as the proof of Theorem 4.3". This matches the analyst's description.

(4) The Lean route. On the site, step R1.H2.R1.H2.R1.H2.R1.H1 is solved=true. Its statement is (4*(mk '' {G | card = 2^m ∧ commutator G ≤ center G}).ncard)^27 * 2^(9m^2) ≤ 2^(2m^3), so it has the same constants. PR #802 is merged, commit 5b2ba4d, with 1 check passed. In the local copy class2.lean (5445 lines) I found no sorry, admit, native_decide or axiom. It ends

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.H2
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, pc_presentation_count, other
- formalizable: only_with_major_library
- meaning: For a group G of order 2^m, F is the subgroup generated by squares. For a 2-group this is G^2 = Phi(G) = P_2(G). K = F^2[F,G] is P_3(G), the third term of the lower exponent-2 central series. So C is the set of isomorphism classes of groups of order 2^m whose layer Phi(G)/P_3(G) is small: |Phi(G):P_3(G)| <= 2^192000, i.e. dim Phi(G/P_3(G)) <= S = 192000. The choice of representative does not matter because the condition is an isomorphism invariant. Taking log_2 of (4|C|)^27 * 2^(9m^2) <= 2^(2m^3), the claim is: for all sufficiently large m, log_2 |C| <= (2/27)m^3 - (1/3)m^2 - 2. In words, groups of order 2^m with a bounded second layer number at most 2^{(2/27)m^3 - m^2/3 - 2}, eventually. This is the bounded-width population in the 4-way cover (roots / bounded-width / central strip / off-strip) of reduction R1.H2.R1.H2.R2. Its parent is g(2^m)^27 * 2^(9m^2) <= 2^(2m^3).
- verifier agrees: True
- correction: No real error found. I re-derived the classification independently and agree with it; the points below only add to it.

(1) Lean meaning. In a 2-group, [x,y] = x^-2 (x y^-1)^2 y^2, so G^2 contains [G,G]. That gives F = Phi(G) = P_2. K is the join of the two closures, F^2 and [F,G]. Both are normal (F^2 is characteristic in F), so K = F^2[F,G] = P_3. The condition is therefore |P_2 : P_3| <= 2^192000. It is an isomorphism invariant, so choosing the representative with .choose is harmless. The inequality is equivalent to log2|C| <= (2/27)m^3 - m^2/3 - 2. The checks at m = 8, 9, 10, 11 are correct.

(2) Literature, re-checked in the arXiv HTML. Su-Xia Prop 5.7 says: for fixed p and S >= 1, N_{p,<=S}(m) <= p^{(2/27)m^3 - c_S m^2 log2 m}, with c_S = 1/(100 log2(2S+1)), for m above a threshold depending on p and S.
- It has no odd-p restriction; Lemmas 5.1, 5.3 and 5.5 treat p = 2 separately.
- Its proof cites Lemma 2.8, Lemma 5.2, Lemma 5.5 and the tree identity of Prop 5.6, but not Prop 3.5.
- With c ≈ 5.4e-4, the saving beats m^2/3 + 2 once log2 m >= about 619.
- Li-Qiao 2610.14509 (v3, 12 Nov 2026) states log_p f(p^m) <= (2/27)m^3 - (4/9)m^2 + O(m) with no restriction on p. Since C is a subset of all groups, this also gives the step, because 4/9 > 1/3.
So 'true_conditional_on_preprint' is right.

(3) Is there a cheaper route? There is not, and a lower bound shows why. C is not a sparse class.
- Construction. Take H = F_{d0}/P_{c+1}(F_{d0}) with d0(d0+1)/2 <= S, so d0 <= 619 and

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.H3
- truth: true_conditional_on_preprint
- needs: li_qiao_or_su_xia, pc_presentation_count, other
- formalizable: yes_large
- meaning: Fix a large m and look at groups G of order 2^m, counted up to isomorphism. In the Lean code, F is the subgroup generated by squares. For a 2-group that is the Frattini subgroup Phi(G), because G^2 already contains G'. K = F^2[F,G] = P_2(G), the second term of the lower exponent-2 central series. d = log2|G:Phi(G)| is d(G), the minimum number of generators. C is the set of classes with three properties: (i) P_2(G) != 1, so Phi(G) is not central elementary abelian and G is a non-root in Su-Xia's terms; (ii) |Phi(G):P_2(G)| > 2^192000; (iii) |m - 3d/2| <= d/1000, so d/m is within about 4.4e-4 of 2/3. The inequality (4|C|)^27 * 2^(9m^2) <= 2^(2m^3) is the same as log2|C| <= (2/27)m^3 - (1/3)m^2 - 2. So the claim is that, for large m, groups of order 2^m that are not of Frattini class 2, have generator rank in the central strip and have a large Frattini quotient layer number at most 2^((2/27)m^3 - m^2/3 - 2). This is one of four pieces (root, bounded-width, central-wide, off-strip) whose union bound gives the parent statement log2 g(2^m) <= (2/27)m^3 - m^2/3.
- verifier agrees: True
- correction: I agree with the classification and could not refute it. No substantive error found; there are two small nits.

Checked against the sources:
- **Reduction file.** Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.lean (count_from_cover plus max_budget) confirms that H3 is the "central wide" piece of a four-way union bound. Each piece has budget 2^T/4 with T = (2m^3 - 9m^2)/27. So the target is exactly log2|C| <= (2/27)m^3 - m^2/3 - 2 = lambda(m) + m^2/9 - 2.
- **Lean encoding.** F = Phi(G) because squares already generate G' in a 2-group. K = P_2(G) = gamma_3^(2)(G), and it is normal because both generating sets are conjugation-invariant. Nat.log 2 of the Frattini index is d(G) by the Burnside basis theorem. With truncated subtraction, the two strip clauses mean 1000|2m-3d| <= 2d.
- **Emptiness threshold.** C is empty unless m >= ~575,240. Below that the inequality holds trivially.
- **C is not always empty.** For large m it is nonempty: take G = H x C_8 with H a root having d-1 generators. Then P_2(G) = C_2 and s = m-d-1, which is about m/3. So H3 is not vacuous.
- **Su-Xia (arXiv:2610.11092v1).** Prop 6.2 states N_p(m) <= p^(lambda(m) - m^2/300) for m >= m_0(p), with no O(m) term and lambda(m) = 2m^3/27 - 4m^2/9. Their proof treats p = 2 explicitly. It splits non-roots into three groups: s <= 2 (Prop 5.7), off-strip (Prop 3.5, via Newman-Seeley Ch. 5), and the strip (Props 4.4 and 5.6 under |delta| <= d/1000, plus Lemma 6.1).
- **Li-Qiao (arXiv:2610.14509v3).** Thm 1.1 state

### Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.H4
- truth: true_conditional_on_preprint
- needs: sims_upper_bound, pc_presentation_count, li_qiao_or_su_xia, elementary
- formalizable: yes_large
- meaning: For all sufficiently large m, count the isomorphism types of groups G of order 2^m that satisfy two conditions. (1) K ≠ 1. Here F = <x^2> = G^2, which equals Φ(G) for a 2-group, and K = F^2[F,G] = γ_3^{(2)}(G), the third term of the lower exponent-2 central series. So K ≠ 1 means Φ(G) is not central elementary abelian, i.e. G has exponent-2 (Frattini) class at least 3. (2) The generator rank d = log_2|G:Φ(G)| = d(G) lies off the strip 1000|2m−3d| ≤ 2d. The truncated ℕ-subtractions make this conjunction mean exactly 1000|2m−3d| ≤ 2d. Off-strip is equivalent to d/m < 1000/1501 or d/m > 1000/1499, so in particular |d/m − 2/3| > 2/4503. Writing N for this count, the claim (4N)^27 · 2^{9m^2} ≤ 2^{2m^3} is the same as log_2 N ≤ (2/27)m^3 − m^2/3 − 2. In short: groups of order 2^m with Frattini class ≥ 3 and rank not close to 2m/3 are few compared with the 2^{(2/27)m^3} total. This is the 'off-strip' population of the four-way split in the parent reduction R2, which follows Su–Xia.
- verifier agrees: True
- correction: No real error found. Plain meaning, truth, needs (no CFSG, Feit-Thompson or Pyber) and formalizable_now=yes_large all hold up. I have three refinements.

(1) Low-rank region. The per-rank exponent is NOT x^2(1-x)/2 when x=d/m < 1/2. So "for x <= 3/5 the bound is f(3/5)" is wrong as reasoning, though the constant is right.
- In Su-Xia's proof of Prop 3.5 (read in the HTML version), the leading polynomial is B = x^2(y+z-w)/2 + (wy - w^2/2)z + wz^2/2. I re-derived the identity B = f(x) + w(1-2x-y^2)/2 - w^2 z/2.
- For x >= 1/2 this gives B <= f(x) <= 9/125 on [1/2, 3/5]. For x < 1/2, Su-Xia bound B by 1/16 instead, with B well above f(x).
- A numerical maximisation of B over the parameter region gives: global max 2/27; max over x <= 3/5 is 9/125; max over x < 1/2 is 1/16. At x = 0.2, max B = 0.06 while f = 0.016.
- The effect is real, not only an artefact of B. Take Q = <e, f_i | [f_i,f_j] = 1, class 2>, with L_2 = [e,V] of dimension d-1. Its p-multiplicator has dimension about d^2. Its descendants of order p^m give at least p^{(1-2x)x^2 m^3 - O(m^2)} groups of rank d. That exceeds f(x)m^3 for x < 1/3. The bound for x <= 3/5 is still 9/125, so c_eps = min{7/3375, 7eps^2/15} is correct; 7/15 = (1/2)(3/5 + 1/3).

(2) The "conditional on preprint" label is over-cautious. The localisation is an elementary re-optimisation of a published, refereed per-parameter Sims bound: BNV, proof of Thm 5.7, eqs 5.12-5.14 with Prop 5.5 eq 5.5, log_p T_p(m;d,b,sigma) <= d^2(b-q)/2 + d^2u/2 + (qb - 

### Erdos1160.erdos_1160.variants.sum.R2.H1
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, sims_upper_bound, li_qiao_or_su_xia, elementary
- formalizable: only_with_major_library
- meaning: For every large enough m, the number of groups of order 2^m is at least twice the total number of groups of all the smaller 2-power orders 1, 2, 4, ..., 2^(m-1). The Lean sum over Finset.range m runs over k = 0..m-1, so g(1) = 1 is included. Only groups of 2-power order appear. Nothing about groups of other orders is claimed.
- verifier agrees: True
- correction: I agree with the classification: true_conditional_on_preprint, the needs list, and only_with_major_library. I found no error that changes it. Three small fixes to the justification.

(1) The claim "Any proof must show that the ratio g(2^m)/g(2^(m-1)) is eventually at least about 2m" is wrong as a necessity claim.
- Since S(m) = sum_{k<m} g(2^k) >= g(2^(m-1)), R2.H1 only forces g(2^m) >= 2g(2^(m-1)) + 2S(m-1), so the ratio must be at least 2 plus a little.
- An eventual strict ratio above 3 is enough. This is exactly sum_le_of_eventual_growth in the merged R1 file: the deficit 2S(m) - a(m) drops by at least 1 per step.
- The factor 2m only appears as a sufficient condition if you use the crude bound S(m) <= m*g(2^(m-1)).
- This does not change the conclusion. Any constant ratio threshold still needs log2 g(2^m) - log2 g(2^(m-1)) >= O(1). The leading terms leave a gap of only (2/9)m^2, which the Sims O(m^{8/3}) and Newman-Seeley O(m^{5/2}) error terms swamp. The analyst's own thresholds are correct: c > 2/9 with Higman's 12/27, and c > 7/27 with the desk's 13/27. The desk's R1.H2.R1.H2 uses c = 9/27.

(2) "sims_upper_bound" is not a need as a statement. Sims's bound neither suffices nor is used directly. It enters only as a technique inside Li-Qiao and Su-Xia.
- Su-Xia (arXiv:2610.11092) Theorem 1.2 alone gives f(p^m) = M_p(m)(1 + O(p^{-m/3})) for every fixed prime including p = 2, where M_p has exponent (2/27)m^3 - (4/9)m^2 + linear(m mod 3).
- That formula settles the consecu

### Erdos1160.erdos_1160.variants.sum.R2.H2
- truth: open
- needs: higman_lower_bound, li_qiao_or_su_xia, pyber_prescribed_sylow, cfsg, other
- formalizable: not_foreseeable
- meaning: For every large m, each n with 1 <= n < 2^m that is not a power of 2 has g(n) <= 2^(m-1) * g(2^(m-2)). There is one binding case. The only number below 2^m that is not a power of 2 but has 2-part 2^(m-2) is n = 3*2^(m-2). Writing k = m-2, the step therefore contains the claim g(3*2^k) <= 2^(k+1) * g(2^k) for all large k: groups of order 3*2^k outnumber the 2-groups of order 2^k by a factor of at most 2^(k+1). Every other n has 2-part at most 2^(m-3), and there the bound has about 2^((2/9)m^2) of slack. In R2, H2 is combined with H3 (2^(2m) g(2^(m-2)) <= g(2^m)) to give 2^(m+1) g(n) <= g(2^m) for every n that is not a power of 2.
- verifier agrees: False
- correction: The headline fields are right and should stay as they are: truth=open, formalizable_now=not_foreseeable, and the needs list. I re-derived them. The only n below 2^m with 2-part 2^(m-2) is n = 3*2^(m-2), so the critical case is correctly identified. The small-case table matches A000001. The quotes from Su-Xia match the source text: Prop 8.9 gives log2 f(3*2^a) <= Phi(a) + O(a), and the c=0 term of (29) carries 2^{19a}. For the non-critical n, a consecutive-ratio bound g(2^{j+1})/g(2^j) >= 2^{cj^2} is required, and only the Li-Qiao/Su-Xia precision supplies it.

The error is a necessity claim in part (a) of the justification and in the notes. The justification says the groups with a non-normal Sylow 3 (G/O_2 equal to C3 or S3) 'would need an equivariant, Sims-type count of 2-groups with an automorphism of order 3'. That is false for the G/O_2 = C3 half, which has an elementary pointwise bound:

1. G = K ⋊ C3 with |K| = 2^k. For a fixed K, the isomorphism classes number at most the Aut(K)-classes of subgroups of order 3 in A = Aut(K).
2. Let N be the kernel of A -> GL(K/Phi(K)). It is a 2-group (Burnside). If XN/N and YN/N are conjugate, then X and Y are A-conjugate, since both are Sylow 3-subgroups of YN after conjugation. So the class count is at most the number of order-3 subgroups of a Sylow 3-subgroup of GL_d(F_2), where d = d(K).
3. That Sylow subgroup is C3 wr Syl_3(S_{floor(d/2)}). The elements with x^3=1 number sum_sigma 3^{m'-c(sigma)}, with m' = floor(d/2) and c(sigma

### Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H1
- truth: true_known
- needs: elementary, pc_presentation_count, higman_lower_bound
- formalizable: yes_large
- meaning: For every large enough m, take any n with 1 <= n < 2^m whose 2-part is not too big (v_2(n) <= 7m/11). Then the number of nilpotent groups of order n, up to isomorphism, multiplied by 4^m, is at most g(2^(m-2)), the number of groups of order 2^(m-2). This includes n = 1 and n = 2^a with a <= 7m/11. A finite nilpotent group is the direct product of its Sylow subgroups, so the count is at most the product over p | n of f(p^{e_p}), where f(p^e) is the number of groups of order p^e. The step is therefore a statement about p-groups only: (product of p-group counts) * 4^m <= #(2-groups of order 2^(m-2)), for n below 2^m with a small 2-part.
- verifier agrees: True
- correction: I re-derived the classification independently and found no real error. It is true_known, elementary but large to formalize, and needs no CFSG, Feit-Thompson, Sims, Pyber or the 2026 preprints.

Checks:
(1) Reduction to p-groups. Group.isNilpotent_of_finite_tfae is at Mathlib/GroupTheory/Nilpotent.lean:1236 and Sylow.directProductOfNormal at Sylow.lean:840, as the analyst said. They give N_nil(n) = prod_p f(p^{e_p}), and the inequality also holds as an upper bound.
(2) pc count. A central series with factors of order p gives a_i^p in <a_{i+1..k}> (k-i exponents) and [a_j,a_i] in <a_{j+1..k}> (k-j exponents). That totals C(k,2)+C(k,3) = C(k+1,3) = (k^3-k)/6 exponents, so f(p^k) <= p^{(k^3-k)/6}, uniformly in p.
(3) Upper estimate. log2 LHS <= 2m + (1/6)[a^3 + (m-a)^3/(log2 3)^2]. This is convex in a. At a=0 it is 0.06635 m^3; at a=7m/11 it is 0.0461 m^3.
(4) Higman for p=2. With W = F_2^{d(d+1)/2} and the upper-triangular bilinear cocycle beta, squares give q(v) = beta(v,v) and commutators give c = beta + beta^T, with q(v+v') = q(v)+q(v')+c(v,v'). So W = Phi(H) is central elementary abelian. An isomorphism H/U ≅ H/U' acts on W/U as the natural map T_g for g in GL_d(2), so T_g(U) = U'. The count is #classes >= 2^{s(D-s)-d^2}. At d = 2k/3, s = k/3 this is exactly (2/27)k^2(k-6), and I checked that the bound also holds for k ≡ 1 or 2 mod 3. So the p=2 caveat is harmless; my own derivation settles it without Higman's paper.
(5) Threshold. A numeric check of the two explicit bounds 

### Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H2
- truth: true_known
- needs: elementary, pc_presentation_count, higman_lower_bound, krull_schmidt_or_cancellation
- formalizable: yes_large
- meaning: For every large m, take any n < 2^m that is not a power of 2 and whose 2-part 2^k is large: k = v_2(n) > 7m/11. Write n = 2^k·n' with n' odd and n' ≥ 3. A finite nilpotent group is the direct product of its Sylow subgroups, so the number of nilpotent groups of order n is exactly g(2^k)·∏_{p odd} g(p^{a_p}). The step says this number is at most 2^(m-2)·g(2^(m-2)). Since n < 2^m, n' < 2^J where J = m-k, so 2 ≤ J < 4m/11 and k ≤ m-2. In words: the nilpotent groups of order n, made of a 2-group of order 2^k and an odd nilpotent group of order below 2^J, are fewer than 2^(m-2) times the number of groups of order 2^(m-2).
- verifier agrees: True
- correction: I agree with the mathematics: the step is true, CFSG, Feit-Thompson, Pyber and Sims are not needed, and formalizable_now = yes_large is right. The classification has one factual error and one misleading label.

1. Factual error in the notes, part (b). R3.H1.R1.H2.R1.H1, stated as "∀ p a, p.Prime → g(p^a)^6·p^a ≤ p^(a^3)", is already solved. The desk shows solved=true, and its brief says "ALREADY SOLVED", solved in PR 6695. The notes call it unsolved. R1.H2.R1.H1 (2^(2m^3) ≤ g(2^m)^27·2^(13m^2)) is also solved, but only for large m (it is a ∀ᶠ statement). For small d = J-2 below that threshold, use g ≥ 1 instead. So the PC count and the Higman-type bound are both done. What remains:
- (a) Sylow / FiniteGrp.{0} quotient bookkeeping, medium.
- (d) the Remak-Krull-Schmidt fiber bound g(2^k)·g(2^d) ≤ (m-1)^d·g(2^(m-2)) with k+d = m-2. This is the only large missing piece.
- (e) arithmetic.
I confirmed that Mathlib has no Krull-Schmidt for groups. It has a Fitting decomposition only for modules and Lie modules (RingTheory/Artinian/Module, Algebra/Lie). Algebra/Group/Irreducible/Indecomposable.lean is about indecomposable monoid elements (root systems), which is unrelated.

2. The label "krull_schmidt_or_cancellation" is misleading. Cancellation alone (Lovász hom-counting, G×C_2 ≅ G'×C_2 ⇒ G ≅ G') is elementary. It is needed for every J ≥ 4, but it only covers J ≲ (m/0.0663)^(1/3) ≈ 2.47 m^(1/3). The middle range needs the unique-decomposition fiber bound (r+1)^d, so it needs Krull-

### Erdos1160.erdos_1160.variants.sum.R2.H2.R1.H3
- truth: open
- needs: li_qiao_or_su_xia, sims_upper_bound, higman_lower_bound, pyber_prescribed_sylow, cfsg, pc_presentation_count, other
- formalizable: not_foreseeable
- meaning: For every large enough m, and every n with 1 <= n < 2^m that is not a power of 2, the number of non-nilpotent groups of order n (up to isomorphism) is at most 2^(m-2) * g(2^(m-2)). The hard case is n = 3*2^(m-2), the non-power-of-2 order below 2^m with the largest 2-part. Write k = m-2. At that order the step says: the number of non-nilpotent groups of order 3*2^k is at most 2^k * g(2^k). Every other admissible n has a 2-part of 2^(m-3) or less, or an odd part of 5 or more, which leaves room of size about 2^((2/9)m^2).
- verifier agrees: False
- correction: Most of the analyst's facts check out. The data ratios match (0.25, 0.17, 0.11, 0.075, 0.060, 0.072, 0.074 for k=3..9). G/O_2(G) is C3 or S3, and the reduction to n=3*2^k holds. Su-Xia Prop 8.9 reads as quoted, with the coarse factor 2^{(10+|H|^2)a} in eq. (29), so the O(k) constant is 19 or 46. Li-Qiao Lemma 15.5 has error O(n^{3/2}). CFSG enters only through BNV 16.20 / Pyber for unbounded odd parts.

The error is in points (3) and (4) and the notes. The analyst says the decisive claim nonnil(3*2^k) <= 2^k g(2^k) needs linear-term precision and new mathematics. It does not, because it splits into two parts.

(a) Sylow-3 normal part. These groups are C3 x| P with P mapping onto C2, at most one per Aut(P)-orbit of index-2 subgroups. The elementary abelian P gives 1 orbit; every other P has d(P) <= k-1. So the count is at most 1 + (g(2^k)-1)(2^{k-1}-1) < 2^{k-1} g(2^k). This is exact and elementary, and using orbits avoids the analyst's hidden need for g(2^k) >= 2^{k-1}.

(b) The rest. Here C3 acts nontrivially on N = O_2(G), so Out(N) has an element of odd order. If the outer action on C3 were trivial, C3 would act on N as an inner automorphism of 2-power order, hence trivially, and the Sylow-3 would be normal.
- Su-Xia Lemmas 8.6-8.8 bound this part by 2^{O(k)} times #{N of order 2^k with Out(N) not a 2-group} when G/N = C3.
- When G/N = S3 the bound is 2^{O(k)} times the sum over such bad N of order 2^{k-1} of |Aut N|. Cauchy-Schwarz with Su-Xia Prop 8.5 (log2 M_2(b) = lamb

### Erdos1160.erdos_1160.variants.sum.R2.H3
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count
- formalizable: only_with_major_library
- meaning: For every large enough m, the number of groups of order 2^m is at least 4^m times the number of groups of order 2^(m-2). In logs: log2 f(2^m) - log2 f(2^(m-2)) >= 2m, where f is the number of groups of a given order up to isomorphism. The step only involves the count g at powers of 2, so it is purely a statement about 2-groups. No group of non-prime-power order appears in it. The Lean g counts isomorphism classes in FiniteGrp.{0} with Set.ncard, and its docstring argues the set is finite for n >= 1, so g(2^k) is the real count. Because the claim is eventual, the truncated subtraction m-2 in Lean does not matter.
- verifier agrees: True
- correction: I agree with the classification (true conditional on 2026 preprints, no CFSG, Feit–Thompson or Pyber needed, open before 2026, major library needed). I found no substantive error, and no cheaper route.

SMALL CASES, CHECKED:
- H3 fails for m = 1..10 and holds at m = 0.
- At m = 10: 4^10 * 56092 = 58,816,724,992 > 49,487,367,289, the corrected a(10) (Burrell 2022). Ratio about 2^19.75.
- Higman's count p^{s(N-s) - r^2}, with N = r(r+1)/2, settles m = 11 and m = 12 without the OEIS a(11) comment.
  - m = 11: r = 7, s = 4 gives 2^47 ≈ 1.4e14 > 4.40e13.
  - m = 12: r = 7, s = 5 gives 2^66, slightly better than the analyst's r = 8, s = 4 giving 2^64. Either beats 4^12 * g(2^10) ≈ 8.3e17.
- For m = 13 the crude pc bound g(2^11) <= 2^220 against Higman's 2^91 is useless, as the analyst says.

EXACT GAP:
- Taking Higman's lower bound exactly, H3 needs log2 f(2^n) <= (2/27)n^3 - (26/9)n - 140/27 for large n.
- Any upper bound (2/27)n^3 + a*n^2 + O(n) with a < 0 suffices; a = 0 does not.
- Sims gives error +O(n^{8/3}) and Newman–Seeley +O(n^{5/2}). Neither can work.

CHEAPER ROUTE?
- A ratio or construction argument (central extensions of H by C2^2, counted as Aut(H)-orbits on the 2-multiplicator) cannot be combined with published upper bounds. Its gain per typical H is only 2^{Theta(n^2)}, which the O(n^{5/2}) error swamps.
- So the construction would have to work uniformly for every H, and it fails for, e.g., cyclic or low-rank H, which have O(1) extensions.
- It would also need smal

### Erdos1160.erdos_1160.variants.sum.R3.H1
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, li_qiao_or_su_xia, pyber_prescribed_sylow, cfsg, sims_upper_bound, pc_presentation_count, hall_sylow_basis, feit_thompson
- formalizable: not_foreseeable
- meaning: There is a fixed cutoff r >= 1 with the following property. For all large m (write m = k + r), every order n < 2^m that is not a multiple of 2^(m-r) has at most g(2^m)/2^m groups, i.e. 2^m g(n) <= g(2^m). In words: an order whose 2-adic exponent falls short of m by more than r has at least 2^m times fewer groups than 2^m. The range covers three kinds of order. (i) Smaller powers of two 2^a with a <= m-r-1. This forces log2 g(2^m) - log2 g(2^(m-r-1)) >= m for a fixed r. (ii) All odd n < 2^m. (iii) All mixed orders 2^a q with q > 1 odd and a <= m-r-1, q < 2^(m-a). For every r these include orders that admit non-solvable groups, e.g. 15*2^(k-3) (multiples of 60).
- verifier agrees: True
- correction: I agree with the core classification: true conditional on the preprints, formalizable_now = not_foreseeable. I checked it against the source. The Su-Xia v1 PDF (arXiv:2610.11092) has the following:
- Cor 8.10 is sum_{1<=n<2^m} f(n) <= K 2^{-cm^2} f(2^m). So H1 holds for any r>0.
- Sec 8.7 sets R=1000 (or 2000 with Pyber's n^{75mu+16}). It uses BNV Thm 16.20 (n^{(97/4)mu+278852}) and Cor 16.21 for the odd cofactor f(q), plus Cor 7.1 (log_p X(m) = lambda(m)+O(m)). For H1's index, set m_SX = k+r-1; deficit >= 1000 then corresponds to r = 1000.

The Li-Qiao v3 abstract (12 Nov 2026) confirms Sims' quadratic-error conjecture in the stronger -(4/9)m^2+O(m) form, and that the paper uses Pyber's prescribed-Sylow theorem. On the project side, R1.H2.R1.H1 (the Higman-type bound) is marked solved, and so is the pc bound R3.H1.R1.H2.R1.H1. The small-case data checks out, including Burrell's corrected g(1024). The formal-conjectures file confirms Pantelidakis proved the odd-n case for m>=3619 (BNV Q22.16). Mathlib has no Hall-subgroup or Sylow-system theory; the only "Hall" hits are coprimality lemmas in Sylow.lean, SchurZassenhaus.lean and ZGroup.lean.

None of the following is a refutation; they are refinements.

(1) Sims' published bound is not a real need for H1. It enters only because R3.H1.R1 chose an odd budget of r^3/27, so R3.H1.R1.H2.R1 needs 1/12 at p=3. The cubic identity 2(a+r)^3 - 2a^3 = 2r^3 + 6a^2 r + 6ar^2 leaves room for an odd budget of (2-delta)r^3/27. With that budget

### Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, sims_upper_bound, li_qiao_or_su_xia, pc_presentation_count
- formalizable: yes_large
- meaning: Let E(n) = 27*log2 g(2^n) - 2n^3. This is 27 times the amount by which log2 of the number of groups of order 2^n differs from the Higman-Sims main term (2/27)n^3. The step says there is one constant C such that E(a) <= E(m) + C(m+1)^2 for every a <= m with m >= 3. Equivalently, g(2^m)/g(2^a) >= 2^((2/27)(m^3-a^3) - (C/27)(m+1)^2). As the exponent grows, the error term relative to (2/27)n^3 can never fall by more than a quadratic amount. The statement involves only groups of 2-power order.
- verifier agrees: True
- correction: I could not refute the classification. I checked each of its claims and found no substantive error, only small refinements.

1. Literature. I fetched the arXiv abstract of Li-Qiao arXiv:2610.14509 v3 (100 pages). It proves log_p f(p^m) <= (2/27)m^3 - (4/9)m^2 + O(m). With Higman this gives (2/27)m^3 - (4/9)m^2 + Theta(m), so E(m) = -12m^2 + O(m) and the step holds for some fixed C (about 13 for large m). The paper calls the O(m^2) error "Sims' conjecture" rather than a BNV conjecture; this is only an attribution detail. Its methods are a refinement of Sims, graded Lie brackets, and incidence and Fourier estimates for alternating forms. Pyber's prescribed-Sylow theorem is used only for the 2-group domination result, not for the p-group upper bound. So the analyst is right that this step needs no CFSG, Feit-Thompson, Pyber or Hall theory. "True conditional on the preprint" stands, and "yes_large" understates the size: it means formalizing a 100-page 2026 preprint.

2. Search for a cheaper route. The most promising unconditional idea is lifting each H of order 2^a to the groups of order 2^m that contain H as a subgroup or section. One group G of order 2^m comes from at most 2^{2am} = 2^{O(m^2)} such H, so this would prove the step if every H lifted to at least 2^{(2/27)(m^3-a^3)-O(m^2)} groups. It fails for H of large exponent, for example H cyclic of order 2^{m/2}. A section of exponent 2^k forces lower exponent-p class at least k. A layer-count heuristic then gives only about 

### Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2
- truth: true_known
- needs: feit_thompson, sims_upper_bound, pyber_prescribed_sylow, hall_sylow_basis, other
- formalizable: only_with_major_library
- meaning: There is a constant D such that for every odd number q and every r with q < 2^r, the number g(q) of groups of order q is at most 2^((r^3+D)/27). The right-hand side grows with r, so the tightest case is r = bitlength(q), roughly log2 q. The claim is therefore that the supremum over odd q of 27*log2 g(q) - bitlength(q)^3 is finite. In words: log2 of the number of groups of odd order q is at most (log2 q)^3/27, up to an additive constant at orders just below a power of two. Oddness is essential. For q = 2^a we have 27*log2 g(2^a) ~ 2a^3, which is far above (a+1)^3, so the claim fails without it.
- verifier agrees: True
- correction: No substantive error found. The verdict, the needs list and formalizable_now all stand. I have four refinements, none of which changes the classification.

(1) TRUTH, re-derived. For odd q < 2^r, every prime factor is at least 3, so mu <= log_3 q < r/log2 3. Pyber's bound f(n) <= n^((2/27)mu^2 + O(mu^(5/3))) then gives 27*log2 g(q) <= 2r^3/(log2 3)^2 + O(r^(8/3)), about 0.796 r^3. The BNV excerpt confirms this form of the bound, that logs are base 2, that the soluble case is self-contained, and that the general case (Ch. 16) relies on CFSG. The cited data check out: g(3^7) = 9310 gives 356 against 1728, and g(3^8) = 1396077 gives 551 against 2197. Without oddness the statement is false, since 2a^3 > (a+1)^3 + D for large a. The child reduction H2.R1 checks out too: 81a^2 <= 16r^2 implies 72a^2 <= 15r^2; 121a^2 <= 49r^2 implies 36a^2 <= 15r^2; and the effective coefficient is 15/432 < 1/27.

(2) OVERSTATED NECESSITY CLAIM. The justification says a "sub-quadratic-in-log gluing cost is required". Only the total count has to meet the bound. With sharp Sims-type p-group inputs, the p-power part contributes at most (2/27)/(log2 3)^2 r^3, about 0.0295 r^3. So any gluing cost (the number of groups with prescribed Sylow types) of up to about 0.0075 r^3 in log2 would suffice, and that is cubic. With the child's inputs (coefficient 1/6 for p >= 5 and 1/12 for p = 3, worst case about 0.0332 r^3), the slack is about 0.0038 r^3. Pyber's n^(75mu+16), equivalently the child's E(r+1)^2, is th

### Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H1
- truth: true_known
- needs: elementary, pc_presentation_count
- formalizable: yes_large
- meaning: For every prime p and every a >= 0, the number of groups of order p^a up to isomorphism is at most p^((a^3 - a)/6). Since 6 divides a^3 - a, the Lean form g(p^a)^6 * p^a <= p^(a^3) is exactly equivalent to g(p^a) <= p^((a^3-a)/6). Here g is the ncard of the image of {G : FiniteGrp.{0} | Nat.card G = n} in the isomorphism quotient. The exponent is C(a+1,3) = C(a,2) + C(a,3), which is the number of free exponents in a power-commutator (pc) presentation. This is the classical elementary upper bound for p-groups, much weaker than Sims' (2/27)a^3.
- verifier agrees: True
- correction: I found no mathematical error, and the classification stands: true_known, elementary, no CFSG, Feit-Thompson, Sims or Pyber needed. I re-derived it and checked it against the sources.

1. **Exponent count.** In a central series with factors of order p, g_i^p lies in G_{i+1}, which gives p^(m-i) choices. For i<j, [g_i,g_j] lies in G_{j+1}, which gives p^(m-j) choices. Summing, sum(m-i) = C(m,2) and sum_j (j-1)(m-j) = C(m,3). The total is C(m+1,3) = (m^3-m)/6.

2. **Rigidity (equal data gives isomorphic groups).** The analyst's argument is correct, including the inverse-conjugation point: x_k^{-1} P_{k+1} x_k ⊆ P_{k+1}, together with x_k^p ∈ P_{k+1} (or finiteness by induction), gives x_k P_{k+1} x_k^{-1} ⊆ P_{k+1}. Then |P| ≤ p^m. P maps onto each of the two groups, both of order p^m, so all three are isomorphic.

3. **Arithmetic.** g ≤ p^((a^3-a)/6) gives g^6 * p^a ≤ p^(a^3). The tight case (2,2) is right: 2^6 * 4 = 2^8.

4. **No cheaper route.** Generator or Cayley-table bounds fail. With n = p^a they give exponents of order a^2 p^a or a^3 (log p)^2, which never fit under (a^3-a)/6, and the bound is tight at (2,2) anyway.

5. **Citation.** Moravec, ISBN 978-961-6832-93-9, Theorem 3.5.34, is confirmed (book page 130): f(p^n) ≤ p^((n^3-n)/6), proved by counting (n^3-n)/6 parameters with at most p values each.

6. **Usage in the parent.** This matches the reduction file. odd_cubic_of_sylow uses pc only for p ≥ 5 and drops the factor p^a in hb. The H1 and H2 docstrings say what 

### Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H2
- truth: true_known
- needs: sims_upper_bound
- formalizable: yes_large
- meaning: For the prime 3 only: the number g(3^a) of isomorphism classes of groups of order 3^a satisfies 12*log_3 g(3^a) <= a^3 + B(a+1)^2 for one fixed constant B and every a >= 0. Equivalently, log_3 g(3^a) <= a^3/12 + O(a^2). This is an upper bound on how many 3-groups there are, with cubic coefficient 1/12 (about 0.0833) and a quadratic error term. The statement mentions only orders that are powers of 3, so it is about p-groups and nothing else.
- verifier agrees: True
- correction: No substantive error found, so no correction. I re-derived each part and tried to refute it.

(1) Truth. Sims gives log_3 g(3^a) <= (2/27)a^3 + C*a^(8/3). Multiplying by 12 gives (8/9)a^3 + 12C*a^(8/3), which is at most a^3 once a >= (108C)^3. The finitely many smaller a are absorbed into B, and a=0 gives g(1)=1. In Lean, `g (3^a)^12` parses as (g(3^a))^12. Erdos1160.g is the true count (Set.ncard of a finite set), so there is no junk-value loophole. The OEIS checks for a<=8 are correct, a=2 is the tightest (4096 <= 6561), and the a^3/9 margin is correct.

(2) Parent arithmetic. In R3.H1.R1.H2.R1.lean, the p=3 branch needs 36a^2 <= 15r^2, which follows from 2^11 <= 3^7, so a <= 7r/11 < sqrt(15/36)*r. Coefficient 1/12 is therefore exactly enough. For p >= 5, H1's 1/6 bound with 2^9 <= 5^4 suffices. The 1/30.1, 1/15.1 and 1/32.3 figures are right.

(3) Is Sims necessary, or is there a cheaper route? I tried two cheap refinements of the pc-presentation count, and neither gets below 1/12.
(a) Weighted pc count. Use the lower exponent-p central series, so [P_s,P_t] <= P_{s+t} and P_s^p <= P_{s+1}, and charge each relation only for generators of high enough weight. Many equal layers already give m^3/12. Three layers in ratio (1/sqrt3, rest split evenly) give (x - x^3)/4 at x = 1/sqrt3, which is 1/(6*sqrt3), about 0.096. That is above 1/12.
(b) Definitions argument. Keep only the power relations and the relations [a_j,a_i] with a_i of weight 1; by the p-cover / linear-tail argument 

### Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H3
- truth: true_known
- needs: pyber_prescribed_sylow, feit_thompson, hall_sylow_basis, other
- formalizable: only_with_major_library
- meaning: There is one absolute constant E with the following property. For every odd q, the number of groups of order q is at most 2^{E(r+1)^2} times the product, over primes p dividing q, of the number of groups of order p^{v_p(q)}. Here r is any number with q < 2^r; the sharpest case is r = floor(log2 q) + 1. Put differently: once the isomorphism type of each Sylow subgroup is fixed, there are at most q^{O(log q)} = 2^{O(log^2 q)} groups of odd order q with those Sylow types. Summing over the at most ∏ f(p^{a_p}) possible tuples of Sylow types gives the claim. This is Pyber's prescribed-Sylow estimate, restricted to odd orders and with its exponent weakened from O(μ log n) to O(log^2 n).
- verifier agrees: True
- correction: I agree with the classification: true_known, needs Pyber's prescribed-Sylow bound plus Feit–Thompson (or CFSG), formalizable only with a major library. I found no real error. My checks:

(1) The statement and the definition of g match. In reductions/Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.lean, H3 is exactly the stated Prop. g is the ncard of isomorphism classes in FiniteGrp.{0}, which is the true count for n ≥ 1. q = 0 is excluded by Odd, and q = 1 holds trivially.

(2) Truth is settled by a published result. Pyber (Annals 1993) bounds the number of groups of order n with specified Sylow subgroups by n^{75μ+16}; Venkataraman's survey states it in this form. For odd q < 2^r we have μ ≤ log_3 q < r, so q^{75μ+16} ≤ 2^{r(75r+16)} ≤ 2^{75(r+1)^2}. E = 75 works.

(3) The overhead must be quadratic. Diagonal actions of C_3^a on C_7^b, with a ≈ b/2, give about 3^{b²/4} groups with the same Sylow types. That is 2^{Ω(log² n)}, so no 2^{o(log²)} prescribed-Sylow estimate exists.

(4) I found no cheaper route that avoids Feit–Thompson or CFSG.
- BNV ch. 2, "Some basic observations", says plainly that elementary methods stop at f(n) ≤ n^{nλ(n)} ("about as far as one can go with elementary methods"). That bound is useless here, even for cube-free q, where the target is 2^{O(log² q)}.
- Without solvability, nothing elementary controls non-soluble groups of odd order.
- A cheaper soluble-only argument for n^{O(log n)}, if one exists, would still need Feit–Thompson, so the formaliz

### Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H3
- truth: true_known
- needs: pyber_prescribed_sylow, cfsg, hall_sylow_basis, elementary
- formalizable: not_foreseeable
- meaning: Write an order below 2^m as n = 2^a·q with q odd. The step says the number of groups of that order exceeds (number of groups of order 2^a) × (number of groups of order q) by at most a factor 2^{(E/27)(m+1)^2}, with one constant E for every a, q and m. The 27th powers only clear denominators. So the claim is log2 g(2^a q) ≤ log2 g(2^a) + log2 g(q) + O((log2 n)^2). Put differently, gluing a 2-group to an odd-order part costs at most quasi-polynomially many extra isomorphism types, n^{O(log n)}. That is small next to the cubic size (2/27)a^3 of log2 g(2^a). The parent reduction R3.H1.R1 combines H1 (the dyadic cubic comparison), H2 (a smaller cubic exponent for odd orders) and H3 into the large-deficit bound 2^{k+R}·g(n) ≤ g(2^{k+R}). The comment in the reduction file cites Blackburn–Neumann–Venkataraman (BNV), Theorem 16.20, for H3. That theorem is Pyber's bound for groups with prescribed Sylow subgroups.
- verifier agrees: True
- correction: The core classification holds: true_known, needs pyber_prescribed_sylow + cfsg (+ hall_sylow_basis and elementary bookkeeping), formalizable_now not_foreseeable. Re-derivation: Pyber gives f(n) <= n^{75mu+16} * prod_p f(p^{v_p(n)}). Li-Qiao arXiv:2610.14509 cite this form as [Pyb93, p.204]. The odd factors give prod_{p odd} f(p^{a_p}) <= g(q), because Sylows of a nilpotent group are unique. With n < 2^m and mu < m, the slack n^{75mu+16} <= 2^{91(m+1)^2}, so E = 2457 works. The edge cases (a=0, q=1) are fine and the quoted OEIS values are correct. I found no CFSG-free proof of a prescribed-Sylow bound for non-solvable groups, even with only n^{O(log n)} slack. Feit-Thompson indeed does not help for mixed orders. So "needs cfsg" should read "every known proof uses CFSG", which is what the analyst effectively says.

Minor factual corrections (none change the verdict):
(1) Note 4 says "Burnside transfer is not in Mathlib either". This is false. Mathlib/GroupTheory/Transfer.lean contains Burnside's normal p-complement theorem, MonoidHom.ker_transferSylow_isComplement' (N(P) <= C(P) gives a normal complement). It also has IsCyclic.isComplement': a cyclic Sylow subgroup for the smallest prime has a normal complement. Hence the cyclic-Sylow-2 subcase is elementary for every a, not only a <= 1, and its group theory is already in Mathlib. Such a G is N x| C_{2^a} with |N| = q, so the count is <= g(q)*|Aut N| <= g(q)*q^{log2 q} <= g(q)*2^{m^2}. The a=1 case is the special case P = C_2 a

### Erdos1160.erdos_1160.variants.sum.R3.H2
- truth: true_conditional_on_preprint
- needs: higman_lower_bound, li_qiao_or_su_xia, sims_upper_bound, pc_presentation_count, other
- formalizable: only_with_major_library
- meaning: Fix r >= 1 and 1 <= q < 2^r. The claim is that for all large k (the threshold may depend on r and q), 2^(k+r) * g(2^k q) <= g(2^(k+r)). Put m = k+r. Then any order n = 2^k q in the band below 2^m whose 2-adic deficit m - v_2(n) is bounded carries at most a 2^(-m) fraction of the groups of order 2^m. Three things follow from the statement. (a) The case q = 1 is a statement about 2-groups only: 2^(k+r) g(2^k) <= g(2^(k+r)). (b) An even q = 2^s q' reduces to the odd q' with r - s in place of r, so the claim is the same as its odd-q version. (c) For odd q >= 3 it counts groups of non-prime-power order 2^k q, solvable or not (for example q = 15 allows A5-type quotients). The statement asks for a factor 2^(k+r) of saving, which is much more than the qualitative g(n) < g(2^m).
- verifier agrees: True
- correction: I re-derived the classification independently and agree with it: true conditional on a preprint, needs a major library to formalize, and needs neither CFSG nor Feit-Thompson in principle. I found one real gap in the source check and two wording issues. None of them changes the classification.

1. Li-Qiao gives all of H2, not only q=1 (correction). The analyst only read the Li-Qiao abstract. The body of arXiv:2610.14509v3 has Corollary 1.5, restated as Cor 15.11 in Section 15.7. It states F(2^m - 1)/f(2^m) = 2^{-2m^2/9 + O(m)}. Take m = k+r and n = 2^k q < 2^m. Then 2^m g(n) <= 2^m F(2^m - 1) <= 2^{m - 2m^2/9 + O(m)} g(2^m) <= g(2^m) for large m. That proves H2 for every (r, q).
   - So H2 follows from either of two independent unrefereed preprints, not "only if Su-Xia is correct". The label true_conditional_on_preprint still stands.
   - Same caveat as Su-Xia: used as a black box, Li-Qiao's Cor 1.5 imports CFSG. It relies on Cor 15.10, whose large-odd-part case (Prop 15.9) uses Pyber's prescribed-Sylow theorem.

2. The bounded-odd-q argument checks out. Steps 1-3 are elementary. Two choices of the Sylow 2-core give c <= v_2(q!), and #Hom(H, Out N) <= |Aut N|^{c + Omega(q)} because a group of order 2^c q is generated by c + Omega(q) elements. Lemma 8.8 is the factor-set encoding.
   - I checked R3.H2.R1.H1 as stated in Lean. It is true and elementary: fix the sections to act exactly by action h, and fix reference factor values in each Z(N)-coset. Then equal central corrections

### Erdos1160.erdos_1160.variants.sum.R3.H2.R1.H2
- truth: true_conditional_on_preprint
- needs: elementary, higman_lower_bound, li_qiao_or_su_xia, pc_presentation_count, other
- formalizable: only_with_major_library
- meaning: Fix r ≥ 1 and 0 < q < 2^r, and write q = 2^e·q' with q' odd. For every large enough k there is a finite list of "templates" (N_b, H_b, action_b). Each template has a kernel group N_b, a quotient group H_b, and a choice of automorphisms of N_b for the elements of H_b. Every group G of order 2^k·q must be an extension of some template. The kernel is N_b ≅ core_G(P) = O_2(G), the largest normal 2-subgroup, and the quotient is H_b ≅ G/O_2(G). The outer action that G induces on N_b must match action_b modulo inner automorphisms. Weight each template by |Z(N_b)|^{|H_b|^2}, a crude count of its factor sets. The total weight times 2^{k+r} must be at most g(2^{k+r}). The template condition is the counting device of Su–Xia, Proposition 8.9 / eq. (29). Combined with the solved R3.H2.R1.H1, it gives the parent claim 2^{k+r}·g(2^k q) ≤ g(2^{k+r}).
- verifier agrees: True
- correction: I agree with the substance of the classification: true conditional on the preprints, formalizable only with a major library, and no CFSG, Feit-Thompson, Pyber or Hall theory needed. I checked it against the merged files R3.lean and R3.H2.R1.lean, the desk API (R3.H2.R1.H1 and R1.H2.R1.H1 are solved; R1.H2.R1.H2 is open), and the Su-Xia text for Prop 8.5, Lemmas 8.6-8.8, Prop 8.9 and eq. (29). I found four errors or overstatements, none of which changes the verdict.

(1) Arithmetic slip in item 4. At (r,q)=(1,1), k=9, the step needs 2^{10}·Σ_{|G|=512}|Z(G)| ≤ f(2^{10}). So the average |Z(G)| must be at most 49487367289/(1024·10494213) ≈ 4.61, not "about 2.30". The 2.30 figure divides by 2^{k+2}=2^{11} instead of 2^{k+r}=2^{10}. The conclusion that k=9 almost surely fails still stands: groups of order 512 whose Frattini subgroup Φ(G) is central (2-class 2) have |Z(G)| ≥ |Φ(G)| = 2^{9-d}, and the typical generator rank d is about 5 or 6. The k ≤ 8 failures (2^{k+2}f(2^k) > f(2^{k+1})) check out.

(2) The necessity claim "It needs the strong Sims bound log_2 f(2^m) = λ(m)+O(m)" is too strong. For the q'=1 instances only an upper bound with second-order coefficient below −2/9 is needed: log_2 f(2^m) ≤ (2/27)m^3 − (2/9+ε)m^2. Against the solved Lean lower bound (2/27)m^3 − (13/27)m^2, the coefficient only has to be below −7/27. The project's open step R1.H2.R1.H2 (coefficient −1/3) therefore suffices for every q'=1 instance, with margin (2/27)a^2. This is still beyond Sims and Newm