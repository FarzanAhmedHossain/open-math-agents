# Li-Qiao formalization plan

## route
Use Li-Qiao (arXiv:2610.14509v3) alone, through the existing H3.R2 split, which already proves the rank <= m/7 case (low_rank_bound). The leaves to close are H3.R2.H1 (class 3, rank > m/7) and H3.R2.H2 (class >= 4, rank > m/7). Step ids are prefixed by Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.

Why not Su-Xia (arXiv:2610.11092) or a mix:
- Su-Xia goes through the R1.H2.R1.H2.R2 cover. Its central strip H3 (Secs 4-6) needs H^2(Q,F_2) as central extensions, p-covering groups and nuclei, and a pencil or orbit theory. Its off-strip H4 needs the uniform BNV 5.5/5.6 Sims count, about 9k lines.
- Su-Xia's listed nodes come to about 25k lines, plus the truncated Secs 5-6 (about 6-8k), so about 31-33k. Its group cohomology also has a poor Mathlib base.
- Li-Qiao needs no cohomology. Its only p=2-specific part (Part II, Sec 10) is pure linear algebra over F_2, which gives clean reduction cuts.
- A mix gains nothing. The Su-Xia pieces that could be reused (BNV Ch.5 Sims count) are what Li-Qiao Parts I and III replace.

Li-Qiao items not needed: BLQR25, Higman, Prop 6.5, Prop 12.1(i), Sec 15, and the q >= 3 numerics.

Key simplification: for class exactly 3, Sec 5 (the adjoint-cocycle comparison, Thm 5.2 to Cor 5.11) is not needed. The positive-excess components c(1,j,k,3,v) can be counted trivially, because b_3 = b_c = 0 means Prop 5.10 saves nothing at excess 1. The breadth saving comes only from b_2, through Prop 4.3 (p.25) with Jacobi from Hall-Witt in G. So class 3 needs only Secs 2-4, 6, 11 and 12-14, plus Part II. Do class 3 first: it checks every interface statement before the Sec 5 file is written.

## total_est_lines
30000

## dag_summary
Dependency chain (page citations are to lq.txt page markers):

1. FOUNDATION. Sims-lite library (3.7k, done), plus:
   - INF-1 conditional counting
   - INF-2 Burnside basis and relative-order normal form
   - INF-3 V, W and the map lambda_G (pp.12-13)
   - BNV-5.2 strict flag of a minimal core
   - Sec 2.1 LQ-Sims generating sets (pp.12-14)
   - Prop 2.4 rigidity (p.14), re-keyed from library Theorem R
   - Prop 2.5 data count (pp.14-15)
   - Thm 3.1 power words (p.22)
   This is about 3k new lines for general class, about 2.3k for class 3.

2. GRADED LAYER, on top of 1:
   - Sec 2.2 generic N-series Lie ring (pp.16-17)
   - Sec 2.3 Sims data in L (pp.17-19)
   - Lemma 4.1 (pp.23-24)
   - breadth (48)-(51), (80)-(81)
   - Prop 4.2 with the crude subgroup bound (p.24)
   - Prop 4.3 (p.25)
   - Rem 4.4 / eq (54) (pp.25-26)
   - Lemma 6.1 (p.40)
   This gives the gr-level part of (53)/(55).

3. FIBRE LAYER (class >= 4 only), on top of 1 and 2: Thm 5.2 -> Props 5.3/5.4 -> F-series -> Prop 5.5 -> Thm 5.6 -> Lemma 5.7 -> Cor 5.8 -> Prop 5.9 -> Prop 5.10 -> Cor 5.11, i.e. (74), pp.28-39. Plus the positive-excess part r_i m_{i+1} of Thm 3.1.

4. MULTIPLICITY, on top of 2:
   - Rem 6.4 (p.43)
   - Sec 13.1 S_{Z0} (pp.78-79)
   - core centraliser K (149)-(150)
   - Prop 13.1 (pp.79-80)
   - Prop 13.2 (pp.80-81)
   - Cor 14.1 (pp.81-82)
   Needed only for lambda in {0,1}.

5. PART II, pure F_2 linear algebra, independent of 1-4:
   - D.Alt, Lemma 2.7 (pp.19-20), Prop 7.2 (p.45)
   - Lemmas 8.1/8.2 (pp.45-50), Lemma 9.1, Prop 9.2 (pp.51-53), Prop 10.1 (p.53)
   - Sec 10 chain (Prop 10.2, 10.5, Lemmas 10.7-10.9, Prop 10.10, Reed-Muller 10.11, Prop 10.12, Lemmas 10.13-10.14, Prop 10.15, Prop 10.3) -> Prop 10.4 (pp.54-66)
   - Eq (123) and Thm 7.1 (pp.44, 66-67)

6. PART III ARITHMETIC, on top of the outputs of 2-5:
   - Lemma 6.2 / (83)-(84) (p.41)
   - Thm 6.3 assembly (p.42)
   - Lemma 11.1 (p.67), (129)-(130) (p.70), Lemma 11.2 (pp.68-69), Thm 11.3 (pp.69-71)
   - (134)-(135) (p.72), F_theta (138)-(139) (p.73)
   - Prop 12.1(ii) (pp.74-77), (145)-(147) (pp.77-78)
   - Lemma 14.2 (pp.82-84), (157) (p.85)
   - Thm 14.3 case split (pp.84-86): nonsaturated / lambda >= 2 / small core / lambda in {0,1} with multiplicities
   Then glue to the leaf statements: the 24-factor and the 2^(9m^2) form.

Unique new lines: about 30k on top of the 3.7k library.
- Part I: about 9k.
- Class-3 specialisations: about 2.5k.
- Part II at p=2: about 7.5k, including the overrun.
- Part III: about 6.5k.
- Interface statements and glue: about 4k.

Counting the re-included library and foundation copies across the 9 files, about 55-60k lines are submitted in all.

## split_feasible_under_512KiB
True

## split_plan
Calibration: the library is 162,912 bytes for 3695 lines, about 44 B/line. So 512 KiB is about 11.9k lines, and the library alone uses about 32% of a file.

Every group-level file must re-include:
- the library: 3.7k lines. It can be trimmed to about 2.0k (commutator calculus plus Theorem L, without the codes, shapes and cubic parts) in files that do not need nf/rigidity.
- the LQ foundation: 2.3-3k lines.
That is 6-6.7k duplicated lines (about 270-295 KiB) per group file, leaving about 5k lines for new content. The Part II linear-algebra files need no library, only D.Alt plus Lemma 2.7 (about 750 lines, 33 KiB) duplicated.

Interface technique. Hypotheses are group-level counting Props that inline Mathlib-definable invariants:
- r1 = Group.rank G; r2 = Group.rank of γ2/γ3; m_i = log2|γ_i|.
- lambda from |G:γ2| = 2^(r1+lambda).
- Sims rank s = sInf of Group.rank H over subgroups H with γ2 = ⁅H,H⁆ ⊔ γ3.
- breadth b_i at the graded level, as a max over u in a core image; union-bound over ∃-core sets.
- N_2(r1,r2,s) as the Finset.card of tuples of alternating ZMod 2 matrices with Sims rank s.
- "gr G ≅ gr G'" as the existence of isos γ_i/γ_{i+1} ≃* γ'_i/γ'_{i+1} intertwining commutators.
- Absolute constants are existential (∃ C ∀ m ...).
Each statement is about 40-150 lines of inline Prop; no auxiliary defs are allowed.

REDUCTION A, of open leaf H3.R2.H1 (class 3, rank > m/7). Proposed id ...H3.R2.H1.R1:
- A.H1 CNT3: the class-3 Sims count. Thm 6.3 / (55) / (54) at c=3, with max over b2 in [m3/s, min(m2,m3)], plus the parameter constraints e <= C(lambda,2) (Lemma 6.1), s-1 <= r2 <= C(s,2) and s2 <= r2(lambda+1) (126). File: library 3.7k + about 5k new, about 8.7k lines (about 380 KiB). This is the FIRST MILESTONE.
- A.H2 MULT3: Cor 14.1 at c=3 for lambda <= 1. File: library + foundation + Rem 6.4 + Secs 13-14.1, about 9.5k lines (about 420 KiB).
- A.H3 N2A: Thm 7.1(i) plus Prop 10.1, pure F_2. About 3.2k lines.
- A.H4 N2B: Prop 10.4, minimally hollowing subspaces, pure F_2. About 5-6k lines.
- A.main: Eq 123, Thm 7.1(ii) glue, Thm 11.3, Lemmas 11.1/11.2, (129)-(130), Prop 12.1(ii), P4, Lemma 14.2 (the r1 < m/12 subcase is covered by low_rank_bound's range), (157), the summation over parameters, and the 24-factor glue. Pure arithmetic and ncard, about 4-4.5k lines.

REDUCTION B, of open leaf H3.R2.H2 (class >= 4, rank > m/7). Proposed id ...H3.R2.H2.R1:
- B.H1 GRCOUNT: the number of gr-equivalence classes per parameters and breadth, from Props 4.2/4.3 and Rem 4.4. File: trimmed library 2k + foundation without rigidity 2.5k + Secs 2.2/2.3/4 3k, about 7.5-8k lines.
- B.H2 GRMULT: the same with the multiplicity saving for lambda <= 1. File: B.H1 content plus about 3k, about 10.5k lines. Tight; split further if needed.
- B.H3 FIB: for each G0, the number of classes with gr G ≅ gr G0 is at most 2^(C(r1,2)m3 + s·Tcore − C(r1−s,2)·Σ_{i>=3} b_i + Σ r_i m_{i+1} + C·m·log m), i.e. Sec 5 plus the fibre part of Thm 3.1. File: library + foundation 6.5k + Sec 2.2 + Sec 5 4k, about 10.5-11k lines (about 470 KiB). The tightest file. Fallback: move Thm 5.2 to Props 5.3/5.4 into a group-level 'matched pairs form an N-series' Prop.
- B.H4 = N2A and B.H5 = N2B: byte-identical statements, so the A proofs are resubmitted.
- B.main: union over b with #classes <= #gr-classes × max fibre; Part III general; Thm 11.3 general; Lemma 6.2. About 6k lines.

Closing A and B closes H3.R2, then H3 with the solved H1/H2 siblings, then R1.H2.R1.H2.R1.H2 with the FC2 sibling, then the frontier R1.H2.R1.H2. Open leaf H3.R1.H2 and the Su-Xia leaves R1.H2.R1.H2.R2.H2/H3/H4 are not needed; they belong to alternative reductions. All 9 files fit at 3.2-11k lines, but FIB and GRMULT are close to the cap.

## first_milestone
CNT3, the class-3 Sims-rank count, proved as hypothesis A.H1 of the proposed reduction ...H3.R2.H1.R1. One file: the re-included Sims-lite library plus about 5k new lines.

Statement, self-contained in a Prop: ∃ C, ∀ m r1 r2 s lam, consider the set of FiniteGrp.{0} classes with
- Nat.card = 2^m;
- γ3 nontrivial and central;
- Group.rank = r1;
- rank(γ2/γ3) = r2;
- Sims rank s, inlined as sInf;
- |G:γ2| = 2^(r1+lam);
- m2 = log2|γ2|, m3 = log2|γ3|.

Conclusion:
(a) The set is empty unless 2 <= s <= r1, s-1 <= r2 <= C(s,2), m2-m3-r2 <= C(lam,2) and m2-m3 <= r2(lam+1).
(b) log2 of its ncard is at most C·m·(Nat.log 2 m + 1) + PW + min{A, B}, where:
- PW = Σ_i [r_i m_{i+1} + (r_i − 1)(s_i − r_i)] (Thm 3.1, p.22);
- A = (C(r1,2) − r2)·m2 + max over b2 in [ceil(m3/s), min(m2−m3, m3)] of b2·[s(r2 + m3 − b2 + 1) − C(r1−s,2)] ((55) at c=3, p.26);
- B = N_2(r1,r2,s) + the (54)/(42) remainder, with N_2 the inline Finset count of r2-tuples of alternating ZMod 2 matrices on F_2^r1 with span condition and Sims rank s (pp.19, 25-26).

Proof content:
- INF-1 conditional counting;
- INF-2 Burnside basis and relative orders in abelian 2-groups;
- INF-3 V, W, lambda_G;
- BNV-5.2 minimal core flag;
- Sec 2.1 generating sets for c=3;
- Prop 2.4 rigidity, re-keyed from library Theorem R;
- Prop 2.5;
- Thm 3.1;
- Lemma 2.7(iii), crude form;
- breadth b2;
- Prop 4.2 at i=2 and Prop 4.3, with Jacobi from Hall-Witt in a class-3 group;
- Rem 4.4;
- Lemma 6.1.

It is on the critical path: every case of A.main except the λ <= 1 multiplicity case consumes it, as does Lemma 11.2 at c=3. Most of it (about 3k of the new lines) is the foundation that MULT3, GRCOUNT, GRMULT and FIB re-include verbatim. Prerequisite: first submit reduction ...H3.R2.H1.R1, whose main is pure arithmetic (about 4k lines). Work out its exact CNT3 statement before proving anything.

## first_milestone_est_lines
8700

## first_milestone_closes_any_step
No currently open step. Every open frontier leaf (H3.R1.H2, H3.R2.H1, H3.R2.H2, R1.H2.R1.H2.R2.H2/H3/H4) needs at least 9k new lines; only R2.H1 (ELEM) is small, and it is off this route. CNT3 would close the new step ...R1.H2.R1.H2.R1.H2.R1.H3.R2.H1.R1.H1, once the proposed reduction ...H3.R2.H1.R1 is merged. That is hypothesis H1 of the reduction of open leaf H3.R2.H1.

## risks
['Unrefereed preprint: the load-bearing new parts are Sec 5 (Thm 5.6, Cor 5.11), Remark 6.4 (used by Prop 13.2) and Sec 10 at p=2. A gap in any of them invalidates the corresponding hypothesis after a large investment. Mitigation: class 3 avoids Sec 5 entirely; do it first.', 'Interface misstatement: inline definitions of Sims rank, N_2, breadth and gr-isomorphism must match exactly across CNT3, MULT3, GRCOUNT, FIB and N2A/N2B. If they do not, the main file fails. Write and type-check all the hypothesis statements, and the main arithmetic against them, before proving any leaf.', "Constants that are not explicit in the paper (C in Thm 7.1 and Prop 9.2, C0 in (145), M(theta) in Prop 12.1, C5 in Lemma 14.2, h0 in Prop 10.4) must be either existentially quantified in the hypotheses or made explicit. Thm 11.3's choice of H and m_A depends on them.", "Garbled text extraction: Lemma 11.1's left side, its 117m^2 constant, a = min{(2/5)(s-1)^2, r1/2} in Thm 7.1(ii), and (42) were partly reconstructed. Check them against the PDF before freezing the statements.", 'File-size and compile limits: FIB (about 11k lines) and GRMULT (about 10.5k) are near the 512 KiB / 30 min / 7 GB cap. Plan library trimming and a fallback split of Sec 5 into its own group-level Prop.', 'Pressure on m^2 precision: the slack against Li-Qiao Thm 1.4 is only (1/9 + 1/1024)m^2. The crude subgroup bound (loss s|b|m), dropping delta_p, and the m log m data counts must each be checked against Prop 12.1 and (83)-(84). Multiplicities for lambda in {0,1} are unavoidable: they are worth about 5/9 m^2.', 'Library gaps: the strict-chain core and greedy p-chains give neither minimality nor independence mod Phi, and can overcount r1. The generating-set existence must be redone with Burnside-basis selection (INF-2, BNV-5.2), and translated to relative-order normal forms.', 'Mathlib gaps that cost more than estimated: Burnside basis, Gaussian binomials, Reed-Muller/Boolean degree, Fourier analysis on F_2 matrices (Lemma 10.13, Prop 10.15), and quotient-of-subgroup coercions in Thm 5.2. The Sims-lite blueprint undershot by 30-60%.', 'Real and natural-number inequality proofs (Prop 12.1 case split, (129)-(130), Lemma 11.1, Lemma 14.2 with m^(1/3) terms) may be slow or brittle under nlinarith. Use integer surrogates.']

# Skeptic checks

## sound=False
- The plan's own numbers do not add up. It lists 11 proof files: CNT3, MULT3, N2A, N2B, A.main, GRCOUNT, GRMULT, FIB, N2A', N2B', B.main. Two reduction files come on top. Summing its per-file midpoints (8.7+9.5+3.2+5.5+4.25+7.75+10.5+10.75+3.2+5.5+6) gives about 75k submitted lines, not the stated '55-60k across 9 files'.
- The 30k unique total is optimistic. The cited pages (pp.12-26, 28-39, 40-45, 45-67, 67-86) come to about 76 pages of dense, unrefereed research mathematics. 30k lines is about 395 Lean lines per page. Coq Odd Order ran at about 500-700 lines per page of source, and it also built its own library. Here Mathlib is thin for p-groups: no Burnside basis, Gaussian binomials, Reed-Muller degree, Fourier analysis on F_2 matrix spaces, or easy quotient-of-subgroup layers. A realistic range is 45-70k unique lines, and about 100-150k submitted once the per-file duplication is counted.
- The plan's risk list says 'the Sims-lite blueprint undershot by 30-60%', but no estimate in the plan carries that correction. The blueprint on disk (C:\Users\monir\open-math-agents\.oma\h2\blueprint.md, line 722) estimated about 5200 lines and the library came out at 3695, so the stated calibration is not even consistent with the evidence. Either way, the estimates are unadjusted guesses.
- The comparator is the wrong size. The 3695-line library proves only a weak 2/25 Sims bound, which closed the p=3 leaf R3.H1.R1.H2.R1.H2. It assumes relative orders p and rests on BNV inputs that the blueprint says are only cited by LQ (BNV 5.2, 5.6). 'Re-keying' its rigidity and normal forms to LQ Sims generating sets with relative orders p^a(i,j) (blueprint note 4(a)) is a rewrite. The 2.3-3k 'foundation' budget for 8 items (INF-1/2/3, BNV-5.2, Sec 2.1, Props 2.4/2.5, Thm 3.1) is about 300 lines each. That is implausible: the plan's own risk list says generating-set existence must be redone with Burnside-basis selection, and in the library existence plus shapes alone took about 1.5k lines.
- Sec 5 is the hardest and least-checked part of the paper (pp.28-39, Thm 5.2 through Cor 5.11, with the quotient-coercion Mathlib gap). It is budgeted at 4k lines, about 330 per page. With 6.5k duplicated lines, FIB is already about 11.5k lines, roughly 500 KiB at 44 B/line, which leaves no margin under the 512 KiB cap. Realistically Sec 5 alone is 8-12k lines, so FIB must become 2-3 files, each re-including about 6.5k lines. The same applies to GRMULT (10.5-11k).
- The first milestone, CNT3 (8.7k lines in one file), is probably over budget. Its roughly 5k new lines must cover the whole foundation plus Sec 2.2/2.3, Lemma 4.1, Props 4.2/4.3, Rem 4.4, Lemma 6.1, Lemma 2.7(iii) and Thm 3.1. Realistically that is 8-10k new lines, so 12-14k in total, which exceeds one file. 'The first milestone is one file' is therefore unlikely without a further nested reduction.
- Part II at p=2 is 7.5k lines for about 23 pages, including the Fourier analysis of the GL_k(2) indicator (Lemma 10.13, Prop 10.15), Reed-Muller (Prop 10.11) and the determinant constraint (Prop 10.10). N2B at 5-6k for pp.54-66 is optimistic; 8-10k is more realistic. File size is not the problem here, since these files carry no library, but the total is understated.
- A.main is called 'pure arithmetic, 4-4.5k lines', yet it carries Thm 11.3, Lemmas 11.1/11.2, (129)-(130), Prop 12.1(ii) (4 pages), Lemma 14.2 (3 pages), the Thm 14.3 case split, the parameter summation and the 24-factor glue. Much of this is multivariate real inequalities with m^(1/3) terms and constants the paper never makes explicit (C, h0, M(theta), C5, C0). It also needs bridge facts, such as Group.rank G <= m for |G|=2^m and the ranges of all parameters, for the union over parameter tuples. Expect 7-10k lines and brittle nlinarith. Making the implicit constants explicit is unbudgeted work.
- The per-file overhead model is not fully justified, and it misses an option. A hypothesis proof imports its step module, and reduction modules import their parent: R_..._H3_R2 imports R_..._R1 and contains proved lemmas such as lift_kernel and low_rank_bound. So def-free lemmas placed in reduction A or B would be inherited by every descendant, and need not be re-included. This is blocked for the library as written, which has 68 def/abbrev/structure declarations while reduction files allow only H defs. The plan neither exploits this nor explains why it cannot. The cost model of 6-6.7k duplicated lines in every group file is therefore unverified in both directions.
- Compile limits are not calibrated. No compile time or memory figure for the 3.7k-line library is cited. The 30 min / 7 GB limits, not the 512 KiB cap, are likely the binding constraints for 10-11k-line files of heavy group theory (simp, group, nlinarith over commutator identities). 'split_feasible_under_512KiB: true' is argued from bytes alone.
- The interface statements will not be the 40-150 lines each that the plan assumes. The CNT3 conclusion uses PW = sum_i [r_i m_{i+1} + (r_i-1)(s_i-r_i)], but r_3, s_1, s_2 (relative-order data) are not among the fixed parameters (m, r1, r2, s, lam), so the statement is ill-formed as written. It also uses 'N_2 + remainder' where log2 N_2 is meant. Each fix adds inline quantifiers that every consumer file must unfold. Inline definitions of gr-isomorphism (isomorphisms of subgroupOf quotients that intertwine commutator maps), Sims rank (an sInf over subgroups) and breadth, repeated byte-identically across about 8 hypotheses plus both mains, will each need several hundred lines of per-file bridging to the local definitions. The 4k glue budget does not cover that.
- The existing assets are overstated. The task says merged or solved pieces of the frontier subtree (FC2 etc.) are in proofs\Erdos1160...R1.H2.R1.H2.*. The only matching file is ...R1.H3.R2.H1.lean, an 820-byte sorry stub for the very leaf being planned. Solved status therefore rests only on the tree_map/desk claims, not on local Lean files.

Files checked: library C:\Users\monir\open-math-agents\proofs\Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H2.R1.H2.lean, parent reduction C:\Users\monir\open-math-agents\reductions\Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.lean, blueprint.md, tree_map.md, and the section headers of lq.txt.

Verified facts:
- The library is 3695 lines and 162,912 bytes (44 B/line, as the plan states). It is general in p (hp : p.Prime), but it was used to close the p=3 leaf R3.H1.R1.H2.R1.H2 with the 2/25 bound. It contains 68 def/abbrev/structure declarations.
- The leaf statements are as the plan describes. H3.R2.H1 is class exactly 3 with |gamma_3| > 2 and rank > m/7. H3.R2.H2 is class >= 4. The target is (24N)^27 * 2^(9m^2) <= 2^(2m^3), i.e. log2 N <= (2/27)m^3 - m^2/3 - O(1). The H3.R2.H1 proof file is a sorry stub.
- Reduction files do hold proved lemmas (lift_kernel, low_rank_bound, ...), and child modules import their parents. Shared def-free code can therefore be inherited instead of duplicated, which the plan ignores.

Verdict:
- The route is reasonable (Li-Qiao, class 3 first), and 'feasible under 512 KiB' holds in principle, because nested reductions can always split further.
- The size accounting is optimistic and internally inconsistent: its per-file figures add to about 75k submitted lines, against the claimed 55-60k.
- Realistic figures are 45-70k unique lines and 100-150k submitted, over 15-25 files.
- FIB, GRMULT and probably CNT3 each need a further split.

Before committing to the plan:
- measure the library's compile time and memory;
- fix the CNT3 statement (bind r_i and s_i, and use log2 N_2);
- decide whether def-free shared lemmas can live in the reduction files A and B.

## sound=False
- The CNT3 statement does not type-check as written. The binder list is only m r1 r2 s lam, but the conclusion uses m2 and m3, which are not quantified (the set ranges over groups whose m2 and m3 vary). PW = Σ_i [r_i m_{i+1} + (r_i−1)(s_i−r_i)] also uses r3 and the layer sizes s_i, which are not parameters. At c=3 the i=3 term (r3−1)(m3−r3) depends on r3, and s_i clashes with the Sims rank s. Fix: quantify m2, m3 and r3 (or take a max over r3 ≤ m3, absorbed into C·m·log m), and write s1 = r1+lam, s2 = m2−m3, s3 = m3 explicitly.
- Alternative B is not specified, and its stated source is wrong. 'The (54)/(42) remainder' cites (42) (p.18-19), Sims' naive count, which carries an O(m^2) error term. That error cannot be absorbed at the required precision (slack about m^2/9). The correct B is the δ_p form of Thm 6.3 / (86) (p.42). Concretely, B is A with the first-layer part (C(r1,2)−r2)s2 − C(r1−s,2)b2 replaced by N_2 + (C(r1,2)−r2)(s2−r2). The cost term s·b2·(r2+m3−b2+1) and the max over b2 must still apply inside B.
- The milestone closes no existing step. Reduction ...H3.R2.H1.R1 does not exist in C:\Users\monir\open-math-agents\reductions; the only file for H3.R2.H1 is a 9-line sorry stub at C:\Users\monir\open-math-agents\proofs\Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.H1.lean. So 'CNT3 closes ...R1.H1' depends on a reduction whose main (about 4-4.5k lines) is unwritten. That main includes Thm 11.3, Prop 12.1(ii) and Lemma 14.2, whose constants the paper leaves implicit, plus glue to N2A/N2B/MULT3 with byte-identical inline N_2 and Sims-rank definitions. The plan itself says to fix the statements first, so the real first milestone is that reduction file with all hypothesis statements type-checked. Proving CNT3 before main checks against it risks a statement mismatch and wasted work.
- The 5k-line estimate is optimistic. The Sims-lite library has no Frattini, Group.rank or Burnside-basis material, no graded Lie ring, no subgroup-count bound (Lemma 2.7(iii)) and no Gaussian binomials (grep found none). Its rigidity is keyed to strict-chain codes, not to Sims generating sets with (d_k), f and relative orders a(i,j) (p.13-14), so Prop 2.4 must be essentially rebuilt. Other new work: the uniform conditional-counting chain (data → power words → brackets by breadth → deeper), Lemma 2.3 (s−1 ≤ r2), and the Hall-Witt Lie ring. With the documented 30-60% undershoot this is about 6.5-8k new lines, so 10-12k with the 3.7k library, which is at or over the about 11.9k-line / 512 KiB cap for one file.
- Minor point: the min{A,B} should be applied per b2 before taking the max over b2 (log of the sum over b2 ≤ log m + max_b2 min(A(b2),B(b2))). The stated min(max_b2 A, B) is valid only once B is given its own max over b2.

Verdict: unsound as stated. The core mathematics holds; the problems are in the statement's specification, its sequencing and its size.

What I checked and found correct against lq.txt:
- Def 2.1 / (17) (p.11) matches the inline sInf Sims rank.
- Constraint (a) is correct:
  - 2 ≤ s ≤ r1 (p.11).
  - s−1 ≤ r2 ≤ C(s,2) is Lemma 2.3 / BNV Cor 5.3 (p.12).
  - m2−m3−r2 ≤ C(lam,2) is Lemma 6.1 (p.40).
  - m2−m3 ≤ r2(lam+1) follows from exp(L2) | exp(L1) ≤ p^(lam+1).
- A matches (55) at c=3 (p.26). Tcore and Σ_{i≥3} b_i are empty sums, leaving (C(r1,2)−r2)m2 + b2[s(r2+m3−b2+1) − C(r1−s,2)].
- The b2 range [ceil(m3/s), min(m2−m3, m3)] is (48)/(51)/(80) (pp.24-25, 41).
- The key simplification is right. At c=3, Cor 5.11 / (74) reduces to the trivial count C(r1,2)·m3 of the c(1,j,k,3,v) entries: index ranges p.14 and the combination on p.39, including the −r2·m3 zero tails. So Sec 5 really is unnecessary for class 3.
- PW is (47) (p.22). The data count is Prop 2.5 (p.15), p^{O(m log m)}.

On the critical path: H3.R2.H1 is hypothesis H1 of the merged reduction ...R1.H3.R2. Its main combines H1 and H2 with the proved low_rank_bound. Closing it is needed on this route, and A.main would consume CNT3.

The objections are listed in problems: unbound variables, the mis-cited and unspecified B, the claimed closure resting on an unwritten reduction, and the file-size risk.

Files examined:
- C:\Users\monir\open-math-agents\reductions\Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.lean (H1 lines 21-26, main line 298)
- C:\Users\monir\open-math-agents\proofs\Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R1.H2.R1.H3.R2.H1.lean (sorry stub)
- C:\Users\monir\open-math-agents\.oma\h2\tree_map.md
- lq.txt lines 600-960, 1150-1660, 2520-2780

# DAG by part

## LQ-part-I
Nothing in Part I is specific to p = 2: every statement and proof in Secs 2-6 is uniform in p, and ZMod 2 needs no special care.

The frontier needs log2 g(2^m) <= (2/27)m^3 - m^2/3. The FC2 part is already solved, with coefficient -10/27. So only the non-FC2 groups remain. Li-Qiao Thm 1.4 bounds them by (2/27)m^3 - (4/9 + eps)m^2. That leaves a quadratic slack of only (1/9 + eps)m^2, so Part I has to be formalized to exact m^2 precision. Linear and m log m errors are harmless.

What Part III and Part II actually consume from Part I:
- PROP-2.4 and PROP-2.5;
- THM-3.1;
- THM-5.1 (eq 55, used directly in Part II Lemma 11.2);
- THM-6.3;
- REM-6.4 (Part III Prop 13.2);
- LEM-6.1 and LEM-6.2 with (80), (81), (83), (84);
- REM-4.4 / eq (54), only for Part II Thm 11.3 in the nonsaturated range.

The whole Sec 5 chain is required: THM-5.2 -> PROP-5.3/5.4 -> F-series -> PROP-5.5 -> THM-5.6 -> LEM-5.7 -> COR-5.8 -> PROP-5.9 -> PROP-5.10 -> COR-5.11 -> THM-5.1. The breadth savings are what bring the class >= 3 cubic coefficient from 2/25 down to 2/27.

Not needed for the upper bound:
- PROP-6.5, since delta_p <= 0 by definition and can be dropped;
- Lemma 2.7(i), (ii), (iv) inside Part I.

Part I alone does not finish the job. The frontier also needs:
- Part II: N_p bounds in the nonsaturated range, including the binary endpoint (Sec 10). This is the only p = 2-specific part.
- Part III: Prop 12.1 optimisation, Prop 13.1 multiplicities and Prop 13.2. The multiplicity division by roughly |GL_{r1}| x |GL_{r2}| is worth about 5/9 m^2, far more than the 1/9 m^2 slack, so it cannot be skipped.

Minimality of the Sims rank (BNV-5.2) is not used in the counting steps of Part I itself (Secs 3-5). Part I uses it only for the independence of the core in V, which Thm 3.1, Prop 4.3 and r_1 = d(L_1) depend on, and Part II needs the exact Sims rank. The library's maximal strict chain is therefore not enough.

### INF-0 Sims-lite library (re-included) (routine, ~0 lines, pp n/a (blueprint .oma/h2/blueprint.md))
The existing kernel-accepted 3695-line library. It provides commutator calculus C1-C5 (including the three-subgroup lemma mod N and [gamma_a,gamma_b] <= gamma_{a+b}), Theorem L (core generators generate every layer, at subgroup level), strict-chain cores S1/S2, greedy p-power chains, normal forms nf/nf_surj, Existence, Rigidity via the diagonal subgroup of G x G', and a shape/code count.
- depends: 
- mathlib gap: none: already done

### INF-1 Conditional-count framework (routine, ~300 lines, pp implicit throughout Secs 3-6)
For a finite type of arrays A x B and the set S of pairs realised by some group: card S <= card(proj_A S) * max over a in proj_A S of card(fibre_a). Iterated for chains of projections, so that statements of the form 'the number of distinct arrays arising from groups realising fixed data is at most p^E' can be multiplied. The realised set is defined by an existential over (G : Type) [Group G] [Fintype G] together with a list of generators.
- depends: 
- mathlib gap: Finset.card_le_mul_card_image exists, but there is no packaging for 'distinct arrays realised by some group'. Universe and Type-existential bookkeeping is needed.

### INF-2 Abelian p-group Burnside basis and minimal generating sets (classical, ~350 lines, pp used in Sec 2.1 p.13, Thm 3.1 proof p.22, (35)-(37) p.18)
For a finite abelian p-group L, elements generate L iff their images span L/pL over F_p. Hence d(L) = dim L/pL, any generating set contains a minimal one, and a minimal generating set has F_p-independent images in L/pL. Also: for an ordered generating set with relative orders p^{a_j}, the coordinate normal form sum e_j x_j with 0 <= e_j < p^{a_j} is unique, and sum a_j = log_p |L|.
- depends: 
- mathlib gap: Mathlib has the structure theorem (AddCommGroup.equiv_directSum_zmod_of_finite) and frattini, but no Burnside basis theorem and no relative-order normal form for abelian groups. The library's nf works with elementary p-chains, so a translation layer is needed.

### INF-3 Frattini quotients V, W and the map lambda_G (eqs 18-20) (classical, ~350 lines, pp p.12 (Def 2.1, eqs 17-20))
V = G/G^p G_2 ≅ L_1/pL_1 and W = G_2/G_3 G_2^p ≅ L_2/pL_2 are F_p-spaces of dimensions r_1 and r_2. Commutation induces an alternating bilinear map lambda_G : V x V -> W whose values span W. The Sims rank is s(G) = min{dim U : U <= V, lambda(U,U) = W}.
- depends: INF-2
- mathlib gap: Not in Mathlib: the F_p-module structure on the p-elementary quotients and bilinearity of the commutator mod G_3 G_2^p. LinearMap / AlternatingMap exist.

### BNV-5.2 Strict flag for a minimal core (with Lemma 2.3) (classical, ~300 lines, pp p.12-13 (Lemma 2.3, Sec 2.1 citing BNV Prop 5.2/Cor 5.3))
If U <= V has minimal dimension s with lambda(U,U) = W, then U has an ordered basis u_1..u_s such that W_k = span{lambda(u_a,u_b) : a<b<=k} is strictly increasing, 0 = W_1 < ... < W_s = W. Consequently s-1 <= r_2 <= C(s,2) (Lemma 2.3), and the core generators are F_p-independent in V.
- depends: INF-3
- mathlib gap: Not in Mathlib. This is the linear-algebra version of the library's S1. The library's strict chain gives neither minimality nor independence mod Phi, so this must be redone.

### SEC2.1 LQ-Sims generating set existence (classical, ~1100 lines, pp p.12-14 (Sec 2.1))
Every nonabelian group of order p^m has an ordered generating set (g_{i,j}) with: g_{1,1..s} a minimal core with the strict flag (d_k); g_{1,*} a minimal generating set of L_1; g_{2,j} = [g_{1,f(j)}, g_{1,k}] for d_{k-1} < j <= d_k, giving a basis of W and a minimal generating set of L_2; g_{i,j} (i >= 3) chosen from {[g_{i-1,a}, g_{1,b}] : b <= s} (with a > d_{b-1} when i = 3) as a minimal generating set of L_i; relative orders a(i,j) (eq 25); a unique Sims normal form (26) with 0 <= e(i,j) < p^{a(i,j)}; power words (27) and commutator coefficients (28).
- depends: INF-0, INF-2, INF-3, BNV-5.2
- mathlib gap: Not in Mathlib. This adapts the library's Theorem E. It needs Theorem L (Lemma 2.2 / eq 34: G_{i+1} = [G_i, H]), extraction of minimal generating sets from candidate commutators (BNV 3.7, via INF-2), and translation between relative-order normal forms and the library's elementary p-chains.

### PROP-2.4 Rigidity (BNV Thm 5.6) (classical, ~250 lines, pp p.14)
For nonabelian G, the isomorphism class is determined by p, c, s, (r_i), (d_k), f, the higher index pairs, (a(i,j)), the full power word array b(i,j,u,v), and the commutator coefficients c(i,j,k,u,v) in the selected ranges: (1,j<k<=r_1); (2, k<=s, j>d_{k-1}); (i>=3, k<=s).
- depends: INF-0, SEC2.1
- mathlib gap: Not in Mathlib. The library's Theorem R already proves exactly this index pattern (I_1, I_2 with cidx k <= st i, I_3 core). What remains is to re-key it to the LQ data and the relative-order power words.

### PROP-2.5 Count of recorded Sims presentation data (classical, ~150 lines, pp p.15-16)
The number of choices of recorded data (c, s, (r_i), (d_k), f, the higher index pairs, a(i,j)) is at most 2^{O(m)} m^{2m} C(m-1, sum r_i - 1) = p^{O(m log m)}.
- depends: SEC2.1
- mathlib gap: Routine Fintype counting, analogous to the library's shape count (m+2)^{5m}.

### SEC2.2 Graded Lie ring of an N-series (generic) (classical, ~700 lines, pp p.16-17 (eqs 29-31; Gorenstein 5.6))
For any descending series (F_i) of a group with [F_i, F_j] <= F_{i+j} and F_{c+1} = 1, the commutator induces well-defined biadditive alternating maps F_i/F_{i+1} x F_j/F_{j+1} -> F_{i+j}/F_{i+j+1} satisfying the Jacobi identity (31), via Hall-Witt mod F_{i+j+k+1}. Applied to the LCS, this gives the associated graded Lie ring L = ⊕ L_i (29)-(31) and Remark 2.6. Applied to the comparison series in G(0) x G(1), it is reused in Sec 5.2.
- depends: INF-0
- mathlib gap: Not in Mathlib: there is no Lazard / associated graded Lie ring of a group filtration. LieRing exists, but there is no graded construction from groups. Build this once, generically, so that Sec 2.2 and Sec 5.2 share it. Working layer-by-layer with bilinear maps between quotient groups, rather than a DirectSum LieRing instance, is recommended.

### SEC2.3 Sims data inside L (eqs 32-41) (routine, ~400 lines, pp p.17-19)
Homogeneous generators ḡ_{i,j} and C_core = <ḡ_{1,1..s}>. (34): L_2 = <[C_core, C_core]>, L_{i+1} = [L_i, C_core]. The Sims lift (36). (37): p^{a(i,j)} ḡ_{i,j} = sum_{v<j} b(i,j,i,v) ḡ_{i,v}, so (a, b(i,j,i,·)) determine the graded abelian group. (41): the L_{i+1}-component of [g_{i,j}, g_{1,k}] equals [ḡ_{i,j}, ḡ_{1,k}]_L. The bracket on L_2 x C_core is recovered from the recorded c(2,j,k,3,v) via Jacobi, by induction on k.
- depends: SEC2.1, SEC2.2, INF-2
- mathlib gap: Not in Mathlib; this is a bookkeeping layer. The recovery-by-Jacobi step is short but fiddly.

### LEM-2.7(iii) Subgroup count in abelian p-groups (crude form suffices) (classical, ~150 lines, pp p.20 (Lemma 2.7(iii)); used in Prop 4.2 p.24)
An abelian p-group of order p^e has at most p^{b(e-b+1)} subgroups of order p^b (BNV 20.15). For Part I, the crude bound p^{be} suffices: a subgroup of order p^b is generated by <= b elements. Also, every subgroup of order <= p^b lies in one of order exactly p^b.
- depends: INF-2
- mathlib gap: The exact bound is not in Mathlib. The crude bound needs d(K) <= log_p|K| (via INF-2). Mathlib's Sylow.exists_subgroup_card_pow_prime_le gives the extension to exact order. Parts (i), (ii), (iv) of Lemma 2.7 are not used by Part I. They are used by Parts II/III and the abelian count.

### THM-3.1 Power word arrays (new, ~250 lines, pp p.22)
For fixed recorded data, log_p #{realised b(i,j,u,v)} <= sum_i sum_{v<=r_i} [r_i m_{i+1} + (r_i - v)(a(i,v) - 1)] <= sum_i [r_i m_{i+1} + (r_i - 1)(s_i - r_i)]. The key fact is b(i,j,i,v) ≡ 0 mod p, by independence of ḡ_{i,·} in L_i/pL_i.
- depends: SEC2.1, INF-2, INF-1
- mathlib gap: Not in Mathlib. With elementary p-chains this says: the coefficient on chain heads is 0 and the coefficients on the a(i,v)-1 non-head chain entries are free.

### LEM-4.1 Bracket determined by core restrictions (new, ~180 lines, pp p.23-24)
Two graded Lie brackets on L with L_2 = <[C,C]_t> and L_{i+1} = [L_i, C]_t: (i) if they agree on L_1 x C and L_2 x C, they agree on L_2 x L_1; (ii) if they agree on L_i x C for all i, they agree on L_a x L_b for max(a,b) >= 2; (iii) adding agreement on L_1 x L_1 gives agreement everywhere.
- depends: SEC2.2, SEC2.3
- mathlib gap: Not in Mathlib. This is the Lie analogue of the library's Theorem L (BNV 20.13 with L_1 replaced by C_core). Induction plus Jacobi.

### DEF-48/49/51 Breadth sequence (routine, ~150 lines, pp p.24-25 (48)-(51), p.41 (79)-(81))
b_i = max_{u in C_core} log_p |[L_i, u]_L|, attained at h_i; |ker ad(h_i)| = p^{s_i - b_i}; 0 <= b_i <= min(s_i, s_{i+1}), b_c = 0. (51): s_{i+1} <= s b_i. (80): m_3/s <= |b| <= m_3. (81): the number of breadth sequences is <= 2^{m_3} <= 2^m.
- depends: SEC2.3
- mathlib gap: First isomorphism theorem for AddMonoidHom and cardinalities: available. Otherwise routine.

### PROP-4.2 Higher core bracket maps (new, ~250 lines, pp p.24)
For a fixed breadth sequence, log_p #{families of maps L_i x C_core -> L_{i+1}, 2 <= i <= c-1} <= sum_{i=2}^{c-1} s b_i (r_i + s_{i+1} - b_i + 1). Per core generator: choose a subgroup of order p^{b_i} containing the slice image, then the images of the r_i generators.
- depends: DEF-48/49/51, LEM-2.7(iii), SEC2.3, INF-1
- mathlib gap: Not in Mathlib. With the crude subgroup bound the exponent becomes s b_i (r_i + s_{i+1}), which loses at most s|b|m in total. That is negligible against the -C(r1-s,2)|b| saving for s = O(sqrt m), but this must be checked against Part III Prop 12.1 / (83)-(84).

### PROP-4.3 Leading layer L_1 x L_1 -> L_2 (new, ~350 lines, pp p.25)
With c >= 3 and a fixed core map L_2 x C_core -> L_3 of breadth b_2, the number of restrictions L_1 x L_1 -> L_2 is <= p^{C(r1,2)s_2 - C(r1-s,2) b_2}. The core-outside pairs are free (p^{s_2} each). For outside-outside pairs, ad(h_2)[x,y] is fixed by Jacobi (52), so each lies in one coset of ker ad(h_2). Combined with Prop 4.2 this gives the bracket count (53). For c = 2 the trivial bound applies.
- depends: LEM-4.1, PROP-4.2, DEF-48/49/51, SEC2.2, INF-1
- mathlib gap: Not in Mathlib. This is a fibre count: a set whose pairwise differences lie in ker has size <= |ker|.

### REM-4.4 Np-alternative (eq 54) (new, ~250 lines, pp p.25-26)
With the r_2 defining values fixed, the leading-layer exponent is <= min{(C(r1,2) - r2)s_2 - C(r1-s,2) b_2, N_p(r1,r2,s) + (C(r1,2) - r2)(s_2 - r2)}, where N_p is log_p of the number of surjective alternating maps of Sims rank exactly s (21).
- depends: PROP-4.3, INF-3, BNV-5.2
- mathlib gap: Needs N_p as a Fintype count of AlternatingMap/LinearMap with Sims rank exactly s, and the lift count |pL_2| = p^{s2-r2}. NOT needed for the saturated range: there delta_p <= 0 is simply dropped. It is needed only for Part II Thm 11.3 (nonsaturated range).

### THM-5.2 Coordinate-preserving partial isomorphisms (new, ~1000 lines, pp p.28-31)
Let G(0), G(1) realise the same recorded data and full power words, and let all Sims-generator commutators agree at excesses < eps. Then for k <= u <= c with u < k + eps: (i) there is a unique coordinate-preserving isomorphism phi_{k,u} : G_k(0)/G_{u+1}(0) -> G_k(1)/G_{u+1}(1) (62); (ii) it intertwines conjugation by corresponding generators (63). Also the remainder lemma (66): a matched pair differs by z in G_{k+eps}(1).
- depends: SEC2.1, INF-0
- mathlib gap: Not in Mathlib. This is the heaviest single item: a step-by-step extension over the cyclic extensions K_{i,j} = <g_{i,j}> K_{i,j-1} inside quotient groups, with normality, unique expressions and multiplication checks (65). Quotient-of-subgroup coercions are painful. The library's diagonal-subgroup trick handles only the k = 1 case directly (as a rigidity of G/G_{u+1}). General k needs the paper's construction.

### PROP-5.3 Products and inverses of matched pairs (new, ~180 lines, pp p.31-32)
Pairs matched below excess eps in degree i are closed under products and inverses. The first possible difference Delta_{i,eps} (61) is additive: Delta(g1 g2) = Delta(g1) + Delta(g2) and Delta(g^-1) = -Delta(g).
- depends: THM-5.2
- mathlib gap: Not in Mathlib; uses centrality of G_{i+eps}/G_{i+eps+1} in G_i/G_{i+eps+1}.

### PROP-5.4 Commutators of matched pairs (new, ~300 lines, pp p.32-33)
If (g1(0),g1(1)) is matched in degree i and (g2(0),g2(1)) in degree j (below excess eps), then the commutator pair is matched in degree i+j when i+j <= c, and is trivial otherwise.
- depends: THM-5.2, PROP-5.3
- mathlib gap: Not in Mathlib. Needs expansion of [w1, w2] for Sims words into products of conjugates of generator commutators (induction on word length with [xy,z] and [x,yz]), the same in both groups, then transport by phi_{i+j,u}.

### SEC5.2-N Comparison N-series F_i (new, ~120 lines, pp p.33-34)
F_i <= G(0) x G(1) (pairs matched below eps in degree i; F_i = 1 for i > c) is a descending terminating N-series: F_{i+1} <= F_i and [F_i, F_j] <= F_{i+j}. Hence gr F is a graded Lie ring.
- depends: PROP-5.3, PROP-5.4, SEC2.2
- mathlib gap: Mathlib has the subgroups of the product. The Lie structure comes from the generic SEC2.2.

### PROP-5.5 Commutator comparison via Sims lifts (new, ~250 lines, pp p.34-35)
For 1 <= i <= c-eps: F_i/F_{i+1} ≅ L_i ⊕ L_{i+eps} via (pi_i, Delta_{i,eps}). For matched pairs with data (x, xi), (y, eta): Delta_{i+j,eps}([g1(0),g2(0)], [g1(1),g2(1)]) = delta(x,y) + [x,eta]_L + [xi,y]_L, where delta(x,y) is the Sims-lift commutator difference (67).
- depends: SEC5.2-N, PROP-5.3, SEC2.3
- mathlib gap: Not in Mathlib; first isomorphism theorem plus biadditivity in gr F.

### THM-5.6 Commutator differences are adjoint cocycles (new, ~250 lines, pp p.35-36)
Under agreement at excesses 1 <= e < eps and a common bracket, delta extends to an alternating biadditive map delta : L x L -> L with delta(L_i,L_j) <= L_{i+j+eps}, satisfying (71): [x,delta(y,z)] + [y,delta(z,x)] + [z,delta(x,y)] = delta([x,y],z) + delta([y,z],x) + delta([z,x],y).
- depends: PROP-5.5, SEC5.2-N, SEC2.2
- mathlib gap: Not in Mathlib; Jacobi in gr F transported through (68)/(72).

### LEM-5.7 Recovery in the second layer (new, ~100 lines, pp p.36)
If delta(C_core, C_core) = 0 and delta(y_j, ḡ_{1,k}) = 0 for k <= s and j > d_{k-1}, then delta(L_2, C_core) = 0 (induction on k via (71) and y_j = [ḡ_{1,f(j)}, ḡ_{1,l}]).
- depends: THM-5.6, SEC2.3
- mathlib gap: none beyond the above

### COR-5.8 Recovery at the current excess (new, ~220 lines, pp p.37)
If excess-eps components agree for every selected relation with a core input, then delta(L, C_core) = 0, delta(L_{>=2}, L) = 0, and [delta(x,y), h]_L = 0 for x, y in L_1 and h in C_core. So only the outside-outside first-layer relations (s < j < k <= r_1) can differ at excess eps.
- depends: THM-5.6, LEM-5.7, SEC2.3
- mathlib gap: none beyond the above. Needs the generation of L_{>=2} by left-normed core words (from 34 / Theorem L).

### PROP-5.9 Agreement from selected relations (new, ~130 lines, pp p.38)
If the excess-e components agree for all selected relations and all 1 <= e < eps, then the commutators of the Sims lifts of any x in L_i and y in L_j agree at all excesses < eps. This supplies the hypothesis of Thm 5.2 from selected-relation data only.
- depends: COR-5.8, THM-5.6
- mathlib gap: none beyond the above; induction on e

### PROP-5.10 One-excess estimate (new, ~300 lines, pp p.38-39)
With all components at excesses < eps and the bracket fixed: each outside-outside L_{eps+2}-component lies in a coset of ker ad(h_{eps+2}) (size p^{s_{eps+2} - b_{eps+2}}). So all selected excess-eps components have <= p^{C(r1,2)s_{eps+2} + s sum_{i=2}^{c-eps-1} r_i s_{i+eps+1} - C(r1-s,2) b_{eps+2}} choices.
- depends: PROP-5.9, COR-5.8, DEF-48/49/51, INF-1
- mathlib gap: Not in Mathlib; a fibre count relative to a reference group.

### COR-5.11 Positive-excess bound (new, ~150 lines, pp p.39)
For a fixed bracket, log_p #{positive-excess components} <= C(r1,2) m_3 + s sum_{i=2}^{c-2} r_i m_{i+2} - C(r1-s,2) sum_{i=3}^{c-1} b_i (74).
- depends: PROP-5.10, INF-1
- mathlib gap: Iterated conditional counting plus Finset.sum reindexing identities.

### THM-5.1 Fixed-breadth relation bound (new, ~250 lines, pp p.26 (statement), p.39-40 (proof))
For fixed recorded data, power word array and breadth sequence b: log_p #{commutator coefficient arrays} <= (C(r1,2) - r2) m_2 + s sum_{i=2}^{c-2} r_i m_{i+2} + sum_{i=2}^{c-1} b_i [s(r_i + s_{i+1} - b_i + 1) - C(r1-s,2)] (55). Combines (53) and (74), then subtracts r_2 m_2 for the defining commutators g_{2,j} = [g_{1,f(j)}, g_{1,k}]. The case c = 2 is handled separately.
- depends: PROP-4.2, PROP-4.3, COR-5.11, PROP-2.4, INF-1
- mathlib gap: Assembly only. Part II Lemma 11.2 also uses (55) directly.

### LEM-6.1 e <= C(delta,2) (new, ~250 lines, pp p.40)
With delta = s_1 - r_1 and e = s_2 - r_2: e <= C(delta,2). Decompose L_1 = ⊕<x_j> with |x_j| = p^{1+t_j}. Then pL_2 is generated by the elements p[x_j,x_k], of orders <= p^{min(t_j,t_k)}, and sum_{j<k} min(t_j,t_k) <= sum_{j<k} t_j t_k <= C(delta,2).
- depends: SEC2.2, INF-2
- mathlib gap: Needs the structure theorem (in Mathlib) applied to the layer L_1, the bound 'order of a group generated by elements of order p^{n_i} is <= prod p^{n_i}' (not packaged), and bilinearity of the bracket (SEC2.2).

### LEM-6.2 Tcore bounds (with 83-84) (routine, ~150 lines, pp p.41)
Tcore = sum_{i=2}^{c-2} r_i m_{i+2} satisfies Tcore <= (m_2^2 - s_2^2)/2 and Tcore <= s m_2 (|b| - b_2). Hence the bounds (83)-(84) on X (78).
- depends: DEF-48/49/51
- mathlib gap: Finset sum inequalities only

### THM-6.3 Joint array bound (main Part I result) (new, ~250 lines, pp p.42 (statement and proof to p.43))
For fixed recorded data and breadth sequence: E := log_p #{(power word array, commutator array) pairs} <= (1/2) r_1^2 m_2 + X + (1/2) m_2 z_bal + 3 m_2 m_3 + 2 m_2 e + r_1 + delta_p, with z_bal = r_1 - 2m_2 and delta_p = min{0, N_p - (C(r1,2) - r2) r2 + C(r1-s,2) b_2} <= 0. For the saturated range one may take the weaker statement with delta_p replaced by 0.
- depends: THM-3.1, THM-5.1, LEM-6.2, REM-4.4
- mathlib gap: Arithmetic over Nat/Int with the parameters (75)-(76). The dependence on REM-4.4 is needed only for the version with delta_p.

### REM-6.4 Saving from affine constraints on core-outside coefficients (new, ~250 lines, pp p.43)
If the core-outside leading coefficients c(1,j,k,2,v) mod p (j <= s < k) satisfy affine equations of rank >= q, uniformly over the conditional choices, then q may be subtracted from (55) and from (85) with delta_p omitted. Part III Prop 13.2 uses this with q = s (dim K) r_2.
- depends: THM-6.3, PROP-4.3, THM-5.1
- mathlib gap: Needs counting the solutions of a rank-q affine system over F_p inside the (Z/p^{a})-coordinate fibres; the reduction L_2 -> L_2/pL_2 has constant fibres of size p^{s2-r2}. Not in Mathlib in this form.

### PROP-6.5 Saturated-range map count (new, ~250 lines, pp p.43)
For C(s-1,2) < r_2 <= C(s,2): N_p(r1,r2,s) = C(r1,2) r2 + O(1), and delta_p = 0. Uses the fact that a uniformly random map restricted to Λ²U is surjective with probability prod (1 - p^{-j}) > 1/4.
- depends: REM-4.4, INF-3
- mathlib gap: Needs the count of surjective linear maps over F_p (not in Mathlib) and the product bound (43)-(44). NOT needed for the frontier upper bound, because delta_p <= 0 by definition. It only explains why nothing is lost in the saturated range.

## LQ-part-II
All of Part II's F2 content is needed, apart from what is specific to q >= 3. Thm 1.1 at p = 2 (and the weaker frontier log2 g(2^m) <= (2/27)m^3 - m^2/3) is assembled from fnab = fns + fsat (88). Part II supplies only Thm 11.3: fns(2^m) <= 2^{(2/27)m^3 - A m^2} for A > 4/9 (Thm 1.1), or for any A > 1/3 (frontier). The remaining (2/27)m^3 - (4/9)m^2 + O(m) comes from Part III (fsat) plus Higman.

Weakening the target to -1/3 removes nothing in Part II. Thm 11.3's proof needs a saving c*h*m^2 that is linear in h = s-1, with c > 0 and an uncontrolled absolute error C*m^2, so H must be taken large whatever A is. That forces three things:
(a) Thm 7.1(i) at p = 2 for r2 <= C(h,2)-1. This needs Lemma 8.1 (upper bound), Lemma 8.2 with kappa_2 < 2 (needed exactly at M = C(h,2)-1), Lemma 9.1 and Prop 9.2.
(b) Thm 7.1(ii), the binary endpoint r2 = C(h,2), which occurs for every h. The trivial endpoint bound loses about h r1^2/2 ~ (2/9)h m^2, more than the available saving (about h m^2/6). The rank bound must give theta < sqrt3/2 (Lemma 11.1 uses theta <= 4/5). Both halves of Prop 10.3 are needed: (121) alone gives theta = 1 and (122) alone gives theta = 2. So all of Section 10 is required: 10.1, 10.2, 10.3, 10.4, 10.5, 10.7-10.15.
(c) Lemma 11.2 for bounded r2. Its proof rests on Part I Thm 5.1 (55), which is the most expensive dependency.

Not needed: the q >= 3 numerics in Lemma 8.2 (kappa_q < 1.563), Prop 9.2 for q >= 3, Remark 10.6, and uniformity in p.

Part II at p = 2 itself is about 8,000 Lean lines (sum of the Part II rows: about 7,800). Part I's (42), Props 2.4/2.5, Thm 3.1 and Thm 5.1 add roughly 6,000 more, partly reusable from Sims-lite.

### P1.Lemma2.7 (classical, ~450 lines, pp 19-20 (Part I); used on pp.52, 54, 65)
(Part I, used throughout Part II.) For every prime power q >= 2: (i) q^{k(n-k)} <= [n,k]_q <= phi(2)^{-1} q^{k(n-k)}; (ii) for 0 <= a <= R/2, the number of alternating forms of rank <= 2a on an R-dimensional F_q-space is <= 2 phi(2)^{-2} q^{a(2R-2a-1)}; (iii) |GL_d(q)| <= q^{d^2}. Here phi(2) = prod_{j>=1}(1-2^{-j}) > 1/4 by (43)-(44). Part II also uses #{C in F2^{k x k} : rank C <= rho} <= [k,rho]_2 2^{k rho} (p.65).
- depends: 
- mathlib gap: Mathlib has Matrix.card_GL_field and Module.card_eq_pow_finrank. It has no Gaussian binomials, no count of k-dimensional subspaces of F_q^n, no count of low-rank alternating forms or matrices, and no explicit bound on prod(1-2^{-j}). A rank-free proof of (ii): pick K inside rad A with codim 2a, then count forms on X/K, giving [R,2a]*2^{C(2a,2)}. This avoids needing 'alternating rank is even'.

### D.Alt (routine, ~300 lines, pp 44-45, 54)
Shared definitions over F2. Alt(X) is the alternating (symmetric, zero-diagonal) R x R matrices over ZMod 2, of dimension C(R,2). rad A, and rank A = R - dim rad A. A|_{UxU} is the restriction. Z_h(A) = {H in Gr(h,X) : A|_{HxH}=0} and I_h(A) = |Z_h(A)|. A subspace A <= Alt(X) is h-hollowing if every h-space H has some nonzero A in A with A|_H = 0. It is minimally h-hollowing if no proper subspace is. It is faithful on U if res_U is injective on A. B_H = {A in B : A|_H = 0}. The Sims rank of a surjective phi : Lambda^2 X -> W is s(phi) = min{dim U : phi(Lambda^2 U) = W} (91).
- depends: 
- mathlib gap: Mathlib has LinearMap.BilinForm, IsAlt, the orthogonal complement and its finrank formula for nondegenerate reflexive forms, and Matrix.rank. It has no Grassmannian as a Finset, no 'totally isotropic locus', and no hollowing notion. Recommendation: encode phi as an r2-tuple of alternating matrices to avoid exteriorPower. These definitions must be re-included in every reduction file (about 300 lines each time).

### Prop7.2 (routine, ~200 lines, pp 45)
Let phi : Lambda^2 X -> W be surjective and A = phi*(W*) <= Alt(X). (i) phi(Lambda^2 U) = W iff res_U is injective on A, i.e. A is faithful on U. (ii) For 0 <= h < dim X, A is h-hollowing iff s(phi) > h. (iii) s(phi) = s iff A is (s-1)-hollowing and s-faithful.
- depends: D.Alt
- mathlib gap: Uses annihilator/dual-space duality (Submodule.dualAnnihilator exists). In tuple-of-matrices form it is linear independence of the restricted tuple.

### Eq123 (routine, ~150 lines, pp 66)
(123) 2^{N_2(r1,r2,s)} <= |GL_{r2}(2)| * #{A <= Alt(F2^{r1}) : dim A = r2, A is (s-1)-hollowing}, with |GL_{r2}(2)| <= 2^{r2^2}. Here N_2(r1,r2,s) is log2 of the number of surjective alternating maps F2^{r1} x F2^{r1} -> F2^{r2} of Sims rank s (21).
- depends: Prop7.2, P1.Lemma2.7
- mathlib gap: Fibre counting of the map phi -> dual image, where each fibre is a GL_{r2}-torsor. Mathlib has the Finset card machinery but not this map.

### Lemma9.1 (classical, ~150 lines, pp 51)
If 0 <= h < dim X and A <= Alt(X) is h-hollowing, then dim A >= h. Equivalently, s(phi) <= dim W + 1 (BNV Prop 5.2, the greedy strictly increasing flag W_k).
- depends: Prop7.2
- mathlib gap: Not in Mathlib. The Sims-lite library's strict_chain_exists (S1) is the group-level analogue, but it is not directly reusable. A linear-algebra greedy argument is needed.

### Lemma8.1 (classical, ~450 lines, pp 45-46)
Let A in Alt(X) with dim X = R, rank 2a, r0 = R - 2a. Then I_h(A) = sum_{l=max(0,h-r0)}^{min(h,a)} [r0, h-l]_q q^{l(r0-h+l)} prod_{i<l}(q^{2a-2i}-1)/(q^{i+1}-1). Only the upper bound '<=' is needed, via the injection H -> (J = H cap rad A, L = p(H), f : L -> K/J).
- depends: D.Alt, P1.Lemma2.7
- mathlib gap: No symplectic geometry in Mathlib. That means no count of isotropic l-subspaces, and no 'nondegenerate alternating forms have even dimension' (a symplectic basis). The isotropic count can be done by ordered-basis counting using BilinForm.finrank_orthogonal: v_{i+1} in span(v_1..v_i)^perp minus the span. Also missing: the graph-of-f parametrization of complements.

### Lemma8.2 (new, ~600 lines, pp 46-50)
For q = 2, rank A = 2a, 0 <= h <= R: I_h(A)/[R,h]_2 <= (4/3) phi(2)^{-4} 2^{-lambda_h(a)}, where lambda_h(a) = a_h(2h-a_h-1)/2 and a_h = min{a, max(h-1,0)} (95). If a >= h-1, then I_h(A)/[R,h]_2 <= kappa_2 2^{-C(h,2)} with kappa_2 = max(kappa^-, kappa^+) < 1.72 (96)-(99). It suffices to prove kappa_2 < 2, which is the margin Prop 9.2 needs at M = C(h,2)-1.
- depends: Lemma8.1, P1.Lemma2.7
- mathlib gap: Exact normalized identity (100), the loss function L(a,j) (101) with monotone first differences, geometric tail sums, and the product inequality (102). Explicit numerics for kappa^- and kappa^+ need truncated products and series: replace the infinite products by finite truncations to avoid Mathlib's tprod API. The q >= 3 numerics are not needed.

### Prop9.2 (new, ~600 lines, pp 51-53)
(q = 2 case.) Let 1 <= h < R, h <= M <= C(h,2) - 1, and let H_2(R,M,h) be the set of M-dimensional h-hollowing subspaces of Alt(F2^R). Then log2 |H_2(R,M,h)| <= (M-h) C(R,2) + C(R^2+M^2) for an absolute C. Proof: covering (104)-(105). The cutoff a gives k_a = dim L_a(A) >= h - C0. When C(h,2)-M < C, (96) with kappa_2 < 2 is used. Count with d = h - C0 low-rank forms (106).
- depends: Lemma8.2, Lemma9.1, P1.Lemma2.7, D.Alt
- mathlib gap: Pure finite counting. The difficulty is bookkeeping the absolute constants (C, C0, the h a = O(M) claim) as explicit existentials, and the ordered-list overcount of subspaces. The Prop is needed at q = 2 only.

### Prop10.1 (new, ~200 lines, pp 53)
Let 3 <= h < R and M = C(h,2). The family of M-dimensional h-hollowing subspaces of Alt(F2^R) that are not minimally h-hollowing has log2-size <= (M-h)C(R,2) + C(R^2+M^2). Proof: such a space contains a minimal B of dimension t with h <= t < M. Apply Prop 9.2 to B, then count the superspaces of B: [C(R,2)-t, M-t]_2 <= 2^{(M-t)C(R,2)+2}.
- depends: Prop9.2, Lemma9.1, P1.Lemma2.7
- mathlib gap: Needs a count of the M-dimensional subspaces containing a fixed t-dimensional subspace (via the quotient), which Mathlib lacks. It also needs the existence of a minimal hollowing subspace (well-founded on dim, easy).

### Prop10.2 (new, ~100 lines, pp 54)
If B <= Alt(X) is minimally h-hollowing, then the B_H with dim B_H = 1 (H in Gr(h,X)) span B. Proof: otherwise a hyperplane C containing them is still h-hollowing.
- depends: D.Alt
- mathlib gap: Elementary. It needs dim(C cap B_H) >= 1 when dim B_H >= 2 and C is a hyperplane (Submodule.finrank_sup_add_finrank_inf).

### Prop10.5 (routine, ~220 lines, pp 55-56)
For A in B_H, let J = H cap rad A, H = H1 + J, d = dim H1, H^A = {x : x^T A h = 0 for all h in H}, and H^A = rad A + H1 + X0. Then codim H^A = d, b = A|_{X0 x X0} is nondegenerate, and rank A = 2d + dim X0 <= 2h + dim X0 (108). Only the inequality and the nondegeneracy of b are needed.
- depends: D.Alt
- mathlib gap: Can be proved without block matrices, by dimension counting: rank A = R - dim rad A and codim H^A <= h. Nondegeneracy needs (H^A)^{perp_A} = rad A + H1. Mathlib's BilinForm orthogonal API covers most of it.

### Lemma10.7 (new, ~320 lines, pp 56-57)
Let B be minimally h-hollowing with dim B = M = C(h,2), and let H have B_H = span{A}. For a basis A = A1, ..., AM of B there is an ordered basis z1..zh of H such that the M-1 rows r(z_i,z_j) (i<j<=h-2), r(z_i,z_{h-1}), r(z_i,z_h) (i<=h-2) form a basis of V0 = {c in F2^M : c1 = 0}. Here r(x,y) = (x^T A_r y)_r.
- depends: Prop10.2, D.Alt
- mathlib gap: The square evaluation matrix R_{B,H} (C(h,2) x M) has a 1-dimensional left kernel. Reordering the basis so that the unique relation has a nonzero (h-1,h) coefficient is painful Fin/Equiv.swap index work.

### Lemma10.8 (new, ~150 lines, pp 57-58)
For u, v in X0, let H_{u,v} = K + <z_{h-1}+u> + <z_h+v> with K = <z1..z_{h-2}>. This sum is direct, of dimension h. Its first M-1 evaluation rows lie in V0, and the last row has first coordinate b(u,v).
- depends: Lemma10.7, Prop10.5
- mathlib gap: Elementary. Needs X0 cap H = 0.

### Lemma10.9 (new, ~150 lines, pp 58)
For u in X0 and j <= h-2 there are unique w_j(u) in W = span{r(z_i,z_j) : i<j<=h-2} and P(u)_{ij}, Q(u)_{ij} in F2 with r(z_j,u) = w_j(u) + sum_i P(u)_{ij} r(z_i,z_{h-1}) + sum_i Q(u)_{ij} r(z_i,z_h). The maps P, Q : X0 -> F2^{(h-2)x(h-2)} are linear.
- depends: Lemma10.7
- mathlib gap: Basis.repr coordinates. Routine but index-heavy.

### Prop10.10 (new, ~420 lines, pp 58-59)
For u, v in X0 with b(u,v) = 1: F(u,v) := det [[I+P(u), P(v)], [Q(u), I+Q(v)]] = 0 (109). If det(I+P(u)) = 1, then by the Schur complement F(u,v) = det(I + R_u(v)) with G_u = Q(u)(I+P(u))^{-1} and R_u(v) = Q(v) - G_u P(v) (111). Hence b(u,v) = 1 implies det(I+R_u(v)) = 0 (114)-(115).
- depends: Lemma10.8, Lemma10.9
- mathlib gap: Uses Matrix.fromBlocks and Matrix.det_fromBlocks_one11 or det_fromBlocks11 (both in Mathlib). The heavy part is the coefficient extraction from the dependence (110) in the Lemma 10.7 basis.

### Lemma10.11 (classical, ~400 lines, pp 59-60)
Reed-Muller. If a nonzero f : F2^n -> F2 has degree <= d, then |supp f| >= 2^{n-d}. If also f(0) = 1, then codim span(supp f) <= d. Used together with: degree <= d is preserved under affine restriction, and u -> det(I+P(u)) for linear P has degree <= h-2.
- depends: 
- mathlib gap: Not in Mathlib: no Reed-Muller codes and no Boolean degree. Mathlib has Schwartz-Zippel, but that gives the wrong inequality. Recommended self-contained route: define 'DegLE d f' inductively (sums of products of at most d affine functionals). Prove that the derivative x -> f(x+v)+f(x) lowers degree, then do the support bound by induction on dim. The second assertion follows from the first applied to the delta function on a complement of span(supp f).

### Prop10.12 (new, ~320 lines, pp 60-61)
For u in S0 = {u in X0 : det(I+P(u)) = 1}: dim X0 <= dim R_u(X0) + 2(h-2). Also |S0| >= 2^{dim X0-(h-2)} (113).
- depends: Prop10.10, Lemma10.11, Prop10.5
- mathlib gap: Lower bound on U = {w in S0 : G_w = G_u} via Reed-Muller on an affine fibre of R_u. Upper bound by injecting w -> lambda_w into the annihilator of L (codim <= h-2). Uses Module.Dual and dualAnnihilator.

### Lemma10.13 (classical, ~450 lines, pp 61-62)
For k >= 1 and C in F2^{k x k} of rank r: sum_{A in GL_k(2)} (-1)^{tr(C^T A)} = (-1)^r 2^{k(k-r)+C(r,2)} phi_{k-r}(2) (116). In particular, |1^_GL(C)| <= 2^{k(k-r)+C(r,2)}, and this is nonincreasing in r.
- depends: P1.Lemma2.7
- mathlib gap: The paper's proof uses Moebius inversion on the subspace lattice and the Gaussian binomial theorem; Mathlib has neither. A cheaper elementary proof (not in the paper) works by row-by-row recursion: reduce to C = diag(I_r,0) by GL x GL invariance, then T(k,r) = -2^{r-1} T(k-1,r-1). That reduction needs the rank normal form PCQ = E_r, which is only partly in Mathlib. Only the upper bound plus the monotone majorant are needed.

### Lemma10.14 (routine, ~130 lines, pp 63)
For u in S0, lambda_u(R_u(v)) := b(u,v) is a well-defined linear functional on R_u(X0). C_u = {C : tr(C^T M) = lambda_u(M) for all M in R_u(X0)} is a nonempty affine space of dimension (h-2)^2 - dim R_u(X0).
- depends: Prop10.10, Prop10.5
- mathlib gap: Trace pairing nondegeneracy (Matrix.traceForm or direct E_ij) and extension of functionals (LinearMap.exists_extend). Mostly available.

### Prop10.15 (new, ~380 lines, pp 63-64)
For 0 != u in S0, with rho_u = min{rank C : C in C_u} (1 <= rho_u <= h-2): dim R_u(X0) <= (h-2)^2 + (h-2) + 1 - (h-2)rho_u + C(rho_u,2) (117). Proof: N0 = #{M in ker lambda_u : I+M invertible} >= 2^{dim R_u - (h-2) - 1} by Reed-Muller (118). Fourier inversion gives N0 = 2^{dim R_u - (h-2)^2} sum_{C in C_u} 1^(C)(-1)^{tr C} (120), so N0 <= max_{C_u} |1^(C)|.
- depends: Lemma10.11, Lemma10.13, Lemma10.14
- mathlib gap: Mathlib has no Fourier analysis on F2^n with explicit (-1)^<.,.> characters. Needed: character orthogonality over a subspace (the sum is |S| or 0) and Fourier inversion on F2^{k x k}. About 150 of the lines are generic infrastructure; AddChar exists in Mathlib but is awkward for this.

### Prop10.3 (new, ~420 lines, pp 54 (statement), 65-66 (proof))
Let B <= Alt(F2^R) be minimally h-hollowing with dim B = C(h,2), and let B_H = span{A}. Then rank A <= ((10-sqrt10)/9) h^2 + O(h). Proof: (121) combines Props 10.12 and 10.15. (122) is the injection u -> (C_u, D_u = G_u^T C_u), counted by rank class: dim X0 <= rho(3(h-2)-rho) + O(h). Then max_{x in [0,1]} min(3x-x^2, 1-x+x^2/2) = (10-sqrt10)/9 < 0.76.
- depends: Prop10.5, Prop10.12, Prop10.15, Lemma10.14, P1.Lemma2.7
- mathlib gap: Assembly plus an explicit O(h) constant, which must be made explicit. Use a rational bound such as 0.78 h^2 + C h instead of sqrt10; any theta' < 4/5 suffices for Prop 10.4.

### Prop10.4 (new, ~220 lines, pp 54)
There is an absolute h0 such that for h0 <= h < R, M = C(h,2), theta = 4/5, a = min{theta h^2/2, R/2}: log2 #{M-dim minimally h-hollowing subspaces of Alt(F2^R)} <= (M-h)C(R,2) + h a(2R-2a-1) + O(hR + h^4) (107). Proof: B is spanned by unique hollowing forms (Prop 10.2) of rank <= 2a (Prop 10.3). Choose h independent ones from the rank-<=2a set (Lemma 2.7(ii)) and the rest freely.
- depends: Prop10.2, Prop10.3, P1.Lemma2.7, Lemma9.1
- mathlib gap: Ordered-basis overcount. Routine once Prop 10.3 is in hand.

### Thm7.1 (new, ~280 lines, pp 44 (statement), 66-67 (proof))
(p = 2.) For 2 <= s <= r1 and s-1 <= r2 <= C(s-1,2): (i) if r2 < C(s-1,2), then N_2(r1,r2,s) <= (r2-s+1)C(r1,2) + C(r1^2+r2^2) (89); (ii) if r2 = C(s-1,2), then with a = min{(2/5)(s-1)^2, r1/2}, N_2 <= (r2-s+1)C(r1,2) + (s-1)a(2r1-2a-1) + C(r1^2+r2^2) (90). C is absolute. For s-1 < h0, use the trivial count r2 C(r1,2).
- depends: Eq123, Prop9.2, Prop10.1, Prop10.4, Lemma9.1
- mathlib gap: Assembly plus case split. This is the natural self-contained hypothesis 'H_N2' to isolate in a reduction file. It is purely linear algebra over F2 with no group theory.

### Lemma11.1 (new, ~250 lines, pp 67-68)
Let m >= 2, h >= 1, R >= 0, R + C(h,2) <= m, w = m - R - C(h,2), 0 <= theta <= 4/5. Then the endpoint presentation exponent E = (1/2)R^2(m-R) + (h/2)(m-theta h^2)(m+theta h^2-2R) + (h^2/2)(R-m) - (h^3/8)(h-1)(h-3), which is (124)'s left-hand side after substitution, satisfies E <= (2/27)m^3 - (11/1602) h m^2 + 117 m^2.
- depends: 
- mathlib gap: A real polynomial inequality with side conditions h^2 <= 3m and 3-4theta^2 >= 11/25. The paper gives the completed-square decomposition. Expect a nlinarith/polyrith-assisted proof in several steps; there is no Mathlib gap.

### Eq129-130 (new, ~200 lines, pp 70)
Strengthened cubic comparison (BNV Lemma A.2). With x = r1/m, y = r2/m, z = 1-x-y, u = h/m, 0 <= u <= min(x,y): B(x,y,z,u) = x^2(y+z-u)/2 + (uy - u^2/2)z + u z^2/2 satisfies 2/27 - B >= u/(12*...); precisely m^3 B <= (2/27)m^3 - (11/3456) h m^2 (130). Cases: x >= 7/12, 1/2 <= x <= 7/12, x <= 1/2.
- depends: 
- mathlib gap: Three-case real inequality via identity (129). nlinarith-level. The existing Sims-lite cubic_ineq is a weaker analogue and not reusable.

### P1.Eq42 (classical, ~1500 lines, pp 19)
(Part I / BNV Eq. 5.14.) For fixed recorded Sims presentation data and power-word array, log_p #(commutator coefficient arrays) <= N_p(r1,r2,s) + C(r1,2)(m-r1-r2) + (s-1)r2 - C(s-1,2)... (exact form (42), p.19) + O(m^2). More precisely: N_p + r1-terms + ((s-1)r2 - (s-1)^2/2)(m-r1-r2) + (m-r1-r2)^2/2 + O(m^2).
- depends: P1.Prop2.4
- mathlib gap: Part I, outside this extraction. The Sims presentation with alternating-map residues and naive lifts. The Sims-lite library's codes and shapes are a different presentation, so only the commutator calculus, nf/nf_surj and the rigidity pattern carry over. Estimate is for adapting Sims-lite.

### P1.Prop2.4-2.5-Thm3.1 (classical, ~1200 lines, pp 14-18, 21)
(Part I.) Recorded Sims presentation data plus a power-word array plus a commutator coefficient array determine G up to isomorphism (Prop 2.4 = BNV Thm 5.6). The recorded data have p^{O(m log m)} choices (Prop 2.5). Power-word arrays have <= p^{m^2} choices (Thm 3.1, naive count).
- depends: 
- mathlib gap: Part I. Partly covered by the Sims-lite library: rigidity via the diagonal subgroup, nf_surj, Theorem L (core generates every layer, i.e. Lemma 2.2).

### P1.Thm5.1 (new, ~3500 lines, pp 26-41 (Sections 4-6))
(Part I.) Fixed-breadth relation bound (55): with fixed data, power array and core breadth sequence b, log_p #(commutator arrays) <= (r1/2... ) i.e. C(r1,2)(sum stuff) - r2 m2 + sum_{i=2}^{c-2} s r_i m_{i+2} + sum_{i=2}^{c-1} b_i s(r_i + s_{i+1} - b_i + 1) - C(r1-s,2)-type term. Used only through (125): log_p|P| <= (1/2) r1^2 (m2 - |b|) + 5 s m^2, together with T_core <= m2/2 and |b| >= m3/s ((80)-(82)).
- depends: P1.Prop2.4-2.5-Thm3.1
- mathlib gap: Part I. Graded Lie ring of G, breadth sequences, adjoint-cocycle comparison (Thm 5.6), recovery lemmas 5.7-5.11. Very large: comparable to or bigger than the whole Sims-lite library.

### Lemma11.2 (new, ~350 lines, pp 68-69)
For every prime p, K >= 1 and m >= 3, the number of isomorphism classes of nonabelian groups of order p^m with r2 <= K is <= p^{(2/27)(K/(K+1)) m^3 + (5K+11) m^2}. Proof: (125) plus m2 - |b| <= (r2/(r2+1))(m - r1 + 1), using s2 <= r2(delta+1) from p^{delta+1} L1 = 0 (126).
- depends: P1.Thm5.1, P1.Prop2.4-2.5-Thm3.1, Lemma9.1
- mathlib gap: The Part II-specific part is small: the exponent bound for L2 and the two-affine-function optimization. All the weight is in Part I Thm 5.1. No cheaper substitute was found: the Sims-lite count has leading constant 2/25 > 2/27, so it cannot give a cubic saving for bounded r2.

### Thm11.3 (new, ~450 lines, pp 69-71)
For every A > 0 there is m_A (independent of p) such that for all primes p and m >= m_A, fns(p^m) := #{nonabelian G of order p^m with r2 <= C(s-1,2)} <= p^{(2/27)m^3 - A m^2} (127). At p = 2: for h = s-1 >= H, use (131) when r2 < C(h,2) (Thm 7.1(i) + (42) + (130)) and (132) when r2 = C(h,2) (Thm 7.1(ii) + (42) + Lemma 11.1 with theta = 2a/h^2 <= 4/5). This gives saving (11/3456)H - C. For h < H, r2 <= K = C(H-1,2) and Lemma 11.2 applies. Choose H, then m_A >= (27/2)(K+1)(A+5K+12) (133).
- depends: Thm7.1, P1.Eq42, Eq129-130, Lemma11.1, Lemma11.2, P1.Prop2.4-2.5-Thm3.1, Lemma9.1
- mathlib gap: Assembly. Sum over parameters (r1, r2, s, m-r1-r2), with the m^2 multiplicity absorbed. The unspecified absolute C must be existentially quantified so that H and m_A can be chosen. For the frontier, any A > 1/3 suffices when combined with Part III's fsat bound, but because C is uncontrolled, H and Lemma 11.2 are needed regardless of how small A is.

## LQ-part-III
Thm 1.1 at p=2 (= Thm 14.4, p.86) does need BLQR25. Its proof is f(2^m) = f_{H_2}(2^m) + (f - f_{H_2}), using the upper half of (159), [BLQR25, Thm 1.3 and Sec 4.3], to get f_{H_2}(2^m) <= 2^{(2/27)m^3 - (4/9)m^2 + C_H m}. Li-Qiao do not reprove it; Thm 14.3 handles only the groups outside H_p.

The -1/3 frontier needs neither BLQR25, nor Higman's lower bound, nor Prop 12.1(i). Three reasons:
- The FC2 / class-<=2 parts are already solved: the FC2 file reaches -10/27, and the class-<=2 and |gamma_3| <= 2 leaves are solved.
- The open leaf H3 has m3 >= 2.
- Its target log2 N <= (2/27)m^3 - m^2/3 - 3 is weaker than Thm 14.3's -(4/9 + 1/1024)m^2.

What the frontier does need is Thm 14.3 restricted to class >= 3, so all of P1-P13 except X1/X2. That in turn needs:
- all of Part I: Prop 2.4 = BNV 5.6, Prop 2.5, Thm 3.1, Secs 4-5, Thm 6.3, Rem 6.4, Prop 6.5;
- all of Part II, including the p=2-specific binary endpoint Sec 10, because Thm 11.3 at p=2 uses Thm 7.1(ii) at r2 = C(s-1,2).

Two simplifications are available for the -1/3 target:
- Multiplicities (Sec 13) are needed only for lambda in {0,1}. For lambda >= 2, the plain bound (2/27)(m-lambda)^3 + O(m) from P4 already gives -4/9.
- Prop 12.1 is needed only in its m3 > 0 form, and only with an error term under (1/9)M^2 rather than -(1/128)M^2.

### U1 Sims rank basics (Def 2.1, Lemma 2.2 = BNV Prop 3.8, Lemma 2.3 = BNV Cor 5.3) (classical, ~400 lines, pp pp.11-12)
Definition: s(G) = min{d(H) : H <= G, G_2 = [H,H]G_3}. If G_2 = [H,H]G_3, then H_i = G_i for 2 <= i <= c. For nonabelian G: 2 <= s <= r1 and s-1 <= r2 <= C(s,2).
- depends: 
- mathlib gap: Mathlib has lowerCentralSeries but no Sims rank. Lemma 2.2 is close to the Sims-lite Theorem L (core generators generate every layer), which can be reused.

### U2 Frattini quotients and the commutator form (18)-(20) (classical, ~700 lines, pp pp.12-13)
V = G/Phi(G) = L1/pL1 and W = G_2/(G_3 Phi(G_2)) = L2/pL2 are F_p-spaces of dimensions r1 and r2. beta_G(x Phi, y Phi) = [x,y] G_3 Phi(G_2) is a well-defined alternating bilinear map whose values span W. s(G) = min{dim U : beta_G(U,U) = W}, and a Sims core H gives U = H Phi/Phi with dim U = s.
- depends: U1
- mathlib gap: Missing: Burnside basis theorem and Phi(G) = G^p[G,G] for p-groups. The solved FC2 file proves frattini_eq_squareCore for p=2, which can be reused. Also missing: V and W as ZMod p-modules and beta_G as a LinearMap.BilinForm (all hand-built).

### U3 Existence of ordered Sims generating sets (Sec 2.1, (23), (25), (33)) (classical, ~2000 lines, pp pp.12-14)
Every nonabelian p-group has an ordered Sims generating set (g_{i,j}), i in [c], j in [r_i], with these properties. The core is g_{1,1..s}, independent mod Phi. The flags d_k and the auxiliary function f make g_{2,j} = [g_{1,f(j)}, g_{1,k}] for d_{k-1} < j <= d_k. Higher-weight generators are iterated commutators with core generators, given by recorded index pairs. a(i,j) is the relative-order exponent. C_core = HG_2/G_2.
- depends: U1, U2
- mathlib gap: There is no polycyclic or Sims presentation machinery. The Sims-lite strict-core-chain and layer code (exists_layers, exists_shape_valid) is the closest asset, but it lacks the d_k flags and relative orders.

### U4 Prop 2.4 (BNV Thm 5.6): the Sims data determine the isomorphism class (classical, ~2500 lines, pp p.14)
The isomorphism class of a nonabelian p-group G is determined by p, c, s, (r_i), (d_k) and three arrays with the stated index ranges: relative orders a(i,j), power words b(i,j,u,v) and commutator coefficients c(i,j,k,u,v). Only core-k commutators are recorded for i >= 2.
- depends: U3
- mathlib gap: Missing: PresentedGroup normal-form theory. The Sims-lite rigidity argument (diagonal subgroup of G x G', nf_surj, card_diag_le) can be adapted, but the full Sims code has more positions and a weight-2 flag structure.

### U5 Prop 2.5: counting recorded Sims presentation data (classical, ~400 lines, pp pp.14-15)
At most 2^{O(m)} choices of (c, s, (r_i), (d_k)), at most m^{2m} choices of f and index pairs, and at most C(m-1, sum r_i - 1) <= 2^{m-1} relative-order arrays. In total at most m^{2m+2} 2^{3m-1} = p^{O(m log m)}.
- depends: U3
- mathlib gap: Finset cardinality bookkeeping only.

### U6 Lemma 2.7 and (43)-(44): finite-field estimates (classical, ~1500 lines, pp pp.19-20)
phi(2) = prod_j (1-2^-j) >= 9/32. (i) q^{k(n-k)} <= [n choose k]_q <= phi(2)^{-1} q^{k(n-k)}. (ii) The number of alternating forms of rank <= 2a on F_q^R is at most 2 phi(2)^{-2} q^{a(2R-2a-1)}. (iii) |GL_d(q)| <= q^{d^2}, and |GL_d(q)| >= phi(2) q^{d^2}. An abelian group of order p^e has at most p^{b(e-b+1)} subgroups of order p^b. (iv) There are at most 2^{m-1} abelian groups of order p^m.
- depends: 
- mathlib gap: Mathlib has card_GL_field. Missing: counts of subspaces (Gaussian binomials), the phi(2) product bound, the count of alternating forms by rank (needs the Sp_2j orbit count), and the subgroup count in abelian p-groups.

### U7 Associated graded Lie ring and its Sims presentation (Sec 2.3, Lemma 4.1) (classical, ~2000 lines, pp pp.17-19, 23-24)
L = sum_i G_i/G_{i+1} with the bracket induced by commutators is a graded Lie ring. The partial commutator coefficient arrays determine the brackets L_1 x L_1 -> L_2 and L_i x C_core -> L_{i+1}, and hence the whole graded bracket (Lemma 4.1(iii)).
- depends: U1, U3
- mathlib gap: Mathlib has no Lie ring associated to the lower central series of a group (only LieRing and LieAlgebra lower central series). Bilinearity mod G_{i+j+1} is partly in the Sims-lite commutator calculus.

### U8 Thm 3.1 / (47): counting power word arrays (new, ~800 lines, pp pp.22-23, 42)
For fixed recorded data, the weight-i power relations contribute at most r_i m_{i+1} + (r_i - 1)(s_i - r_i) to log_p of the number of full power word arrays. In total: log <= r1 m2 + lambda r1 + m2(e + m3) + m3^2.
- depends: U3, U5
- mathlib gap: Counting only, given U3.

### U9 Props 4.2-4.3: leading commutator coefficients and breadth (new, ~1200 lines, pp pp.24-26)
The core breadth sequence b = (b_i), from rank considerations of the core bracket maps L_i x C_core -> L_{i+1}, satisfies the breadth relations (51): s_{i+1} <= s b_i and b_i <= s_{i+1}. Fixing a breadth leaves at most p^{b_i(s_{i+1} - b_i + 1)} choices per layer (via Lemma 2.7(iii)). The core-outside leading values are counted freely in L2 (Prop 4.3).
- depends: U6, U7
- mathlib gap: Needs linear algebra over ZMod p^k-modules and subgroup counts.

### U10 Thm 5.1 (55): fixed-breadth relation bound, with Thm 5.2, Props 5.3-5.5, Thm 5.6, Lemma 5.7, Cor 5.8, Props 5.9-5.10, Cor 5.11 (new, ~6000 lines, pp pp.26-40)
Fix the recorded data, the power word array and the core breadth. Then log_p #(commutator coefficient arrays) <= (C(r1,2) - r2) m2 + X, with X = s T_core + sum_{i=2}^{c-1} b_i (s(r_i + s_{i+1} - b_i + 1) - C(r1-s,2)) as in (78), after the r2 defining-commutator saving. The proof compares two groups with the same Lie bracket; commutator differences are adjoint cocycles (Thm 5.6), and relations are recovered layer by layer.
- depends: U4, U7, U8, U9
- mathlib gap: Missing: group cohomology in the needed form (adjoint cocycles of a graded Lie ring), and N-series comparison of two groups. This is the biggest and most novel part of Part I.

### U11 Lemma 6.1 (new, ~300 lines, pp p.40)
e = s2 - r2 <= C(lambda, 2), where lambda = s1 - r1. In particular lambda = 0 implies e = 0.
- depends: U7
- mathlib gap: Needs the finite abelian group structure theorem (in Mathlib) plus biadditivity of the L1 bracket.

### U12 Lemma 6.2 and (80), (81), (83), (84) (routine, ~300 lines, pp pp.40-41)
(80): m3/s <= |b| <= m3 <= m2, and m3 > 0 implies b2 >= 1. (81): the number of core breadth sequences is at most 2^{m3} <= 2^m. (82): T_core <= (m2^2 - s2^2)/2 and T_core <= s m2(|b| - b2). (83)-(84): X <= s min{(m2^2 - s2^2)/2, s m2(|b| - b2)} + (s(2m2+1) - C(r1-s,2))|b| <= s m2^2/2 + ...
- depends: U9
- mathlib gap: Finite-sum inequalities only.

### U13 Thm 6.3 (85)-(86): joint array bound (new, ~600 lines, pp pp.42-43)
For fixed recorded data and core breadth b: E <= (1/2) r1^2 m2 + X + (1/2) m2 zbal + 3 m2 m3 + 2 m2 e + lambda r1 + delta_p. Here zbal = r1 - 2m2, m = r1 + m2 + lambda and delta_p = min{0, N_p(r1,r2,s) - (C(r1,2) - r2) r2 + C(r1-s,2) b2}.
- depends: U8, U10, U12
- mathlib gap: Arithmetic combination of U8 and U10.

### U14 Remark 6.4: extra affine constraints (new, ~500 lines, pp p.43)
Suppose that, after fixing the power words, the higher core brackets and the core-core leading values, the core-outside leading coefficients c(1,j,k,2,v) mod p (j <= s < k) satisfy affine equations of rank >= q, uniformly. Then q can be subtracted from (55) and, when delta_p = 0, from (85). Choices that specify the equations are counted separately.
- depends: U10, U13
- mathlib gap: Needs the internals of the U10 proof, so it should be formalised inside U10 as a parametrised version, not as a black box.

### U15 Prop 6.5: saturated range has delta_p = 0 (new, ~400 lines, pp p.43)
If C(s-1,2) < r2 <= C(s,2), then N_p(r1,r2,s) = C(r1,2) r2 + O(1) and delta_p = 0.
- depends: U6
- mathlib gap: Needs a count of surjective linear maps restricted to wedge^2 U, plus the phi(2) bound.

### U16 (42) (BNV eq. 5.14): Sims commutator count (classical, ~700 lines, pp p.19)
log_p #(commutator coefficient arrays) <= N_p(r1,r2,s) + C(r1,2)... + (s-1) r2 - (s-1)^2/2 ... terms in w = m - r1 - r2, + O(m^2). This is used only in the nonsaturated range.
- depends: U3, U4
- mathlib gap: Same infrastructure as U10 but cruder.

### U17 Thm 7.1(i): non-endpoint map count (Prop 7.2, Lemmas 8.1-8.2, Lemma 9.1, Prop 9.2) (new, ~3500 lines, pp pp.44-53)
If p >= 3, or p = 2 and r2 < C(s-1,2), then N_p(r1,r2,s) <= (r2 - s + 1) C(r1,2) + O(r1^2 + r2^2). The proof dualises to h-hollowing (h+1)-faithful spaces of alternating forms (h = s-1) and counts totally isotropic subspaces.
- depends: U6
- mathlib gap: Missing: spaces of alternating forms (Alt(X) as a subspace of LinearMap.BilinForm), isotropic-subspace counts, Grassmannians over F_q.

### U18 Thm 7.1(ii): binary endpoint (Sec 10: Props 10.1, 10.3-10.5, Lemmas 10.7-10.9, Prop 10.10, Prop 10.12, Lemmas 10.13-10.14, Prop 10.15) (new, ~6000 lines, pp pp.53-66)
If p = 2 and r2 = C(s-1,2), let a = min{floor(sqrt(5/2)(s-1)/... ), floor(r1/2)} as in (90). Then N_2(r1,r2,s) <= (r2-s+1) C(r1,2) + (s-1) a (2r1 - 2a - 1) + O(r1^2 + r2^2). The proof uses unique hollowing forms, determinant constraints, and Fourier analysis of the indicator of GL_k(F_2). It is specific to p = 2.
- depends: U6, U17
- mathlib gap: Missing: Fourier transform on F_2 matrix spaces (only AddChar and ZMod Fourier basics exist), polynomial-method rank bounds over F_2. Very large.

### U19 Lemma 11.1: endpoint absorption (routine, ~300 lines, pp p.67)
For m >= 2, h >= 1, R + C(h,2) <= m, w = m - R - C(h,2) and 0 <= alpha <= 4/5: (1/2)R^2(m-R-h) + (1/2)h^3 - h^2 w/2 + ... + alpha h^3 R - alpha^2 h^5/2 <= (2/27)m^3 - (11/1602) h m^2 + O(m^2).
- depends: 
- mathlib gap: A real polynomial inequality. nlinarith/polyrith with an explicit O-constant.

### U20 Lemma 11.2: bounded second-layer rank (new, ~600 lines, pp pp.68-69)
For r2 <= K and m >= 3, the number of nonabelian groups of order p^m is at most p^{(2/27)(K/(K+1)) m^3 + (5K+11) m^2}.
- depends: U5, U8, U10, U12, U4
- mathlib gap: Uses (55) of U10 directly. Not CFSG-dependent.

### U21 Thm 11.3: nonsaturated range (new, ~900 lines, pp pp.69-71)
For every A > 0 there is m_A, independent of p, such that the number of nonabelian groups of order p^m with r2 <= C(s-1,2) is at most p^{(2/27)m^3 - A m^2}. For the frontier take A = 4/3.
- depends: U5, U8, U16, U17, U18, U19, U20, U4
- mathlib gap: Real optimisation (129)-(130) over B(x,y,z,u), done with nlinarith. The constant C in (133) is not explicit, so the Lean proof must produce it.

### P1 (134)-(135): saturated-range parameter bounds (routine, ~100 lines, pp p.72)
If C(s-1,2) < r2 <= C(s,2) and 2 <= s <= r1, then s^2 < 2(m2 - m3) + 3s, so s <= C sqrt(m2) (for example s <= 3 + sqrt(2 m2)).
- depends: U1, U12
- mathlib gap: Nat.sqrt arithmetic.

### P2 (138)-(139): objective F_theta (routine, ~100 lines, pp p.73)
F_theta := (1/2) r1^2 m2 + X + 3 m2 m3 + theta m2 zbal. In the saturated range, E <= F_{1/2} + 2 m2 e + lambda r1 (Thm 6.3 with delta_p = 0).
- depends: U13, U15
- mathlib gap: None.

### P3 Prop 12.1(ii) (part (i) not needed, since m3 >= 2 on the frontier leaf) (new, ~1100 lines, pp pp.74-77)
There is an absolute C > 0 such that, for each fixed theta (needed: theta = 1/2 and theta = -5/6), in the saturated range with m3 > 0 and r1 + m2 >= M(theta): F_theta <= (2/27)(r1+m2)^3 - (1/128)(r1+m2)^2. The proof uses identity (141): (2/27)(r1+m2)^3 - (1/2)r1^2 m2 = zbal^2(4r1+m2)/54. It then splits by r1 < m2, r1 > 3m2, and m2 <= r1 <= 3m2, maximising (142)-(144) over |b| in [b2, ...]. For the -1/3 target, a weaker version is enough: F_theta <= (2/27)(r1+m2)^3 + c(r1+m2)^2 with c < 1/9. This is not much easier, because the X <= -m2^2/4 + ... argument is still needed.
- depends: P1, P2, U12
- mathlib gap: Real and integer inequalities with case splits; heavy use of nlinarith and sqrt bounds. The threshold M(theta) has to be made explicit or existential.

### P4 (145)-(147) and the bounded-lambda refinement (p.77) (routine, ~300 lines, pp pp.77-78)
(145): E <= (2/27)(m-lambda)^3 + C0 m^2. (146): m^3 - (m-lambda)^3 >= lambda m^2. For 0 <= lambda <= D: E <= (2/27)(m-lambda)^3 + (D^2 + 27/8) m. On the frontier with m3 > 0, for each fixed lambda this gives E <= (2/27)m^3 - (2 lambda/9) m^2 + O_lambda(m). That bound suffices without multiplicities when lambda >= 2, since -4/9 < -1/3.
- depends: P3, U11
- mathlib gap: None.

### P5 Sec 13.1: the family S_{Z0} (new, ~900 lines, pp pp.78-79)
Write L1 = G/G_2 = Z_2 (+) Z_1, with Z_1 the elementary part of a cyclic decomposition, so d(Z_2) <= lambda. Write the core images as b_k + e_k and set Z_core = span{e_k}. Choose a complement Z0 of Z_core in Z_1. Then max{0, r1 - s - lambda} <= dim Z0 <= r1 - s, and L1 = (Z_2 (+) Z_core) (+) Z0. Fix the core, the first r1 - dim Z0 weight-1 generators and all higher-weight generators. For every ordered basis of Z0, lifts give Sims generating sets (148) with identical recorded data, a(1,j) = 1 on the free positions, and the same core breadth sequence.
- depends: U3, U2
- mathlib gap: Mathlib has the finite abelian structure theorem (AddCommGroup.equiv_directSum_zmod_of_finite) and complements of subspaces. Missing: the Burnside basis extension (Rob96 5.3.2) inside an abelian p-group, and transporting it to the Sims-set axioms of U3.

### P6 Core centraliser (149)-(150) (new, ~150 lines, pp pp.79-80)
K = {v in V : beta_G(v, U) = 0} satisfies K ∩ U = 0 (otherwise the Sims rank would drop to s-1). Hence dim K <= r1 - s. K is constant on S_{Z0}.
- depends: U2, U1
- mathlib gap: Linear algebra only.

### P7 Prop 13.1: multiplicity of relation arrays (new, ~700 lines, pp pp.79-80)
S_{Z0} produces at least phi(2) p^{(dim Z0)^2 - (dim Z0)(dim K)} distinct pairs (power word array, commutator coefficient array). Proof: Z0 embeds in V. If two bases (x_l) and (y_l) give the same arrays, the coefficients c(1,k,r1-dim Z0+l,2,v) mod p agree, so x_l - y_l lies in K. Then divide |GL(dim Z0, p)| >= phi(2) p^{(dim Z0)^2} by the p^{(dim Z0)(dim K)} bases per pair.
- depends: P5, P6, U6, U4
- mathlib gap: Needs card_GL_field, a lower bound by phi(2), and the identification of array coordinates with beta_G values from (19).

### P8 Prop 13.2: joint bound with dim K fixed (new, ~800 lines, pp pp.80-81)
For fixed recorded data, b and dim K: E <= F_{1/2} + 2 m2 e + lambda r1 + (dim K)(r1 - dim K - s r2) + log_p(phi(2)^{-1}). There are at most phi(2)^{-1} p^{(dim K)(r1 - dim K)} choices of K (Lemma 2.7(i)). Each K imposes an affine system of rank s(dim K) r2 on the core-outside leading coefficients, which Remark 6.4 subtracts.
- depends: U13, U14, U15, U6, P6, P2
- mathlib gap: This is where Remark 6.4 is load-bearing. U10 must be proved in a form that accepts affine constraints.

### P9 Cor 14.1 (152)-(153): group count with fixed parameters (new, ~600 lines, pp pp.81-82)
For fixed recorded data, b, dim Z0 and dim K: log_p #(isomorphism classes) <= F_{1/2} + 2 m2 e + lambda r1 - (dim Z0)^2 + (dim K)(r1 + dim Z0 - dim K - s r2) + O(1), with O(1) <= 2 log_2(phi(2)^{-1}). Also 0 <= r1^2 - (dim Z0)^2 <= 2 r1(s + lambda). Summing over parameter choices costs p^{O(m log m)}. The proof divides P8 by P7, using the injectivity in Prop 2.4.
- depends: P5, P6, P7, P8, U4, U5, U12
- mathlib gap: Needs the counting principle #classes <= #codes / min multiplicity as a Finset lemma (fiberwise card bound). Routine but fiddly.

### P10 Lemma 14.2: small-core bound (new, ~700 lines, pp pp.82-84)
There is C5 such that for theta > 0, A > 0 and D >= 0: the number of nonabelian saturated groups with lambda <= D and s r2 < theta r1 is at most p^{(2/27)m^3 - A m^2} once m >= C5(1 + theta^2 + D^2 + (1+theta)(A+1)^{3/2}). Frontier use: theta = 2, D = lambda0 - 1, A = 4/3. In the proof, the subcase r1 < m/12 is already covered by the r1 <= m/7 lemma proved in the H3.R2 reduction file; the subcase m2 < m/12 still needs the E <= m^3/24 + ... bound.
- depends: U13, U15, U11, U12, U5, P2
- mathlib gap: Real inequalities with m^{1/3} and m^{8/3} terms. Best done with integer cube-root surrogates.

### P11 Identity (157) and theta shift (routine, ~40 lines, pp p.85)
With r1 + m2 = m - lambda and zbal = r1 - 2m2: -r1^2 = -(4/9)(m-lambda)^2 - (4/3) m2 zbal - (5/9) zbal^2. Also F_{1/2} - (4/3) m2 zbal = F_{-5/6}.
- depends: P2
- mathlib gap: ring.

### P12 Thm 14.3, frontier version (class >= 3 only, p = 2, target -1/3) (new, ~900 lines, pp pp.84-86)
For all large m: log_2 #{G : |G| = 2^m, m3 >= 1} <= (2/27)m^3 - (1/3 + delta)m^2 for some delta > 0 (delta = 1/1024 with the paper's constants; any delta > 0 with 27 delta m^2 >= 81 suffices for H3). The case split is: (a) nonsaturated: U21 with A = 4/3. (b) Saturated, lambda >= lambda0 with 2 lambda0/27 > C0 + 1/3 + 1: from (145)/(146). (c) Saturated, lambda < lambda0, s r2 < 2r1: P10. (d) Saturated, 2 <= lambda < lambda0: P4, which needs no multiplicities for the -1/3 target (the paper instead runs (e) for all 1 <= lambda <= D). (e) Saturated, lambda in {0,1}, s r2 >= 2r1: P9 with dim Z0 bounds, then P11, then P3 at theta = -5/6. This gives <= (2/27)m^3 - (4/9 + 2 lambda/9)m^2 + C7 m^{3/2}. The case lambda = m3 = 0 (FC2) does not arise. The abelian case does not arise.
- depends: U21, P4, P9, P10, P11, P3, P1, U11, U5, U12
- mathlib gap: Assembly plus summation over p^{O(m log m)} parameter choices. Needs explicit m-thresholds or Filter.eventually bookkeeping.

### P13 Glue to the leaf H3 statement (routine, ~250 lines, pp -)
From P12: eventually (8N)^27 * 2^(9m^2) <= 2^(2m^3), where N = #{[G] : |G| = 2^m, not (commutator G <= center G), 2 < |lowerCentralSeries 2|}. This translates Mathlib's lowerCentralSeries indexing, isIsomorphicSetoid classes of FiniteGrp and Nat.card into (m3 >= 1), and absorbs the factor 8^27 into delta m^2.
- depends: P12
- mathlib gap: Reuse finite_order_classes and the quotient-image ncard lemmas from the existing reduction files.

### X1 NOT NEEDED for the frontier: (159) = [BLQR25, Thm 1.3 and Sec 4.3] upper bound and Higman lower bound [Hig60, Thm 2.3] (classical, ~0 lines, pp p.86)
p^{(2/27)m^3 - (4/9)m^2} <= f_{H_p}(p^m) <= p^{(2/27)m^3 - (4/9)m^2 + C_H m}. This is needed for Thm 1.1 / Thm 14.4, but not for the leaf H3. FC2 is handled by the solved file (coefficient -10/27 < -1/3), and H3 has m3 >= 2.
- depends: 
- mathlib gap: n/a (excluded).

### X2 NOT NEEDED: Prop 12.1(i), Thm 14.4 small-m part, Prop 14.5, Cor 14.6, Sec 15 (routine, ~0 lines, pp pp.74, 86-99)
Prop 12.1(i) applies only when m3 = 0. Thm 14.4 for m < m0 uses f(p^m) <= p^{C9 m^3}, which is irrelevant because the target is eventual. Prop 14.5 is a lower bound, Cor 14.6 is the general-n bound, and Sec 15 concerns cumulative domination.
- depends: 
- mathlib gap: n/a.

## SX
For the 2-group frontier at p = 2 on the Su–Xia route, the only thing needed is the non-root bound N_2(m) <= 2^{lambda(m) + m^2/9 - 2}. The root part is the SOLVED FC2 file with -10/27. This is Prop 6.2 with its saving m^2/300 turned into an allowed loss of m^2/9.

**Needed**
- Prop 3.5 (off-strip), which carries all of BNV Ch. 5: Sims rank (Cor 5.3), the alternating-map counts (5.5)/(5.6), and the restricted presentation (Thm 5.6/5.7) with (d, b, sigma) kept.
- Lemmas 4.1 and 4.2 (p-covering group, nucleus, allowable lines, reachability).
- Prop 4.3 (nucleus bounds, including the matrix-space rank bound).
- Prop 4.4 (weighted root count, s >= 3). The m^2/9 slack lets the first bound in (9) cover R >= 4 and the one-form bound cover R = 2, 3. The Waterhouse/Sergeichuk pencil step is needed only for the R = 1 stratum. It can be replaced by adapting the FC2 file's orbit counting for GL(A) x GL(W_0).
- Lemma 5.1, as a low-degree LHS statement for central C_2-extensions with eps only bounded by 1. Lemma 5.2 (capacity and the H^3 inflation-kernel bound), Prop 5.3 / Cor 5.4 (annihilator tails, using H^{<=3}(C_2^d) = Sym^{<=3}), and Prop 5.6 (descendant tree).
- Lemma 6.1.
- Prop 5.7 with Lemma 5.5, for s <= 2. This is the only consumer of Leary's d_3 = Bockstein formula and of the Bockstein on H^*(C_2^d). It cannot be dropped: for s = 1 in the strip, Prop 5.6 alone overshoots the target by about d^2/2.

**Not needed**
- Section 3.1: Prop 3.1, Lemmas 3.2/3.3, Cor 3.4.
- Lemmas 2.5-2.7 (sharp root count; FC2 is already solved).
- Section 7.
- Section 8: Lemmas 8.1-8.8, Props 8.5/8.9, Maróti, Pyber, BNV 16.20.

**Size**
- Su–Xia route at p = 2: about 52k Lean lines in total. A realistic range is 40-70k. The total is the sum of the per-node estimates calibrated on Sims-lite (3695 lines for BNV Ch. 5-level work with constant 2/25) and the FC2 file (2865 lines).
- Without the s <= 2 population (Leary, Lemma 5.5, Prop 5.7): about 46k.

### SX-PG (classical, ~500 lines, pp Sec 2, sx.txt l.283-337; reachability paragraph after Lemma 4.2, l.1005-1008; termination in proof of Lemma 5.2, l.1347)
Basic p-group facts at p=2. (i) Phi(G) = G^2 = gamma_2^(2)(G), and the Burnside basis theorem: d(G) = dim G/Phi(G), and a subset generates G iff its image generates G/Phi. (ii) Every nontrivial normal subgroup meets Z(G); hence gamma_3^(2)(G) has a central chain of order-2 steps, each normal in G. (iii) The series gamma_i^(2) terminates. (iv) Lemma 2.1: gamma_3^(2)(G) = 1 iff Phi central of exponent 2.
- depends: 
- mathlib gap: Mathlib has frattini, IsPGroup and center-meets-normal. It lacks the Burnside basis theorem and Phi = G^p G'. The FC2 file already has frattini_eq_squareCore.

### SX-GAUSS (classical, ~700 lines, pp Sec 3.1 eq.(7), l.788-806; used in Prop 5.3, l.1460-1466)
The number of k-dimensional subspaces of F_q^n is the Gaussian binomial [n,k]_q = prod_{i<k}(q^n - q^i)/(q^k - q^i). Bounds: [d,r]/[a,r] <= G_q q^{r(d-a)} with G_q = prod(1 - q^{-i})^{-1} < 4. Also |GL(n,q)| >= q^{n^2}/4, and prod(1 - u_i) >= 1 - sum u_i.
- depends: 
- mathlib gap: Mathlib has no subspace count over finite fields. It has card GL.

### SX-L2.2 (routine, ~1500 lines, pp Sec 2.1, l.341-393)
Free root U_r = F_r/(F_r^{4} gamma_2(F_r)^2 gamma_3(F_r)) at p=2. W_r = Phi(U_r) is central elementary abelian with basis x_i^2 and [x_j,x_i] (i<j), and |U_r| = 2^{r+D_r} with D_r = r(r+1)/2. Every root with parameters (r,s) is U_r/N for some N <= W_r of codimension s. Aut(U_r) -> GL(r,2) is onto, and its kernel fixes W_r pointwise.
- depends: SX-PG
- mathlib gap: Mathlib has FreeGroup and quotients. It lacks relatively free groups and normal forms (collection). Independence is proved by maps to C_4 and UT_3(F_2).

### SX-P2.4 (routine, ~1100 lines, pp Sec 2.1-2.2, l.395-502 and l.605-631)
Lemma 2.3 and Prop 2.4 at p=2. A root G is determined up to isomorphism by y_G = (beta, pi), where beta: Lambda^2 V -> W is the commutator, pi: V -> W is the squaring map, and pi(v+w) = pi(v) + pi(w) + beta(v,w). The GL(V) x GL(W) orbits on admissible pairs (span(im beta, im pi) = W) correspond bijectively to root classes in R_2(d,s). Each beta has exactly 2^{ds} quadratic refinements. Lemma 2.8: B_2(d,s) <= 2^{sD_d}; B(d,0) = 1; B(d,s) = 0 for s > D_d.
- depends: SX-L2.2
- mathlib gap: No gap beyond SX-L2.2. Partly present in the FC2 file (BilinearExtension, classOf, isomorphism_preserves_alternating).

### BNV-5.3 (classical, ~400 lines, pp cited as [1, Cor 5.3, p.33] in Prop 3.5, l.853-856; reproved in Prop 4.3, l.1078-1081)
Sims rank. Let beta: Lambda^2 V -> W be onto, with dim W = b. If sigma is the least dim U <= V with beta(Lambda^2 U) = W, then 2 <= sigma <= min(d, b+1). Proof: every hyperplane of U has proper exterior image, and a projective line count gives p^sigma - 1 <= (p+1)(p^b - 1).
- depends: 
- mathlib gap: Not in Mathlib. Needs exterior powers of F_2-spaces (Mathlib has exteriorPower, but thin API) or explicit alternating bilinear maps.

### BNV-5.5 (classical, ~3000 lines, pp [1, Prop 5.5, pp.33-34], quoted in Prop 3.5, l.858-868)
Counts of labeled alternating maps Lambda^2 F_p^d -> F_p^b with minimal surjective-subspace dimension sigma (q = sigma - 1). The log count N_p(d,b,sigma) satisfies N <= d^2(b-q)/2 + O((d+b)^{8/3}) (Sims, eq. 5.5) and N <= d^2(b-q)/2 + dbq/2 + O((d+b)^{5/2}) (Newman-Seeley, eq. 5.6).
- depends: BNV-5.3, SX-GAUSS
- mathlib gap: Entirely absent. Needs Gaussian-binomial counting of subspaces and of alternating maps with prescribed spanning data.

### BNV-5.6 (classical, ~5000 lines, pp [1, Thm 5.6 p.38, construction pp.35-40, proof of Thm 5.7 pp.41-43], quoted l.870-882)
Restricted presentation theorem and the Sims count with layer data kept. Every nonabelian group of order p^m with r_1 = d, r_2 = b and Sims rank sigma is determined by structural indices, power data and a restricted set of commutator data. With u = m-d-b and q = sigma-1: log_p T_p(m;d,b,sigma) <= N_p(d,b,sigma) + d^2u/2 + (qb - q^2/2)u + qu^2/2 + O(m^2), uniformly in the parameters. This covers BNV eqs (5.12)-(5.14), and the structural-index factor 2^{3m-2}p^{m^2}.
- depends: SX-PG, BNV-5.3, BNV-5.5
- mathlib gap: Absent from Mathlib. The in-house Sims-lite library (3695 lines: strict core chains, codes with shapes, rigidity via the diagonal of G x G') does the same kind of rigidity with constant 2/25, without Sims rank or Frattini data. It must be extended to keep (d, b, sigma) and to reach the sharp 2/27 leading term.

### SX-P3.5 (classical, ~900 lines, pp Sec 3.2, l.825-916)
Off-strip localization, p=2. For each eps > 0, the number of groups of order 2^m with |d(G)/m - 2/3| >= eps is at most 2^{(2/27 - c_eps)m^3 + O(m^{8/3})}, with c_eps = min(7/3375, 7eps^2/15). Proof: optimize the leading polynomials A and B over x = d/m, y, z, w (A <= x^2(1-x)/2 for x >= 3/5; B <= 9/125 or 1/16 for x <= 3/5), plus a partition bound for abelian groups. For the frontier only an eventual cubic saving at fixed eps = 1/10000 is needed.
- depends: BNV-5.6, BNV-5.5
- mathlib gap: The polynomial inequalities are routine (nlinarith or polyrith with case splits). Everything else is in BNV-5.5 and BNV-5.6.

### SX-L4.1 (classical, ~1500 lines, pp Sec 4.1, l.922-961)
p-covering group of a root Q (p=2). Take a minimal presentation F/R = Q and set K = F/R^2[R,F], M = R/R^2[R,F], and nucleus N = gamma_3^(2)(K), with nu(Q) = dim N. Then K is finite, M is central elementary abelian with M <= Phi(K), gamma_4^(2)(K) = 1, K/N = U_d, H^2(Q,F_2) = M^*, and r(Q) = D_d - s + nu(Q). R is finitely generated by Schreier's lemma.
- depends: SX-L2.2, COH-BASE
- mathlib gap: Mathlib has FreeGroup and Schreier's lemma. It lacks p-covering groups and the identification of H^2(Q,F_p) with central-extension classes via pushouts. The nu-only part (K, N and nu) needs no cohomology.

### SX-L4.2 (classical, ~1300 lines, pp Sec 4.1, l.963-1008)
Allowable extensions. Let L(Y) = inf(H^2(Y/Phi(Y))) in H^2(Y) for Y/gamma_3^(2)(Y) = Q. A central C_2-extension has class in L(Y) iff its kernel is not in gamma_3^(2)(E). Also dim L(Y) = D_d - s, h(Y) = r(Y) - (D_d - s) >= 0, and the number of allowable lines is 2^{D_d - s}(2^{h(Y)} - 1). Every G with G/gamma_3^(2)(G) = Q and |gamma_3^(2)| = 2^t is reached by a length-t chain of allowable C_2-extensions.
- depends: SX-L4.1, SX-PG, COH-BASE
- mathlib gap: Inflation, pullback and pushout of central extensions, and injectivity of inflation on L_0. None of this is in Mathlib in the needed form.

### MATRIX-RANK (classical, ~700 lines, pp inside Prop 4.3, l.1084-1096)
If every matrix in a linear space S of a x b matrices over F_q has rank <= R, then dim S <= R max(a,b). Proof: linearized polynomials sum_{i<b-R} c_i Z^{q^i} over F_{q^a} give a complementary space of rank >= R+1.
- depends: 
- mathlib gap: Not in Mathlib (Flanders/Meshulam type). GaloisField and root counting exist, but linearized polynomials as F_q-linear maps do not.

### SX-P4.3 (new, ~2000 lines, pp Sec 4.2, l.1010-1115)
Nucleus bounds for a root Q with s >= 1: nu(Q) <= s(s+3)/2 and nu(Q) <= (s+1)R_beta. Here R_beta is the maximum rank in the Jacobi dual J_beta = ker J_beta^* in (V tensor W)^*, with J_beta(x^y^z) = x tensor beta(y,z) + cyclic terms. Also R_beta = 0 gives nu = 0, and R_beta = 1 gives nu <= 2. The proof uses maps T, S onto N, the relations TJ_beta = 0 and T(x,q(y)) = S beta(x,y) - c_p T(y,beta(x,y)) with c_2 = 1, the exterior leading-monomial rank bound kappa_B <= b(b+3)/2, BNV-5.3, and MATRIX-RANK.
- depends: SX-L4.1, BNV-5.3, MATRIX-RANK, SX-P2.4
- mathlib gap: Hall-Witt and collection identities in a class-3 group (the Sims-lite commutator calculus helps). Exterior-algebra row reduction. Purely group theory and linear algebra; no cohomology.

### ORBIT-AUX (classical, ~1600 lines, pp Prop 4.4, l.1184-1219; refs [10],[12])
Orbit bound replacing the k=2 pencil step in (9), for the R=1 stratum only. Option (A): every ordered pair of alternating forms on F_2^n is a direct sum of Kronecker, finite-regular and infinity blocks (Waterhouse 1977 for char 2, Sergeichuk otherwise), so there are at most 2^{2n} GL(n)-orbits on pairs. Option (B), recommended: adapt the FC2 file's OrbitUp incidence counting to H = GL(A) x GL(W_0) acting on Hom(Lambda^2 A, W_0) with n = d-R and k = s-R large. This gives #orbits <= 2^{k C(n,2) - n^2 - k^2 + loss} with loss << d^2/2.
- depends: SX-P2.4
- mathlib gap: Option (A): Mathlib has no Kronecker or pencil theory. It has the PID module structure theorem, which covers only the regular part. Estimate 5000-8000 lines. Option (B): reuses the FC2 file (2865 lines, incidence_stratified, all_quadratic_orbits_upper); about 1600 lines of adaptation. Rank classification of single alternating forms (Darboux) is also missing from Mathlib, but (B) avoids it.

### SX-P4.4 (new, ~2500 lines, pp Sec 4.3, l.1117-1261)
Weighted root count, p=2. Assume d >= 1000, s >= 3, t >= 1, m = d+s+t, z = s+t, delta = m - 3d/2, |delta| <= d/1000. Then sum over Q in R_2(d,s) with nu(Q) > 0 of 2^{t(D_d - s) + t nu(Q)} <= 2^{F(d,z) - d^2/20}, where F = zD_d - d^2 - z^2. Proof: stratify by Jacobi rank R. Delta_R = C(d,3) - C(d-R,3) is the codimension of TJ_beta = 0. GL is transitive on rank-R witnesses. Use bounds (9) via the equivariant surjection Y_T -> Hom(Lambda^2 A, F_2^k), then the case arithmetic. With the m^2/9 frontier slack, d^2/20 can be weakened to about -(d^2/4) + C d log d. Then the first bound n_R <= 2^{sD - Delta_R} suffices for R >= 4, the one-form bound for R = 2, 3, and the two-form/pencil bound only for R = 1.
- depends: SX-P4.3, SX-P2.4, ORBIT-AUX
- mathlib gap: The counting framework (orbits of an equivariant surjection, transitivity on rank-R tensors, the exterior monomial count) is routine but long. The arithmetic needs nlinarith work at d >= 1000.

### COH-BASE (classical, ~5000 lines, pp Sec 4.1 l.922, Sec 5.1-5.3)
Cohomology H^n(G,F_2) for n <= 3 of finite groups with trivial coefficients, via inhomogeneous cochains. Needed: cup products H^1 x H^2 -> H^3; inflation and restriction, functorial and compatible with cup; H^1 = Hom(G,F_2); H^2 in bijection with equivalence classes of central C_2-extensions, compatibly with pullback and pushout; the Bockstein from 0 -> F_2 -> Z/4 -> F_2 -> 0 and its naturality.
- depends: 
- mathlib gap: Mathlib has groupCohomology (Rep, inhomogeneous cochains, H^n, low-degree H^1/H^2 API, some functoriality). It lacks cup products, the full H^2 <-> extensions bijection with naturality, and the Bockstein. This is the largest gap.

### COH-LHS (classical, ~6500 lines, pp Sec 5.1, l.1267-1318)
Lemma 5.1 without the Bockstein identification. Let 1 -> C_2 -> E -> Y -> 1 be a nonsplit central extension with class xi. Then H^1(E) = H^1(Y), and r(E) = r(Y) - 1 + a_Y(xi) + eps with eps in {0,1}, where a_Y(xi) = dim ker(cup xi: H^1(Y) -> H^3(Y)). Also dim ker(inf: H^3(Y) -> H^3(E)) = d + r(Y) - r(E). The same holds with h in place of r for allowable extensions.
- depends: COH-BASE
- mathlib gap: Mathlib has no spectral sequences and no LHS sequence. Plan: prove the low-degree LHS facts for central C_2 extensions directly on cochains, up to total degree 3, including exactness at the (3,0) spot.

### COH-LEARY (classical, ~3200 lines, pp l.1287-1293, ref [5])
For a central C_2-extension: d_3(tau) = Bock_Y(xi) mod H^1(Y) cup xi (Leary 1993). Hence eps_Y(xi) = 1 iff Bock_Y(xi) is in H^1(Y) cup xi.
- depends: COH-LHS, COH-BASE
- mathlib gap: Absent. Needed only for Lemma 5.5, i.e. only for the bounded-width population s <= 2 (Prop 5.7). Prop 5.6 needs only eps <= 1.

### COH-ELAB (classical, ~4000 lines, pp Prop 5.3 l.1434-1443; Lemma 5.5 l.1506-1529)
For V = C_2^d: H^{<=3}(V,F_2) = Sym^{<=3}(V^*) as algebras, with dimensions d, D_d, C(d+2,3). The quotient map to Lambda(V^*) and the splitting H^2 = E + P are used. Cup with a nonzero linear class is injective H^2 -> H^3. For Lemma 5.5 also: Bock = Sq^1 is a derivation with dx_i = x_i^2, and rank(d + x_1) on Sym^2 is N_d + 1.
- depends: COH-BASE
- mathlib gap: Absent. Needs low-degree Kunneth or explicit cocycles, and linear independence of the monomial classes (detected by restriction to small subgroups).

### SX-L5.2 (new, ~2000 lines, pp Sec 5.2, l.1320-1403)
(a) Subgroup criterion: if Phi(H) gamma_3^(2)(G) = Phi(G), then Phi(H) = Phi(G), H is normal and gamma_3^(2)(H) = gamma_3^(2)(G). Restriction then injects H^2(Y)/L(Y) into H^2(H)/L(H). Capacity: for a descendant Y of Q with s >= 1 and |gamma_3^(2)(Y)| = 2^j, 0 <= h(Y) <= s(s+3)/2 + 2sj. (b) For an epimorphism X -> Y with kernel of order 2^j inside Phi(X) and d(X) = d(Y) = d: dim ker(H^3(Y) -> H^3(X)) <= jd + r(Y) - r(X).
- depends: COH-LHS, SX-L4.2, SX-L4.1, SX-P4.3, SX-PG
- mathlib gap: Restriction maps on H^2 and their compatibility with L. Otherwise group theory.

### SX-P5.3 (new, ~2100 lines, pp Sec 5.3, l.1405-1490)
Annihilator tails. K_Y = d(s+j) + s - h >= 0. For every affine coset C of L(Y) and 3 <= r <= a <= d: Pr_C(a_Y(xi) >= a) <= min{1, G_2 2^{r(d-a) - C(d,2) + 3K_Y/(r-2)}}, and the same for uniform allowable lines. Inputs: Z_Y = ker(H^3(V) -> H^3(Y)) has dim <= K_Y; the exterior-shadow inequality (r-2) dim F <= 3 dim(A ^ F); Gaussian double counting. Cor 5.4: if d >= 10000 and K_Y <= 3d^2/5, then Pr(a >= a0) <= 2^{-(d/2 - 1000)a0} for a0 >= d/100, and Pr(a >= 100) <= 2^{-9d^2/20}.
- depends: SX-L5.2, COH-ELAB, SX-GAUSS
- mathlib gap: Finite probability over affine cosets of F_2-spaces is routine. The exterior-shadow row reduction is not in Mathlib.

### SX-P5.6 (new, ~2200 lines, pp Sec 5.5, l.1549-1646)
Descendants of a fixed root. Assume d >= 10000, s,t >= 1, |delta| <= d/1000, b_0 = D_d - s. Then for every Q in R_2(d,s): D_2(Q,t) <= 2^{t(b_0 + nu(Q)) + E_2(d,s,t)}, with E = (2s+1)w(s+w) + 50U(U+1) + t log2(d+3), U = ceil(2 delta_+ + 10), w = ceil((delta - s + 1000)_+). Also D_2(Q,t) = 0 if nu(Q) = 0. Proof: the allowable-extension tree with branching n_i = 2^{b_0}(2^{h_i} - 1), the tree identity #leaves = E[1_surv prod n_i], clipped conditional moments of 2^{z_i a_i} by backward induction, and the pathwise capacity bound.
- depends: SX-L4.2, SX-P5.3, COH-LHS, SX-L5.2, COH-ELAB
- mathlib gap: Finite-tree expectation identities need a custom development (no probability monad needed; finite weighted sums suffice).

### SX-L5.5 (new, ~1500 lines, pp Sec 5.4, l.1494-1547)
Let Q be a root with d >= 64 and 1 <= s <= d/16, and let Y with Y/gamma_3^(2)(Y) = Q have depth j <= d/8. For a uniform allowable line, Pr(a_Y(xi) + eps_Y(xi) > 0) <= 2^{-d^2/4}. Proof: inflation loses at most K_Y dimensions in H^3; cup with chi and d + lambda have rank at least N_d - K_Y on L(Y); union bound over chi and lambda.
- depends: COH-LEARY, COH-ELAB, SX-L5.2
- mathlib gap: Only through COH-*.

### SX-P5.7 (new, ~1500 lines, pp Sec 5.6, l.1648-1702)
Bounded Frattini layer. For fixed S >= 1 and large m, the number of groups of order 2^m with dim Phi(G/gamma_3^(2)G) <= S is at most 2^{(2/27)m^3 - c_S m^2 log2 m}, with c_S = 1/(100 log2(2S+1)). Proof: survival forces about log m exceptional steps, each costing 2^{-d^2/4}; roots counted by B <= 2^{sD} (Lemma 2.8); crude capacity bounds elsewhere. Needed for s <= 2 in the strip. For 3 <= s <= S, SX-P4.4 with SX-P5.6 also works, so the in-house bounded-width split at S = 192000 can be served either way.
- depends: SX-L5.5, SX-L5.2, SX-P2.4, SX-L4.2, COH-LHS
- mathlib gap: Elementary analysis of the recursion u_{i+1} <= B + (A+1)u_i and of the threshold. Uniformity in S is not required.

### SX-L6.1 (routine, ~500 lines, pp Sec 6, l.1706-1746)
In the range of Prop 5.6, with z = s+t and k = 0: F(d,z) + E_2(d,s,t) <= lambda(m) + O(d log d). This uses the exact identity F - lambda = 5d delta/6 - (d/3 + 5/9)delta^2 - 2delta^3/27 and the cubic bound for the error terms.
- depends: 
- mathlib gap: Real-arithmetic inequalities only.

### SX-P6.2w (new, ~800 lines, pp Sec 6.1, l.1750-1786)
Weakened Prop 6.2 at p=2: N_2(m) <= 2^{lambda(m) + m^2/9 - 2} eventually. The paper proves N_2 <= 2^{lambda - m^2/300}. Split: (i) s <= 2 by SX-P5.7; (ii) off-strip by SX-P3.5 with eps = 1/10000; (iii) central strip with s >= 3: count(d,s,t) <= 2^{F - (saving) + E}, using SX-P4.4, SX-P5.6 and SX-L6.1, then sum over at most (m+1)^2 triples.
- depends: SX-P5.7, SX-P3.5, SX-P4.4, SX-P5.6, SX-L6.1
- mathlib gap: Bookkeeping over isomorphism classes, in the in-house Lean encoding with Nat.card of a quotient by isIsomorphicSetoid.

### FRONTIER (routine, ~300 lines, pp Thm 1.3 proof, l.1790-1797 (analog))
log2 g(2^m) <= (2/27)m^3 - m^2/3 for large m. Combine the SOLVED FC2 count R_2(m) <= 2^{(2/27)m^3 - (10/27)m^2 + O(m)} with SX-P6.2w.
- depends: SX-P6.2w
- mathlib gap: None. The reduction files R1.H2.R1.H2.R1/R2 already exist.
