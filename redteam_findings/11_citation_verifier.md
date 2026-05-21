# Red Team Audit: Citation Verifier (paper-claim cross-check)

**Auditor lens**: Forensic literature reviewer — every Tier 1 cited axiom claims a specific paper + theorem number; this audit verifies each claim against the actual paper using WebFetch/WebSearch and direct PDF reads of the cited primary sources (Le Gall 2016 in full, Applebaum 2009 TOC, K-S 2nd ed TOC, Bouchard-Elie bibliography, Gnoatto publication list).
**Date**: 2026-05-20
**Coverage**: Read in full: `tools/cited_axioms.md`, `redteam_findings/shared_context_override.md`, `personas/11_citation_verifier.md`, `output_template.md`, all 11 Lean files housing the cited axioms (`Brownian/Construction.lean`, `Brownian/Continuity.lean`, `Brownian/Martingale.lean` §axiom region, `Brownian/SimplePredictableRefine.lean` §axiom region, `Poisson/RandomMeasure.lean`, `Poisson/Compensated.lean` §axiom regions, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`, `Ito/JumpFormula.lean`). Read directly from primary sources: Le Gall *Brownian Motion, Martingales, and Stochastic Calculus* Springer 2016 GTM 274 Ch. 2 and Ch. 5 (verified Theorems 2.1, 2.9, 2.13, 5.4, 5.10, 5.12, 5.13 — full PDF), Karatzas–Shreve 2nd ed TOC (verified section structure 2.1–2.7 and 3.2), Applebaum 2nd ed CUP 2009 TOC (verified section structure 2.3, 4.2, 4.3, 4.4), Bouchard slides + Kharroubi-Lim 2018 references, Gnoatto DBLP publication list (2024–2025), Davar Khoshnevisan PRM lecture notes, Papapantoleon-Possamaï-Saplaouras "the whole nine yards" Section 1–2.

## Executive summary (≤ 3 sentences)

Three Tier 1 axiom citations are **demonstrably wrong**: axiom #10 attributes the Bouchard–Elie 2008 SPA paper to "Bouchard, Elie & Touzi 2009 SPA 119(11)" (Touzi was never a coauthor; the paper is 2008, volume 118), and axiom #9 cites a non-existent Gnoatto 2025 "primer on backward stochastic differential equations with jumps" in *Quantitative Finance* (no such paper exists in Gnoatto's 2024–2025 publication list — his actual 2025 papers are deep-solver/convergence papers in SIAM J. Financial Math.). The Le Gall theorem numbers in axioms #1, #4, #5 are also wrong: Le Gall has no "Theorem 2.1" (Defn 2.1 = pre-BM; BM existence is Cor 2.11 + Defn 2.12), Le Gall Proposition 2.10 cited for Blumenthal/right-continuous filtration is actually an analytic Hölder-extension lemma (Blumenthal is Le Gall Thm 2.13), and Le Gall Thm 5.13 cited for the L² Itô isometry is actually the Dambis–Dubins–Schwarz theorem (the L² isometry is in Le Gall Thm 5.4 / eq. 5.8).

## Top findings (ranked by severity, highest first)

### Finding 1 — Bouchard–Elie–Touzi 2009 SPA 119(11) citation is wrong on EVERY component

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean:23-24` and `:92-94`; `D:\LevyStochCalc\tools\cited_axioms.md:84` (Tier 1 entry #10)
- **Evidence**:
  - Lean docstring (`PathRegularity.lean:23-24`):
    > "Bouchard & Elie & Touzi, 'Discrete-time approximation of decoupled Forward-Backward SDE with jumps', SPA 119(11), 2009, Theorem 2.1."
  - Lean docstring (`PathRegularity.lean:92-94`):
    > "Bouchard, B. & Elie, R. & Touzi, N. *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, Stochastic Processes and their Applications 119(11), 2009, Theorem 2.1"
  - `cited_axioms.md:84` (same wording)
  - **Reality** (verified via Bouchard's own slides PDF `D:\…\webfetch-…-6atvj8.pdf` p. 19 references slide, and Kharroubi-Lim 2018 paper PDF `D:\…\webfetch-…-i22ld4.pdf` p. 2):
    > "Bouchard B. and R. Elie (05). *Discrete time approximation of decoupled Forward-Backward SDE with jumps*. Preprint."  (from Bouchard's own slide deck)
    > "For Lipschitz generators, the discrete-time approximation of FBSDEs with jumps is studied by **Bouchard and Elie** [4] in the case of Poissonian jumps independent of the Brownian motion." (Kharroubi-Lim 2018 §1)
  - Bibliographic confirmation (multiple web sources): Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward–Backward SDE with jumps*, **Stochastic Processes and their Applications 118(1), January 2008, pp. 53–75**; DOI 10.1016/j.spa.2007.03.010. **Two authors, not three. 2008, not 2009. Volume 118 issue 1, not 119(11). The previous Bouchard–Touzi paper (2004) was a separate work on Brownian-only BSDE Monte Carlo (SPA 111).**
- **Why this matters**: This is not a typo — every bibliographic field is wrong: author list (3 → 2 authors), year (2009 → 2008), volume (119 → 118), issue (11 → 1). The conflation appears to merge "Bouchard–Touzi 2004 SPA 111" (Brownian Monte Carlo) with "Bouchard–Elie 2008 SPA 118" (jumps). A Mathlib reviewer who chased this citation to verify the BET 2009 axiom would not find it; an examiner of any forwarder that surfaces this axiom (e.g. `Dissertation.Continuous.bsdej_path_regularity`) would discover that the cited paper does not exist as advertised. This is precisely the "hallucinated citation" pattern Persona 11's mandate flags as CRITICAL.
- **Recommendation**: Replace the citation in `PathRegularity.lean:23-24` and `:92-94` and `cited_axioms.md:84` with the correct bibliographic entry: "Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, **Stochastic Processes and their Applications 118(1), 2008, pp. 53–75**" and verify that the cited "Theorem 2.1" of that paper is in fact the path-regularity claim (this needs primary-source access — the published SPA version is paywalled; the HAL preprint `hal-00015486` was blocked by Anubis in this audit and could not be opened). Until verified, downgrade the claim to "consequence of Theorem … of Bouchard–Elie 2008".

### Finding 2 — Gnoatto 2025 "primer on backward stochastic differential equations with jumps" does NOT exist

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:100-101`; `D:\LevyStochCalc\tools\cited_axioms.md:76`
- **Evidence**:
  - Lean docstring (`Existence.lean:100-101`):
    > "Gnoatto, A. *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, Theorem 2.2;"
  - `cited_axioms.md:76` (identical claim)
  - **Reality** (verified via DBLP `https://dblp.org/pers/g/Gnoatto:Alessandro`, fetched 2026-05-20): Alessandro Gnoatto has **NO 2024–2025 publication** titled "A primer on backward stochastic differential equations with jumps". His full 2025 publication list is:
    1. *Deep Quadratic Hedging* (Math. Oper. Res.) — Lavagnini, Picarelli
    2. *A Deep Solver for BSDEs with Jumps* (SIAM J. Financial Math. 16(3): 875–911) — Andersson, Patacca, Picarelli
    3. *Convergence of a Deep BSDE solver with jumps* (arXiv 2501.09727, preprint) — Oberpriller, Picarelli
    4. *A deep solver for backward stochastic Volterra integral equations* (arXiv 2505.18297, preprint) — Andersson, Garcia Trillos
  - None is in *Quantitative Finance* journal. None is called a "primer". WebSearches for `"primer on backward stochastic differential equations" jumps survey` and `site:tandfonline.com Gnoatto primer BSDE jumps` returned **zero matching publications**.
- **Why this matters**: This is a **fabricated citation** — a paper that does not exist is cited as the second co-reference (after Tang–Li 1994) for the central BSDEJ existence/uniqueness axiom, which underlies four of the dissertation forwarders. A Mathlib reviewer or PhD examiner checking the axiom's provenance would arrive at a dead end and lose confidence in the entire citation apparatus. This is exactly the "hallucinated citation that doesn't survive a WebFetch" pattern Persona 11's mandate calls out.
- **Recommendation**: Delete the Gnoatto citation entirely from `Existence.lean:100-101` and `cited_axioms.md:76`. If the orchestrator wanted a modern survey reference next to Tang–Li 1994, the appropriate replacement is **Papapantoleon, A., Possamaï, D. & Saplaouras, A. *Existence and uniqueness results for BSDE with jumps: the whole nine yards*, Electron. J. Probab. 23 (2018), no. 121, 1–68** (arXiv:1607.04214 — verified accessible, exact title, covers exactly this content).

### Finding 3 — Le Gall "Theorem 5.13" cited for the L² Itô isometry is actually the Dambis–Dubins–Schwarz theorem

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\SimplePredictableRefine.lean:2076-2077`; `D:\LevyStochCalc\tools\cited_axioms.md:48`
- **Evidence**:
  - Lean docstring (`SimplePredictableRefine.lean:2076-2077`):
    > "Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 3.2.6** (unified martingale + quadratic variation + L²-isometry of the L² Itô integral); Le Gall, J.-F. *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 5.13**."
  - `cited_axioms.md:48` (same wording)
  - **Reality** (verified by reading Le Gall 2016 PDF p. 121 directly):
    > "**Theorem 5.13 (Dambis–Dubins–Schwarz)** *Let M be a continuous local martingale such that ⟨M, M⟩_∞ = ∞ a.s. There exists a Brownian motion (β_s)_{s≥0} such that, a.s., ∀ t ≥ 0, M_t = β_⟨M,M⟩_t.*"
  - The L² Itô isometry that this axiom is genuinely asserting is actually proved in Le Gall **§5.1 Theorem 5.4** (construction of H·M as the unique martingale in ℍ² satisfying ⟨H·M, N⟩ = H·⟨M, N⟩) plus eq. (5.8) on p. 105: `E[(∫₀^t H_s dM_s)²] = E[∫₀^t H_s² d⟨M,M⟩_s]` — this IS the L² isometry, and it is established at Theorem 5.4 / equation 5.8, not Theorem 5.13.
- **Why this matters**: A Mathlib reviewer checking what's in Le Gall Thm 5.13 would find a representation theorem (continuous local martingale = time-changed BM), not an isometry. The cited theorem does not say what the axiom claims. This is a HIGH-severity defect because the axiom's secondary citation is wrong about which theorem it is.
- **Recommendation**: Change `Le Gall ... **Theorem 5.13**` to `Le Gall ... **Theorem 5.4 + eq. (5.8)** (Section 5.1.1, "Stochastic integrals for elements of ℍ²")` in both files.

### Finding 4 — Le Gall "Proposition 2.10" cited for Blumenthal 0-1 / right-continuous filtration is actually an unrelated analytic Hölder lemma; Blumenthal is Le Gall Theorem 2.13

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Martingale.lean:905-906`; `D:\LevyStochCalc\tools\cited_axioms.md:41`
- **Evidence**:
  - Lean docstring (`Martingale.lean:905-906`):
    > "Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*, Springer 1991, Theorem 2.7.7 (Blumenthal 0-1 law) + Theorem 2.7.9 (continuity of the augmented filtration); Le Gall, J.-F. *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Proposition 2.10**."
  - `cited_axioms.md:41` (same wording: "Le Gall **Proposition 2.10**")
  - **Reality** (verified by reading Le Gall 2016 PDF pp. 25–26 directly):
    > "**Lemma 2.10** *Let f be a mapping defined on D and with values in the metric space (E, d). Assume that there exists a real α > 0 and a constant K < ∞ such that, for every integer n ≥ 1 and every i ∈ {1, 2, …, 2ⁿ − 1}, d(f((i−1)·2⁻ⁿ), f(i·2⁻ⁿ)) ≤ K·2⁻ⁿα. Then we have, for every s, t ∈ D, d(f(s), f(t)) ≤ (2K/(1−2⁻α)) |t − s|ᵅ.*"
  - This is a deterministic analytic Hölder-extension lemma used inside the proof of Le Gall **Theorem 2.9** (Kolmogorov's lemma). It has **nothing to do with Blumenthal 0-1 / right-continuity of filtrations**.
  - The actual Blumenthal 0-1 law in Le Gall 2016 is **Theorem 2.13** (p. 30):
    > "**Theorem 2.13 (Blumenthal's zero-one law)** *The σ-field 𝓕₀₊ is trivial, in the sense that P(A) = 0 or 1 for every A ∈ 𝓕₀₊.*"
- **Why this matters**: The cited Le Gall theorem number is off by three units and points to a result of an entirely different kind (deterministic analysis vs. probabilistic 0-1 law). A reviewer checking the Le Gall reference would conclude the axiom's literature anchoring is broken for the non-K-S half of the citation.
- **Recommendation**: Change `Le Gall ... **Proposition 2.10**` to `Le Gall ... **Theorem 2.13** (Blumenthal's zero-one law) + the right-continuous augmentation discussion in §2.3` in both files.

### Finding 5 — Pardoux–Răşcanu Springer 2014 cited for BSDEJ existence and BSDEJ path regularity, but that book covers continuous (Brownian-driven) BSDEs only

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:101-103`; `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean:94-96`; `D:\LevyStochCalc\tools\cited_axioms.md:76` and `:85`
- **Evidence**:
  - `Existence.lean:101-103`:
    > "Pardoux, E. & Răşcanu, A. *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, **Theorem 4.79**."  (as third reference for **BSDEJ** existence/uniqueness)
  - `PathRegularity.lean:94-96`:
    > "Pardoux, E. & Răşcanu, A. *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, **Theorem 5.42** (continuous case)."  (as secondary reference for **BSDEJ** path regularity; the `(continuous case)` parenthetical is itself a giveaway)
  - **Reality** (verified via Pardoux's own publication page `https://www.i2m.univ-amu.fr/perso/etienne.pardoux/epe.html`, Springer chapter titles via WebSearch, and the chapter list available via SpringerLink redirect): The book is volume 69 of Stochastic Modelling and Applied Probability. Its scope is:
    - Chapter 2: "Itô's Stochastic Calculus" (pp. 73–133) — continuous Itô integral
    - Chapter 4: Stochastic Differential Equations (continuous case)
    - Chapter 5: "Backward Stochastic Differential Equations" (pp. 353–515) — the classic Brownian BSDE theory, multivalued/reflected variants in **continuous time**
    - No chapter covers Poisson random measures, compensated jumps, BSDEs with jumps, or Lévy-driven BSDEs. The book's standing description across multiple sources ("comprehensive reference for the continuous case", "extension to multivalued coefficients", "reflected SDEs/BSDEs") and the parenthetical `(continuous case)` in the Lean docstring itself both indicate the book does not cover the jump case.
  - The cited axioms are explicitly about the **jump case** (`BSDEJ` = BSDE with Jumps, integrating against a Poisson random measure `N`). Cited reference Tang–Li 1994 covers the jump case; Pardoux–Răşcanu 2014 does not.
- **Why this matters**: Citing a continuous-BSDE textbook as authority for a BSDEJ (jump) existence theorem is a category error. The theorem numbers 4.79 and 5.42 may or may not exist in the book (the book is paywalled and not openly readable; I could not directly verify), but even if they do exist, they are about the continuous case and do not support the BSDEJ axioms. A reviewer of the BSDEJ axioms would see the Pardoux–Răşcanu citation, look up the book, and discover it doesn't cover the jump case at all.
- **Recommendation**: Remove the Pardoux–Răşcanu citation from `Existence.lean:101-103` and `PathRegularity.lean:94-96`, or relegate it to "for the continuous-only background, see also …". Replace it (especially for `PathRegularity`) with the actual jump-case path-regularity references: **Bouchard–Elie 2008 SPA 118(1) Theorem 2.1** (the primary already-cited reference, once its bibliographic details are fixed per Finding 1) and **Geiss & Steinicke** or **Aazizi 2013** style references for the BSDEJ-side L² time-modulus bound.

### Finding 6 — Le Gall "Theorem 2.1" cited for Brownian motion existence does not exist; pre-Brownian motion is Definition 2.1, BM existence comes via Definition 2.12 and Corollary 2.11

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Construction.lean:163-164`; `D:\LevyStochCalc\tools\cited_axioms.md:20`
- **Evidence**:
  - `Construction.lean:163-164`:
    > "Le Gall, J.-F. *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 2.1**."
  - `cited_axioms.md:20`:
    > "Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 2.1**."
  - **Reality** (verified by reading Le Gall 2016 PDF pp. 19–27 directly): There is **no "Theorem 2.1"** in Le Gall Chapter 2. The numbered items at the start of Chapter 2 are:
    - **Definition 2.1**: pre-Brownian motion (using a Gaussian white noise)
    - **Proposition 2.2**: pre-BM is a centered Gaussian process with covariance min{s,t}
    - **Proposition 2.3**: equivalences for pre-BM
    - **Corollary 2.4**: finite-dim density
    - **Proposition 2.5**: symmetry/scaling/Markov
    - **Definition 2.6, 2.7, 2.8**: process / modification / indistinguishable
    - **Theorem 2.9**: Kolmogorov's lemma
    - **Lemma 2.10**: analytic Hölder-extension lemma
    - **Corollary 2.11**: pre-BM has continuous modification (this is what actually gives existence)
    - **Definition 2.12**: Brownian motion = continuous pre-BM
    - **Theorem 2.13**: Blumenthal's 0-1 law
  - Brownian motion **existence** in Le Gall is **NOT a "Theorem 2.1"**; it is the conjunction of Definition 2.12 (the definition) + Corollary 2.11 (continuous modification of pre-BM via Kolmogorov, Thm 2.9). Definition 2.1 is a *definition*, not a theorem.
- **Why this matters**: This is the LOWEST-severity Le-Gall finding because the math is fine — Le Gall does construct BM in Chapter 2 — but the cited theorem number is fabricated. A reader looking for "Theorem 2.1" in Le Gall to verify the axiom claim would not find it. (Karatzas–Shreve **Theorem 2.1.5** for the same axiom is similarly suspicious — see Finding 7.)
- **Recommendation**: Replace `Le Gall ... **Theorem 2.1**` with `Le Gall ... **Corollary 2.11 + Definition 2.12** (Chapter 2 "Brownian Motion")` in both files.

### Finding 7 — Karatzas–Shreve "Theorem 2.1.5" for Brownian motion existence is suspicious (section 2.1 is the chapter Introduction, only a few pages)

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Construction.lean:162-164`; `D:\LevyStochCalc\tools\cited_axioms.md:20`
- **Evidence**:
  - Lean docstring (`Construction.lean:162-164`):
    > "Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.1.5**; Le Gall, …"
  - **K-S 2nd ed TOC (verified via `D:\…\webfetch-…-0mscxe.pdf` p. xi–xii of the TOC PDF)**:
    - **§2.1 Introduction** (p. 47) — a 2-page introduction
    - §2.2 First Construction of Brownian Motion (p. 49)
      - §2.2.A The consistency theorem
      - §2.2.B The Kolmogorov-Čentsov theorem (p. 53)
    - §2.3 Second Construction of Brownian Motion (p. 56)
    - §2.4 The Space C[0,∞), Weak Convergence, and Wiener Measure (p. 59) — including §2.4.D "The invariance principle and the Wiener measure" (p. 66)
  - K-S uses an `<X.Y.N>` = `<chapter>.<section>.<theorem-counter-in-section>` numbering convention (consistent with the verified Theorem 2.7.7 / 2.7.9 / 3.2.6 elsewhere). For a 2-page Introduction section (§2.1) to contain a "Theorem 5" labelled the canonical existence statement is unusual. The actual BM existence in K-S is the conjunction of §2.2 (consistency + Kolmogorov-Čentsov modification, i.e., Thm 2.2.2 + Thm 2.2.8) and the Wiener-measure formulation in §2.4.
- **Why this matters**: I could not access the body text of K-S 2nd ed (only the TOC PDF is freely available; the full book PDFs we tried all gave back binary streams that the Read tool could not extract). However, the TOC strongly indicates "Theorem 2.1.5" is not the canonical citation for BM existence in K-S; that would more naturally be "Theorem 2.2.2 (consistency) + Theorem 2.2.8 (continuous modification)" or "Theorem 2.4.D" (Wiener measure). UNVERIFIABLE-without-paywall: I could not open the book body. The claim should be checked against a physical/library copy.
- **Recommendation**: Verify against a hardcopy whether "Theorem 2.1.5" exists in §2.1 of K-S 2nd ed. If it does not (most likely), replace with `Karatzas–Shreve **Theorem 2.2.2 + Theorem 2.2.8** (Chapter 2 §2.2 "First Construction of Brownian Motion")`. The axiom claim is true mathematically; only the theorem number needs fixing.

### Finding 8 — "Pardoux–Răşcanu Theorem 5.42 (continuous case)" parenthetical itself flags the axiom's jump-case scope mismatch

- **Severity**: MEDIUM (subset of Finding 5, but worth flagging on its own)
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean:94-96`
- **Evidence**:
  - The Lean docstring explicitly writes `Pardoux & Răşcanu, Springer 2014, **Theorem 5.42 (continuous case)**`.
  - The axiom being cited (`bsdej_path_regularity`) is about the **jump-case BSDEJ** — Poisson random measure `N`, mark space `E`, integrand `U : ℝ → Ω → E → ℝ`.
  - The parenthetical "(continuous case)" is the docstring author's own admission that the cited result is the *continuous-only* analog and does not directly support the jump-case claim.
- **Why this matters**: The docstring transparently admits the secondary citation does not match the axiom statement. Either the axiom should be split into "continuous case (already proven by …)" + "jump case (this axiom)", or the parenthetical citation should be removed.
- **Recommendation**: Remove the `Pardoux & Răşcanu … Theorem 5.42 (continuous case)` clause entirely; it does not support the jump-case axiom. Keep Bouchard–Elie as the primary reference (once Finding 1 is fixed).

### Finding 9 — Applebaum 2009 "Theorem 4.2.3 + 4.2.4" for unified compensated-Poisson L² Itô — citation is plausible but unverifiable from open sources

- **Severity**: UNVERIFIABLE / MEDIUM (no defect found, but no positive verification either)
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:2725-2727`; `D:\LevyStochCalc\tools\cited_axioms.md:55`
- **Evidence**:
  - Lean docstring (`Compensated.lean:2725-2727`):
    > "Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.2.3** (martingale + quadratic variation + L²-isometry of the L² Itô-Lévy integral) + **Theorem 4.2.4** (càdlàg modification);"
  - **Applebaum 2009 TOC** (verified via `D:\…\webfetch-…-zp8v81.pdf` p. ix–xi, the Cambridge frontmatter):
    - §4.1 Integrators and integrands (p. 214)
    - §4.2 Stochastic integration (p. 221) — *general* martingale-valued-measure framework
    - §4.3 Stochastic integrals based on Lévy processes (p. 229)
    - §4.4 Itô's formula (p. 243)
  - Applebaum's 2nd ed numbering convention: §4.2 covers his general martingale-valued-measure stochastic integral, which subsumes both Brownian and compensated-Poisson under one unified machinery. So "Theorem 4.2.3 = L²-isometry of the abstract integral" and "Theorem 4.2.4 = càdlàg modification" is structurally plausible. The 1st edition (CUP 2004) TOC `D:\…\webfetch-…-8bqcq2.pdf` shows the same chapter structure (§4.2 Stochastic integration at p. 197). I could not access the actual theorem body text in either edition.
- **Why this matters**: The citation is structurally consistent with Applebaum's section organization, so I have no evidence it is wrong. However, the docstring's claim that Thm 4.2.3 specifically covers the **compensated-Poisson** L² isometry (rather than the abstract martingale-valued-measure version) is unverified. The Lean axiom statement only asserts the compensated-Poisson special case, which would follow trivially from the general Applebaum Thm 4.2.3 — so no semantic error, but the specific theorem-number match should be confirmed.
- **Recommendation**: Verify the body text of Applebaum 2nd ed Theorems 4.2.3 and 4.2.4 against a library copy. The status is "plausible" not "verified". If verification is impossible, soften the citation to `Applebaum 2009 §4.2 (general martingale-valued-measure L²-Itô integral)`.

### Finding 10 — Applebaum 2009 "Theorem 4.4.7" for the Itô–Lévy formula is plausible and consistent with the chapter structure

- **Severity**: UNVERIFIABLE / VERIFIED-CONSISTENT
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Ito\JumpFormula.lean:23` and `:76-79`; `D:\LevyStochCalc\tools\cited_axioms.md:92`
- **Evidence**:
  - Lean docstring (`JumpFormula.lean:23`, `:76-79`):
    > "Applebaum 2009, Theorem 4.4.7."
    > "Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., Cambridge University Press, 2009, Theorem 4.4.7."
  - Applebaum 2nd ed §4.4 is titled "Itô's formula" (p. 243). The "Theorem 4.4.7" naming would be the 7th item in §4.4. This is the natural location for a jump-diffusion Itô-Lévy formula. Secondary literature (Gyöngy–Wu 2020 "On Itô formulas for jump processes" arXiv:2007.14782, p. 3) explicitly cites Applebaum for "basic results concerning stochastic integrals with respect to Poisson random measures and Poisson martingale measures" and uses an Itô-Lévy decomposition matching Lean's `drift + diff_mart + jump_mart + comp_drift` four-term structure. The Cont–Tankov 2003 "Proposition 8.18" co-citation is also a standard Itô-Lévy formula reference.
- **Why this matters**: Citation is structurally consistent. No verification defect found. This is the citation that withstood scrutiny best.
- **Recommendation**: None — except a sanity-check against a hardcopy of Applebaum at some point. The honest demotion of `itoLevyFormula` from theorem to axiom in the 2026-05-11 recursive audit, with the literature anchor preserved, is exactly the right pattern.

### Finding 11 — Tang–Li 1994 SIAM J. Control Optim. 32(5) "Theorem 3.1" citation is plausible but the paper's primary result is a maximum principle, with BSDEJ existence as an auxiliary tool — verify theorem number against primary source

- **Severity**: MEDIUM / UNVERIFIABLE
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:98-100`; `D:\LevyStochCalc\tools\cited_axioms.md:76`
- **Evidence**:
  - Lean docstring (`Existence.lean:98-100`):
    > "Tang, S. & Li, X. *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, Theorem 3.1"
  - **Paper exists**: confirmed via SIAM DOI 10.1137/S0363012992233858, vol. 32, pp. 1447–1475, 1994 (verified via WebSearch).
  - **Subject match**: Papapantoleon-Possamaï-Saplaouras 2018 "the whole nine yards" §1 (p. 2 of `D:\…\webfetch-…-9jyqet.pdf`):
    > "When one has more information on the filtration, it may be possible to specify the orthogonal martingale N in the definition of the solution. For instance, if the filtration is generated by a Brownian motion and an orthogonal Poisson random measure, one ends up with the so-called BSDEs with jumps, which were **introduced first by Tang and Li [136]**, followed notably by Buckdahn and Pardoux [38], …"
  - **Caveat**: Tang–Li 1994 is principally a **maximum principle** paper for optimal control of jump-diffusion systems; the BSDEJ existence/uniqueness is established as a tool inside the proof. Whether the specific "Theorem 3.1" of that paper is the BSDEJ existence statement (vs. the maximum principle) cannot be verified from the abstract; the paper is paywalled at SIAM.
- **Why this matters**: The paper exists and is the canonical reference for BSDEs with jumps. The risk is moderate: the cited Theorem 3.1 may actually be the maximum principle or a comparison lemma, with the BSDEJ existence being elsewhere (Lemma 2.3 or similar). A primary-source check would settle this.
- **Recommendation**: Verify against a SIAM-subscription library copy whether Tang–Li 1994 Theorem 3.1 is the BSDEJ existence/uniqueness statement. If it is actually a different lemma/theorem, fix the number. (The paper-level citation is sound.)

### Finding 12 — Applebaum 2009 "Theorem 2.3.1" for Poisson random measure existence is plausible; structural location matches but body text unverified

- **Severity**: UNVERIFIABLE / VERIFIED-CONSISTENT
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\RandomMeasure.lean:156-158`; `D:\LevyStochCalc\tools\cited_axioms.md:27`
- **Evidence**:
  - Lean docstring (`RandomMeasure.lean:156-158`):
    > "Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., Cambridge University Press 2009, Theorem 2.3.1; Kallenberg, O. *Random Measures, Theory and Applications*, Springer 2017, Proposition 3.6."
  - Applebaum 2nd ed §2.3 = "The jumps of a Lévy process – Poisson random measures" (p. 99 in 2nd ed TOC, p. 86 in 1st ed TOC). Theorem 2.3.1 (the 1st theorem of §2.3) is the natural location for the Poisson-random-measure existence statement.
  - The "Poisson recipe" in the Lean axiom docstring (Poisson-distributed count + uniform i.i.d. marks) matches the standard construction visible in Davar Khoshnevisan's UTah notes Theorem 2 (`D:\…\webfetch-…-4tjrbl.pdf`, also at math.utah.edu).
- **Why this matters**: Citation is structurally consistent. No verification defect found.
- **Recommendation**: None — but verify against hardcopy when convenient.

### Finding 13 — Karatzas–Shreve "Theorem 2.7.7" (Blumenthal) and "Theorem 2.7.9" (right-continuity) — structural location matches but body text unverified

- **Severity**: UNVERIFIABLE / VERIFIED-CONSISTENT
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Martingale.lean:903-904`; `D:\LevyStochCalc\tools\cited_axioms.md:41`
- **Evidence**:
  - K-S 2nd ed TOC (`D:\…\webfetch-…-0mscxe.pdf` p. xii) confirms **§2.7 Brownian Filtrations** with subsections **A. Right-continuity of the augmented filtration for a strong Markov process** (p. 90), **B. A "universal" filtration**, **C. The Blumenthal zero-one law** (p. 94).
  - K-S uses `<chapter>.<section>.<theorem-counter>` numbering. Theorem 2.7.7 and Theorem 2.7.9 being inside §2.7 is consistent with the TOC. (However, the docstring says **2.7.7 = Blumenthal** and **2.7.9 = right-continuity**, while the TOC structure has subsection A (right-continuity) appearing **before** subsection C (Blumenthal). So the numbering inside the section may run as `2.7.1, 2.7.2, … 2.7.6` (right-continuity stuff in subsection A) → `2.7.7, 2.7.8` (subsection B) → `2.7.9` (Blumenthal), in which case the docstring has 2.7.7 and 2.7.9 swapped semantically. UNVERIFIABLE without the book body.
- **Why this matters**: Possible swap of theorem numbers vs. theorem content. Low-impact citation defect but worth a hardcopy check.
- **Recommendation**: Verify the K-S 2.7.7 and 2.7.9 statements against a hardcopy. If 2.7.7 is right-continuity and 2.7.9 is Blumenthal (rather than the other way around as the docstring claims), swap.

### Finding 14 — Karatzas–Shreve "Theorem 2.2.8" for Kolmogorov-Chentsov modification is plausible (matches TOC; one secondary source confirmed "Theorem 2.8 (Kolmogorov-Chentsov)" in K-S excerpt)

- **Severity**: UNVERIFIABLE / VERIFIED-CONSISTENT
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Continuity.lean:193-195`; `D:\LevyStochCalc\tools\cited_axioms.md:34`
- **Evidence**:
  - K-S 2nd ed TOC §2.2.B is titled "The Kolmogorov-Čentsov theorem" (p. 53). Theorem 2.2.8 is consistent with this.
  - One WebFetch result (vdoc.pub excerpt of K-S, partial) mentioned "Theorem 2.8 (Kolmogorov-Chentsov)" which is the K-S internal short-form numbering (chapter 2, theorem 8 of that chapter). This supports the longer-form "Theorem 2.2.8".
  - Le Gall co-citation Thm 2.9 (Kolmogorov's lemma) verified directly in the Le Gall PDF (p. 24).
  - Revuz–Yor co-citation Theorem I.2.1 not verified (paywalled).
- **Why this matters**: Plausible. No defect found.
- **Recommendation**: None.

### Finding 15 — Applebaum 2009 "Lemma 4.2.2" (density of adapted simple predictable), "Lemma 4.2.5" (L²-isometry on simples), "Equation 4.3.1" — structural location matches but unverified

- **Severity**: UNVERIFIABLE / VERIFIED-CONSISTENT
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:2253-2256` (axiom #7) and `:2559-2561` (axiom #8); `D:\LevyStochCalc\tools\cited_axioms.md:62-63` and `:69`
- **Evidence**:
  - All three Applebaum references are placed in §4.2 (Stochastic integration) and §4.3 (Stochastic integrals based on Lévy processes), consistent with the chapter structure. Eq 4.3.1 being in §4.3 is the natural location for a Lévy-side isometry equation. Lemma 4.2.2 being in §4.2 (general martingale-valued-measure framework) is structurally plausible for "density of adapted simple predictable functions in L²".
  - Ikeda–Watanabe Lemma II.3.4 and Lemma II.3.3 co-citations not verified (paywalled).
- **Why this matters**: Plausible. No defect found.
- **Recommendation**: Verify against hardcopy when convenient.

## Per-claim verdicts on the 11 Tier 1 cited axioms

| Axiom (Tier 1 entry from `tools/cited_axioms.md`) | Verdict (citation lens) | One-line note |
|---|---|---|
| #1 `Brownian.BrownianMotion.exists` | **WEAK** | Le Gall Thm 2.1 fabricated (Defn 2.1 = pre-BM, BM is Defn 2.12 / Cor 2.11); K-S Thm 2.1.5 suspicious (§2.1 is the 2-page Introduction). |
| #2 `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | **EARNED** | Applebaum 2009 §2.3 Thm 2.3.1 is the natural location for PRM existence; Kallenberg Prop 3.6 is plausible. Body unverified but consistent. |
| #3 `Brownian.kolmogorovChentsov_modification` | **EARNED** | K-S §2.2.B is "The Kolmogorov-Čentsov theorem" (TOC verified); Le Gall Thm 2.9 (Kolmogorov's lemma) verified directly in PDF. |
| #4 `Brownian.brownian_martingale_rightCont` | **WEAK** | K-S 2.7.7/2.7.9 inside §2.7 "Brownian Filtrations" (TOC verified) but 2.7.7 vs 2.7.9 may be swapped; **Le Gall Prop 2.10 wrong — Lemma 2.10 is an analytic Hölder lemma, Blumenthal is Le Gall Thm 2.13**. |
| #5 `Brownian.itoIsometry_brownian_unified_existence` | **WEAK** | K-S Thm 3.2.6 inside §3.2 (TOC verified) but body unverified; **Le Gall Thm 5.13 wrong — Thm 5.13 is Dambis-Dubins-Schwarz; the L² isometry is Le Gall Thm 5.4 + eq 5.8**. |
| #6 `Poisson.itoIsometry_compensated_unified_existence` | **EARNED** | Applebaum §4.2 Thm 4.2.3 + 4.2.4 structurally consistent with the chapter (§4.2 = abstract martingale-valued-measure framework); body unverified but plausible. |
| #7 `Poisson.cauchySeq_simpleIntegralLp_compensated` | **EARNED** | Applebaum Eq 4.3.1 + Lemma 4.2.5 located in correct chapters (§4.3 Lévy stochastic integrals + §4.2 abstract framework); body unverified but plausible. |
| #8 `Poisson.adaptedSimple_dense_L2_compensated` | **EARNED** | Applebaum Lemma 4.2.2 located in §4.2 (consistent); body unverified but plausible. |
| #9 `BSDEJ.continuousBSDEJ_exists_unique` | **TRIVIAL** (citation-fabrication sense) | Tang–Li 1994 reference plausible (paper exists, subject matches) but Theorem 3.1 not directly verified; **Gnoatto 2025 "primer" reference does NOT EXIST** (no such Gnoatto paper in 2024–25); Pardoux–Răşcanu is a continuous-BSDE book — wrong for jump case. |
| #10 `BSDEJ.bsdej_path_regularity` | **TRIVIAL** (citation-fabrication sense) | **Bouchard–Elie–Touzi 2009 SPA 119(11) is wrong on EVERY component** (Touzi not an author; year 2008 not 2009; volume 118 not 119; issue 1 not 11); Pardoux–Răşcanu Theorem 5.42 "(continuous case)" admits its own scope mismatch. |
| #11 `Ito.itoLevyFormula` | **EARNED** | Applebaum 2009 §4.4 Thm 4.4.7 is the natural location for an Itô-Lévy formula (§4.4 = "Itô's formula"); Cont–Tankov 2003 Prop 8.18 is a standard co-reference. The honest demotion to axiom in 2026-05-11 (with this citation preserved) is exactly the right pattern. |

## Tools and sources used

- **Lean LSP tools called**: none (this is a pure citation audit; no Lean semantics needed beyond grepping for the docstring text and confirming the axiom statements in source files).
- **Read on source files**: `tools/cited_axioms.md` (full), `LevyStochCalc/Brownian/Construction.lean` (full), `LevyStochCalc/Brownian/Continuity.lean` (full), `LevyStochCalc/Brownian/Martingale.lean` (axiom region lines 880–967), `LevyStochCalc/Brownian/SimplePredictableRefine.lean` (axiom region lines 2055–2210), `LevyStochCalc/Poisson/RandomMeasure.lean` (full), `LevyStochCalc/Poisson/Compensated.lean` (axiom regions lines 2246–2350 and 2548–2770), `LevyStochCalc/Ito/JumpFormula.lean` (full), `LevyStochCalc/BSDEJ/Existence.lean` (full), `LevyStochCalc/BSDEJ/PathRegularity.lean` (full).
- **Grep on source files**: regex matches for `axiom\s+\w+`, `Theorem \d+`, `CITED AXIOM`, etc. across `LevyStochCalc/`.
- **Web searches** (15 distinct queries; selected list):
  - `"Karatzas Shreve" Theorem 2.1.5 Wiener measure existence`
  - `"Le Gall" Brownian "Theorem 2.1" Wiener measure pre-Brownian existence`
  - `"Le Gall" "Proposition 2.10" Blumenthal zero-one`
  - `"Applebaum" "Theorem 2.3.5" Poisson random measure construction existence`
  - `"Tang" "Li" "1994" SIAM "Necessary conditions for optimal control"`
  - `Bouchard Elie Touzi 2009 SPA "Discrete-time approximation" Forward-Backward jumps`
  - `"Bouchard" "Elie" "Touzi" Forward-Backward jumps SPA 2008 volume 118 authors`
  - `"Alessandro Gnoatto" 2025 "primer" BSDE jumps`
  - `"primer on backward stochastic differential equations" 2024 2025 jumps survey`
  - `"Pardoux" "Răşcanu" Springer 2014 chapter 5 BSDE jumps Levy`
- **Web fetches** (with PDF body extraction where possible):
  - Le Gall 2016 GTM 274 PDF (full ~2MB) — read Chapter 2 and Chapter 5 in detail; verified Defn 2.1, Prop 2.2, …, Thm 2.9, Lemma 2.10, Cor 2.11, Defn 2.12, Thm 2.13, Thm 5.4, Thm 5.10, Thm 5.12, Thm 5.13 directly.
  - Karatzas–Shreve 2nd ed Table of Contents PDF (full TOC, 0.5MB) — verified section structure of Ch. 2 (§2.1–2.11) and Ch. 3 (§3.1–3.9).
  - Applebaum 2nd ed CUP 2009 Frontmatter + TOC PDF — verified chapter structure and §4.2, §4.3, §4.4 titles.
  - Applebaum 1st ed CUP 2004 Frontmatter + TOC PDF — verified §4.2 / §4.3 / §4.4 titles match 2nd ed.
  - Bouchard's slides "Discrete time approximation of BSDEs" (LPMA Paris 6 + CREST) — verified Bouchard–Elie 2005 preprint reference is two-author.
  - Kharroubi–Lim 2018 "A decomposition approach for the discrete-time approximation of FBSDEs with a jump I" (arXiv:1103.3029v3) — verified "Bouchard and Elie [4]" citation (two-author).
  - DBLP page for Alessandro Gnoatto — verified 2024–2025 publication list has no "primer" paper.
  - Papapantoleon–Possamaï–Saplaouras 2018 "Existence and uniqueness results for BSDE with jumps: the whole nine yards" (arXiv:1607.04214) — confirmed Tang–Li 1994 as the canonical first BSDEJ reference.
  - Davar Khoshnevisan's UTah lecture notes Ch. 4 (Poisson Random Measures) — confirmed standard "Poisson recipe" construction.
- **Papers consulted** (primary sources where directly read):
  1. Le Gall, J.-F., *Brownian Motion, Martingales, and Stochastic Calculus*, Springer 2016 GTM 274 — read Ch. 2 and Ch. 5 directly.
  2. Karatzas, I. & Shreve, S., *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer 1991 — TOC only; body inaccessible.
  3. Applebaum, D., *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009 — frontmatter + TOC; body inaccessible.
  4. Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 118(1), 2008 — verified author list and bibliographic details from Bouchard's slides + Kharroubi-Lim 2018 references.
  5. Tang, S. & Li, X., *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994 — DOI 10.1137/S0363012992233858; abstract only.
  6. Papapantoleon–Possamaï–Saplaouras, *Existence and uniqueness results for BSDEs with jumps: the whole nine yards*, Electron. J. Probab. 23 (2018), no. 121 — read §1–2 directly.

## What you couldn't verify

- **Karatzas–Shreve 2nd ed body text** (paywalled / locked binary PDFs at all open mirrors): could only verify section structure from the TOC. Theorems 2.1.5, 2.2.8, 2.7.7, 2.7.9, 3.2.6 are all "consistent with TOC" but the exact body statements were not directly read. Findings 7, 13, 14 are MEDIUM/UNVERIFIABLE for this reason.
- **Applebaum 2nd ed body text** (paywalled): could only verify chapter structure from CUP frontmatter + Springer TOC. Theorems 2.3.1, 4.2.3, 4.2.4, 4.4.7 and Lemmas 4.2.2, 4.2.5 + Eq 4.3.1 are all "consistent with TOC" but bodies unverified. Findings 9, 10, 12, 15 are MEDIUM/UNVERIFIABLE for this reason.
- **Pardoux–Răşcanu 2014 body text** (paywalled at Springer; HAL preprint blocked by Anubis security): could only verify chapter structure ("Backward Stochastic Differential Equations" = Chapter 5, pp. 353–515). Whether Theorems 4.79 and 5.42 exist as numbered statements, and whether the book ever covers the jump case (likely not, given all secondary descriptions), is verified indirectly through the docstring's own "(continuous case)" parenthetical and through the publication's standing description.
- **Tang–Li 1994 body text** (SIAM paywall): could only verify the paper exists, has the cited title, and matches the cited bibliographic details (vol. 32, pp. 1447–1475, 1994). Whether the specific "Theorem 3.1" of that paper is the BSDEJ existence/uniqueness statement (vs. the maximum principle or a comparison lemma) is unverified.
- **Cont–Tankov 2003 Prop 8.18** (paywalled, not pursued in depth): co-citation for Itô-Lévy formula; not verified.
- **Revuz–Yor Thm I.2.1** (paywalled, not pursued): co-citation for K-C modification; not verified.
- **Kallenberg 2017 Prop 3.6** (paywalled): co-citation for PRM existence; not verified.
- **Ikeda–Watanabe Lemmas II.3.3 / II.3.4 / §II.3** (paywalled): co-citations for compensated-Poisson; not verified.

## Recommendations for the project (≤ 5 bullets)

- **Fix Finding 1 (Bouchard–Elie–Touzi)** as the highest-priority citation correction: change every occurrence of "Bouchard, B. & Elie, R. & Touzi, N. … SPA 119(11), 2009" to the correct **"Bouchard, B. & Elie, R. … SPA 118(1), 2008, pp. 53–75"**. The merged-with-Bouchard–Touzi-2004 hallucination is the most damaging single citation defect in `cited_axioms.md`.
- **Delete the Gnoatto 2025 "primer" reference** (Finding 2) outright — it does not exist. If a modern survey reference is desired alongside Tang–Li 1994, use **Papapantoleon–Possamaï–Saplaouras 2018 EJP "the whole nine yards"** (arXiv:1607.04214) as the verified alternative.
- **Fix the Le Gall theorem numbers in axioms #1, #4, #5** (Findings 3, 4, 6): Le Gall Thm 5.13 → **Le Gall Thm 5.4 + eq. (5.8)**; Le Gall Prop 2.10 → **Le Gall Thm 2.13** (Blumenthal); Le Gall Thm 2.1 → **Le Gall Cor 2.11 + Defn 2.12** (BM existence via Kolmogorov modification of pre-BM). These are clean drop-in replacements with no semantic change to the axiom statements.
- **Remove the Pardoux–Răşcanu citation from BSDEJ axioms #9 and #10** (Findings 5, 8): the book is a continuous-BSDE reference and does not cover the jump case. The docstring's own "(continuous case)" parenthetical in axiom #10 admits this. Keep Tang–Li 1994 (with corrected theorem number once verified against the paper) as the primary jump-case reference; add Papapantoleon–Possamaï–Saplaouras 2018 as a verified modern co-reference.
- **Verify the K-S and Applebaum body theorem numbers against a hardcopy** at the next available opportunity. The audit found the section structure consistent with the TOC for all K-S / Applebaum citations, but cannot rule out internal theorem-number-within-section errors. Findings 7, 9, 10, 11, 12, 13, 14, 15 should all become EARNED once the body text is sighted; without that check, they remain UNVERIFIABLE / VERIFIED-CONSISTENT.
