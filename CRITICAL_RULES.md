# CRITICAL RULES — check before EVERY action in this repo

This file is the user's standing constraints. Re-read on every prompt
before doing ANY edit, commit, or analysis on this repo or sister repos.

## Rule 0 (overrides everything else)

**NEVER weaken a claim to match content. ALWAYS strengthen content to
match the statement, name, or claim.**

Concretely:
- If a theorem named `jacodYor_representation` has a trivial-witness
  proof body, the fix is NOT to rename it (`centered_decomposition`),
  NOT to weaken the statement, and NOT to delete it. The fix is to
  prove the real Jacod-Yor martingale representation.
- If a theorem named `exists_unique` proves only `Nonempty`, the fix is
  NOT to rename it `exists`. The fix is to also prove uniqueness.
- If `IsBSDEJSolution` is satisfiable by Y=0 because adaptedness is
  missing, the fix is NOT to weaken the axiom claim. The fix is to add
  adaptedness so the literature Tang-Li claim is honest.
- If `JumpDiffusion`'s `is_solution : True` field doesn't enforce the
  SDE equation, the fix is NOT to remove the field. The fix is to
  replace `True` with the actual SDE integral equation.

## Rule 1 — no new axioms

Do NOT add new `axiom` declarations to "honestly acknowledge" a defect.
Demoting a trivial-witness theorem to a documented axiom counts as a
new axiom. Don't do that. The existing Tier 1 cited axioms
(`BrownianMotion.exists`, `PoissonRandomMeasure.exists_of_sigmaFinite`,
the unified-existence axioms, the BSDEJ axioms) remain — they were
established in prior sessions and the user accepted them. New axioms
require explicit user approval.

## Rule 2 — no trivial-witness theorems

A theorem whose proof body discharges an existential with a vacuous
witness (`⟨0, 0, 0, change⟩`, `is_solution := trivial`, etc.) is
forbidden. The fix is per Rule 0: strengthen the proof, not soften the
claim.

## Rule 3 — no `sorryAx` in load-bearing public theorems

The lint baseline (`tools/sorry_baseline.txt`) must remain at or below
its current size. If a real proof can't be completed in this session,
the work must still progress (e.g., factor out lemmas) — don't park a
`sorry` in a load-bearing theorem and call it done.

## Conflict resolution

Rule 0 dominates Rules 1, 2, 3. If you cannot satisfy Rule 0 without
violating one of the others, STOP and ask the user. Do not silently
choose the weakest path.

## Specific items currently in violation (red-team findings, 2026-05-20)

Items that this rule says I must STRENGTHEN, not weaken:

| Item | Current state | Rule-0 fix |
|---|---|---|
| `Ito.Setting.JumpDiffusion.exists_unique` | trivial-witness theorem (constant path `X t ω = x₀`, `is_solution := trivial`) | Prove Applebaum 2009 Thm 6.2.9: real Picard iteration for the jump-diffusion SDE under Lipschitz `(μ, σ, γ)`. Requires multidim Brownian + compensated-Poisson stochastic integrals along `X`. Also strengthen `is_solution` field from `True` to the actual SDE integral equation. |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` | trivial-witness theorem (`⟨0, 0, 0, ξ−𝔼[ξ]⟩; ring`) | Prove Jacod 1976 / Jacod-Shiryaev Thm III.4.34: predictable representation of L² martingales on the `(W, N)` filtration. Pin `BM_integral` to `∫Z·dW` and `jump_integral` to `∫∫U Ñ`. Requires both stochastic integral primitives. |
| `Ito.JumpFormula.itoLevyFormula` (currently axiom) | axiom statement is itself a trivial-witness shape: `∃ four reals summing to change` admits `⟨change, 0, 0, 0⟩` | Prove Applebaum 2009 Thm 4.4.7: the Itô-with-jumps formula. Pin each of the four terms to its literature integral form (Lévy generator integral, Brownian Itô integral, compensated-Poisson integral, compensator drift). |

These are multi-session pieces of work. Progress must be made by
building real primitives, not by demoting/weakening.

## Process

On every prompt:
1. Re-read this file.
2. Before any edit: ask "does this STRENGTHEN content to match claim?"
3. If the edit weakens / renames / demotes / deletes a claim — STOP.
