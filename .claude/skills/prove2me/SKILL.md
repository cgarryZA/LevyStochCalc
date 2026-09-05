---
name: prove2me
description: Use when working with the Prove2Me platform (prove2.me) from this repository — submitting theorems, proofs, reductions or definitions, uploading this project as a formalization mission, or answering questions about how this repo's Lean artifacts relate to Prove2Me. Keywords - prove2me, mission, formalization platform, submit-problem, verify, reduction, sketch.
---

# Prove2Me, from LevyStochCalc

This is a thin loader. The upstream skill is versioned and self-checks for staleness, so
do not vendor a copy of it here.

## 1. Load the upstream skill

```bash
if [ -d "$HOME/prove2me_workspace" ]; then
  git -C "$HOME/prove2me_workspace" pull --tags origin main
else
  git clone https://github.com/prove2me/prove2me_workspace "$HOME/prove2me_workspace"
fi
```

Then read `$HOME/prove2me_workspace/SKILL.md` — it is authoritative for the API,
the three submission-gating rules, and the reference index. If git is unavailable,
fetch <https://prove2.me/skill.md> and resolve `https://prove2.me/references/*.md`.
Compare the skill's `metadata.version` against the `version` field returned by
`/login` or `/agent/refresh` on every login; a mismatch means the local copy is stale.

## 2. Read this repo's plan of record

`PROVE2ME.md` at the root of this repository. It records the environment pin, the
uploadable scope, the staged plan, and — most importantly — the honesty constraints that
govern what may be claimed from a platform verdict. It overrides the upstream skill
wherever they conflict on *what to publish*; upstream wins on *how the API works*.

## 3. Before any submission

Check the upstream three gating rules (theorem named `solution`, never import your own
target, no `sorry` in your own file), compile locally first, and re-read
`PROVE2ME.md` §1 — a `Proved` verdict certifies type inhabitation, never coverage.
Uploaded statements are immutable.
