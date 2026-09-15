/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry

Generates the fully-qualified names of every LevyStochCalc public-API declaration that
`_audit.lean` should cover (GOAL.md §1.A): every theorem, definition, opaque or instance whose
home module lies under `LevyStochCalc.*` (the library itself, not Mathlib and not the two
upstream packages BrownianMotion/MathFin), excluding axioms (none are expected), inductives,
constructors, recursors, quotient info, structure projections, and compiler-generated
auxiliary/internal/private names. Prints one fully-qualified name per line, sorted.

Run via:  lake env lean tools/gen_audit_names.lean > /path/to/all_names.txt
-/

import LevyStochCalc

open Lean

namespace GenAuditNames

/-- `n` is the module of a declaration belonging to the LevyStochCalc library proper (as opposed
to Mathlib or the upstream `BrownianMotion` / `MathFin` packages, whose modules do not start with
`LevyStochCalc.`). -/
def isLibModule (n : Name) : Bool :=
  let s := n.toString
  s == "LevyStochCalc" || s.startsWith "LevyStochCalc."

/-- The `ModuleIdx`s (as raw `Nat`s) of every currently-loaded module belonging to the
LevyStochCalc library proper. Computed once over the (short) module list rather than once per
constant, since `env.constants` has ~10³ constants for every module. -/
def libModuleIdxs (env : Environment) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  for h : i in [0:env.header.moduleNames.size] do
    if isLibModule env.header.moduleNames[i] then
      s := s.insert i
  return s

/-- `comp` is exactly `pfx` followed by one or more digits (e.g. `match_1`, `proof_12`, `eq_3`),
the equation-compiler / well-founded-recursion auxiliary naming convention — as opposed to a
genuine identifier that merely starts with the same letters (e.g. `eq_comm`). -/
def isNumberedAux (pfx : String) (comp : String) : Bool :=
  comp.startsWith pfx &&
  (let rest := comp.toList.drop pfx.length
   rest.length > 0 && rest.all Char.isDigit)

/-- `comp` is one dotted component of a compiler-generated auxiliary declaration: an equation
lemma, a `match`/well-founded-recursion proof obligation, or a structural-recursion / injectivity
/ no-confusion / `sizeOf` helper that the equation/structure compiler emits alongside a genuine
`def`/`theorem`. -/
def isAuxComponent (comp : String) : Bool :=
  comp == "noConfusion" || comp == "noConfusionType" ||
  comp == "sizeOf" || comp.startsWith "sizeOf_" ||
  comp == "injEq" || comp == "inj" ||
  comp == "rec" || comp == "casesOn" || comp == "brecOn" ||
  comp == "below" || comp == "binductionOn" || comp == "ibelow" ||
  comp == "mk" ||
  comp == "eq_def" || comp == "eq_unfold" ||
  isNumberedAux "match_" comp || isNumberedAux "proof_" comp || isNumberedAux "eq_" comp

/-- `s` (the `toString` of some name) has some dotted component that marks it as a
compiler-generated auxiliary declaration (see `isAuxComponent`). -/
def isAuxNameStr (s : String) : Bool :=
  (s.splitOn ".").any isAuxComponent

/-- `info` is a theorem, definition, or opaque (this subsumes user-written `instance`s, which are
elaborated as `def`s tagged in the instance extension; axioms are skipped — none are expected in
this library — as are inductives, constructors, recursors, and quotient formers). -/
def isAuditableKind : ConstantInfo → Bool
  | .thmInfo _ | .defnInfo _ | .opaqueInfo _ => true
  | .axiomInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => false

/-- Should `n` (with info `info`) be part of the public-API audit set, given the precomputed set
of LevyStochCalc module indices? Cheap checks (`isAuditableKind`, the module-index membership
test) come first so the `Name.toString`-based checks only run on candidates that already passed. -/
def shouldInclude (env : Environment) (libMods : Std.HashSet Nat) (n : Name) (info : ConstantInfo)
    (idx : Nat) : Bool :=
  isAuditableKind info &&
  libMods.contains idx &&
  !n.isInternal &&
  !Lean.isPrivateName n &&
  !env.isProjectionFn n

/-- The sorted, deduplicated (deduplication is automatic: `env.constants` is a map) array of
fully-qualified names to audit. -/
def auditNames (env : Environment) : Array String := Id.run do
  let libMods := libModuleIdxs env
  let mut names : Array String := #[]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if shouldInclude env libMods n info idx.toNat then
        let s := n.toString
        if !isAuxNameStr s then
          names := names.push s
  return names.qsort

#eval show MetaM Unit from do
  let env ← getEnv
  for s in auditNames env do
    IO.println s

end GenAuditNames
