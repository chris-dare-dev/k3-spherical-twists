/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists
import Lean.Elab.Command

/-!
Invariant: no constant of any `K3Twists` module depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. That rules out `sorry` (`sorryAx`), a declared `axiom` and
`native_decide` (`Lean.ofReduceBool`). Geometric inputs that Mathlib cannot prove yet are
hypotheses (fields of structures named `…Hypotheses`), never axioms, so they pass.

Run from `src/lean`: `lake env lean scripts/AxiomAudit.lean`. It fails with one line per
offending constant.

It reads the compiled environment, so no syntax can hide a `sorry` from it, and every constant
counts: private, auto-generated and instance declarations included. The umbrella `K3Twists`
imports every module of the library (`lake exe mk_all --lib K3Twists --check` keeps it so), and
an empty audit fails too. Declarations are selected by module, not by name, because they live in
Mathlib's namespaces. Adapted from the axiom audit of derived-alg-geo-lean.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules : Nat := 0
  let mut constants : Nat := 0
  let mut offending : Array MessageData := #[]
  for i in [0:env.header.moduleNames.size] do
    unless (`K3Twists).isPrefixOf env.header.moduleNames[i]! do continue
    modules := modules + 1
    for c in env.header.moduleData[i]!.constNames do
      constants := constants + 1
      let extra := (← collectAxioms c).filter (!allowed.contains ·)
      unless extra.isEmpty do
        offending := offending.push m!"{c} depends on {extra}"
  if constants == 0 then
    throwError "no constant of a K3Twists module is in the environment"
  unless offending.isEmpty do
    throwError m!"{offending.size} constants depend on an axiom outside propext, \
      Classical.choice and Quot.sound:\n{MessageData.joinSep offending.toList "\n"}"
  logInfo m!"{constants} constants in {modules} modules depend only on propext, \
    Classical.choice and Quot.sound"
