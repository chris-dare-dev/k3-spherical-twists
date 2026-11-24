import K3Twists

/-!
# Axiom audit

Every declaration in the `K3Twists` namespace depends on no axioms beyond Lean's three standard
ones (`propext`, `Classical.choice`, `Quot.sound`): there is no `sorry` and no added axiom. The
geometric inputs of the point-mass corollary are hypotheses (fields of `PointMassInputs`), not
axioms, so they do not appear here.

Run from `src/lean`: `lake env lean ../../tests/lean/AxiomAudit.lean`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if (`K3Twists).isPrefixOf n && !n.isInternal then
      checked := checked + 1
      for a in (← collectAxioms n) do
        unless allowed.contains a do
          bad := bad.push (n, a)
  unless bad.isEmpty do
    throwError m!"declarations with axioms beyond propext, Classical.choice, Quot.sound: {bad}"
  if checked == 0 then
    throwError "no declarations found in the K3Twists namespace"
  logInfo m!"{checked} declarations in K3Twists use no axioms beyond propext, Classical.choice \
    and Quot.sound"
