import Mertens
import Lean.Util.CollectAxioms

/-! Audits all public project theorems visible through the umbrella import,
including proved auxiliary lemmas. Source hypotheses appear in the printed
types, separately from logical axioms. -/
open Lean in
run_cmd do
  let env ← getEnv
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names := #[]
  for (name, info) in env.constants.toList do
    if `Mertens |>.isPrefixOf name then
      match info with
      | .axiomInfo _ => throwError "Unexpected project axiom: {name}"
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  let scan := names.forM Lean.CollectAxioms.collect
  let (_, result) := (scan.run env).run {}
  for ax in result.axioms do
    unless permitted.contains ax do throwError "Unexpected proof dependency: {ax}"
  logInfo m!"Audited {names.size} public Mertens theorems. Logical axioms: {result.axioms}."

#print Mertens.SourceInputs
#check Mertens.johnston_from_sources
#print axioms Mertens.Input.kernel_mass
#print axioms Mertens.Budget.upperBound_lt
#print axioms Mertens.johnston_from_sources

#print axioms Mertens.error_two_gt_half
#print axioms Mertens.error_left_limit
#print axioms Mertens.error_jump_97
