module

public meta import Lean

/-!
# The fully specified retained-source application

Construct only the final application of the already checked source producer.
All arguments are existing terms proved in the ordinary source proof. Avoid
repeated dependent argument inference for the cached witnesses; Lean's kernel
checks the resulting term as part of the enclosing theorem. No axiom, new
witness, new hypothesis or analytic claim is generated.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.LeadingSourceTemplate
open Lean Meta Elab Tactic

/-- Close the exact source join with the SAME local producer and its 23 proved
arguments (`app:ch_response:eq:response-graded-source`). -/
elab "close_cached_leading_source_application " source:ident " [" args:term,* "]" : tactic =>
  withMainContext do
    unless args.getElems.size == 23 do
      throwError "cached leading source: expected exactly 23 arguments"
    let producer ← Term.elabTerm source none
    let inputs ← args.getElems.mapM fun stx ↦ Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars (mkAppN producer inputs)
    if proof.hasMVar then throwError "cached leading source: unresolved argument metavariable"
    (← getMainGoal).assign proof
    replaceMainGoal []

end JanetCartan.PhysicalPrimary.LeadingSourceTemplate
