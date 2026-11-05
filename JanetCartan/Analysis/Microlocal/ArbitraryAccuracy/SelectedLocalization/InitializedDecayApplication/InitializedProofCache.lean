module

public meta import Lean

/-!
# Inferring an applied producer's theorem type

This command elaborates a proof term, infers its exact type, and adds an ordinary
kernel-checked theorem. It avoids re-elaborating a separately restated large
continuation. All binders must be explicit; there are no axioms or admissions.
-/

public meta section
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization.InitializedProofCache
open Lean Meta Elab Command

syntax "proof_from " ident bracketedBinder* " := " term : command

elab_rules : command
  | `(proof_from $name:ident $binders:bracketedBinder* := $value:term) => do
    let declarationName := (← getCurrNamespace) ++ name.getId
    liftTermElabM do
      Term.elabBinders binders fun params => do
        let proof ← Term.elabTerm value none
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        let type ← instantiateMVars (← inferType proof)
        let declarationType ← instantiateMVars (← mkForallFVars params type)
        let declarationValue ← instantiateMVars (← mkLambdaFVars params proof)
        if declarationValue.hasMVar || declarationType.hasMVar then
          throwError "producer application has unresolved metavariables"
        addDecl (.thmDecl {
          name := declarationName, levelParams := [],
          type := declarationType,
          value := declarationValue }) (forceExpose := true)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization.InitializedProofCache
