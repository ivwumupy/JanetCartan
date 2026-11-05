module
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalizedTargetProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Actual selected target's true physical R profile

The SAME normalizedTarget52 has all physical tensor cNorm bounds. The order-only
coefficient depends only on the original dimension/domain, hence precedes the
smoothing order and history. Its one extra input is the honest CURRENT-stage
finite-moment frequency threshold, not tensor success or an initial Tref change.
Consumer: actual completed-mean/Schwartz physical profiles (`main:prop:mean`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedNormalizedTargetProfiles
open Lean Meta Elab Command
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)

run_elab do
  withActualSelectedFields fun p f _ _ _ => do
    withTransparency .default do
      let selected := p[:52].toArray
      let u ← OriginalSelectedMeanRegularity.targetArguments selected
      unless f[4]!.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
        throwError "actual physical target: literal original normalizedSource10 changed"
      let R := f[4]!.getAppArgs[4]!
      let profileRoot := `JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles
      let cost := app (profileRoot ++ `Ctarget) #[u[0]!,u[1]!]
      for later in selected[33:] do
        if (cost.find? (· == later)).isSome then
          throwError "actual physical target: coefficient depends on a later history or smoothing input"
      let S := app (profileRoot ++ `Starget) #[u[0]!,u[1]!,u[13]!,u[14]!]
      let gate ← termWith [(`S,S),(`R,R)] "S ≤ R"
      withLocalDeclNoLocalInstanceUpdate `hPhysicalTargetFrequency .default gate fun hR => do
        let kType ← termWith [(`n,u[0]!)] "Set (JanetCartan.Euclidean n)"
        withLocalDeclNoLocalInstanceUpdate `K .default kType fun K => do
          withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
            let proof := app (profileRoot ++ `normalized_target_profile)
              #[u[0]!,u[7]!,u[1]!,u[2]!,R,u[13]!,u[14]!,u[15]!,u[16]!,u[17]!,
                u[18]!,u[8]!,u[20]!,hR,K,q]
            let proofType ← inferType proof
            let some rawTarget := proofType.find? (·.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10)
              | throwError "actual physical target: source producer lost its literal normalized tensor"
            let named := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget selected
            let target := proofType.replace fun e => if e == rawTarget then some named else none
            let params := selected ++ #[hR,K,q]
            let type ← instantiateMVars (← mkForallFVars params target)
            let value ← instantiateMVars (← mkLambdaFVars params proof)
            let env ← getEnv
            for e in #[type,value] do
              let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
              unless missing.isEmpty do throwError "actual physical target: missing {missing.toList}"
              if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
                throwError "actual physical target: unresolved or extra analytic input"
            let (type,value) := Lean.ShareCommon.shareCommon (type,value)
            let name := `JanetCartan.PhysicalMean.OriginalSelectedMeanData.normalizedTarget_cNorm_profile
            addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
            addDocStringCore name "The literal original normalizedTarget52 has cNorm K q ≤ Ctarget(n,originalD,q)*Rj^q at every physical order and set. The coefficient precedes all history and approximation inputs; only the genuine CURRENT-stage finite-moment frequency is numerical. No measured-tensor inversion or target-profile hypothesis (main:prop:mean)."
            logInfo "actual normalized target physical profile55: true R, prehistory/m-uniform tensor budget, one current-stage numeric gate"
end JanetCartan.PhysicalMean.OriginalSelectedNormalizedTargetProfiles
end
