module

public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairEstimatesTemplate
public import JanetCartan.Iteration.PhysicalPairs.FractionalSize

/-!
# Final costs and real orders for the actual signed correction

The consumer is `RevisedStage.increment_estimates_of_physicalSobolev_profiles`
in `main:thm:step`. The integer estimates already concern the actual complete
full-source correction. Their chosen constants are nonnegative by their
original producers. The existing Fourier split at the same carrier gives the
literal exponent `r + 1` at every real order, with only the sum of the two
original integer costs and no additional threshold (`main:eq:pair-high-size`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairProfilesTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPairs.OriginalSelectedPairProfiles
private def estimates := `JanetCartan.PhysicalPairs.OriginalSelectedPairEstimates
private def selection := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def uniformSize := `JanetCartan.PhysicalPairs.OriginalUniformStageSize
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  let ci ← getConstInfo key
  let some value := ci.value? (allowOpaque := true)
    | throwError "actual signed profiles: missing checked original body {key}"
  return (value.beta p).headBeta

private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "actual signed profiles: unresolved or additional analytic input {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual signed profiles: missing original producer {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual signed profile {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original complete-source signed correction: the genuine prehistory costs are nonnegative and the physical Fourier split preserves the exact real-order carrier exponent. Same original full Picard source, sample, correction and initial size threshold; no new analytic premise or threshold (main:eq:pair-high-size; main:thm:step)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual signed profiles: nonstandard axioms {name}: {axioms}"
  logInfo m!"Actual original signed profile {key}/{p.size}: {axioms}"

elab "derive_original_selected_pair_profile " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "actual signed profiles: unknown mode"
  if mode.getNat < 2 then
    let key := if mode.getNat == 0 then `Clag else `Csize
    forallTelescope (← getConstInfo (estimates ++ key)).type fun p result => do
      unless result.isConstOf ``Real && p.size == (if mode.getNat == 0 then 36 else 37) do
        throwError "actual signed profiles: original static cost telescope changed {key}"
      let raw ← body (estimates ++ key) p
      let proof ← if mode.getNat == 0 then do
        unless raw.isAppOfArity `JanetCartan.PhysicalPairs.OriginalUniformStageLag.constant 40 do
          throwError "actual signed profiles: lag cost no longer uses its original producer"
        pure (app `JanetCartan.PhysicalPairs.OriginalUniformStageLag.constant_nonneg raw.getAppArgs)
      else do
        unless raw.isAppOfArity (uniformSize ++ `constant) 41 do
          throwError "actual signed profiles: size cost no longer uses its original producer"
        let priced ← body (uniformSize ++ `constant) raw.getAppArgs
        unless priced.isAppOfArity `JanetCartan.PhysicalPairs.OriginalStageSize.cost 2 do
          throwError "actual signed profiles: original size cost factorization changed"
        let a := priced.getAppArgs
        let hD := mkApp (app (selection ++ `D_nonneg) raw.getAppArgs[:40].toArray)
          raw.getAppArgs[40]!
        pure (app `JanetCartan.PhysicalPairs.OriginalStageSize.cost_nonneg #[a[0]!,a[1]!,hD])
      let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,app (estimates ++ key) p]
      save (if mode.getNat == 0 then `Clag_nonneg else `Csize_nonneg) p proof target
    return
  let integer := estimates ++ `size
  forallBoundedTelescope (← getConstInfo integer).type (some 59) fun p rest => do
    unless p.size == 59 && rest.isForall && rest.bindingDomain!.isConstOf ``Nat do
      throwError "actual signed profiles: unchanged integer size59 prefix missing"
    let bound ← instantiateForall rest #[mkNatLit 0]
    let some S := bound.find? (·.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction 55)
      | throwError "actual signed profiles: lost SAME actual signed correction55"
    let some cost0 := bound.find? (·.isAppOfArity (estimates ++ `Csize) 37)
      | throwError "actual signed profiles: original static integer price missing"
    let fixed := cost0.getAppArgs[:36].toArray
    unless fixed == p[:33].toArray ++ #[p[53]!,p[54]!,p[56]!] do
      throwError "actual signed profiles: history, target or current scale entered the cost"
    let D := app (estimates ++ `Csize) fixed
    let raw ← body (estimates ++ `Csize) cost0.getAppArgs
    unless raw.isAppOfArity (uniformSize ++ `constant) 41 do
      throwError "actual signed profiles: original size producer disappeared"
    let early := raw.getAppArgs[:38].toArray
    let initial := app (estimates ++ `sizeThreshold) (p[:33].toArray ++ #[p[54]!,p[56]!])
    let hR := app `JanetCartan.PhysicalPairs.OriginalStageSize.stage_one
      #[initial,p[33]!,app (selection ++ `early_hS) early,p[57]!,p[35]!]
    let R := (← inferType hR).appArg!
    let natural ← withLocalDeclNoLocalInstanceUpdate `order .default (mkConst ``Nat) fun k =>
      mkLambdaFVars #[k] (app integer (p.push k))
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let A := app `JanetCartan.RevisedScales.forcingExponent #[n]
    let proof := app ``JanetCartan.PhysicalPairs.FractionalSize.all_real
      #[n,N,S,D,p[58]!,R,A,hR,natural]
    save `real_size p proof (← inferType proof)

end JanetCartan.PhysicalPairs.OriginalSelectedPairProfilesTemplate
end
