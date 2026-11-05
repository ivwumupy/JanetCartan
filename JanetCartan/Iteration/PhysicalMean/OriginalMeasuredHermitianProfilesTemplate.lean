module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredHermitianProfiles
public import JanetCartan.Iteration.PhysicalMean.CanonicalForcingProfiles
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
public meta import Lean

/-!
# The same coefficient geometry for the actual measured Hermitian field

Consumers: the full physical mean kernel in `app:ch_mean_pairs:eq:comparison-input`
and its uncontracted annular realization in `app:ch_mean_pairs:defn:mean-canonical`.
The cutoff and working domains below are projections of the already selected
original mean continuation. No second cutoff, physical output recut, or choice
of a mean-comparison radius is made. The geometry has only the original22 and
its retained row as inputs, before the source scale or any history.

The separate Sampling leaf provides the exact cut matrix amplitude. Its
response assumptions must be discharged by the actual original graded event;
these geometric getters alone do not claim that analytic conclusion.
-/

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfilesTemplate
open Lean Meta Elab Command
open PhysicalSampling.OriginalMeasuredKernelsApplication (withRow)

private def ns := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles

private def nativeTelescope (type : Expr) (count : Nat)
    (k : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  go count type #[]
where
  go : Nat → Expr → Array Expr → MetaM Unit
    | 0, result, xs => k xs result
    | remaining + 1, type, xs => do
      let .forallE name domain body bi := type.consumeMData
        | throwError "actual measured Hermitian: native telescope ended at {xs.size}"
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => go remaining (body.instantiate1 x) (xs.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
          go remaining (body.instantiate1 x) (xs.push x)

private def save (short : Name) (params : Array Expr) (term : Expr)
    (data := false) : MetaM Expr := do
  let env ← getEnv
  let missing := term.getUsedConstants.filter (fun n ↦ (env.find? n).isNone)
  unless missing.isEmpty do
    throwError "actual measured Hermitian field: import all these producers before publishing {short}: {missing}"
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let missingType := type.getUsedConstants.filter (fun n ↦ (env.find? n).isNone)
  unless missingType.isEmpty do
    throwError "actual measured Hermitian field: missing imported type dependencies in {short}: {missingType}"
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "actual measured Hermitian field: unresolved or non-static input in {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  addDocStringCore name "The literal SAME original measured-row construction. Geometry and budgets retain their declared prehistory inputs; actual-stage amplitude fields use the original graded response and no response-success assumption (app:ch_mean_pairs:eq:comparison-input)."
  logInfo m!"checked SAME original measured Hermitian field {short} at {params.size} inputs"
  return mkAppN (mkConst name) params

/-- Retain the original geometry directly from its prehistory mean37 spine.
Every transaction closes over only the original22 and its actual retained row. -/
elab "retain_actual_mean_coefficient_geometry " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let info ← getConstInfo `JanetCartan.PhysicalSampling.OriginalMeasuredMean.initialized
  let some body := info.value? (allowOpaque := true)
    | throwError "actual measured Hermitian field: original static mean unavailable"
  nativeTelescope info.type 37 fun fixed _ => do
   let initialized := (body.beta fixed).headBeta
   unless initialized.isAppOfArity `JanetCartan.PhysicalSampling.OriginalChoices.Mean.continuation 62 do
     throwError "actual measured Hermitian field: original static mean62 changed"
   let init := initialized.getAppArgs
   let p := fixed[:22].toArray.push fixed[32]!
   unless p.size == 23 && init.size == 62 do
     throwError "actual measured Hermitian field: original geometry23/mean62 changed"
   let fields : Array (Name × Nat × Bool) := #[
     (`workingCompact, 28, true), (`workingDomain, 29, true),
     (`workingCompact_isCompact, 30, false), (`workingDomain_isOpen, 31, false),
     (`workingCompact_subset_workingDomain, 32, false),
     (`coefficientCutoff, 33, true), (`coefficientCutoff_contDiff, 34, false),
     (`coefficientCutoff_tsupport_subset, 36, false)]
   let j := which.getNat
   if h : j < fields.size then
     let (name, index, data) := fields[j]
     discard <| save name p init[index]! data
   else if j == 8 then
     let hκΩ ← mkAppM `Set.Subset.trans #[init[36]!, init[32]!]
     discard <| save `coefficientCutoff_tsupport_in_workingDomain p hκΩ
   else if j == 9 then
     discard <| save `coefficientCutoff_hasCompactSupport p init[35]!
   else
     throwError "actual measured Hermitian field: unknown coefficient geometry field"

private def bodyAt (name : Name) (args : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "actual measured Hermitian field: missing saved body {name}"
  return (body.beta args).headBeta

private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)

/-- Read only the saved actual event's result and its literal measured family.
There is no second event, density, kernel choice or reconstruction of thresholds. -/
private def withActualRow
    (next : Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let event := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.exists_on_original_history
  nativeTelescope (← getConstInfo event).type 50 fun args result => do
    unless args.size == 50 && result.isAppOfArity ``Exists 2 do
      throwError "actual measured Hermitian field: original graded event50 changed"
    let name := `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel
    let some family := result.find? (·.isAppOfArity name 60)
      | throwError "actual measured Hermitian field: same measured family60 absent"
    let joined := family.getAppArgs
    let body ← bodyAt name joined
    unless body.isLambda do
      throwError "actual measured Hermitian field: original measured family is not a row lambda"
    withLocalDeclNoLocalInstanceUpdate `i .default body.bindingDomain! fun i => do
      let row := (body.beta #[i]).headBeta
      unless row.isAppOfArity `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel 64 do
        throwError "actual measured Hermitian field: original Row.kernel64 changed"
      next args joined row.getAppArgs i

/-- Discharge the earlier cut-amplitude leaf's analytic inputs with the SAME
actual original response and rates. Budgets precede R and history; the remaining
fields have only the actual50 and row, not response-success assumptions. -/
elab "construct_actual_mean_cut_amplitude " which:num : command =>
    liftTermElabM <| withTransparency .reducible <| withActualRow fun args joined row i => do
  let input := `JanetCartan.PhysicalSampling.OriginalMeasuredHermitianProfiles
  let params := args.push i
  match which.getNat with
  | 0 =>
    discard <| save `cutAmplitudeBudget (args[:44].toArray.push i)
      (app (input ++ `cutAmplitudeBudget) row[:45].toArray) true
  | 4 =>
    discard <| save `cutAmplitudeBudget_nonneg (args[:44].toArray.push i)
      (app (input ++ `cutAmplitudeBudget_nonneg) row[:45].toArray)
  | 1 =>
    discard <| save `cutAmplitude params
      (app (input ++ `cutAmplitude) (row[:60].toArray.push row[61]!)) true
  | 2 =>
    let rates := app `JanetCartan.PhysicalSampling.OriginalCommonStage.stage_rates
      (joined[:46].toArray ++ #[joined[47]!, joined[48]!, joined[49]!])
    let rowRates := mkApp (tail rates 6) i
    let unit ← forallBoundedTelescope (← inferType rowRates) (some 1) fun color _ =>
      mkLambdaFVars color (part (mkAppN rowRates color) 1)
    let jets := mkApp
      (app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.uncut_response_jets args) i
    let proof := app (input ++ `cutAmplitude_jets_global)
      (row[:60].toArray ++ #[row[61]!, row[62]!, unit, row[63]!, jets])
    discard <| save `cutAmplitude_jets_global params proof
  | 3 =>
    let current := `JanetCartan.PhysicalSampling.OriginalMeasuredCurrent
    let full ← bodyAt (current ++ `mean_on_full_response) row[:60].toArray
    unless full.isAppOfArity (current ++ `mean_before_response) 62 do
      throwError "actual measured Hermitian field: actual full-response spine changed"
    let mean ← bodyAt (current ++ `mean_before_response) full.getAppArgs
    unless mean.isAppOfArity `JanetCartan.PhysicalSampling.OriginalMeasuredMean.continuation 70 do
      throwError "actual measured Hermitian field: actual mean70 changed"
    let m := mean.getAppArgs
    let initialized ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredMean.initialized m[:37].toArray
    unless initialized.isAppOfArity `JanetCartan.PhysicalSampling.OriginalChoices.Mean.continuation 62 do
      throwError "actual measured Hermitian field: actual geometry62 changed"
    let init := initialized.getAppArgs
    let hκΩ ← mkAppM `Set.Subset.trans #[init[36]!, init[32]!]
    let t ← inferType m[56]!
    let normal := t.getAppArgs[t.getAppNumArgs - 2]!
    unless normal.isAppOfArity `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
      throwError "actual measured Hermitian field: actual leading coefficient changed"
    let a := normal.getAppArgs
    let proof ← forallBoundedTelescope (← inferType row[62]!) (some 1) fun colors _ => do
      let c := colors[0]!
      let inputs := a[:12].toArray ++ #[m[52]!, m[53]!, a[12]!, init[33]!, init[29]!,
        init[31]!, init[34]!, hκΩ, m[55]!, m[56]!, m[57]!, m[58]!, m[59]!,
        mkApp row[61]! c, ← mkAppM `ne_of_gt #[mkApp row[62]! c], mkApp row[63]! c]
      let smooth := app `JanetCartan.Sampling.contDiff_cutCorrectedDerivativeAmplitude inputs
      mkLambdaFVars colors smooth
    discard <| save `cutAmplitude_contDiff params proof
  | _ => throwError "actual measured Hermitian field: unknown actual amplitude field"

end JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfilesTemplate
end
