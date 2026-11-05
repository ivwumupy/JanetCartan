module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryStatement
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMean
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedCorrection
public import JanetCartan.Iteration.PhysicalPairs.Secondary
public import JanetCartan.Iteration.RevisedStage.Cutoff
import all JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicard
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# One original family for the physical revised step

These fields are the literal objects consumed by
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`
(`main:thm:step`, `main:eq:self-off`, `main:eq:mean-equation`). The original
selected data determine the full forcing, cutoff count, sample and external
amplitude. The finite Picard count is shared by the primary, mean, full self
and signed response. No new analytic or sampling choice is made here.

The signed response retains its original numerical window gate. Actual
estimates and the uniform selection of that gate are separate producers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepFieldsTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalStepFields
private def meanRoot := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def pairRoot := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction

private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p

private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

/-- Open the unchanged selected52 and native50, their literal normalized-source
arguments, and the original cutoff count, then one common finite Picard count.
This interface is only a term-construction helper; it assumes no estimate. -/
def withStage
    (next : Array Expr → Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  PhysicalMean.OriginalFullSourcePicard.withFullData fun native selected _ _ J => do
    unless native.size == 50 && selected.size == 52 do
      throwError "original step fields: selected52/native50 changed"
    let source := (((← getConstInfo (meanRoot ++ `normalizedTarget)).value!
      (allowOpaque := true)).beta selected).headBeta
    unless source.isAppOfArity `JanetCartan.PhysicalSmoothing.normalizedSource 10 do
      throwError "original step fields: not the original finite-moment normalized source"
    unless J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 do
      throwError "original step fields: lost the original common cutoff count"
    withLocalDeclD `N (mkConst ``Nat) fun N =>
      next selected native source.getAppArgs J N

private def save (key : Name) (p : Array Expr) (value : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p (← inferType value))
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "original step fields: added or unresolved data in {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "original step fields: unavailable original dependency {missing.toList}"
    for old in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
        `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate,
        `JanetCartan.PhysicalMean.OriginalPeriodicBackground.forcing] do
      if e.getUsedConstants.contains old then
        throwError "original step fields: background-only forcing escaped in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Checking original common step field {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
    (forceExpose := true)
  addDocStringCore name "The literal original physical step field on selected52, one complete forcing, one cutoff count, one sample and one finite Picard count. The external amplitude is exactly the normalized source's delta=R^(-k). The signed field retains only its existing numerical window gate; no analytic success premise or replacement field (main:thm:step; main:eq:self-off; main:eq:mean-equation)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original step fields: nonstandard axioms {axioms}"
  logInfo m!"PASS original common step field {key}/{p.size}: {axioms}"

elab "construct_original_step_field " mode:num : command => liftTermElabM do
  unless mode.getNat < 8 do throwError "original step fields: unknown field"
  withStage fun selected native a J N => do
    let p := selected.push N
    if mode.getNat == 0 then
      save `primary p (app `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary.field
        (selected ++ #[N,a[6]!]))
      return
    if mode.getNat == 1 then
      save `mean p (app (meanRoot ++ `physicalMean) (selected ++ #[J,N]))
      return
    if mode.getNat == 2 then
      save `fullSelf p (app (meanRoot ++ `fullSampledSelf) (selected ++ #[J,N]))
      return
    let P := app (root ++ `primary) p
    let V := app (root ++ `mean) p
    let H := app (root ++ `fullSelf) p
    let b ← termWith [(`n,a[0]!),(`delta,a[6]!),(`R,a[4]!)]
      "delta * R ^ JanetCartan.RevisedScales.forcingExponent n"
    if mode.getNat == 3 then
      let value ← termWith [(`n,a[0]!),(`dim,a[1]!),(`P,P),(`H,H),(`b,b)]
        "JanetCartan.inducedMetric (P : JanetCartan.Euclidean n → JanetCartan.Euclidean dim) - b ^ 2 • H"
      save `offSelf p value
      return
    if mode.getNat == 4 then
      let F := app `JanetCartan.RevisedGlobal.finiteMap #[a[0]!,a[1]!,a[2]!,a[8]!,a[9]!]
      let eR := app `JanetCartan.PhysicalSmoothing.smoothedDefect (a[:6].toArray ++ a[7:].toArray)
      let value ← termWith [(`n,a[0]!),(`dim,a[1]!),(`F,F),(`V,V),(`H,H),(`eR,eR),(`b,b)]
        "JanetCartan.linearizedMetric F (V : JanetCartan.Euclidean n → JanetCartan.Euclidean dim) + H - (b ^ 2)⁻¹ • eR"
      save `meanError p value
      return
    withLocalDeclD `Cscale (mkConst ``Real) fun Cscale => do
      let full := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource selected
      let run := app `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterateWithForcing
        (native ++ #[J,full,N])
      let stem := native[:44].toArray ++ #[Cscale] ++ native[44:].toArray ++ #[J,run]
      let tail ← inferType (app pairRoot stem)
      unless stem.size == 53 && tail.isForall &&
          tail.bindingDomain!.isAppOfArity ``LE.le 4 do
        throwError "original step fields: signed response lost its numerical window gate"
      withLocalDeclD `hSigned tail.bindingDomain! fun hSigned => do
        let params := p ++ #[Cscale,hSigned]
        if mode.getNat == 5 then
          save `signedCorrection params (app pairRoot (stem ++ #[hSigned,a[6]!]))
        else if mode.getNat == 6 then
          let S := app (root ++ `signedCorrection) params
          save `secondary params (app `JanetCartan.PhysicalPairs.physicalSecondary
            #[a[0]!,a[1]!,b,V,S])
        else
          let W := app (root ++ `secondary) params
          save `increment params (app `JanetCartan.RevisedStage.increment #[a[0]!,a[1]!,a[4]!,P,W])

end JanetCartan.RevisedUniform.OriginalStepFieldsTemplate
end
