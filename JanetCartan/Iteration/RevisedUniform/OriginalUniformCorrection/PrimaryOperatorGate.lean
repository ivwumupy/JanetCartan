module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairInitial
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
public meta import Lean

/-!
# The original primary graph's operator gate is already in Tpair

The original `GraphFamily` used by the primary source has coefficient reserve
`sectorLowOrder d`. The ordinary phase also reaches an operator threshold with
a larger reserve, but the two thresholds are separate classical choices. This
leaf uses the exact low-reserve operand of the actual signed window instead:
`SampledHistory.S = max OriginalWindow.S Sop`. All 33 operator arguments agree
with the primary graph. The existing `Tpair` therefore pays this gate at the
initial scale, before any Picard count or remainder order.

Consumer: the admitted history in the original primary source family, hence
`main:eq:primary-strain` and `new:sec:order-of-choices` in `paper-v2.tex`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformCorrectionPrimaryOperatorGateTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def phase := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Native.phase
private def correction := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
private def signed := `JanetCartan.PhysicalPairs.SampledHistory.S
private def pair := `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial
private def sizes := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def graph := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily
private def operator := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles.S
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args

private def bodyAt (key : Name) (args : Array Expr) : MetaM Expr := do
  let ci ← getConstInfo key
  let some value := ci.value? (allowOpaque := true) |
    throwError "original primary operator gate: missing original body {key}"
  return (value.beta args).headBeta

/-- The exact low operator and its elementary maximum bound, with no new
threshold or comparison between separately chosen reserves. -/
private def signedBound (args : Array Expr) : MetaM (Expr × Expr × Expr) := do
  unless args.size == 37 do throwError "original primary operator gate: signed static37 changed"
  let raw ← bodyAt signed args
  unless raw.isAppOfArity ``Max.max 4 do
    throwError "original primary operator gate: signed window no longer contains max(old,Sop)"
  let low := raw.getAppArgs[3]!
  unless low.isAppOfArity operator 33 do
    throwError "original primary operator gate: missing original operator33"
  let reserve := app `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[low.getAppArgs[0]!]
  unless low.getAppArgs[28]! == reserve do
    throwError "original primary operator gate: the primary low reserve changed"
  let proof ← mkAppM ``le_max_right #[raw.getAppArgs[2]!,low]
  return (low,app signed args,proof)

private def save (key : Name) (params : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "original primary operator gate: late history or unresolved input in {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "original primary operator gate: missing original metadata {missing.toList}"
  let name := root ++ key
  if (env.find? name).isSome then throwError "original primary operator gate: duplicate {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact sectorLowOrder operator gate of the SAME original primary GraphFamily is the right operand of the actual signed-window maximum. The existing Tpair reaches it at R₀ before every Picard count, remainder order, target or history; no new threshold and no monotonicity between classical choices is used (main:eq:primary-strain; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original primary operator gate: nonstandard axioms {axioms}"
  logInfo m!"actual original primary operator gate {key}/{params.size}: {axioms}"

run_meta do
  let ci ← getConstInfo phase
  forallBoundedTelescope ci.type (some 51) fun native _ => do
    unless native.size == 51 do throwError "original primary operator gate: native phase51 changed"
    let ordinary ← bodyAt phase native
    unless ordinary.isAppOfArity `JanetCartan.PhysicalPairs.SampledQuadrature.group_phase 42 do
      throwError "original primary operator gate: original ordinary graph42 changed"
    let reached ← inferType ordinary.getAppArgs[37]!
    unless reached.isAppOfArity ``LE.le 4 && reached.getAppArgs[2]!.isAppOfArity
        `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
      throwError "original primary operator gate: original graph34 admission changed"
    let graphArgs := reached.getAppArgs[2]!.getAppArgs
    let histories ← bodyAt graph graphArgs
    unless histories.isAppOfArity
        `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.Histories 5 do
      throwError "original primary operator gate: the exact measured graph family changed"
    let primaryLow := histories.getAppArgs[4]!
    withLocalDeclD `Cscale (mkConst ``Real) fun C => do
      let fixed := native[:44].toArray.push C
      let rest ← instantiateForall (← getConstInfo correction).type fixed
      forallBoundedTelescope rest (some 8) fun late atSigned => do
        unless late.size == 8 && atSigned.isForall &&
            atSigned.bindingDomain!.isAppOfArity ``LE.le 4 do
          throwError "original primary operator gate: actual correction55 signed gate changed"
        let window := atSigned.bindingDomain!.getAppArgs[2]!
        unless window.isAppOfArity signed 37 do
          throwError "original primary operator gate: not the actual correction's signed window"
        let (low,_,proof) ← signedBound window.getAppArgs
        unless primaryLow == low do
          throwError "original primary operator gate: primary and signed operator33 differ"
        save `primaryGraphOperator_le_signedWindow fixed proof
          (← mkAppM ``LE.le #[primaryLow,window])

run_meta do
  let ci ← getConstInfo (pair ++ `Tpair)
  forallBoundedTelescope ci.type (some 3) fun fixed result => do
    unless fixed.size == 3 && result.isConstOf ``Real do
      throwError "original primary operator gate: fixed dimension/scale3 changed"
    let raw := ((ci.value! (allowOpaque := true)).beta fixed).headBeta
    unless raw.isAppOfArity ``Max.max 4 do
      throwError "original primary operator gate: original Tpair maximum changed"
    let old := raw.getAppArgs[2]!
    let size := raw.getAppArgs[3]!
    unless size.isAppOfArity (sizes ++ `earlyS) 38 do
      throwError "original primary operator gate: original pre-accuracy signed size gate changed"
    let bcap := size.getAppArgs
    let (low,_,low_le_signed) ← signedBound bcap[:37].toArray
    let signed_le_size := app (sizes ++ `early_reaches_signed) bcap
    let size_le_initial ← mkAppM ``le_max_right #[old,size]
    let proof ← mkAppM ``le_trans
      #[low_le_signed,← mkAppM ``le_trans #[signed_le_size,size_le_initial]]
    save `primaryGraphOperator_le_Tpair fixed proof
      (← mkAppM ``LE.le #[low,app (pair ++ `Tpair) fixed])

run_meta do
  let name := root ++ `primaryGraphOperator_le_Tpair
  forallBoundedTelescope (← getConstInfo name).type (some 3) fun fixed bound => do
    unless fixed.size == 3 && bound.isAppOfArity ``LE.le 4 do
      throwError "original primary operator gate: lost literal low operator bound"
    withLocalDeclD `R₀ (mkConst ``Real) fun R₀ => do
      let reached ← mkAppM ``LE.le #[bound.getAppArgs[3]!,R₀]
      withLocalDeclD `hInitial reached fun hInitial => do
        let proof ← mkAppM ``le_trans #[app name fixed,hInitial]
        save `primaryGraphOperator_reached (fixed ++ #[R₀,hInitial]) proof
          (← mkAppM ``LE.le #[bound.getAppArgs[2]!,R₀])

end JanetCartan.RevisedUniform.OriginalUniformCorrectionPrimaryOperatorGateTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.primaryGraphOperator_le_signedWindow
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.primaryGraphOperator_le_Tpair
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.primaryGraphOperator_reached
