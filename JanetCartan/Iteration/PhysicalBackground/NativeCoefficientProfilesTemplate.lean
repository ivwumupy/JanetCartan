module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# The native same-reference coefficient profile application

Consumer: the actual whole-outer-weight measured-source high profile in task24,
then `app:ch_background:prop:bg-current` and `new:sec:order-of-choices`.

The source reference is the literal first18 reference dilated by the native
source scale. The normal-current-inverse cap proves positivity and sigma<=1;
no regular-sector cap is inferred or required. The parent joining the regular
operator profiles must check the same reference AND every numerical producer
argument before identifying the selected S/AQ/AB. Its history threshold is an
explicit additional prehistory maximum, not presumed below the native S.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeCoefficientProfilesTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

private def targetNS := `JanetCartan.PhysicalBackground.NativeCoefficientProfiles

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do
    throwError "native coefficient profiles: changed target {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native coefficient profiles: open or history-dependent selection {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

/-- Same literal producer as OriginalOperatorProfiles, but on the native
normal-inverse input prefix. Only numerical order and threshold certificates
are additional inputs; neither a successful coefficient estimate nor a
regular-sector source interval is assumed. -/
elab "realize_native_coefficient_profiles" : command => liftTermElabM do
  let native := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent
  forallBoundedTelescope (← getConstInfo native).type (some 23) fun scales _ => do
    unless scales.size == 23 do
      throwError "native coefficient profiles: expected raw21, sigma, normal-inverse interval"
    let fixed := scales[:21].toArray
    let n := fixed[0]!
    let hn := fixed[1]!
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) fixed[:18].toArray
    let capOne := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact2) fixed
    let hSigmaOne ← mkAppM `le_trans #[.proj ``And 1 scales[22]!, capOne]
    let Gref ← store `Gref scales
      (← mkAppM `JanetCartan.sourceDilationReference #[H, .proj ``And 0 scales[22]!, hSigmaOne]) true
    let original (name : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ name)) #[n, hn]
    let sameDomain := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5)
      fixed[:18].toArray
    let hR ← termWith [(`Gref, Gref), (`H, H), (`R, original `R),
        (`sameDomain, sameDomain), (`hOriginal, original `R_lt_chartRadius)]
      "(by change R < H.domain.chartRadius; rw [sameDomain]; exact hOriginal : R < Gref.domain.chartRadius)"
    let producer := mkAppN
      (mkConst `JanetCartan.PhysicalGeometry.exists_retained_coefficient_profiles)
      #[n, Gref, original `b, original `R, original `b_pos, original `b_lt_R, hR,
        fixed[4]!, fixed[5]!, fixed[6]!]
    forallBoundedTelescope (← inferType producer) (some 8) fun orders _ => do
      unless orders.size == 8 do
        throwError "native coefficient profiles: expected B, hB, rStar, rCoeff, kMin and three numeric certificates"
      let params := scales ++ orders
      let actual ← store `exists_profiles params (mkAppN producer orders)
      discard <| store `S params (← mkAppM ``Classical.choose #[actual]) true
      let hS ← mkAppM ``Classical.choose_spec #[actual]
      discard <| store `hS params (.proj ``And 0 hS)
      let hasAQ := Expr.proj ``And 1 hS
      discard <| store `AQ params (← mkAppM ``Classical.choose #[hasAQ]) true
      let hasAB ← mkAppM ``Classical.choose_spec #[hasAQ]
      discard <| store `AB params (← mkAppM ``Classical.choose #[hasAB]) true
      let profile ← mkAppM ``Classical.choose_spec #[hasAB]
      discard <| store `AQ_nonneg params (.proj ``And 0 profile)
      let tail := Expr.proj ``And 1 profile
      discard <| store `AB_nonneg params (.proj ``And 0 tail)
      discard <| store `continuation params (.proj ``And 1 tail)
  logInfo "native same-reference coefficient S/AQ/AB precede every history; parent threshold/reference guards remain explicit"

end JanetCartan.PhysicalBackground.NativeCoefficientProfilesTemplate
end
