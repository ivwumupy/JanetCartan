module

public import JanetCartan.Iteration.PhysicalBackground.NativeAdmission
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparedQuadratureApplication.ScalarSpan
public meta import Lean

/-!
# The actual native positive amplitude belongs to its original source span

The source53 scalar at input 49 is a member of the linear span of the original
admitted scalars, not a new freely chosen function. Use the original strict
scalar gap and genuine smoothness of the native initial amplitude to put that
same function in the true selected cell's span. Its underlying value is exactly
`positiveDensityAmplitude σ (NativeAdmission.labels ... i q)` for the physical
history being used. There is no size division, change of density, or extra high
profile assumption (`app:ch_response:cor:current-atoms`, `app:ch_waves:eq:WKB-W`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativeSourceScalarApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalSampling.OriginalNativeSourceScalar
private def bg := `JanetCartan.PhysicalBackground.NativeAdmission
private def bd := `JanetCartan.PhysicalSeed.OriginalBoundary
private def store (short : Name) (xs : Array Expr) (v t : Expr) (data := false) : MetaM Expr := do
  let name := ns ++ short
  let type ← instantiateMVars (← mkForallFVars xs t)
  let value ← instantiateMVars (← mkLambdaFVars xs v)
  if type.hasMVar || type.hasFVar || value.hasMVar || value.hasFVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "open actual scalar {name}"
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  return mkAppN (mkConst name) xs

elab "put_original_native_amplitude_in_source_span" : command => liftTermElabM do
  let labelsName := bg ++ `labels
  forallBoundedTelescope (← getConstInfo labelsName).type (some 39) fun p t => do
    unless p.size == 39 do throwError "actual positive scalar: expected native39"
    let .forallE _ rows _ _ ← whnf t | throwError "actual positive scalar: missing true row type"
    withLocalDeclD `i rows fun i => do
      let fixed := p[:21].toArray
      let n := fixed[0]!
      let hn := fixed[1]!
      let c ← mkAppM ``Sigma.fst #[i]
      let inc ← mkAppM ``Subtype.val #[c]
      let chart ← mkAppM ``Prod.fst #[← mkAppM ``Subtype.val #[inc]]
      let slot ← mkAppM ``Sigma.snd #[i]
      let boundary := mkAppN (mkConst (bd ++ `comparison_pos)) #[n,hn]
      let .forallE _ patchT _ _ ← whnf (← inferType boundary) | throwError "missing original boundary patch"
      let patchT ← whnf patchT
      unless patchT.isAppOfArity ``Sigma 2 do throwError "changed native patch type"
      let patch ← mkAppOptM ``Sigma.mk #[some patchT.appFn!.appArg!,some patchT.appArg!,some chart,some slot]
      let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,hn,fixed[20]!]
      let cell := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.cell) ((fixed.set! 20 capped) ++ #[inc,slot])
      let z ← mkAppM ``Subtype.val #[← mkAppM ``Subtype.val #[cell]]
      let pos := mkAppN boundary #[patch,cell]
      let R := (← inferType (.proj ``And 0 (.proj ``And 1 pos))).appArg!
      let hσ := Expr.proj ``And 0 p[23]!
      let hm ← mkAppM `le_of_lt #[← mkAppM `JanetCartan.PhysicalInitialization.positive_leading_scalar_lower_bound #[hσ]]
      let gap ← mkAppM `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.scalar_budget_gap
        #[hσ,mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact5) fixed]
      let lab := mkAppN (mkConst labelsName) (p.push i)
      let initial ← forallBoundedTelescope (← inferType lab) (some 1) fun q _ =>
        mkLambdaFVars q (mkAppN (mkConst `JanetCartan.positiveDensityAmplitude) #[p[21]!,mkAppN lab q])
      let smooth := mkAppN (mkConst (bg ++ `initial_smooth)) (p.push i)
      let hrel ← mkAppM `JanetCartan.PositiveBackground.contDiff_densityOnInitialLabels #[smooth]
      let hadm ← mkAppM `JanetCartan.CurrentMean.mem_initialScalarSpan_of_contDiff #[z,R,hm,gap,hrel]
      let mt ← inferType hadm
      unless mt.isAppOfArity ``Membership.mem 5 do throwError "changed original span domain"
      let target ← mkAppM ``Membership.mem #[mt.getAppArgs[3]!,initial]
      let xs := p.push i
      let hmem ← store `in_source_span xs hadm target
      let scalar ← mkAppM ``Subtype.mk #[initial,hmem]
      let actual ← store `scalar xs scalar (← inferType scalar) true
      let underlying ← mkAppM ``Subtype.val #[actual]
      discard <| store `scalar_eq xs (← mkEqRefl initial) (← mkEq underlying initial)
      logInfo "checked the native protected positive scalar as a member of the actual original source span on its own selected cell; value unchanged"

end JanetCartan.PhysicalSampling.OriginalNativeSourceScalarApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000

put_original_native_amplitude_in_source_span
