module
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceScalar
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
public meta import Lean
/-!
# Coefficient-scale jets of the unchanged native positive baseline

Consumer: the SAME-phase complete and pair amplitude in `main:prop:pairs` and
`main:eq:mean-final-amplitude`. The baseline is the literal phase-cancelled
spatial derivative of the original unscaled positive atom. Its data and static
original-row budget remain in `OriginalBaselineAmplitudeProfiles`, unchanged.

Typed scalar/function caches isolate the actual subtype VALUE and response
identities. No equality of enormous dependent current records is required.
The exact full-parent identity then transfers its whole-chart local smoothness
and every coefficient-scale jet to the original baseline. Only the genuine
outer nonzero sampling weight is used for admission; no inner angular gate,
carrier division, physical-frequency profile or sampling-cardinality cost is
introduced (`main:prop:mean`, `new:sec:order-of-choices`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles.Calculus
/-- Exact equality on the original open chart transports the full local
baseline profile without assuming global raw-atom smoothness (`main:prop:pairs`). -/
theorem baseline_profile_congr {n N : ℕ} {X : Set (Euclidean n)} (hX : IsOpen X)
    (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ) (heq : EqOn B A X)
    (D : ℕ → ℝ) (T : ℝ)
    (hA : ContDiffOn ℝ ∞ A X ∧ ∀ q, ∀ x ∈ X,
      ‖iteratedFDeriv ℝ q A x‖ ≤ D q*T^q) :
    ContDiffOn ℝ ∞ B X ∧ ∀ q, ∀ x ∈ X,
      ‖iteratedFDeriv ℝ q B x‖ ≤ D q*T^q := by
  refine ⟨hA.1.congr (fun x hx ↦ heq hx), ?_⟩
  intro q x hx
  have hg : B =ᶠ[𝓝 x] A := by
    filter_upwards [hX.mem_nhds hx] with y hy using heq hy
  rw [(hg.iteratedFDeriv ℝ q).eq_of_nhds]
  exact hA.2 q x hx
end JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles.Calculus
end
public meta section
namespace JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles
open Lean Meta
private def root := `JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles
private def production := `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles
private def node := `JanetCartan.PhysicalPairs.OriginalBaselineNode
private def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def body (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true)
    | throwError "original native baseline: unavailable {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := body (app key p)
private def save (key : Name) (p : Array Expr) (value target : Expr)
    (doc : String) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "original native baseline: unresolved {key}"
    unless (e.getUsedConstants.filter fun n => (env.find? n).isNone).isEmpty do
      throwError "original native baseline: missing constant in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original native baseline {name}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name doc
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original native baseline: nonstandard axioms in {name}: {ax}"
  logInfo m!"PASS original native baseline {name}/{p.size}/std3: {ax}"
private def withPair (go : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let ci ← getConstInfo (node ++ `native_demodulation_statement)
  forallBoundedTelescope ci.type (some 57) fun p _ => do
    forallBoundedTelescope ((ci.value! (allowOpaque := true)).beta p) (some 2) fun _ t => do
      unless t.isAppOfArity ``Eq 3 do throwError "original native baseline: changed native equality"
      let nf := t.getAppArgs[1]!.appFn!
      let pf ← body (app (parent ++ `amplitude) p[:52].toArray)
      unless nf.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 16 &&
          pf.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 16 do
        throwError "original native baseline: changed full derivative constructor16"
      go p[:52].toArray nf.getAppArgs pf.getAppArgs
private def scalarEquality (na : Array Expr) : MetaM Expr := do
  let scalar ← body na[14]!
  unless scalar.isAppOfArity ``Subtype.val 3 do
    throwError "original native baseline: not the actual source scalar value"
  let datum := scalar.getAppArgs[2]!
  unless datum.isAppOfArity `JanetCartan.PhysicalSampling.OriginalNativeSourceScalar.scalar 40 do
    throwError "original native baseline: changed native scalar40"
  return app `JanetCartan.PhysicalSampling.OriginalNativeSourceScalar.scalar_eq datum.getAppArgs
run_meta do
  withPair fun p na _ => do
    save `nativeScalar p na[14]! (← inferType na[14]!)
      "The literal scalar VALUE of the original native positive atom, cached before every outer sample (main:prop:pairs)." true
run_meta do
  withPair fun p na _ => do
    let r := app (root ++ `nativeScalar) p
    let value := app `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude (na.set! 14 r)
    save `nativeAmplitude p value (← inferType value)
      "The unchanged full corrected derivative constructor of the actual native atom, with its same scalar value (main:prop:pairs)." true
run_meta do
  withPair fun p _ pa => do
    let value ← withLocalDeclD `B (← inferType pa[13]!) fun B => do
      withLocalDeclD `r (← inferType pa[14]!) fun r =>
        mkLambdaFVars #[B,r]
          (app `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude ((pa.set! 13 B).set! 14 r))
    save `parentConstructor p value (← inferType value)
      "The same original full-parent derivative constructor, abstracted only over response and scalar for compact congruence (main:prop:pairs)." true
run_meta do
  withPair fun p na pa => do
    let nb ← body na[13]!
    let pb ← body pa[13]!
    unless nb.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalFullResponse.B 38 &&
        pb.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalFullResponse.B 38 do
      throwError "original native baseline: changed original response38"
    for k in [:38] do
      unless nb.getAppArgs[k]! == pb.getAppArgs[k]! do
        unless (← isProof nb.getAppArgs[k]!) && (← isProof pb.getAppArgs[k]!) do
          throwError "original native baseline: response differs in DATA slot{k}"
    save `response_eq_parent p (← mkEqRefl nb) (← mkEq na[13]! pa[13]!)
      "The actual native and parent responses agree; the same full-response38 data differs only in proof arguments (main:prop:pairs)."
run_meta do
  withPair fun p na pa => do
    let h ← scalarEquality na
    let raw := (← inferType h).getAppArgs[2]!
    save `actual_scalar_eq_parent p (← mkEqRefl raw) (← mkEq raw pa[14]!)
      "The literal original positive-density scalar equals the scalar of the same full parent (main:prop:pairs)."
private def withNative (next : Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (root ++ `nativeScalar)).type (some 52) fun p _ => do
    unless p.size == 52 do throwError "original native baseline: changed native52"
    next p
run_meta do
  withNative fun p => do
    let raw := (← inferType (app (root ++ `actual_scalar_eq_parent) p)).getAppArgs[1]!
    let scalar := app (root ++ `nativeScalar) p
    save `native_scalar_eq_actual p (← mkEqRefl raw) (← mkEq scalar raw)
      "Project the actual source-span subtype VALUE, without equating predicates or dependent current records (main:prop:pairs)."
run_meta do
  withNative fun p => do
    let native := app (root ++ `nativeAmplitude) p
    let scalar := app (root ++ `nativeScalar) p
    let nb := (← inferType (app (root ++ `response_eq_parent) p)).getAppArgs[1]!
    let constructed := mkAppN (app (root ++ `parentConstructor) p) #[nb,scalar]
    save `native_amplitude_from_parent p (← mkEqRefl native) (← mkEq native constructed)
      "Primitive aliases identify the unchanged full constructor while response and scalar remain literally fixed (main:prop:pairs)."
run_meta do
  withNative fun p => do
    let scalarEq := app (root ++ `actual_scalar_eq_parent) p
    let rawParent := (← inferType scalarEq).getAppArgs[2]!
    let hs ← mkEqTrans (app (root ++ `native_scalar_eq_actual) p) scalarEq
    let hb := app (root ++ `response_eq_parent) p
    let nb := (← inferType hb).getAppArgs[1]!
    let constructor := app (root ++ `parentConstructor) p
    let hr ← mkCongrArg (mkApp constructor nb) hs
    let Bmap ← withLocalDeclD `B (← inferType nb) fun B =>
      mkLambdaFVars #[B] (mkAppN constructor #[B,rawParent])
    let hB ← mkCongrArg Bmap hb
    let result ← mkEqTrans (app (root ++ `native_amplitude_from_parent) p) (← mkEqTrans hr hB)
    save `native_amplitude_eq_parent p result
      (← mkEq (app (root ++ `nativeAmplitude) p) (app (parent ++ `amplitude) p))
      "The actual native full corrected derivative amplitude is the SAME full parent function, by compact scalar/response congruence (main:prop:pairs)."
private def instForall (type : Expr) (p : Array Expr) : MetaM Expr := do
  let mut result := type
  for x in p do
    unless result.isForall do throwError "original native baseline: changed actual point/chart telescope"
    result := result.bindingBody!.instantiate1 x
  return result
run_meta do
  let statement := node ++ `amplitude_on_original_statement
  forallBoundedTelescope (← getConstInfo statement).type (some 57) fun p _ => do
    forallBoundedTelescope (← bodyAt statement p) (some 2) fun xy target => do
      unless target.isAppOfArity ``Eq 3 do throwError "original native baseline: missing exact statement"
      let lhs := target.getAppArgs[1]!
      unless lhs.isAppOfArity `JanetCartan.UniformStep.sampledDerivativeAmplitude 7 do
        throwError "original native baseline: changed sampled derivative object"
      let la := lhs.getAppArgs
      let Z := la[3]!.beta #[mkConst ``Unit.unit]
      let θ := la[4]!.beta #[mkConst ``Unit.unit]
      let exponential := app `JanetCartan.PhysicalPairs.CombinedNode.amplitude_eq_exp
        #[la[0]!,la[1]!,Z,θ,xy[0]!]
      let ea := (← inferType exponential).getAppArgs
      let native ← instForall (← bodyAt (node ++ `native_demodulation_statement) p) xy
      let na := native.getAppArgs
      let hp := app (node ++ `native_demodulation) (p ++ xy)
      let rev := mkAppN (mkConst ``Eq.symm [.succ .zero]) #[na[0]!,na[1]!,na[2]!,hp]
      let middle := mkAppN (mkConst ``Eq.trans [.succ .zero])
        #[ea[0]!,ea[1]!,ea[2]!,na[1]!,exponential,rev]
      let fnEq := app (root ++ `native_amplitude_eq_parent) p[:52].toArray
      let pointEq ← mkCongrFun fnEq na[1]!.appArg!
      let pe := (← inferType pointEq).getAppArgs
      let result := mkAppN (mkConst ``Eq.trans [.succ .zero])
        #[ea[0]!,ea[1]!,na[1]!,pe[2]!,middle,pointEq]
      let B := app (production ++ `baselineAmplitude) p[:56].toArray
      let desired ← mkEq (mkApp B xy[0]!) target.getAppArgs[2]!
      save `baseline_eq_parent p (← mkLambdaFVars xy result) (← mkForallFVars xy desired)
        "On the WHOLE original source chart, the SAME unweighted positive baseline56 equals the original full-parent derivative amplitude at its actual outer node. Original phase, atom, cF and sample are unchanged (main:prop:pairs; main:eq:mean-final-amplitude)."
run_meta do
  let name := production ++ `parent_slice_profile
  forallBoundedTelescope (← getConstInfo name).type (some 57) fun p _ => do
    let parentProfile := app name p
    let pt ← inferType parentProfile
    unless pt.isAppOfArity ``And 2 && pt.getAppArgs[0]!.isAppOfArity ``ContDiffOn 11 do
      throwError "original native baseline: changed actual parent profile"
    let smooth := pt.getAppArgs[0]!.getAppArgs
    let A := smooth[9]!
    let X := smooth[10]!
    unless X.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
      throwError "original native baseline: not the whole SourceMasks.chart"
    let B := app (production ++ `baselineAmplitude) p[:56].toArray
    let pa := (← bodyAt (parent ++ `amplitude) p[:52].toArray).getAppArgs
    let D := app (production ++ `Cbaseline) p[:44].toArray
    let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
    let h := app (root ++ `Calculus.baseline_profile_congr)
      #[pa[0]!,pa[1]!,X,app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open X.getAppArgs,
        A,B,app (root ++ `baseline_eq_parent) p,D,T,parentProfile]
    save `baseline_profile p h (← inferType h)
      "The SAME unweighted native positive baseline56 is ContDiffOn infinity on the WHOLE original source chart, with every physical jet bounded by the fixed original-row Cbaseline44(q)*currentCoefficientScale^q. Only the original outer nonzero sampling weight admits the node; no inner angular premise, division, sample count or physical-frequency substitute (main:prop:pairs; main:prop:mean; new:sec:order-of-choices)."
end JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles
end
