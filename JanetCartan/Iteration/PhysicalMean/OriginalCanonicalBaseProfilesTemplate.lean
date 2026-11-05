module

public import JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
import all JanetCartan.Iteration.PhysicalBackground.NativeBaseProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalCompletionProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles
public import JanetCartan.Iteration.RevisedUniform.OriginalSmoothing
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Original base and full strain on the physical cutoff buffer

The physical fields retain `OriginalSmoothing.Dsmooth`; only their defect core
was restricted by `OriginalFinalCore`. For the actual inverse bump radius a,
the unchanged physical cutoff has outer radius 5a/6. The fixed norm buffer
11a/12 lies strictly inside its original chart a and the wide coefficient ball b.

Reuse `NativeBaseProfiles` at base reserve zero on the SAME native raw, source
cutoff, tangent initializer and source-dilated reference. Its closed-b profile
controls BOTH the base and its full strain without a derivative-loss shortcut.
Every budget precedes R₀/history; the additional Sbase gate is truly initial.
Consumers: the original completed mean and its physical cutoff Sobolev profile
(`main:eq:mean-normal-field`, `main:prop:mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric JanetCartan
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (ActualInverse withActualInverse)
open OriginalBackgroundHermitianTemplate (bodyAt)

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def smoothing := `JanetCartan.RevisedUniform.OriginalSmoothing
private def nativeBase := `JanetCartan.PhysicalBackground.NativeBaseProfiles
private def nativeSource := `JanetCartan.PhysicalBackground.NativeSourceProfiles
private def measured := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (bindings : List (Name × Expr)) (code : String)
    (expected : Option Expr := none) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code expected)

private def save (key : Name) (params : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original base: unresolved or later input escaped {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "original base: unavailable producers {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"original base: kernel checking {name} / {params.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "SAME original native current/raw and unchanged physical cutoff. Source-only geometry/budgets precede the physical history; the combined base and FULL strain profile uses the original producer, not differentiation of a coarse norm (main:eq:mean-normal-field, main:prop:mean)."
  liftM <| IO.eprintln s!"original base: kernel passed {name}"
  return app name params

/-- Read the existing original25 source reference from its checked graph spine.
The temporary row/color and physical history cannot enter any fixed geometry. -/
private def regularArguments (p : Array Expr) : MetaM (Array Expr) := do
  let graph := `JanetCartan.PhysicalSampling.OriginalGraphResponse.B
  let query := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.uncut_response_jets p
  forallBoundedTelescope (← inferType query) (some 2) fun point _ => do
    let type ← inferType (mkAppN query point)
    let some g := type.find? (·.isAppOfArity graph 42)
      | throwError "original base: missing original graph42"
    if g.hasLooseBVars then throwError "original base: later observation entered graph"
    let gt := (← instantiateForall (← getConstInfo graph).type g.getAppArgs[:37].toArray).consumeMData
    let .forallE _ reached _ _ := gt | throwError "original base: missing original graph reach"
    unless reached.isAppOfArity ``LE.le 4 do throwError "original base: changed graph gate"
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity (regular ++ `Graph.S) 34 do throwError "original base: changed original S34"
    let fixed := S.getAppArgs
    let ref := fixed[:23].toArray ++ #[fixed[25]!,app (regular ++ `Graph.regular_scale) fixed[:27].toArray]
    for e in ref do
      let closed ← mkLambdaFVars p[:44].toArray e
      if closed.hasFVar || closed.hasLooseBVars then
        throwError "original base: history, row or observation entered original25"
    return ref

elab "construct_original_base_physical_geometry " mode:num : command => liftTermElabM do
  withActualInverse fun d => withTransparency .default do
    let p := d.parameters
    let fixed := p[:44].toArray
    let ref ← regularArguments p
    let Dactual := app (smoothing ++ `Dsmooth) ref[:23].toArray
    let Gref := app `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref d.native39[:23].toArray
    let n := d.native39[0]!
    let hn := d.native39[1]!
    let geo (key : Name) := app (`JanetCartan.PhysicalSeed.OriginalBoundary ++ key) #[n,hn]
    let D := app (root ++ `Dsmooth) fixed
    let radius := app (root ++ `rBuffer) fixed
    match mode.getNat with
    | 0 => discard <| save `Dsmooth fixed Dactual true
    | 1 =>
        let value ← termWith [(`D,D)] "11 * D.chartRadius / 12"
        discard <| save `rBuffer fixed value true
    | 2 =>
        let other := app (regular ++ `Gref) ref
        discard <| save `reference_eq fixed (← mkEqRefl Gref) false (some (← mkEq Gref other))
    | 3 =>
        let chi := app (regular ++ `χ₂) ref[:23].toArray
        let support := app (smoothing ++ `χ₂_support_coefficient_ball) ref[:23].toArray
        let hab := app (smoothing ++ `bump_inner_lt_coefficient_bound) #[ref[0]!,chi,geo `b,support]
        let H := app `JanetCartan.PhysicalSeed.ReferenceBoundary.H d.native39[:18].toArray
        let same := app `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5 d.native39[:18].toArray
        let hR ← termWith [(`Gref,Gref),(`H,H),(`R,geo `R),(`same,same),(`hOriginal,geo `R_lt_chartRadius)]
          "(by change R < H.domain.chartRadius; rw [same]; exact hOriginal : R < Gref.domain.chartRadius)"
        let fields := [(`n,n),(`D,D),(`chi,chi),(`r,radius),(`b,geo `b),(`R,geo `R),(`hab,hab),
          (`hbR,geo `b_lt_R),(`Gref,Gref),(`hR,hR)]
        let proof ← termWith fields
          ("(by\n" ++
           "  have ha : 0 < D.chartRadius := chi.rIn_pos\n" ++
           "  have hab : D.chartRadius < b := hab\n" ++
           "  have hr : 0 < r := by change 0 < 11 * D.chartRadius / 12; positivity\n" ++
           "  have hra : r < D.chartRadius := by change 11 * D.chartRadius / 12 < D.chartRadius; linarith only [ha]\n" ++
           "  have hout : (UniformStep.physicalCutoff (n := n) D).rOut = 5 * D.chartRadius / 6 := by\n" ++
           "    change (chi.rIn / 2 + 2 * chi.rIn) / 3 = 5 * chi.rIn / 6\n" ++
           "    ring\n" ++
           "  have hcut : (UniformStep.physicalCutoff (n := n) D).rOut < r := by\n" ++
           "    rw [hout]; change 5 * D.chartRadius / 6 < 11 * D.chartRadius / 12; linarith only [ha]\n" ++
           "  exact ⟨hr,hra,hab,hbR,hR,hout,hcut⟩\n" ++
           "  : 0 < r ∧ r < D.chartRadius ∧ D.chartRadius < b ∧ b < R ∧ R < Gref.domain.chartRadius ∧ " ++
           "(UniformStep.physicalCutoff (n := n) D).rOut = 5 * D.chartRadius / 6 ∧ " ++
           "(UniformStep.physicalCutoff (n := n) D).rOut < r)")
        discard <| save `radius_geometry fixed proof
    | 4 =>
        let proof ← termWith [(`n,n),(`D,D),(`r,radius),(`h,app (root ++ `radius_geometry) fixed)]
          ("(by rw [(UniformStep.physicalCutoff (n := n) D).tsupport_eq]; " ++
           "exact closedBall_subset_closedBall h.2.2.2.2.2.2.le " ++
           ": tsupport (UniformStep.physicalCutoff (n := n) D) ⊆ closedBall (0 : Euclidean n) r)")
        discard <| save `cutoff_support_buffer fixed proof
    | 5 =>
        let proof ← termWith [(`n,n),(`D,D),(`r,radius),(`b,geo `b),(`R,geo `R),
            (`h,app (root ++ `radius_geometry) fixed)]
          ("(⟨closedBall_subset_ball h.2.1, ball_subset_ball h.2.2.1.le, " ++
           "closedBall_subset_closedBall (h.2.1.trans h.2.2.1).le, " ++
           "closedBall_subset_ball h.2.2.2.1⟩ : " ++
           "closedBall (0 : Euclidean n) r ⊆ D.chart n ∧ D.chart n ⊆ ball 0 b ∧ " ++
           "closedBall (0 : Euclidean n) r ⊆ closedBall 0 b ∧ closedBall (0 : Euclidean n) b ⊆ ball 0 R)")
        discard <| save `buffer_containments fixed proof
    | 6 =>
        let raw ← bodyAt (measured ++ `on_exterior_plateau) d.native39
        unless raw.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
          throwError "original base: changed cancellation64"
        let F := raw.getAppArgs[34]!
        let actualMap ← termWith [(`Gref,app (regular ++ `Gref) ref),(`u,p[47]!)]
          "RevisedGlobal.finiteMap Gref.map u"
        discard <| save `current_map_eq p (← mkEqRefl F) false (some (← mkEq F actualMap))
    | _ => throwError "original base: unknown physical geometry mode"

end JanetCartan.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
end


public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (ActualInverse withActualInverse)
open OriginalBackgroundHermitianTemplate (bodyAt)

/-- The native density certificate uses rDensity+3+(n-1)+2 for raw synthesis.
At base reserve zero, retain its rCoeff and weaken only the numerical orders. -/
private def profileArguments (d : ActualInverse) : MetaM (Array Expr × Array Expr × Array Expr) := do
  let x := d.source45
  let n := x[0]!
  let rawReserve ← termWith [(`n,n),(`rd,x[33]!)] "rd + (3 + (n - 1)) + 2"
  let lowReserve ← termWith [(`n,n)] "(0 : ℕ) + 1 + n"
  let low ← termWith [(`n,n),(`rd,x[33]!)]
    "(by omega : 0 + 1 + n ≤ rd + (3 + (n - 1)) + 2)"
  let coeff ← termWith [(`h,low),(`hc,x[35]!)] "h.trans hc"
  let reserve ← termWith [(`h,low),(`hr,x[37]!),(`n,n)]
    "(Nat.add_le_add_right h (ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)).trans hr"
  let base := x[:33].toArray ++ #[mkNatLit 0,x[34]!,coeff,x[36]!,reserve]
  let source := x[:33].toArray ++ #[lowReserve,x[34]!,coeff,x[36]!,reserve]
  let high := x[:33].toArray ++ #[rawReserve] ++ x[34:].toArray
  return (base,source,high)

elab "retain_original_base_budget " mode:num : command => liftTermElabM do
  withActualInverse fun d => withTransparency .default do
    let fixed := d.parameters[:44].toArray
    let (args,source,_) ← profileArguments d
    let S := app (nativeBase ++ `fieldS) args
    let C := app (nativeBase ++ `C) args
    let Craw := app (nativeSource ++ `Craw) source
    match mode.getNat with
    | 0 => discard <| save `Sbase fixed S true
    | 1 =>
        let named := app (root ++ `Sbase) fixed
        let h := app (nativeBase ++ `fieldS_ge_two) args
        let expected ← termWith [(`S,named)] "2 ≤ S"
        discard <| save `two_le_Sbase fixed h false (some expected)
    | 2 => discard <| save `Cbase fixed C true
    | 3 =>
        let named := app (root ++ `Cbase) fixed
        let h := app (nativeBase ++ `C_nonneg) args
        let expected ← termWith [(`C,named)] "∀ s : ℕ, 0 ≤ C s"
        discard <| save `Cbase_nonneg fixed h false (some expected)
    | 4 => discard <| save `Craw fixed Craw true
    | 5 =>
        let expected ← termWith [(`C,app (root ++ `Craw) fixed)] "∀ s : ℕ, 0 ≤ C s"
        discard <| save `Craw_nonneg fixed (app (nativeSource ++ `Craw_nonneg) source) false (some expected)
    | _ => throwError "original base: unknown retained budget field"

elab "retain_original_base_inputs " mode:num : command => liftTermElabM do
  withActualInverse fun d => withTransparency .default do
    let p := d.parameters
    let (_,source,high) ← profileArguments d
    let raw := app `JanetCartan.PhysicalBackground.NativeAdmission.raw d.native39
    match mode.getNat with
    | 0 =>
        let oldRaw ← bodyAt `JanetCartan.PhysicalBackground.NativeAdmission.raw d.native39
        unless oldRaw.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent 47 do
          throwError "original base: changed original raw47"
        let h := app `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent_mem oldRaw.getAppArgs
        let type ← inferType h
        let expected := type.replace fun e => if e == oldRaw then some raw else none
        discard <| save `raw_mem p h false (some expected)
    | 1 =>
        let sourceRaw := app (nativeSource ++ `raw) high
        discard <| save `raw_high_eq p (← mkEqRefl raw) false (some (← mkEq raw sourceRaw))
    | 2 =>
        let sourceArgs := source ++ d.source45[38:].toArray
        let sourceRaw := app (nativeSource ++ `raw) sourceArgs
        let C := app (nativeSource ++ `Craw) source
        let namedC := app (root ++ `Craw) p[:44].toArray
        let h := app (nativeSource ++ `raw_grade_profile) sourceArgs
        let expected := (← inferType h).replace fun e =>
          if e == sourceRaw then some raw else if e == C then some namedC else none
        discard <| save `raw_grade_profile p h false (some expected)
    | 3 =>
        let cancel ← bodyAt (measured ++ `on_exterior_plateau) d.native39
        unless cancel.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
          throwError "original base: changed cancellation64"
        let c := cancel.getAppArgs
        let tail ← instantiateForall (← getConstInfo `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear).type p
        forallBoundedTelescope tail (some 2) fun later _ => do
          let linear ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear (p ++ later)
          unless linear.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
            throwError "original base: changed original source linear28"
          let e := linear.getAppArgs
          let expectedSmooth ← termWith [(`chi,e[14]!)] "IsSmoothPeriodic (chi : Torus _ → ℝ)"
          unless ← isDefEq (← inferType e[17]!) expectedSmooth do
            throwError "original base: source cutoff's actual smoothness changed"
          let V := app (measured ++ `Vbase) d.native39
          let actualBase ← mkAppM `JanetCartan.PhysicalBackground.baseVariation #[e[14]!,raw,c[34]!,c[57]!]
          discard <| save `base_eq_source_initialization p (← mkEqRefl V) false (some (← mkEq V actualBase))
    | _ => throwError "original base: unknown actual raw/input field"

elab "specialize_original_base_wide_profile " mode:num : command => liftTermElabM do
  withActualInverse fun d => withTransparency .default do
    let p := d.parameters
    let fixed := p[:44].toArray
    let (args,_,_) ← profileArguments d
    let S := app (root ++ `Sbase) fixed
    let reached ← termWith [(`S,S),(`R0,p[44]!)] "S ≤ R0"
    withLocalDeclNoLocalInstanceUpdate `hBaseReached .default reached fun hReached => do
      let fullArgs := args ++ d.source45[38:].toArray ++ #[hReached]
      let V := app (measured ++ `Vbase) d.native39
      let cancel ← bodyAt (measured ++ `on_exterior_plateau) d.native39
      unless cancel.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
        throwError "original base: changed actual cancellation64"
      let F := cancel.getAppArgs[34]!
      let n := d.native39[0]!
      let hn := d.native39[1]!
      let geo (key : Name) := app (`JanetCartan.PhysicalSeed.OriginalBoundary ++ key) #[n,hn]
      let fields := [(`F,F),(`V,V),(`b,geo `b),(`R,geo `R),(`C,app (root ++ `Cbase) fixed),
        (`T,app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!])]
      match mode.getNat with
      | 0 =>
          let expected ← termWith fields "ContDiffOn ℝ ∞ V (ball 0 R)"
          discard <| save `Vbase_smooth_wide (p.push hReached) (app (nativeBase ++ `smooth) fullArgs) false (some expected)
      | 1 =>
          let expected ← termWith fields
            "∀ s : ℕ, cNorm (closedBall 0 b) s V + cNorm (closedBall 0 b) s (linearizedMetric F V) ≤ C s * T ^ s"
          discard <| save `base_strain_profile_wide (p.push hReached)
            (app (nativeBase ++ `base_strain_profile) fullArgs) false (some expected)
      | 2 =>
          let Gref := app `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref d.native39[:23].toArray
          let hV := app (root ++ `Vbase_smooth_wide) (p.push hReached)
          let proof ← termWith (fields ++ [(`Gref,Gref),(`u,p[47]!),(`hV,hV)])
            ("(AmbientResponse.contDiffOn_linearizedMetric isOpen_ball " ++
             "(RevisedGlobal.contDiffOn_finiteMap Gref.contDiff.contDiffOn u) hV : " ++
             "ContDiffOn ℝ ∞ (linearizedMetric F V) (ball 0 R))")
          discard <| save `strain_smooth_wide (p.push hReached) proof
      | 3 =>
          let D := app (root ++ `Dsmooth) fixed
          let r := app (root ++ `rBuffer) fixed
          let hV := app (root ++ `Vbase_smooth_wide) (p.push hReached)
          let hstrain := app (root ++ `strain_smooth_wide) (p.push hReached)
          let bound := app (root ++ `base_strain_profile_wide) (p.push hReached)
          let h := app (root ++ `buffer_containments) fixed
          let proof ← termWith (fields ++ [(`n,n),(`D,D),(`r,r),(`hV,hV),(`hstrain,hstrain),(`bound,bound),(`h,h)])
            ("(by\n" ++
             "  intro s\n" ++
             "  have hv := cNorm_mono_set_of_contDiffAt h.2.2.1 (isCompact_closedBall (0 : Euclidean n) b)\n" ++
             "    (fun x hx ↦ (hV.contDiffAt (isOpen_ball.mem_nhds (h.2.2.2 hx))).of_le (by simp : (s : ℕ∞ω) ≤ ∞))\n" ++
             "  have hs := cNorm_mono_set_of_contDiffAt h.2.2.1 (isCompact_closedBall (0 : Euclidean n) b)\n" ++
             "    (fun x hx ↦ (hstrain.contDiffAt (isOpen_ball.mem_nhds (h.2.2.2 hx))).of_le (by simp : (s : ℕ∞ω) ≤ ∞))\n" ++
             "  exact (add_le_add hv hs).trans (bound s)\n" ++
             "  : ∀ s : ℕ, cNorm (closedBall (0 : Euclidean n) r) s V + " ++
             "cNorm (closedBall (0 : Euclidean n) r) s (linearizedMetric F V) ≤ C s * T ^ s)")
          discard <| save `base_strain_profile_buffer (p.push hReached) proof
      | 4 =>
          let D := app (root ++ `Dsmooth) fixed
          let hV := app (root ++ `Vbase_smooth_wide) (p.push hReached)
          let h := app (root ++ `buffer_containments) fixed
          let proof ← termWith (fields ++ [(`n,n),(`D,D),(`hV,hV),(`h,h)])
            "(hV.mono (h.2.1.trans (ball_subset_closedBall.trans h.2.2.2)) : ContDiffOn ℝ ∞ V (D.chart n))"
          discard <| save `Vbase_smooth_physical_chart (p.push hReached) proof
      | _ => throwError "original base: unknown actual field profile"

end JanetCartan.PhysicalMean.OriginalCanonicalBaseProfilesTemplate
end

