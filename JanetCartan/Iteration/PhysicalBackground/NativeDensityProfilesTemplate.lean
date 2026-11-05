module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-! SAME admitted density and positive initial profiles. The native raw producer
is instantiated at reserve rDensity+3+(n-1)+2; synthesis spends precisely that
one fixed shift, and the positive square root preserves rDensity. Consumer:
`exists_history_retained_normal_coefficient_profiles` at its original Rr.
All constants close before history; there is no high-density input premise. -/

public meta section
namespace JanetCartan.PhysicalBackground.NativeDensityProfilesTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

private def targetNS := `JanetCartan.PhysicalBackground.NativeDensityProfiles

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do
    throwError "native density profiles: changed same-density target {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasFVar || type.hasFVar || value.hasMVar || type.hasMVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native density profiles: open or future-history dependence in {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

elab "realize_native_density_high_profiles" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalBackground.NativeSourceProfiles
  let admission := `JanetCartan.PhysicalBackground.NativeAdmission
  let density := `JanetCartan.PhysicalBackground.NativeDensity
  let info ← getConstInfo (source ++ `raw)
  forallBoundedTelescope info.type (some 33) fun fixed _ => do
    unless fixed.size == 33 do throwError "native density profiles: expected original admission33 prefix"
    let original := fixed[:21].toArray
    let n := original[0]!
    withLocalDeclD `rDensity (mkConst ``Nat) fun rDensity => do
      let rawReserve ← termWith [(`n, n), (`rDensity, rDensity)]
        "rDensity + (3 + (n - 1)) + 2"
      let atReserve := mkAppN (mkConst (source ++ `raw)) (fixed.push rawReserve)
      forallTelescope (← inferType atReserve) fun rest _ => do
        unless rest.size == 11 do
          throwError "native density profiles: expected coefficient4/history6/operator-scale1 tail"
        let sourceArgs := fixed ++ #[rawReserve] ++ rest
        let inputs := fixed ++ #[rDensity] ++ rest
        let before := fixed ++ #[rDensity] ++ rest[:4].toArray
        let sourceBefore := fixed ++ #[rawReserve] ++ rest[:4].toArray
        let admittedArgs := fixed ++ rest[4:10].toArray
        let src (name : Name) := mkAppN (mkConst (source ++ name)) sourceArgs
        let adm (name : Name) := mkAppN (mkConst (admission ++ name)) admittedArgs
        let raw := src `raw
        unless ← isDefEq raw (adm `raw) do
          throwError "native density profiles: high and admitted raw outputs differ"
        let order := mkAppN (mkConst (admission ++ `admissionOrder)) original
        let C := mkAppN (mkConst (density ++ `admissionC)) (original.push order)
        let hC ← mkAppM ``And.left
          #[mkAppN (mkConst (density ++ `admission_mask_spec)) (original.push order)]
        let Craw := mkAppN (mkConst (source ++ `Craw)) sourceBefore
        let hCraw := mkAppN (mkConst (source ++ `Craw_nonneg)) sourceBefore
        let labelC ← store `labelC before (← termWith [(`n, n), (`C, C), (`Craw, Craw)]
          "fun s : ℕ ↦ C s * Craw (s + (3 + (n - 1)) + 2)") true
        let hLabelC ← store `labelC_nonneg before (← termWith
          [(`n, n), (`labelC, labelC), (`hC, hC), (`hCraw, hCraw)]
          "(fun s ↦ mul_nonneg (hC s).le (hCraw (s + (3 + (n - 1)) + 2)) : ∀ s, 0 ≤ labelC s)")
        let labels := adm `labels
        let labelsType ← whnf (← inferType labels)
        let .forallE _ index _ _ := labelsType |
          throwError "native density profiles: original label carrier index disappeared"
        let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[rest[4]!, rest[6]!]
        let hScale ← termWith [(`R0, rest[4]!), (`stage, rest[6]!),
            (`hThreshold, mkAppN (mkConst (admission ++ `hS)) fixed[:32].toArray),
            (`hReached, rest[5]!)]
          "(one_le_currentCoefficientScale (by linarith [hThreshold.trans hReached]) stage : 1 ≤ currentCoefficientScale R0 stage)"
        withLocalDeclD `i index fun i => do
          let labelEstimate := mkApp (adm `label_estimate) i
          let Kvalue ← forallBoundedTelescope (← inferType labelEstimate) (some 1) fun _ type => do
            let some norm := type.find? (·.isAppOf `JanetCartan.cNorm) |
              throwError "native density profiles: original label norm lost its compact"
            let args := norm.getAppArgs
            pure args[args.size - 3]!
          let K ← store `labelSet (original.push i) Kvalue true
          unless Kvalue.isAppOf `Metric.closedBall do
            throwError "native density profiles: label compact is not the original closed ball"
          let kargs := Kvalue.getAppArgs
          let hK ← store `labelSet_compact (original.push i)
            (← mkAppM `ProperSpace.isCompact_closedBall #[kargs[kargs.size - 2]!, kargs.back!])
          let v := mkApp (adm `v) i
          let profile ← mkAppM `JanetCartan.PhysicalBackground.label_profile_of_raw_profile
            #[K, raw, v, C, Craw, ← termWith [(`hC, hC)] "fun s : ℕ ↦ (hC s).le",
              labelEstimate, rDensity, src `raw_grade_profile]
          let target ← termWith [(`K, K), (`label, mkApp labels i), (`rDensity, rDensity),
              (`scale, scale), (`labelC, labelC)]
            "HasDerivativeProfile K label rDensity scale labelC"
          let profile ← store `label_profile (inputs.push i) profile false (some target)
          let positiveExists ← mkAppM `JanetCartan.PhysicalBackground.exists_positive_initial_profile
            #[K, hK, ← termWith [] "(1 : ℝ)", labelC, hLabelC]
          let initialC ← store `initialC (before.push i)
            (← mkAppM ``Classical.choose #[positiveExists]) true
          let initialSpec ← mkAppM ``Classical.choose_spec #[positiveExists]
          discard <| store `initialC_nonneg (before.push i) (← mkAppM ``And.left #[initialSpec])
          let range ← termWith [(`K, K), (`hRange, mkApp (adm `labels_range) i)]
            "fun p (_ : p ∈ K) ↦ hRange p"
          let unitProfile := mkAppN (← mkAppM ``And.right #[initialSpec])
            #[mkApp labels i, mkApp (adm `labels_smooth) i, range, scale, hScale, rDensity, profile]
          let unitSmooth ← termWith [(`hSmooth, mkApp (adm `labels_smooth) i),
              (`hRange, mkApp (adm `labels_range) i)]
            "(positiveDensityAmplitude_properties (show (0 : ℝ) < 1 by norm_num) hSmooth hRange).1"
          let hSigma ← termWith [(`hs, fixed[23]!)] "(And.left hs).le"
          let initialProfile ← mkAppM `JanetCartan.PhysicalBackground.native_positive_initial_profile_scaled
            #[K, fixed[21]!, hSigma, mkApp labels i, unitSmooth, rDensity, scale, initialC, unitProfile]
          let initial ← termWith [(`sigma, fixed[21]!), (`label, mkApp labels i)]
            "fun p ↦ positiveDensityAmplitude sigma (label p)"
          let initial ← store `initial (inputs.push i) initial true
          let initialTarget ← termWith [(`K, K), (`initial, initial), (`rDensity, rDensity),
              (`sigma, fixed[21]!), (`scale, scale), (`initialC, initialC)]
            "HasDerivativeProfile K initial rDensity scale (fun s ↦ sigma * initialC s)"
          discard <| store `initial_profile (inputs.push i) initialProfile false (some initialTarget)
  logInfo "same admitted v and positive initial profile: synthesis shift n+4 paid once, square root preserves rDensity, constants before history"

end JanetCartan.PhysicalBackground.NativeDensityProfilesTemplate
end
