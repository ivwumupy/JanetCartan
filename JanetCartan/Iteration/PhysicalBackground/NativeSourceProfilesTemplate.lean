module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Literal native measured-source and zero-inverse high profiles

Consumer: the SAME smooth density/positive initial profile in
`app:ch_background:prop:bg-current`. All analytic inputs are instantiated
from the actual native map, coefficient, whole-chi mean and inverse producers.
Only additional NUMERICAL reserve and prehistory threshold inequalities occur.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeSourceProfilesTemplate
open Lean Meta Elab Command Term
private def termWith (bindings : List (Name × Expr)) (code : String)
    (target? : Option Expr := none) : TermElabM Expr := do
  try
    NativeReferenceSourceTemplate.termWith bindings code target?
  catch error =>
    throwError "native source profiles local term `{code}`: {error.toMessageData}"

private def targetNS := `JanetCartan.PhysicalBackground.NativeSourceProfiles

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do throwError "native source profiles: target changed {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasFVar || type.hasFVar || value.hasMVar || type.hasMVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native source profiles: open or future-history dependence in {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

private def mapProfileCode : String :=
  "(by\n" ++
  "  intro s\n" ++
  "  have hm := cNorm_mono_set (hMapBuffer.trans ball_subset_closedBall) (isCompact_closedBall _ _) (hF.of_le (by simp : (s : ℕ∞ω) ≤ ∞))\n" ++
  "  exact hm.trans ((hMapProfile s).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hScale (by omega)) (hA s)))\n" ++
  "  : HasDerivativeProfile K F (rSource + 2) scale Amap)"

private def frameProfileCode : String :=
  "(by\n" ++
  "  intro s\n" ++
  "  have he := ResponseTransfer.DiagonalPdo.cNorm_affineFrameExtension_on_subset ext isOpen_ball hExtChart Q hQ hKext s\n" ++
  "  have hp := hExtended s\n" ++
  "  change cNorm K s (affineFrameExtension ext Q) ≤ AQ s * scale ^ (s - rCoeff) at hp\n" ++
  "  rw [he] at hp\n" ++
  "  exact hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hScale (by omega)) (hAQ s))\n" ++
  "  : HasDerivativeProfile K Q rSource scale AQ)"

elab "realize_native_measured_source_high_profiles" : command => liftTermElabM do
  let admission := `JanetCartan.PhysicalBackground.NativeAdmission
  let native := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let density := `JanetCartan.PhysicalBackground.NativeDensity
  let reference := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let geometry := `JanetCartan.PhysicalBackground.NativeSourceGeometry
  let coefficients := `JanetCartan.PhysicalBackground.NativeCoefficientProfiles
  let leading := `JanetCartan.PhysicalInitialization.CurrentLeading
  let leadingProfile := `JanetCartan.PhysicalBackground.NativeLeadingProfiles
  let mean := `JanetCartan.PhysicalBackground.NativeMeanProfiles
  let originalCurrent := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let boundary := `JanetCartan.PhysicalSeed.OriginalBoundary
  let rawInfo ← getConstInfo (admission ++ `raw)
  forallBoundedTelescope rawInfo.type (some 39) fun all _ => do
    unless all.size == 39 do throwError "native source profiles: expected admission39"
    let fixed := all[:31].toArray
    let original := all[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!, original[1]!, original[20]!]
    let selected := original.set! 20 capped
    let src (name : Name) := mkAppN (mkConst (reference ++ name)) selected
    let originalField (name : Name) := mkAppN (mkConst (boundary ++ name)) original[:2].toArray
    let geo (name : Name) := mkAppN (mkConst (geometry ++ name)) original
    let n := original[0]!
    let rawBody := ((rawInfo.value! (allowOpaque := true)).beta all).headBeta
    unless rawBody.isAppOfArity (native ++ `rawCurrent) 47 do
      throwError "native source profiles: changed actual native raw47"
    let nativeArgs := rawBody.getAppArgs
    let datumBody := (((← getConstInfo (native ++ `measuredDatum)).value!
      (allowOpaque := true)).beta nativeArgs).headBeta
    unless datumBody.isAppOfArity `JanetCartan.PhysicalBackground.measuredSourceToL2 8 do
      throwError "native source profiles: source is not literal cutoff1/factor2 measurement"
    let datumArgs := datumBody.getAppArgs
    let Q := datumArgs[4]!
    let indexValue := mkAppN (mkConst (density ++ `geometryIndex)) original
    let index ← inferType indexValue
    let mut current := mkApp (mkAppN (mkConst (admission ++ `current)) all) indexValue
    for _ in [:8] do
      if current.isAppOfArity (leading ++ `Selected.current) 38 then break
      let some name := current.getAppFn.constName? |
        throwError "native source profiles: nonconstant current alias"
      let some body := (← getConstInfo name).value? (allowOpaque := true) |
        throwError "native source profiles: unavailable current alias {name}"
      current := (body.beta current.getAppArgs).headBeta
    unless current.isAppOfArity (leading ++ `Selected.current) 38 do
      throwError "native source profiles: lost actual selected leading current"
    let leadingArgs := current.getAppArgs
    for j in [:31] do
      unless ← isDefEq leadingArgs[j]! fixed[j]! do
        throwError "native source profiles: native leading datum {j} changed"
    let cellCurrent := (((← getConstInfo (leading ++ `Selected.current)).value!
      (allowOpaque := true)).beta leadingArgs).headBeta
    unless cellCurrent.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingCell.current 36 do
      throwError "native source profiles: expected retained leading current36"
    let hdata := cellCurrent.getAppArgs[34]!
    unless hdata.isAppOfArity (leading ++ `AtPatch.fact0) 38 do
      throwError "native source profiles: expected the exact retained AtPatch data"
    let patch := hdata.getAppArgs.back!
    let Amap := mkAppN (mkConst (leading ++ `Amap)) (fixed.push patch)
    let hA := mkAppN (mkConst (leading ++ `fact1)) (fixed.push patch)
    let F := mkAppN (mkConst (leadingProfile ++ `map)) leadingArgs
    let hF := mkAppN (mkConst (leadingProfile ++ `map_smooth)) leadingArgs
    let rawFrame ← mkAppM `JanetCartan.ProjectedStressFrame.projectedStress #[F]
    unless ← isDefEq Q rawFrame do
      throwError "native source profiles: actual source frame differs from the native physical map"
    let mu := src `r
    let hr := src `hr
    let K ← termWith [(`n, n), (`mu, mu)] "closedBall (0 : Euclidean n) (4 * mu)"
    let W ← termWith [(`n, n), (`mu, mu)] "ball (0 : Euclidean n) (5 * mu)"
    let hK ← termWith [(`K, K)] "(isCompact_closedBall _ _ : IsCompact K)"
    let hW ← termWith [(`W, W)] "(isOpen_ball : IsOpen W)"
    let hKW ← termWith [(`K, K), (`W, W), (`mu, mu), (`hr, hr)]
      "(closedBall_subset_ball (by linarith only [(show 0 < mu from hr)]) : K ⊆ W)"
    let theta ← termWith [(`n, n), (`hr, hr)]
      "(FixedCutoffs.physical (n := n) hr 1 : Euclidean n → ℝ)"
    let hTheta ← termWith [(`n, n), (`hr, hr)] "(show ContDiff ℝ ∞ (FixedCutoffs.physical (n := n) hr 1) from (FixedCutoffs.physical (n := n) hr 1).contDiff)"
    let Cmean := mkAppN (mkConst (mean ++ `C)) fixed
    let hCmean := mkAppN (mkConst (mean ++ `C_nonneg)) fixed
    withLocalDeclD `rSource (mkConst ``Nat) fun rSource => do
      withLocalDeclD `rCoeff (mkConst ``Nat) fun rCoeff => do
        let hOrderType ← termWith [(`rSource, rSource), (`rCoeff, rCoeff)] "rSource ≤ rCoeff"
        withLocalDeclD `hSourceCoeff hOrderType fun hSourceCoeff => do
          let hCoeffType ← termWith [(`rCoeff, rCoeff), (`rStar, fixed[26]!)] "2 + rCoeff ≤ rStar"
          withLocalDeclD `hCoeff hCoeffType fun hCoeff => do
            let hReserveType ← termWith [(`n, n), (`rSource, rSource), (`rStar, fixed[26]!)]
              "rSource + canonicalCarrierLowOrder n ≤ rStar"
            withLocalDeclD `hSourceReserve hReserveType fun hReserve => do
              let orders := #[rSource, rCoeff, hSourceCoeff, hCoeff, hReserve]
              let before := all[:33].toArray ++ orders
              let hStar ← termWith [(`n, n), (`rSource, rSource), (`rStar, fixed[26]!), (`hReserve, hReserve)]
                "(by change rSource + (2 * (n + 1) + 14) ≤ rStar at hReserve; omega : 8 ≤ rStar)"
              let coefficientArgs := fixed[:23].toArray ++ #[fixed[24]!, fixed[25]!, fixed[26]!,
                rCoeff, fixed[27]!, hStar, hCoeff, fixed[29]!]
              let coef (name : Name) := mkAppN (mkConst (coefficients ++ name)) coefficientArgs
              let Gref := mkAppN (mkConst (coefficients ++ `Gref)) fixed[:23].toArray
              let Fcoef ← termWith [(`Gref, Gref), (`u, all[36]!)] "RevisedGlobal.finiteMap Gref.map u"
              unless ← isDefEq Fcoef F do
                throwError "native source profiles: coefficient producer is not on the identical physical map/reference"
              let Sop ← store `operatorS before (coef `S) true
              let nativeS := mkAppN (mkConst (admission ++ `S)) all[:32].toArray
              let S ← store `S before (← termWith [(`nativeS, nativeS), (`Sop, Sop)] "max nativeS Sop") true
              discard <| store `hS before (← termWith [(`S, S), (`hnative, mkAppN
                  (mkConst (admission ++ `hS)) all[:32].toArray)]
                "(hnative.trans (le_max_left _ _) : 2 ≤ S)")
              discard <| store `S_le_native_input before (← termWith [(`nativeS, nativeS), (`S, S)]
                "(le_max_left _ _ : nativeS ≤ S)")
              discard <| store `S_le_operator_input before (← termWith [(`Sop, Sop), (`S, S)]
                "(le_max_right _ _ : Sop ≤ S)")
              let residualFn := mkAppN (mkConst `JanetCartan.PhysicalBackground.exists_cutPhysicalResidual_profile)
                #[n, mkApp (mkConst `JanetCartan.embeddingDimension) n]
              let residualApp := mkAppN residualFn
                #[K, W, hK, hW, hKW, theta, hTheta, src `X0, src `X0_smooth, Amap, coef `AQ, Cmean,
                  hA, coef `AQ_nonneg, hCmean]
              let residualExists ← store `residual_exists before residualApp false (some (← inferType residualApp))
              let Cres ← store `residualC before (← mkAppM ``Classical.choose #[residualExists]) true
              let residualSpec ← mkAppM ``Classical.choose_spec #[residualExists]
              let hCres ← store `residualC_nonneg before (.proj ``And 0 residualSpec)
              let Csource ← store `Csource before (← termWith [(`n, n), (`Cres, Cres)]
                "fun s : ℕ ↦ (2 * Real.sqrt (s.factorial : ℝ) * Real.sqrt ((sobolevMultiindices n s).card : ℝ)) * Cres s") true
              let hCsource ← store `Csource_nonneg before (← termWith [(`Csource, Csource), (`hCres, hCres)]
                "(by intro s; change 0 ≤ _ * _; exact mul_nonneg (by positivity) (hCres s) : ∀ s, 0 ≤ Csource s)")
              let Czero := mkAppN (mkConst (originalCurrent ++ `Czero)) fixed
              let hCzero := mkAppN (mkConst (originalCurrent ++ `nonnegative3)) fixed
              let Craw ← store `Craw before (← termWith [(`Czero, Czero), (`Csource, Csource)]
                "fun s : ℕ ↦ Czero s * (Csource s + Csource 0)") true
              discard <| store `Craw_nonneg before (← termWith [(`Craw, Craw), (`hCzero, hCzero), (`hCsource, hCsource)]
                "(fun s ↦ mul_nonneg (hCzero s) (add_nonneg (hCsource s) (hCsource 0)) : ∀ s, 0 ≤ Craw s)")
              let hopType ← termWith [(`Sop, Sop), (`R0, all[33]!)] "Sop ≤ R0"
              withLocalDeclD `hOperatorScale hopType fun hOp => do
                let inputs := before ++ all[33:].toArray ++ #[hOp]
                let scale := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[all[33]!, all[35]!]
                let hScale ← termWith [(`R0, all[33]!), (`stage, all[35]!),
                    (`hNative, mkAppN (mkConst (admission ++ `hS)) all[:32].toArray), (`hReached, all[34]!)]
                  "(one_le_currentCoefficientScale (by linarith [hNative.trans hReached]) stage : 1 ≤ currentCoefficientScale R0 stage)"
                let common := [(`n, n), (`K, K), (`W, W), (`mu, mu), (`hr, hr), (`F, F), (`hF, hF),
                  (`Q, Q), (`ext, original[4]!), (`hcenter, original[5]!), (`hradius, original[6]!),
                  (`b, originalField `b), (`R, originalField `R), (`hbR, originalField `b_lt_R),
                  (`Amap, Amap), (`hA, hA), (`AQ, coef `AQ), (`hAQ, coef `AQ_nonneg),
                  (`scale, scale), (`hScale, hScale), (`rSource, rSource), (`rCoeff, rCoeff),
                  (`rStar, fixed[26]!), (`hSourceCoeff, hSourceCoeff), (`hCoeff, hCoeff), (`hReserve, hReserve)]
                let mapProfile ← termWith (common ++ [(`hMapBuffer, geo `measurement_four_buffer),
                    (`hMapProfile, mkAppN (mkConst (leadingProfile ++ `map_profile)) leadingArgs)]) mapProfileCode
                let hQ ← termWith (common ++ [(`hFon, mkAppN (mkConst (density ++ `current_hF_on)) nativeArgs),
                    (`hi, mkAppN (mkConst (density ++ `current_immersion)) nativeArgs),
                    (`hrank, mkAppN (mkConst (density ++ `current_fullNormalRank)) nativeArgs)])
                  "(contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress isOpen_ball hFon hi hrank) : ContDiffOn ℝ ∞ Q (ball 0 R))"
                let hExtChart ← termWith common
                  "(by rw [hcenter, hradius]; exact closedBall_subset_ball hbR : closedBall ext.center ext.radius ⊆ ball 0 R)"
                let hKext ← termWith (common ++ [(`buffer, geo `measurement_buffer_qext)])
                  "((closedBall_subset_closedBall (by linarith only [(show 0 < mu from hr)])).trans buffer : K ⊆ closedBall ext.center ext.radius)"
                let history := #[all[33]!, hOp] ++ all[35:].toArray
                let coefficientProof := mkAppN (coef `continuation) history
                let rest := Expr.proj ``And 1 (Expr.proj ``And 1 coefficientProof)
                let extendedProfile := Expr.proj ``And 0 (mkAppN rest #[K, hK])
                let frameProfile ← termWith (common ++ [(`hExtChart, hExtChart), (`hQ, hQ),
                    (`hKext, hKext), (`hExtended, extendedProfile)]) frameProfileCode
                let H := mkAppN (mkConst (mean ++ `zero_mean)) all
                let hH ← termWith (common ++ [(`H, H), (`hHsix, mkAppN (mkConst (mean ++ `smooth)) all)])
                  "(hHsix.mono (ball_subset_ball (by linarith only [(show 0 < mu from hr)])) : ContDiffOn ℝ ∞ H W)"
                let hQW ← mkAppM `ContDiffOn.mono #[hQ, geo `measurement_five_chart]
                let hLeadReserve ← termWith common
                  "(by change rSource + (2 * (n + 1) + 14) ≤ rStar at hReserve; omega : rSource + 14 ≤ rStar)"
                let meanProfile := mkAppN (mkConst (mean ++ `profile))
                  (all[:33].toArray ++ #[rSource, hLeadReserve] ++ all[33:].toArray)
                let hResidual := mkAppN (.proj ``And 1 residualSpec)
                  #[F, Q, H, hF, hQW, hH, rSource, scale, hScale, mapProfile, frameProfile, meanProfile]
                let expectedResidual ← termWith (common ++ [(`theta, theta), (`Ractual, datumArgs[5]!), (`Cres, Cres)])
                  "HasDerivativeProfile K (cutReducedSource theta Q Ractual) rSource scale Cres"
                unless ← isDefEq (← inferType hResidual) expectedResidual do
                  throwError "native source profiles: actual cutoff1 tangent-plus-mean residual changed"
                let hResidual ← store `cut_residual_profile inputs hResidual false (some expectedResidual)
                let datum ← store `measuredSource inputs (mkAppN (mkConst (admission ++ `measuredSource)) all) true
                let raw ← store `raw inputs (mkAppN (mkConst (admission ++ `raw)) all) true
                discard <| store `measured_source_mem inputs
                  (mkAppN (mkConst (native ++ `measuredDatum_mem)) nativeArgs)
                discard <| store `raw_mem inputs
                  (mkAppN (mkConst (native ++ `rawCurrent_mem)) nativeArgs)
                let gradeBound ← withLocalDeclD `s (mkConst ``Nat) fun s => do
                  let measuredBound := mkAppN
                    (mkConst `JanetCartan.PhysicalBackground.measuredSourceToL2_gradeNorm_le) (datumArgs ++ #[s])
                  let factorNonneg := mkAppN
                    (mkConst `JanetCartan.PhysicalBackground.native_measured_grade_factor_nonneg) #[n, s]
                  let hp ← mkAppM `JanetCartan.PhysicalBackground.native_measured_grade_line
                    #[factorNonneg, measuredBound, mkApp hResidual s]
                  mkLambdaFVars #[s] hp
                let sourceTarget ← termWith [(`n,n), (`datum,datum), (`A,Csource), (`T,scale), (`r,rSource)]
                  "∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s datum ≤ A s * T ^ (s - r)"
                let hSource ← store `measured_source_grade_profile inputs gradeBound false (some sourceTarget)
                let hZero := mkAppN (mkConst (native ++ `current_zero_estimate)) nativeArgs
                let zeroScalar ← withLocalDeclD `s (mkConst ``Nat) fun s => do
                  let type ← Core.betaReduce (← zetaReduce (← inferType (mkApp hZero s)))
                  unless type.isAppOf ``LE.le do
                    throwError "native source profiles: zero estimate is not an inequality"
                  let a := type.getAppArgs
                  let lhs := a[a.size - 2]!
                  unless lhs.isAppOf ``HAdd.hAdd || lhs.isAppOf ``Add.add do
                    throwError "native source profiles: zero estimate lost its combined norm sum"
                  let pieces := lhs.getAppArgs
                  let normalNorm := pieces[pieces.size - 2]!
                  let rawNorm := pieces.back!
                  unless normalNorm.isAppOf `JanetCartan.GradedScale.gradeNorm &&
                      rawNorm.isAppOf `JanetCartan.GradedScale.gradeNorm do
                    throwError "native source profiles: changed combined zero-inverse estimate"
                  unless ← isDefEq rawNorm.getAppArgs.back! raw do
                    throwError "native source profiles: zero bound concerns a different raw inverse"
                  store `zeroScalar inputs normalNorm.getAppArgs.back! true
                let zeroType ← Core.betaReduce (← zetaReduce (← inferType (mkApp hZero (mkNatLit 0))))
                let rawScale := zeroType.getAppArgs
                let lhs := rawScale[rawScale.size - 2]!
                let rawNorm := lhs.getAppArgs.back!
                let some aug := rawNorm.find? (·.isAppOf `JanetCartan.CarrierSobolev.augmentedInputSobolevScale) |
                  throwError "native source profiles: augmented scalar scale disappeared"
                let low := mkApp (mkConst `JanetCartan.ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder) n
                let proof := mkAppN (mkConst `JanetCartan.PhysicalBackground.native_combined_zero_grades [.zero])
                  #[n, index, aug.getAppArgs[2]!, datum, zeroScalar, raw, scale, hScale, fixed[26]!, low,
                    rSource, hReserve, Czero, Csource, hCzero, hCsource, hSource, hZero]
                let spec ← store `zero_grade_spec inputs proof
                let bindings := [(`n,n), (`I,index), (`z,zeroScalar), (`h,raw), (`D,Craw), (`T,scale), (`r,rSource)]
                let combinedType ← termWith bindings
                  "∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s z + (CarrierSobolev.augmentedInputSobolevScale n I).gradeNorm s h ≤ D s * T ^ (s - r)"
                let rawType ← termWith bindings
                  "∀ s, (CarrierSobolev.augmentedInputSobolevScale n I).gradeNorm s h ≤ D s * T ^ (s - r)"
                let scalarType ← termWith bindings
                  "∀ s, (periodicSobolevScale n (Euclidean n)).gradeNorm s z ≤ D s * T ^ (s - r)"
                discard <| store `combined_zero_grade_profile inputs (.proj ``And 0 spec) false (some combinedType)
                discard <| store `raw_grade_profile inputs (.proj ``And 0 (.proj ``And 1 spec)) false (some rawType)
                discard <| store `zero_scalar_grade_profile inputs (.proj ``And 1 (.proj ``And 1 spec)) false (some scalarType)
  logInfo "actual cutoff1/factor2 source and same native zero inverse profiles; numerical-only extra reserves/threshold, constants before history, literal scale"

end JanetCartan.PhysicalBackground.NativeSourceProfilesTemplate
end
