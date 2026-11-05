module

public import JanetCartan.Iteration.PhysicalBackground.NativeAdmission
public import JanetCartan.Iteration.PhysicalBackground.NativeSourceGeometry
public import JanetCartan.Iteration.PhysicalBackground.RetainedMeasuredCancellation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement.Restriction
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# Actual measured cancellation on the original zero-inverse core

Apply the retained physical cancellation to the same `NativeAdmission.raw`,
positive density, current chart, factor-two datum, and exterior mask. The only
nondefinitional carrier transport is the explicit equality
`positiveDensityAmplitude σ 0 = σ` on the exact native test integral. No new
carrier frame, inverse, source or density is selected. The native exterior
plateau and the measurement cutoff both contain the original fixed half-ball
(`app:ch_background:prop:bg-current`, `app:ch_background:eq:bg-current-identity`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 1800000
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
open JanetCartan JanetCartan.PhysicalBackground JanetCartan.PositiveBackground
open JanetCartan.ContinuumRow JanetCartan.ContinuumRow.CanonicalConic
open JanetCartan.FrozenMenu JanetCartan.ActualCarriers JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open JanetCartan.ContinuumNormal

@[expose] public noncomputable section
namespace JanetCartan.PhysicalBackground

/-- The literal current geometric coefficient formula on the fixed chart core.
This local scalar calculation requires no reduction of the actual history. -/
theorem native_measured_coefficients_core {n N : ℕ} {mu : ℝ} (hr : 0 < mu) (hcell : 4 * mu < 1 / 2)
    (cut : Euclidean n → ℝ) (F : Euclidean n → Euclidean N)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j z, c j z = cut (centeredTorusRepresentative z) *
      GeometricProfile.geometricReducedCoefficients F (centeredTorusRepresentative z) j)
    (hcut : closedBall 0 (4*mu) ⊆ interior {x | cut x = 1}) :
    ∀ x ∈ closedBall 0 mu, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j := by
  intro x hx j
  have hx4 : x ∈ closedBall 0 (4 * mu) := closedBall_subset_closedBall (by linarith only [hr]) hx
  have hrep := PeriodicLocalL2.centeredTorusRepresentative_quotient
    (FixedCutoffs.closedBall_four_subset_cell hcell hx4)
  have hone : cut x = 1 := (show x ∈ {y | cut y = 1} from interior_subset (hcut hx4))
  rw [hc, hrep, hone, one_mul]


/-- Both hypotheses of the measured cancellation apply on the fixed original
inner half-ball, without narrowing a history-dependent core. -/
theorem native_measured_core_hooks {n : ℕ} {mu ri : ℝ} (hcell : 4 * mu < 1 / 2)
    (hi : 0 < ri) (hic : ri < 1 / 2) (hle : ri ≤ mu) :
    ∀ x ∈ closedBall (0 : Euclidean n) (ri / 2),
      x ∈ closedBall (0 : Euclidean n) mu ∧
      torusQuotient x ∈ interior {z | innerCutoff (n := n) hi hic z = 1} := by
  intro x hx
  have hc : 4 * (ri / 2) < 1 / 2 := by linarith only [hcell,hi,hle]
  refine ⟨closedBall_subset_closedBall ((half_le_self hi.le).trans hle) hx, ?_⟩
  rw [NormalizedFrozenGap.innerCutoff_eq_fixedPeriodic_half hi hic hc]
  exact torusQuotient_mem_fixedSourcePlateau (half_pos hi) hc hx


/-- The *restricted* bounded operator occurring in the original normal acts
on the same canonical carrier on the common measurement chart (`bg-T`). -/
theorem native_restricted_measured_test {n N : ℕ} (d : CarrierData n N)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (hcell : 4 * r < 1 / 2)
    (hlocal : 4 * a < 1 / 2) (hra : 6 * r < a)
    (hchart : d.outputChart = PeriodicLocalL2.torusChart (closedBall 0 (4 * a)))
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hmeas : d.measurementCutoff = FixedCutoffs.periodic ha hlocal 1)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ht : ∀ f : carrierInitialTestSpace n, V (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral d f.val) :
    ∀ f : carrierInitialTestSpace n,
      CommonMeasurement.restrictCarrier (FixedCutoffs.periodic hr hcell 1) V (carrierInitialTestToLp f) =ᵐ[volume]
      carrierTestIntegral (CommonMeasurement.commonChartData d (closedBall 0 (4*r))
        (FixedCutoffs.periodic hr hcell 1)) f.val := by
  obtain ⟨_, _, _, _, _, _, _, _, op⟩ :=
    NormalizedMeasurement.supplied_carrier_common_measurement d hr ha hcell hlocal hra hchart hpoint hmeas
  exact ((op V).2.1 ht).1

end JanetCartan.PhysicalBackground
end

public meta section
namespace JanetCartan.PhysicalBackground.NativeMeasuredCancellationApplication
open Lean Meta Elab Term Command
private def termWith (bindings : List (Name × Expr)) (code : String) (target? : Option Expr := none) : TermElabM Expr :=
  _root_.JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code target?

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do throwError "native measured cancellation: target changed {name}"
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar ||
      value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "native measured cancellation: dependence in {name}"
  let name := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation ++ name
  if data then
    addDecl (.defnDecl {name, type, value, levelParams := [], hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, type, value, levelParams := []}) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- Transport ONLY the zero initial scalar label of the exact carrier-test
integral. Neither the spatial current, the measure nor the operator changes. -/
private def actualUntwistedTest (spec sigma : Expr) : TermElabM Expr := do
  let act := Expr.proj ``And 0 spec
  forallBoundedTelescope (← inferType act) (some 1) fun ix _ => do
    let oldTest := Expr.proj ``And 0 (mkAppN act ix)
    let oldType ← inferType oldTest
    let some integ := oldType.find? (·.isAppOf `JanetCartan.ContinuumRow.carrierTestIntegral) |
      throwError "native cancellation: native test integral not found"
    let carrier := integ.getAppArgs[integ.getAppArgs.size-2]!
    let data := carrier.headBeta
    unless data.isAppOfArity `JanetCartan.ContinuumRow.CanonicalCarrier.data 18 do
      throwError "native cancellation: native test carrier18 changed"
    let dargs := data.getAppArgs
    let inType ← whnf (← inferType dargs[12]!)
    let zeroEq ← termWith [(`P,inType.bindingDomain!),(`sigma,sigma)]
      "(by funext p; simp [positiveDensityAmplitude] : (fun _ : P ↦ positiveDensityAmplitude sigma 0) = fun _ ↦ sigma)"
    let setter ← withLocalDeclD `j inType fun j => mkLambdaFVars #[j] (mkAppN data.getAppFn (dargs.set! 12 j))
    let dataEq ← mkAppM ``congrArg #[setter,zeroEq]
    unless ← isDefEq carrier (← inferType dataEq).getAppArgs[1]! do
      throwError "native cancellation: zero-label normalization concerns a different carrier"
    let property ← withLocalDeclD `d (← inferType carrier) fun d =>
      mkLambdaFVars #[d] (oldType.replace fun e => if e == carrier then some d else none)
    let propEq ← mkAppM ``congrArg #[property, dataEq]
    let lifted ← mkAppM ``Eq.mp #[propEq, oldTest]
    mkLambdaFVars ix lifted


elab "realize_native_measured_core_cancellation" : command => liftTermElabM do
  let adm := `JanetCartan.PhysicalBackground.NativeAdmission
  let native := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let srcNS := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let info ← getConstInfo (adm ++ `raw)
  forallBoundedTelescope info.type (some 39) fun all _ => do
    let original := all[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!, original[1]!, original[20]!]
    let selected := original.set! 20 capped
    let src (nm : Name) := mkAppN (mkConst (srcNS ++ nm)) selected
    let out (nm : Name) := mkAppN (mkConst (`JanetCartan.PhysicalBackground.OriginalOuterCutoff ++ nm)) selected
    let natArgs := (((info.value! (allowOpaque := true)).beta all).headBeta).getAppArgs
    let den (nm : Name) := mkAppN (mkConst (`JanetCartan.PhysicalBackground.NativeDensity ++ nm)) natArgs
    let admitted (nm : Name) := mkAppN (mkConst (adm ++ nm)) all
    let nat (nm : Name) := mkAppN (mkConst (native ++ nm)) natArgs
    let chart := mkAppN (mkConst (adm ++ `current)) all
    let ct ← whnf (← inferType chart)
    let index := ct.bindingDomain!
    let datum := (((← getConstInfo (native ++ `measuredDatum)).value! (allowOpaque := true)).beta natArgs).headBeta
    let some mean := datum.find? (·.isAppOfArity `JanetCartan.PositiveBackground.physicalDensityMean 7) | throwError "same physical mean missing"
    let meanArgs := mean.getAppArgs
    let n := original[0]!
    let geom (nm : Name) := mkAppN (mkConst (`JanetCartan.PhysicalBackground.NativeSourceGeometry ++ nm)) original
    let pick := mkAppN (mkConst `JanetCartan.PhysicalBackground.NativeDensity.geometryIndex) original
    let atPick := (← inferType (mkApp chart pick)).getAppArgs
    let static ← withLocalDeclD `i index fun i => do
      let args := (← inferType (mkApp chart i)).getAppArgs
      unless args.size == 15 do throwError "expected original chart15"
      args.mapM fun e => mkLambdaFVars #[i] e
    let hPtype := (← inferType (mkApp (src `hP) pick)).getAppArgs
    let names := [(`P, static[2]!), (`U₀, atPick[3]!), (`hU₀, atPick[4]!),
      (`T, src `T), (`Ω, static[6]!), (`K, static[7]!), (`p₀, static[8]!), (`Rc, static[9]!),
      (`M, static[10]!), (`τ, static[11]!), (`row, static[12]!), (`col, static[13]!),
      (`cP, hPtype[hPtype.size - 2]!), (`CP, hPtype.back!), (`hP, src `hP), (`hτ, src `hτ), (`hpatch, src `hpatch),
      (`r, src `r), (`hr, src `hr), (`hcell, src `hcell), (`χ, src `χ), (`hχ, src `χ_smooth), (`hχc, src `χ_compact),
      (`V, src `window), (`hV, src `window_open), (`hχV, src `χ_support), (`F, atPick[14]!),
      (`chart, chart), (`σ, all[21]!), (`hσ, ← mkAppM ``And.left #[all[22]!]), (`zRoot, src `root),
      (`θ₀, src `theta), (`am, src `am), (`width, src `width), (`ham, src `am_pos), (`hwidth, src `width_pos),
      (`hplateau, out `plateau), (`coeff, nat `coefficient), (`X₀, src `X0)]
    let spec := nat `Vzero_spec
    let hcoeff := Expr.proj ``And 0 (.proj ``And 1 spec)
    let hgap := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 (.proj ``And 1 spec)))
    let (gap, B, psi) ← forallBoundedTelescope (← inferType hgap) (some 1) fun _ type => do
      let args := type.getAppArgs
      let lhs := args[args.size - 2]!
      let some row := args.back!.find? (·.isAppOf `JanetCartan.ContinuumRow.augmentedRow) | throwError "same row lost"
      pure (lhs.getAppArgs[lhs.getAppArgs.size-2]!, row.getAppArgs[row.getAppArgs.size-2]!, row.getAppArgs.back!)
    let binds := [(`n, n), (`hn, original[1]!), (`mu, src `r), (`hr, src `hr), (`hSix, src `measurement_six_cell),
      (`ham, src `am_pos), (`hmua, src `measure_lt_carrier), (`zRoot, src `root), (`am, src `am), (`hInner, src `inner_support_product),
      (`hRphysical, src `product_radius_le_physical), (`hballSix, src `hball), (`ch, chart), (`pvalid, src `hP), (`W, src `window),
      (`oldV, src `Voriginal), (`P, static[2]!), (`hsmall, geom `measurement_five_chart), (`hFbig, den `current_hF_on),
      (`hibig, den `current_immersion), (`hrankbig, den `current_fullNormalRank), (`hFlow, src `product_flow),
      (`hProduct, src `hproduct), (`hRc, src `hRc), (`hTau, src `hτ), (`hFormula, nat `coefficient_formula),
      (`hPlateau, src `coefficient_cutoff_plateau), (`cf, src `coefficient_cutoff), (`hcell, src `hcell), (`hXglob, src `X0_smooth),
      (`hSourceGap, src `source_gap_pos), (`act, Expr.proj ``And 0 spec)]
    let consumer := `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation
    let mut t := (← getConstInfo consumer).type
    let mut args := #[]
    for j in [:60] do
      let .forallE name domain body _ := t | throwError "consumer binder missing {j}"
      let nm := name.eraseMacroScopes
      let localTerm (code : String) : TermElabM Expr := termWith binds code (some domain)
      let arg ← if j < 4 then pure meanArgs[j]!
        else if let some (_,x) := names.find? (fun y => y.1 == nm) then pure x
        else match nm with
        | `hfive => localTerm "by linarith only [(show 0 < mu from hr), (show 6 * mu < 1 / 2 from hSix)]"
        | `hphysical => localTerm ("by\n" ++
          "  intro a\n" ++
          "  let x : Euclidean n := EuclideanSpace.single ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 5) hn⟩ (5 * mu)\n" ++
          "  have hμ : 0 < mu := hr\n" ++
          "  have h₁ : 6 * mu < am a := hmua a\n" ++
          "  have h₂ : 0 < am a := ham a\n" ++
          "  have hn : ‖x‖ = 5 * mu := by simp [x, EuclideanSpace.single, PiLp.norm_single, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 5 * mu)]\n" ++
          "  have hx : x ∈ closedBall 0 (4 * am a) := by rw [mem_closedBall_zero_iff, hn]; linarith only [h₁,h₂,hμ]\n" ++
          "  let p0 := (zRoot a 0, FullPhaseCharts.ActualComparison.spectatorCenter (zRoot a))\n" ++
          "  have hp : p0 ∈ carrierSupport (zRoot a) (r := am a) := ⟨mem_closedBall_self (half_pos h₂).le, mem_closedBall_self (half_pos h₂).le⟩\n" ++
          "  have hh := (hInner a (q := (x,p0)) ⟨hx,hp⟩).1\n" ++
          "  rw [mem_ball_zero_iff, hn] at hh\n" ++
          "  exact hh.le.trans (hRphysical a)")
        | `hball => localTerm "by apply Set.Subset.trans _ hballSix; exact closedBall_subset_closedBall (show 4 * mu ≤ 6 * mu by linarith only [(show 0 < mu from hr)])"
        | `hVP => localTerm "by intro a p hp j; have hh : p ∈ originalOuterWindow (oldV a) (P a).radius := hp; exact (hh.2 j).trans_le (by change (P a).radius ≤ 3 * (P a).radius / 2; linarith only [(show 0 < (P a).radius from (pvalid a).1)])"
        | `hF => localTerm "hFbig.mono hsmall"
        | `himm => localTerm "fun x hx ↦ hibig x (hsmall hx)"
        | `hrank => localTerm "fun x hx ↦ hrankbig x (hsmall hx)"
        | `hflow => localTerm ("by\n" ++
          "  intro a p hp\n" ++
          "  have hh := hProduct a (q := p) ⟨closedBall_subset_closedBall (show 5*mu ≤ 6*mu by linarith only [(show 0 < mu from hr)]) (ball_subset_closedBall hp.1), hp.2⟩\n" ++
          "  exact (ch a).small_subset ((outputCylinder_spec (hRc a) (hTau a)).2 (hFlow a hh))")
        | `hcoeff => pure hcoeff
        | `hcoeff_core => pure (mkAppN (mkConst `JanetCartan.PhysicalBackground.native_measured_coefficients_core)
            #[n, meanArgs[1]!, src `r, src `hr, src `hcell, src `coefficient_cutoff, atPick[14]!, nat `coefficient,
              nat `coefficient_formula, src `coefficient_cutoff_plateau])
        | `ψ => pure psi
        | `gap => pure gap
        | `hgap_pos => localTerm "half_pos (half_pos hSourceGap)"
        | `hgap => pure hgap
        | `hX₀ => localTerm "hXglob.contDiffOn"
        | `B => pure B
        | `hB => do
          let test ← actualUntwistedTest spec all[21]!
          withLocalDeclD `i index fun i => do
            let di := mkApp (den `carrier) i
            let mut app := mkAppN (mkConst `JanetCartan.PhysicalBackground.native_restricted_measured_test)
              #[n, meanArgs[1]!, di, src `r, mkApp (src `am) i, src `hr, mkApp (src `am_pos) i,
                src `hcell, mkApp (src `carrier_cell) i, mkApp (src `measure_lt_carrier) i]
            for code in #["rfl", "by intro x hx; rfl", "rfl"] do
              let t ← whnf (← inferType app)
              unless t.isForall do throwError "missing native restriction geometry slot"
              app := mkApp app (← termWith [] code (some t.bindingDomain!))
            mkLambdaFVars #[i] (mkAppN app #[mkApp (nat `Vzero) i, mkApp test i])
        | _ => throwError "unmatched consumer binder {nm}"
      unless ← isDefEq (← inferType arg) domain do throwError "different native argument {nm}"
      args := args.push arg
      t := body.instantiate1 arg
    let mut proof := mkAppN (mkConst consumer) args
    for field in #[nat `rawCurrent_mem, admitted `v, admitted `smooth, admitted `ae] do
      let type ← whnf (← inferType proof)
      unless type.isForall && (← isDefEq (← inferType field) type.bindingDomain!) do throwError "native raw/v tail mismatch"
      proof := mkApp proof field
    -- Re-express the smoothness and cancellation on the exact public raw and
    -- the single public affine physical mean. No datum, X0, or row is selected.
    let raw := mkAppN (mkConst (adm ++ `raw)) all
    let Hp := mkAppN (mkConst (adm ++ `physicalMean)) all
    let F := atPick[14]!
    let V ← termWith [(`hCell, src `hcell), (`hR, src `hr), (`h, raw), (`F, F), (`X0, src `X0)]
      "baseVariation (FixedCutoffs.periodic hR hCell 2) h F X0"
    let V ← store `Vbase all V true
    let baseType ← termWith [(`mu, src `r), (`V, V)] "ContDiffOn ℝ ∞ V (ball 0 (4 * mu))"
    let pair ← store `on_exterior_plateau all proof
    discard <| store `Vbase_smooth all (.proj ``And 0 pair) false (some baseType)
    let bi (nm : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.SourceInverseBoundary ++ nm)) selected
    let ri := bi `rInner
    let core ← store `core original (← termWith [(`n,n),(`ri,ri)] "closedBall (0 : Euclidean n) (ri / 2)") true
    let hooks := mkAppN (mkConst `JanetCartan.PhysicalBackground.native_measured_core_hooks)
      #[n, src `r, ri, src `hcell, bi `hrInner, bi `hInnerCell, bi `fact7]
    let hookType ← termWith [(`K,core),(`mu,src `r),(`psi,psi)]
      "∀ x ∈ K, x ∈ closedBall 0 mu ∧ torusQuotient x ∈ interior {z | psi z = 1}"
    let hooks ← store `core_plateau original hooks false (some hookType)
    let exactOnCore ← forallBoundedTelescope (← inferType hooks) (some 2) fun xs _ => do
      let rest := mkAppN hooks xs
      mkLambdaFVars xs (mkAppN (.proj ``And 1 pair) #[xs[0]!, .proj ``And 0 rest, .proj ``And 1 rest])
    let target ← termWith [(`n,n),(`K,core),(`F,F),(`V,V),(`Hpositive,Hp)]
      "∀ x ∈ K, ∀ j : Fin n, tensorPairing (ProjectedStressFrame.projectedStress F x j) (linearizedMetric F V x + Hpositive x) = 0"
    discard <| store `cancellation all exactOnCore false (some target)
  logInfo "native measured factor-two cancellation on the original normal's fixed core, same admitted density, raw and physical base"

end JanetCartan.PhysicalBackground.NativeMeasuredCancellationApplication
end

realize_native_measured_core_cancellation
