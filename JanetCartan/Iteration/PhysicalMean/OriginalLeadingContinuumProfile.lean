module

public import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuumProfileTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationColorMasks
import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedDensityMean
import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.CarrierPullback
import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointDensity
import JanetCartan.Iteration.PhysicalBackground.NativePositiveCancellation
import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuum
import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuumTemplate
import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
import JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfiles
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuumProfileTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackground
import all JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfiles
public meta import Lean

/-!
# The exact selected leading-minus-corrected continuum profile

Identify the unchanged full row/color signed integral with the literal selected
comparison in `new:eq:mean-source`. The leading scalar density uses the same
positive initial and genuine carrier, the single original outer square, and the
original normalized masks. Native affine/positive equality is used only on its
proved five-radius window, with the actual four-radius measurement support.
The final native50 source profile retains the sharp h*T^(q-sourceOrder) and the
already fixed prehistory44 budget; no desired norm or global tensor equality is
assumed. The unchanged weighted and analytic-profile producers remain frozen.
-/

public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-! ## Checked value producer: ActualLeadingDensity -/
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open ContinuumRow ContinuumRow.LeadingPrimitive CurrentMean.PreparationTransportPrimitives
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open LeadingWave LeadingWave.FullModulation RawPrimary ActualCarriers.ConstructedCarrierJets

/-- The original uncut leading Hermitian density on the genuine carrier is
exactly the retained positive-normal density; no corrected-continuum equality
is asserted here. -/
private theorem leadingDensity_on_graph
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω Kc p₀ R M τ row col F)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ Vcomp,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T c.Q F row col Φ Y initial
          (w.1,(w.2,T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T c.Q F row col c.forward c.inverse initial w)
    {p : Euclidean n × CarrierParameter}
    (hp : coordinates (adaptedCoordinates T.data.adapted)
      (p.1,CanonicalCarrier.parameter p.2) ∈ Vcomp) (i j : Fin n) :
    hermitianTensor (fullLeadingPrincipalMatrix T c.Q F row col Φ Y initial (carrierGraph T p)) i j =
      ‖c.normal initial p‖^2 * covector c p i * covector c p j := by
  have he := retainedTransportMatrix_eq_fullPrincipal_on_graph c Φ Y initial hcompat hp
  change retainedTransportMatrix c initial p =
    fullLeadingPrincipalMatrix T c.Q F row col Φ Y initial (carrierGraph T p) at he
  rw [← he,retainedTransportMatrix,hermitianTensor_ofReal,principalMatrix_transpose_mul]
  rfl

private theorem original_outer_product_admission
    {n : ℕ} {μ R S : ℝ} (hμ : 0 < μ)
    {V : Set CarrierParameter} {χ : CarrierParameter → ℝ}
    (hbuffer : Metric.closedBall (0 : Euclidean n) (6*μ) ×ˢ
        PhysicalBackground.originalOuterWindow V S ⊆
      Metric.ball (0 : Euclidean n) R ×ˢ PhysicalBackground.originalOuterWindow V S)
    (hχ : tsupport χ ⊆ PhysicalBackground.originalOuterWindow V S)
    {x : Euclidean n} (hx : x ∈ Metric.closedBall (0 : Euclidean n) (4*μ))
    {z : CarrierParameter} (hz : z ∈ tsupport χ) :
    (x,z) ∈ Metric.ball (0 : Euclidean n) R ×ˢ V := by
  have h46 : 4*μ ≤ 6*μ := by linarith only [hμ]
  have hx6 : x ∈ Metric.closedBall (0 : Euclidean n) (6*μ) :=
    Metric.closedBall_subset_closedBall h46 hx
  have hout := hbuffer (show (x,z) ∈ Metric.closedBall (0 : Euclidean n) (6*μ) ×ˢ
    PhysicalBackground.originalOuterWindow V S from ⟨hx6,hχ hz⟩)
  exact ⟨hout.1,hout.2.1⟩

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a _ _ => do
    let some body := (← getConstInfo `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.raw_coefficients).value? (allowOpaque := true) |
      throwError "missing original coefficient proof"
    let coeff := (body.beta p[:51].toArray).headBeta
    unless coeff.isAppOfArity `JanetCartan.PhysicalNormalInverse.OriginalRetained.positive_continuation 51 do
      throwError "changed original retained51"
    let ca := coeff.getAppArgs
    let nativeLe := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.OriginalRetained.S_native) ca[:34].toArray
    let hCurrent ← mkAppM ``le_trans #[nativeLe,ca[35]!]
    let currentArgs := ca[:31].toArray ++ #[ca[34]!,hCurrent] ++ ca[36:40].toArray ++ #[ca[31]!]
    let phase := a[10]!
    unless phase.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingCell.Φ 36 do
      throwError "changed same leading36"
    let current := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.current) phase.getAppArgs
    let ct ← inferType current
    unless ct.isAppOfArity
        `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart 15 do
      throwError "changed original retained chart15"
    let compat := mkApp (mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.compatible) phase.getAppArgs) a[14]!
    let geom := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalCurrent.geometry) currentArgs
    let hcoord := Nat.repeat (fun e => Expr.proj ``And 1 e) 6 geom
    let tg ← inferType hcoord
    unless tg.isAppOfArity ``Set.MapsTo 5 do throwError "lost original coordinate map"
    let ga := tg.getAppArgs
    let core := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.leadingDensity_on_graph)
      (ct.getAppArgs ++ #[current,a[10]!,a[11]!,a[14]!,ga[4]!,compat])
    withLocalDeclNoLocalInstanceUpdate `point .default ga[0]! fun point => do
      let premise := mkApp ga[3]! point
      withLocalDeclNoLocalInstanceUpdate `hpoint .default premise fun hpoint => do
        let proof := mkAppN core #[point,mkAppN hcoord #[point,hpoint]]
        let params := p[:51].toArray ++ #[point,hpoint]
        let type ← mkForallFVars params (← inferType proof)
        let value ← mkLambdaFVars params proof
        for e in #[type,value] do
          if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
            throwError "unclosed leading identity or leaked color"
        let out ← IO.getStdout
        out.putStrLn "kernel checking original leading-density identity on exact exterior product"
        out.flush
        addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingDensity.on_product,levelParams := [],type,value}) (forceExpose := true)
        out.putStrLn "kernel passed original leading-density identity on exact exterior product"
        out.flush

run_meta do
  withWeightedParent fun p a g _ => do
    let core := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingDensity.on_product) p[:51].toArray
    let sampler := g[7]!.getAppArgs[:22].toArray
    let merged := mkAppN (mkConst ``JanetCartan.PhysicalSampling.samplingCappedExtra)
      #[sampler[0]!,sampler[1]!,sampler[2]!,sampler[21]!]
    let capped := mkAppN (mkConst ``JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[a[0]!,sampler[1]!,merged]
    let selected := (#[a[0]!,sampler[1]!] ++ sampler[3:22].toArray).set! 20 capped
    let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) selected
    let hbuffer := mkAppN (mkConst `JanetCartan.PhysicalBackground.OriginalOuterCutoff.product_buffer)
      (selected.push p[50]!)
    let hχ := mkAppN (mkConst `JanetCartan.PhysicalBackground.OriginalOuterCutoff.support_window)
      (selected.push p[50]!)
    let radius := mkAppN (mkConst `JanetCartan.PhysicalBackground.originalProductRadius)
      (selected.push p[50]!)
    let outerName := `JanetCartan.PhysicalBackground.OriginalOuterCutoff
    let originalV := mkAppN (mkConst (outerName ++ `Voriginal)) (selected.push p[50]!)
    let parameterRadius := mkAppN (mkConst (outerName ++ `parameterRadius)) (selected.push p[50]!)
    let cutoff := mkAppN (mkConst (outerName ++ `χ)) (selected.push p[50]!)
    let μ := (← inferType hμ).getAppArgs[3]!
    let admission := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.original_outer_product_admission)
      #[a[0]!,μ,radius,parameterRadius,hμ,originalV,cutoff,hbuffer,hχ]
    let out ← IO.getStdout
    out.putStrLn "outer admission: opening exact four point-domain binders"
    out.flush
    forallBoundedTelescope (← inferType admission) (some 4) fun v _ => do
      unless v.size == 4 do throwError "changed complete exterior membership telescope"
      out.putStrLn "outer admission: checking unchanged measurement compact"
      out.flush
      unless ← isDefEq (← inferType v[1]!) (← mkAppM ``Membership.mem #[g[3]!,v[0]!]) do
        throwError "exterior admission changed original common measurement compact"
      out.putStrLn "outer admission: checking unchanged whole outer cutoff"
      out.flush
      let χ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.χ)
        (sampler.push p[50]!)
      unless ← isDefEq (← inferType v[3]!) (← mkAppM ``Membership.mem #[← mkAppM ``tsupport #[χ],v[2]!]) do
        throwError "exterior admission changed original whole outer support"
      let point ← mkAppM ``Prod.mk #[v[0]!,v[2]!]
      let proof := mkAppN core #[point,mkAppN admission v]
      let params := p[:51].toArray ++ v
      let type ← mkForallFVars params (← inferType proof)
      let value ← mkLambdaFVars params proof
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "unclosed original full-support density identity"
      let out ← IO.getStdout
      out.putStrLn "kernel checking original leading-density identity on full outer support"
      out.flush
      addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingDensity.on_original_outer,levelParams := [],type,value}) (forceExpose := true)
      out.putStrLn "kernel passed original leading-density identity on full outer support"
      out.flush


/-! ## Checked value producer: RawLeadingDensity -/
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a _ _ => do
    let base := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingDensity.on_original_outer) p[:51].toArray
    let target ← inferType base
    let amplitude := `JanetCartan.RawPrimary.fullLeadingPrincipalMatrix
    let some full := target.find? (·.isAppOfArity amplitude 13) |
      throwError "original density lost exact full leading amplitude13"
    let originalQ := full.getAppArgs[6]!
    let same := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.same_witnesses) a[10]!.getAppArgs
    let hQ := Expr.proj ``And 0 same
    let qt ← inferType hQ
    unless qt.isAppOfArity ``Eq 3 do throwError "lost retained same-Q witness"
    unless ← isDefEq qt.getAppArgs[2]! a[6]! do throwError "raw leading Q differs from retained same-Q witness"
    let targetRaw := target.replace fun e => if e == originalQ then some a[6]! else none
    let P ← withLocalDeclNoLocalInstanceUpdate `Q .default (← inferType a[6]!) fun Q => do
      mkLambdaFVars #[Q] (target.replace fun e => if e == originalQ then some Q else none)
    let transport ← mkAppM ``congrArg #[P,hQ]
    let proof := mkAppN (mkConst ``Eq.mp [.zero]) #[target,targetRaw,transport,base]
    let params := p[:51].toArray
    let type ← mkForallFVars params targetRaw
    let value ← mkLambdaFVars params proof
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "unclosed raw-Q original density"
    let out ← IO.getStdout
    out.putStrLn "kernel checking same original outer density with literal raw Q"
    out.flush
    let pair := Lean.ShareCommon.shareCommon (type,value)
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingDensity.on_original_outer_rawQ,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    out.putStrLn "kernel passed same original outer density with literal raw Q"
    out.flush


/-! ## Checked value producer: LeadingIntegral -/
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open ContinuumRow CurrentMean SeparatedSampling LatticeQuadrature
open Sampling.ColoredNormalComparison Sampling.BackgroundQuadrature

private theorem integrable_weighted_matrix {n : ℕ} (ψ : Point → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (A : Point → MetricTensor n) (hA : ∀ z ∈ tsupport ψ, ContinuousAt A z) :
    Integrable (fun z ↦ ψ z • A z) := by
  have hs : Continuous (fun z ↦ ψ z • A z) := continuous_of_tsupport fun z hz ↦
    hψ.continuousAt.smul (hA z (tsupport_smul_subset_left ψ A hz))
  exact hs.integrable_of_hasCompactSupport (hc.smul_right (f' := A))

private theorem integrable_leading_on_parameter_window {n d N : ℕ}
    (X : Set (Euclidean n)) (ζ : Euclidean 3 → Euclidean d) (ψ : Point → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (W : Set (Euclidean 3)) (hW : IsOpen W) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hψW : MapsTo (WithLp.toLp 2) (tsupport ψ) W)
    (K Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hg : MapsTo (fun w : Euclidean n × Point ↦
      (w.1,WithLp.toLp 2 w.2,ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport ψ) K)
    (A : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ A Ω) {x : Euclidean n} (hx : x ∈ X) :
    Integrable (fun z : Point ↦ ψ z •
      hermitianTensor (A (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)))) := by
  apply integrable_weighted_matrix ψ hψ.continuous hc
  intro z hz
  have hnode : Continuous (fun z : Point ↦ WithLp.toLp 2 z) := by fun_prop
  have hζat := (hζ.continuousOn.continuousAt (hW.mem_nhds (hψW hz))).comp hnode.continuousAt
  have hgraph : ContinuousAt (fun z : Point ↦
      (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z))) z :=
    continuousAt_const.prodMk (hnode.continuousAt.prodMk hζat)
  have hK : (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)) ∈ K :=
    hg (show (x,z) ∈ X ×ˢ tsupport ψ from ⟨hx,hz⟩)
  have hAat : ContinuousAt (fun z : Point ↦ A (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z))) z :=
    (hA.continuousOn.continuousAt (hΩ.mem_nhds (hKΩ hK))).comp
      (f := fun z : Point ↦ (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z))) hgraph
  have hH := ((hermitianContinuousBilinear (m := Fin N) (n := Fin n)).continuous.continuousAt.comp
    (f := fun z : Point ↦ A (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z))) hAat).clm_apply hAat
  simpa only [Function.comp_def,hermitianContinuousBilinear_apply,mixedHermitianTensor_self] using hH

private theorem measured_integral_entries {n : ℕ}
    (C : MetricTensor n →L[ℝ] Euclidean n) (ψ : Point → ℝ)
    (A : Point → MetricTensor n) (hA : Integrable (fun z ↦ ψ z • A z)) :
    (∫ z, ψ z • C (A z)) = C (fun i j ↦ ∫ z, ψ z * A z i j) := by
  have he : (∫ z, ψ z • A z) = fun i j ↦ ∫ z, ψ z * A z i j := by
    ext i j
    let E := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (E.integral_comp_comm hA).symm
  rw [← he]
  simpa only [map_smul] using C.integral_comp_comm hA

/-- Only the color-independent original leading field loses its color masks.
The normalized partition is used solely where the unchanged outer weight is
nonzero; no equality with the corrected continuum is assumed. -/
private theorem original_leading_color_integral
    {n p : ℕ} {κ : ℝ → ℝ} (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    (hp : 0 < p) {ψ : Point → ℝ} (hψc : HasCompactSupport ψ)
    {B P h : ℝ} (hpatch : PatchBounds ψ B P) (hh : 0 < h) (hh1 : h ≤ 1)
    (H : Point → Euclidean n) (hH : Continuous (fun z ↦ ψ z • H z)) :
    (∑ c : Fin 3 → Fin (p+1), ∫ z,
      coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c z • (ψ z • H z)) =
      ∫ z, ψ z • H z := by
  classical
  let mask := coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h
  have hi (c) : Integrable (fun z ↦ mask c z • (ψ z • H z)) :=
    ((contDiff_coloredBlockMask hκc hκ p _ h c).continuous.smul hH).integrable_of_hasCompactSupport
      ((hψc.smul_right (f' := H)).smul_left (f := mask c))
  rw [← integral_finsetSum _ (fun c _ ↦ hi c)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : ψ z = 0
  · simp [hz]
  · rw [← Finset.sum_smul, sum_coloredBlockMask_eq_one
      (hκ.continuous.integrable_of_hasCompactSupport hκc) hκint hκ0 hκsupp hp hpatch hh hh1 hz,one_smul]

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue

open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a g _ => do
    let hLeading := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.leading_smooth_from_normal)
      (a[:12].toArray ++ #[a[14]!,a[16]!,a[20]!,a[21]!])
    let t ← inferType hLeading
    let A := t.getAppArgs[t.getAppNumArgs-2]!
    let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.integrable_leading_on_parameter_window)
      #[g[0]!,g[1]!,g[2]!,g[3]!,g[5]!,g[6]!,g[7]!,g[8]!,g[9]!,g[10]!,g[11]!,g[12]!,
        g[13]!,g[14]!,g[16]!,g[17]!,g[18]!,A,hLeading]
    let rawTarget ← inferType proof
    if (rawTarget.find? (· == p[51]!)).isSome then
      throwError "leading matrix integrability itself unexpectedly depends on color"
    -- Only the frozen smoothness certificate carries color; its type and the
    -- leading matrix are independent of it. Use the original packet's zero
    -- member to close that proof, never replacing any corrected amplitude.
    let zeroColor ← forallBoundedTelescope (← inferType p[51]!) (some 1) fun i target => do
      unless i.size == 1 do throwError "changed original finite color type"
      mkLambdaFVars i (← mkNumeral target 0)
    let proof := proof.replace fun e => if e == p[51]! then some zeroColor else none
    let params := p[:51].toArray
    let type ← mkForallFVars params rawTarget
    let value ← mkLambdaFVars params proof
    for (label,e) in #[("type",type),("value",value)] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        for k in [:p.size] do
          if (e.find? (· == p[k]!)).isSome then logInfo m!"remaining actual parameter {label}/{k}"
        for (sourceLabel,args) in #[("raw",a),("geometric",g)] do
          for k in [:args.size] do
            if (args[k]!.find? (· == p[51]!)).isSome then logInfo m!"color certificate {sourceLabel}/{k}"
        throwError "actual leading integral {label}: fvar={e.hasFVar}, mvar={e.hasMVar}, level={e.hasLevelMVar}, loose={e.hasLooseBVars}, placeholder={e.hasSorry}"
    let out ← IO.getStdout
    out.putStrLn "kernel checking original whole-support leading-matrix integrability"
    out.flush
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingIntegral.matrix_integrable,levelParams := [],type,value}) (forceExpose := true)
    out.putStrLn "kernel passed original whole-support leading-matrix integrability"
    out.flush


/-! ## Checked value producer: RowIntegral -/
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open ContinuumRow CanonicalCarrier SeparatedSampling

/-- Exact fixed-row integral identity. Both hypotheses have already checked
native producers: whole-parent weighted integrability and full original outer
support transport. No equality to an affine or corrected mean is assumed. -/
private theorem original_measured_carrier_row {n N : ℕ}
    (C : MetricTensor n →L[ℝ] Euclidean n) (χ : CarrierParameter → ℝ)
    (A : Point → MetricTensor n) (ν : CarrierParameter → Euclidean N)
    (ξ : CarrierParameter → Euclidean n)
    (hI : Integrable (fun z : Point ↦ χ (carrierSamplingEquiv.symm z)^2 • A z))
    (hD : ∀ z ∈ tsupport χ, ∀ i j,
      A (carrierSamplingEquiv z) i j = ‖ν z‖^2 * ξ z i * ξ z j) :
    (∫ z : Point, χ (carrierSamplingEquiv.symm z)^2 • C (A z)) =
      C (fun i j ↦ ∫ z, χ z^2 * ‖ν z‖^2 * (ξ z i * ξ z j) ∂(volume.prod volume)) := by
  have he : (∫ z : Point, χ (carrierSamplingEquiv.symm z)^2 • A z) =
      fun i j ↦ ∫ z, χ z^2 * ‖ν z‖^2 * (ξ z i * ξ z j) ∂(volume.prod volume) := by
    ext i j
    let E := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    calc
      _ = ∫ z : Point, (χ (carrierSamplingEquiv.symm z)^2 • A z) i j :=
        (E.integral_comp_comm hI).symm
      _ = ∫ z, (χ (carrierSamplingEquiv.symm (carrierSamplingEquiv z))^2 •
          A (carrierSamplingEquiv z)) i j ∂(volume.prod volume) :=
        (integral_carrierSamplingEquiv _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [carrierSamplingEquiv.symm_apply_apply]
        change χ z^2 * A (carrierSamplingEquiv z) i j =
          χ z^2 * ‖ν z‖^2 * (ξ z i * ξ z j)
        by_cases hz : χ z = 0
        · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_mul]
        · rw [hD z (subset_tsupport χ hz) i j]
          ring
  rw [← he]
  simpa only [map_smul] using C.integral_comp_comm hI

private theorem original_measured_carrier_graph_row {n N : ℕ}
    (C : MetricTensor n →L[ℝ] Euclidean n) (χ : CarrierParameter → ℝ)
    (ζ : Euclidean 3 → Euclidean (n-1))
    (A : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → MetricTensor n)
    (x : Euclidean n) (ν : CarrierParameter → Euclidean N) (ξ : CarrierParameter → Euclidean n)
    (hI : Integrable (fun z : Point ↦ χ (carrierSamplingEquiv.symm z)^2 •
      A (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z))))
    (hD : ∀ z ∈ tsupport χ, ∀ i j,
      A (x,parameter z,ζ (parameter z)) i j = ‖ν z‖^2 * ξ z i * ξ z j) :
    (∫ z : Point, χ (carrierSamplingEquiv.symm z)^2 • C (A (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z)))) =
      C (fun i j ↦ ∫ z, χ z^2 * ‖ν z‖^2 * (ξ z i * ξ z j) ∂(volume.prod volume)) := by
  refine original_measured_carrier_row C χ
    (fun z : Point ↦ A (x,WithLp.toLp 2 z,ζ (WithLp.toLp 2 z))) ν ξ hI ?_
  intro z hz i j
  have hpar : WithLp.toLp 2 (carrierSamplingEquiv z) = parameter z := by
    ext k
    fin_cases k <;> rfl
  simpa only [hpar] using hD z hz i j

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue

open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a g d => do
    let hi := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingIntegral.matrix_integrable) p[:51].toArray
    forallBoundedTelescope (← inferType hi) (some 2) fun xs _ => do
      unless xs.size == 2 do throwError "changed native51 leading integrability domain"
      let hI := mkAppN hi xs
      let it ← inferType hI
      unless it.isAppOf ``MeasureTheory.Integrable do throwError "missing actual matrix integrability"
      let integrand := it.getAppArgs[it.getAppNumArgs-2]!
      let A ← lambdaTelescope integrand fun z rhs => do
        unless z.size == 1 do throwError "changed original matrix integrand"
        let rhs := JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate.rootLets rhs
        unless rhs.isAppOf ``HSMul.hSMul do throwError "lost single outer scalar weight"
        let matrix := rhs.appArg!
        let some full := matrix.find? (·.isAppOfArity `JanetCartan.RawPrimary.fullLeadingPrincipalMatrix 14) |
          throwError "original matrix integral lost full leading matrix14"
        let graph := full.appArg!
        withLocalDeclNoLocalInstanceUpdate `v .default (← inferType graph) fun v => do
          let field ← mkLambdaFVars #[v] (matrix.replace fun e => if e == graph then some v else none)
          if (field.find? (· == z[0]!)).isSome then throwError "raw leading matrix retained sampling node"
          pure field
      let current := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.current) a[10]!.getAppArgs
      let ct ← inferType current
      unless ct.isAppOfArity
          `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart 15 do
        throwError "changed original leading chart15"
      let normal := mkAppN (mkConst
        `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart.normal)
        (ct.getAppArgs ++ #[current,a[14]!])
      let covector := mkAppN (mkConst
        `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.covector)
        (ct.getAppArgs.push current)
      let χ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.χ) g[7]!.getAppArgs
      let fields ← withLocalDeclNoLocalInstanceUpdate `z .default
        (mkConst `JanetCartan.ContinuumRow.CarrierParameter) fun z => do
          let point ← mkAppM ``Prod.mk #[xs[0]!,z]
          return (← mkLambdaFVars #[z] (mkApp normal point),← mkLambdaFVars #[z] (mkApp covector point))
      let hD := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingDensity.on_original_outer_rawQ) (p[:51].toArray ++ xs)
      let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.original_measured_carrier_graph_row)
        #[a[0]!,a[1]!,mkApp d[0]! xs[0]!,χ,g[5]!,A,xs[0]!,fields.1,fields.2,hI,hD]
      let params := p[:51].toArray ++ xs
      let type ← mkForallFVars params (← inferType proof)
      let value ← mkLambdaFVars params proof
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "unclosed actual measured leading row or leaked color"
      let out ← IO.getStdout
      out.putStrLn "kernel checking exact actual measured original leading row integral"
      out.flush
      let pair := Lean.ShareCommon.shareCommon (type,value)
      addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingRowIntegral.on_measurement_support,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
      out.putStrLn "kernel passed exact actual measured original leading row integral"
      out.flush


/-! ## Checked value producer: ChartAliases -/
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def retainChartAlias (name : Name) (p : Array Expr) (lhs rhs proof : Expr) : MetaM Unit := do
  let type ← mkForallFVars p (← mkEq lhs rhs)
  let value ← mkLambdaFVars p proof
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "unclosed exact chart alias {name}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking factored original chart {name}"
  out.flush
  let pair := Lean.ShareCommon.shareCommon (type,value)
  addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed factored original chart {name}"
  out.flush

private meta def unfoldChartAlias (e : Expr) (stop : Name) : MetaM Expr := do
  let mut result := e
  for _ in [:8] do
    if result.getAppFn.isConstOf stop then return result
    let some name := result.getAppFn.constName? | throwError "chart alias stopped before {stop}"
    let some value := (← getConstInfo name).value? | throwError "opaque chart alias {name}"
    result := JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate.rootLets (value.beta result.getAppArgs)
  throwError "too many original chart aliases before {stop}"

run_meta do
  let original := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let phaseInfo ← getConstInfo (original ++ `Φ)
  forallBoundedTelescope phaseInfo.type (some 38) fun p _ => do
    unless p.size == 38 do throwError "changed original current phase38"
    let phase ← unfoldChartAlias (mkAppN (mkConst (original ++ `Φ)) p)
      `JanetCartan.PhysicalPrimary.LeadingCell.Φ
    unless phase.getAppNumArgs == 36 do throwError "changed underlying leading phase36"
    let lhs := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.current) phase.getAppArgs
    let rhs := mkAppN (mkConst (original ++ `current)) p
    retainChartAlias `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ChartAliases.original p lhs rhs (← mkEqRefl lhs)

run_meta do
  let native := `JanetCartan.PhysicalBackground.NativeAdmission.current
  forallBoundedTelescope (← getConstInfo native).type (some 40) fun p _ => do
    unless p.size == 40 do throwError "changed original native current40"
    let lhs := mkAppN (mkConst native) p
    let rhs ← unfoldChartAlias lhs `JanetCartan.PhysicalInitialization.OriginalCurrent.current
    unless rhs.getAppNumArgs == 38 do throwError "changed underlying original current38"
    retainChartAlias `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ChartAliases.native p lhs rhs (← mkEqRefl lhs)

run_meta do
  withWeightedParent fun p a _ _ => do
    let some body := (← getConstInfo `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope.raw_coefficients).value? (allowOpaque := true) |
      throwError "missing original whole-parent coefficient producer"
    let coeff := (body.beta p[:51].toArray).headBeta
    unless coeff.isAppOfArity `JanetCartan.PhysicalNormalInverse.OriginalRetained.positive_continuation 51 do
      throwError "changed actual positive leading continuation51"
    let ca := coeff.getAppArgs
    let nativeLe := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.OriginalRetained.S_native) ca[:34].toArray
    let hCurrent ← mkAppM ``le_trans #[nativeLe,ca[35]!]
    let currentArgs := ca[:31].toArray ++ #[ca[34]!,hCurrent] ++ ca[36:40].toArray ++ #[ca[31]!]
    let lhs := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.current) a[10]!.getAppArgs
    let rhs := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalCurrent.current) currentArgs
    let proof := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ChartAliases.original) currentArgs
    retainChartAlias `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Chart.raw_as_original p[:51].toArray lhs rhs proof


/-! ## Checked value producer: CurrentDensity -/
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue

private noncomputable def retainedScalarDensity (n N : ℕ)
    (ν : Euclidean n × ContinuumRow.CarrierParameter → Euclidean N)
    (ξ : Euclidean n × ContinuumRow.CarrierParameter → Euclidean n) :
    Euclidean n × ContinuumRow.CarrierParameter → MetricTensor n :=
  fun w i j ↦ ‖ν w‖^2 * ξ w i * ξ w j

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open Lean Meta

private meta def retainCurrentDensity (key : Name) (type value : Expr) (data := false) : MetaM Unit := do
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "unclosed current density {key}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking current scalar density {key}"
  out.flush
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density ++ key
  let pair := Lean.ShareCommon.shareCommon (type,value)
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed current scalar density {key}"
  out.flush

run_meta do
  let f := mkConst `JanetCartan.PhysicalInitialization.OriginalCurrent.current
  forallBoundedTelescope (← inferType f) (some 38) fun p _ => do
    unless p.size == 38 do throwError "changed original current38"
    let current := mkAppN f p
    let ct ← inferType current
    unless ct.isAppOfArity `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart 15 do
      throwError "changed retained current chart15"
    let normal := mkAppN (mkConst `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart.normal)
      (ct.getAppArgs.push current)
    let covector := mkAppN (mkConst `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.covector)
      (ct.getAppArgs.push current)
    let .forallE _ domain _ _ ← whnf (← inferType normal) | throwError "missing exact initial positive density"
    withLocalDeclNoLocalInstanceUpdate `initial .default domain fun initial => do
      let body := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.retainedScalarDensity)
        #[ct.getAppArgs[0]!,ct.getAppArgs[1]!,mkApp normal initial,covector]
      let params := p.push initial
      retainCurrentDensity `current (← mkForallFVars params (← inferType body)) (← mkLambdaFVars params body) true

run_meta do
  let congr ← mkHCongrWithArity (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.current) 39
  retainCurrentDensity `current_congr congr.type congr.proof
  logInfo m!"current density congruence kinds: {repr congr.argKinds}"


/-! ## Checked value producer: DensityAliases -/
open Lean Meta

private meta def scalarDensityAt (c initial : Expr) : MetaM Expr := do
  let ct ← inferType c
  unless ct.isAppOfArity `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart 15 do
    throwError "changed scalar-density chart15"
  let some body := (← getConstInfo `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.current).value? | throwError "missing exact density function"
  let helper ← lambdaTelescope body fun _ body => do
    unless body.getAppFn.isConst do throwError "changed exact scalar-density constructor"
    return body.getAppFn
  let normal := mkAppN (mkConst `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart.normal)
    (ct.getAppArgs ++ #[c,initial])
  let covector := mkAppN (mkConst `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.covector)
    (ct.getAppArgs.push c)
  return mkAppN helper #[ct.getAppArgs[0]!,ct.getAppArgs[1]!,normal,covector]

private meta def retainDensityAlias (name : Name) (p : Array Expr) (lhs rhs proof : Expr) : MetaM Unit := do
  let type ← mkForallFVars p (← mkEq lhs rhs)
  let value ← mkLambdaFVars p proof
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed scalar-density chartAlias {name}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking scalar-density chartAlias {name}"
  out.flush
  let pair := Lean.ShareCommon.shareCommon (type,value)
  addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed scalar-density chartAlias {name}"
  out.flush

private meta def checkDensityAlias (native : Bool) : MetaM Unit := do
  let chartAlias := if native then `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ChartAliases.native else `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ChartAliases.original
  let count := if native then 40 else 38
  forallBoundedTelescope (← getConstInfo chartAlias).type (some count) fun p eqType => do
    unless p.size == count && eqType.isAppOfArity ``Eq 3 do throwError "changed exact generic chart chartAlias"
    let ct := eqType.getAppArgs[0]!
    let lhsChart := eqType.getAppArgs[1]!
    let rhsChart := eqType.getAppArgs[2]!
    unless rhsChart.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalCurrent.current 38 do
      throwError "density chartAlias lost exact current38"
    let cType ← inferType lhsChart
    let normal := mkAppN (mkConst `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart.normal)
      (cType.getAppArgs.push lhsChart)
    let .forallE _ initialType _ _ ← whnf (← inferType normal) | throwError "missing exact initial density"
    withLocalDeclNoLocalInstanceUpdate `initial .default initialType fun initial => do
      let mapper ← withLocalDeclNoLocalInstanceUpdate `c .default ct fun c => do
        mkLambdaFVars #[c] (← scalarDensityAt c initial)
      let proof ← mkAppM ``congrArg #[mapper,mkAppN (mkConst chartAlias) p]
      let lhs ← scalarDensityAt lhsChart initial
      let rhs := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.current) (rhsChart.getAppArgs.push initial)
      let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.DensityAliases ++ (if native then `native else `raw)
      retainDensityAlias name (p.push initial) lhs rhs proof

run_meta checkDensityAlias false
run_meta checkDensityAlias true


/-! ## Checked value producer: DensityJoin -/
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def retainDensityJoin (key : Name) (p : Array Expr) (lhs rhs proof : Expr) : MetaM Unit := do
  let type ← mkForallFVars p (← mkEq lhs rhs)
  let value ← mkLambdaFVars p proof
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed density join {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking actual positive density {key}"
  out.flush
  addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density ++ key,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed actual positive density {key}"
  out.flush

private meta def checkDensityJoin (mode : Nat) : MetaM Unit := do
  withWeightedParent fun p a g _ => do
    let some label := a[14]!.find? (·.isAppOfArity `JanetCartan.PhysicalBackground.NativeAdmission.labels 41) |
      throwError "lost exact original positive labels"
    let native := label.getAppArgs[:39].toArray
    let some body := (← getConstInfo `JanetCartan.PhysicalBackground.NativePositiveCancellation.positiveMean).value? |
      throwError "missing exact positive carrier mean"
    let mean := (body.beta native).headBeta
    unless mean.isAppOfArity `JanetCartan.NormalizedBackground.carrierMean 12 do throwError "changed original carrierMean12"
    let normal := (mkApp mean.getAppArgs[10]! p[50]!).headBeta
    let normalName := `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart.normal
    let some nf := normal.find? (·.isAppOfArity normalName 17) | throwError "missing exact positive normal"
    if mode == 0 then
      retainDensityJoin `initial p[:51].toArray a[14]! nf.getAppArgs[16]! (← mkEqRefl a[14]!)
    else if mode == 1 then
      let cutoff := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.χ) g[7]!.getAppArgs
      let field ← withLocalDeclNoLocalInstanceUpdate `z .default (mkConst `JanetCartan.ContinuumRow.CarrierParameter) fun z => do
        mkLambdaFVars #[z] (← mkAppM ``HPow.hPow #[mkApp cutoff z,mkNatLit 2])
      retainDensityJoin `weight p[:51].toArray field (mkApp mean.getAppArgs[9]! p[50]!) (← mkEqRefl field)
    else
      let raw := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Chart.raw_as_original) p[:51].toArray
      let nat := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ChartAliases.native) (native.push p[50]!)
      let leftCurrent := (← inferType raw).getAppArgs[2]!
      let rightCurrent := (← inferType nat).getAppArgs[2]!
      let l := leftCurrent.getAppArgs.push a[14]!
      let r := rightCurrent.getAppArgs.push nf.getAppArgs[16]!
      unless l.size == 39 && r.size == 39 do throwError "changed exact original density inputs"
      for i in [:38] do
        unless i == 0 || i == 32 || l[i]! == r[i]! do throwError "different original current input {i}"
      let mut proof := mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.current_congr
      let mut ty ← inferType proof
      for i in [:39] do
        for x in #[l[i]!,r[i]!] do
          let .forallE _ _ body _ := ty | throwError "changed congruence arguments at {i}"
          proof := mkApp proof x
          ty := body.instantiate1 x
        let .forallE _ domain body _ := ty | throwError "missing congruence equality at {i}"
        let eqProof ← if i == 38 then do
            let h := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.initial) p[:51].toArray
            if domain.isHEq then mkHEqOfEq h else pure h
          else if domain.isHEq then
            if ← isProof l[i]! then mkAppM ``proof_irrel_heq #[l[i]!,r[i]!] else mkHEqRefl l[i]!
          else if domain.isEq then mkEqRefl l[i]!
          else throwError "unexpected congruence equality kind at {i}"
        proof := mkApp proof eqProof
        ty := body.instantiate1 eqProof
      unless ty.isHEq do throwError "density congruence lost its actual heterogeneous conclusion"
      let finalProof ← mkEqOfHEq proof
      let f := mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.current
      retainDensityJoin `same_current p[:51].toArray (mkAppN f l) (mkAppN f r) finalProof

run_meta checkDensityJoin 0
run_meta checkDensityJoin 1
run_meta checkDensityJoin 2


/-! ## Checked value producer: NativeDensityRow -/
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open ContinuumRow

private noncomputable def scalarDensityRow (n N : ℕ) (w : CarrierParameter → ℝ)
    (ν : Euclidean n × CarrierParameter → Euclidean N)
    (ξ : Euclidean n × CarrierParameter → Euclidean n) (x : Euclidean n) : MetricTensor n :=
  fun i j ↦ ∫ z, w z * ‖ν (x,z)‖^2 * (ξ (x,z) i * ξ (x,z) j) ∂(volume.prod volume)

private theorem scalarDensityRow_congr (n N₀ N₁ : ℕ)
    (w₀ w₁ : CarrierParameter → ℝ)
    (ν₀ : Euclidean n × CarrierParameter → Euclidean N₀)
    (ν₁ : Euclidean n × CarrierParameter → Euclidean N₁)
    (ξ₀ ξ₁ : Euclidean n × CarrierParameter → Euclidean n)
    (hw : w₀ = w₁)
    (hD : (fun p i j ↦ ‖ν₀ p‖^2 * ξ₀ p i * ξ₀ p j) =
      (fun p i j ↦ ‖ν₁ p‖^2 * ξ₁ p i * ξ₁ p j)) (x : Euclidean n) :
    scalarDensityRow n N₀ w₀ ν₀ ξ₀ x = scalarDensityRow n N₁ w₁ ν₁ ξ₁ x := by
  ext i j
  apply integral_congr_ae
  filter_upwards [] with z
  have hd := congrArg (fun D ↦ D (x,z) i j) hD
  simp only at hd
  rw [hw]
  calc
    _ = w₁ z * (‖ν₀ (x,z)‖^2 * ξ₀ (x,z) i * ξ₀ (x,z) j) := by ring
    _ = w₁ z * (‖ν₁ (x,z)‖^2 * ξ₁ (x,z) i * ξ₁ (x,z) j) := congrArg (w₁ z * ·) hd
    _ = _ := by ring

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def saveNativeDensityRow (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p value
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed actual native density row {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking actual native density row {key}"
  out.flush
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed actual native density row {key}"
  out.flush

private meta def checkNativeDensityRow (mode : Nat) : MetaM Unit := do
  withWeightedParent fun p a g _ => do
    let some labels := a[14]!.find? (·.isAppOfArity `JanetCartan.PhysicalBackground.NativeAdmission.labels 41) |
      throwError "lost exact native39 labels"
    let native := labels.getAppArgs[:39].toArray
    let some body := (← getConstInfo `JanetCartan.PhysicalBackground.NativePositiveCancellation.positiveMean).value? |
      throwError "missing same carrier mean"
    let mean := (body.beta native).headBeta
    unless mean.isAppOfArity `JanetCartan.NormalizedBackground.carrierMean 12 do throwError "changed actual carrierMean12"
    let ma := mean.getAppArgs
    let nν := mkApp ma[10]! p[50]!
    let nξ := mkApp ma[11]! p[50]!
    let nw := mkApp ma[9]! p[50]!
    let normalName := `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart.normal
    let some nf := nν.headBeta.find? (·.isAppOfArity normalName 17) | throwError "missing exact native normal17"
    let current := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingCell.current) a[10]!.getAppArgs
    let ct ← inferType current
    let rν := mkAppN (mkConst normalName) (ct.getAppArgs ++ #[current,a[14]!])
    let rξ := mkAppN (mkConst `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.covector) (ct.getAppArgs.push current)
    let cutoff := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.χ) g[7]!.getAppArgs
    let rawWeight ← withLocalDeclNoLocalInstanceUpdate `z .default (mkConst `JanetCartan.ContinuumRow.CarrierParameter) fun z => do
      mkLambdaFVars #[z] (← mkAppM ``HPow.hPow #[mkApp cutoff z,mkNatLit 2])
    let some densityBody := (← getConstInfo `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.current).value? | throwError "missing density constructor"
    let scalar ← lambdaTelescope densityBody fun _ rhs => pure rhs.getAppFn
    let leftDensity := mkAppN scalar #[a[0]!,a[1]!,rν,rξ]
    let rightDensity := mkAppN scalar #[a[0]!,nf.getAppArgs[1]!,nν,nξ]
    let row := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.scalarDensityRow)
      #[a[0]!,nf.getAppArgs[1]!,nw,nν,nξ]
    if mode == 0 then
      let hRaw := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Chart.raw_as_original) p[:51].toArray
      let original := (← inferType hRaw).getAppArgs[2]!
      let hLeft := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.DensityAliases.raw) (original.getAppArgs.push a[14]!)
      let hMiddle := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.same_current) p[:51].toArray
      let hRight := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.DensityAliases.native) (native ++ #[p[50]!,nf.getAppArgs[16]!])
      let proof ← mkEqTrans hLeft (← mkEqTrans hMiddle (← mkEqSymm hRight))
      saveNativeDensityRow `density p[:51].toArray proof (← mkEq leftDensity rightDensity)
    else if mode == 1 then
      saveNativeDensityRow `row p[:51].toArray row (← inferType row) true
    else
      let rawIntegral := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.LeadingRowIntegral.on_measurement_support) p[:51].toArray
      forallBoundedTelescope (← inferType rawIntegral) (some 2) fun x _ => do
        unless x.size == 2 do throwError "changed exact original row support statement"
        let hRow := mkAppN rawIntegral x
        let rt ← inferType hRow
        let hWeight := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Density.weight) p[:51].toArray
        let hDensity := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.density) p[:51].toArray
        let transport := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.scalarDensityRow_congr)
          #[a[0]!,a[1]!,nf.getAppArgs[1]!,rawWeight,nw,rν,nν,rξ,nξ,hWeight,hDensity,x[0]!]
        let hMeasured ← mkAppM ``congrArg #[rt.getAppArgs[2]!.appFn!,transport]
        let proof ← mkEqTrans hRow hMeasured
        let rhs := mkApp rt.getAppArgs[2]!.appFn! (mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.row) p[:51].toArray) x[0]!)
        saveNativeDensityRow `on_measurement_support (p[:51].toArray ++ x) proof (← mkEq rt.getAppArgs[1]! rhs)

run_meta checkNativeDensityRow 0
run_meta checkNativeDensityRow 1
run_meta checkNativeDensityRow 2


/-! ## Checked value producer: ColoredIdentity -/
open Lean Meta
run_meta do
  let name := ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.original_leading_color_integral
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do throwError "changed exact original color normalization universes"
  addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ColorNormalization.generic,levelParams := [],type := info.type,value := mkConst name}) (forceExpose := true)

open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open ContinuumRow CurrentMean SeparatedSampling LatticeQuadrature
open Sampling.ColoredNormalComparison Sampling.BackgroundQuadrature

private theorem weighted_point_section_continuous {n : ℕ}
    (ψ : Point → ℝ) (H : Torus n × Point → Euclidean n)
    (hH : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ ψ w.2 • H (torusQuotient w.1,w.2)))
    (x : Torus n) : Continuous (fun z ↦ ψ z • H (x,z)) := by
  have hquot : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  have hc : Continuous (fun w : Torus n × Point ↦ ψ w.2 • H w) :=
    (hquot.prodMap (.id : IsOpenQuotientMap (@id Point))).isQuotientMap.continuous_iff.mpr hH.continuous
  exact hc.comp (continuous_const.prodMk continuous_id)

/-- Integral linearity and only the original color partition identify the
signed row integral. Both weighted continuous fields will be supplied by the
checked original periodic producers; no integral identity is assumed. -/
private theorem original_colored_difference_identity
    {n p : ℕ} {κ : ℝ → ℝ} (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    (hp : 0 < p) {ψ : Point → ℝ} (hψc : HasCompactSupport ψ)
    {B P h : ℝ} (hpatch : PatchBounds ψ B P) (hh : 0 < h) (hh1 : h ≤ 1)
    (L : Point → Euclidean n)
    (E F : (Fin 3 → Fin (p+1)) → Point → Euclidean n)
    (hE : ∀ c, Continuous (fun z ↦ ψ z • E c z))
    (hF : ∀ c, Continuous (fun z ↦ ψ z • F c z))
    (hvalue : ∀ c z, E c z = L z - F c z) :
    (∑ c, ∫ z, coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c z • (ψ z • E c z)) =
      (∫ z, ψ z • L z) - ∑ c, ∫ z,
        coloredBlockMask p (integerCube (blockCutoff p B h))
          (convolvedBoxWindow κ p) h c z • (ψ z • F c z) := by
  classical
  let mask := coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h
  have hL : Continuous (fun z ↦ ψ z • L z) := by
    have heq : (fun z ↦ ψ z • L z) =
        (fun z ↦ ψ z • E (fun _ ↦ 0) z + ψ z • F (fun _ ↦ 0) z) := by
      funext z
      rw [hvalue,smul_sub,sub_add_cancel]
    rw [heq]
    exact (hE (fun _ ↦ 0)).add (hF (fun _ ↦ 0))
  have hiE (c) : Integrable (fun z ↦ mask c z • (ψ z • E c z)) :=
    ((contDiff_coloredBlockMask hκc hκ p _ h c).continuous.smul (hE c)).integrable_of_hasCompactSupport
      ((hψc.smul_right (f' := E c)).smul_left (f := mask c))
  have hiF (c) : Integrable (fun z ↦ mask c z • (ψ z • F c z)) :=
    ((contDiff_coloredBlockMask hκc hκ p _ h c).continuous.smul (hF c)).integrable_of_hasCompactSupport
      ((hψc.smul_right (f' := F c)).smul_left (f := mask c))
  apply eq_sub_of_add_eq
  calc
    _ = ∑ c, ((∫ z, mask c z • (ψ z • E c z)) + (∫ z, mask c z • (ψ z • F c z))) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ c, ∫ z, mask c z • (ψ z • L z) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← integral_add (hiE c) (hiF c)]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hvalue,smul_sub,smul_sub,sub_add_cancel]
    _ = _ := JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.ColorNormalization.generic hκc hκ hκint hκ0 hκsupp hp hψc hpatch hh hh1 L hL

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue


/-! ## Checked value producer: ActualColoredIdentity -/
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def saveLeadingValue (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p value
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed actual leading value {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking exact signed integral value {key}"
  out.flush
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed exact signed integral value {key}"
  out.flush

private meta def physicalErrorBody (p : Array Expr) : MetaM Expr := do
  let some body := (← getConstInfo `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.physical).value? | throwError "missing original signed physical kernel"
  return (body.beta p).headBeta

private meta def measuredDifference (raw : Expr) : MetaM (Expr × Expr × Expr) := do
  let raw := JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate.rootLets raw
  let difference := raw.appArg!
  unless difference.isAppOfArity ``HSub.hSub 6 do throwError "not the exact measured leading-minus-corrected tensor"
  return (raw.appFn!,difference.getAppArgs[4]!,difference.getAppArgs[5]!)

run_meta do
  withWeightedParent fun p _ _ _ => do
    lambdaTelescope (← physicalErrorBody p) fun w raw => do
      unless w.size == 1 do throwError "changed signed physical pair field"
      let (C,L,_) ← measuredDifference raw
      let field ← mkLambdaFVars w (mkApp C L)
      if (field.find? (· == p[51]!)).isSome then throwError "a color entered the original leading field"
      saveLeadingValue `leading_physical p[:51].toArray field (← inferType field) true

run_meta do
  withWeightedParent fun p a _ d => do
    let error := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.periodic) p
    let pairType := (← inferType error).bindingDomain!
    withLocalDeclNoLocalInstanceUpdate `w .default pairType fun w => do
      let x := Expr.proj ``Prod 0 w
      let z := Expr.proj ``Prod 1 w
      let cx := mkAppN (mkConst `JanetCartan.AmplitudeBound.centeredTorusRepresentative) #[a[0]!,x]
      let point ← mkAppM ``Prod.mk #[cx,z]
      let raw := ((← physicalErrorBody p).beta #[point]).headBeta
      let (_,L,B) ← measuredDifference raw
      let proof ← mkAppM ``map_sub #[mkApp d[0]! cx,L,B]
      let leading := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.leading_physical) p[:51].toArray) point
      let corrected := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalPeriodicBackground.actual_periodicH) p) w
      let rhs ← mkAppM ``HSub.hSub #[leading,corrected]
      saveLeadingValue `periodic_difference (p.push w) proof (← mkEq (mkApp error w) rhs)

run_meta do
  withWeightedParent fun p a g _ => do
    let torus := mkApp (mkConst `JanetCartan.Torus) a[0]!
    withLocalDeclNoLocalInstanceUpdate `x .default torus fun x => do
      let pointType := mkConst `JanetCartan.SeparatedSampling.Point
      let cx := mkAppN (mkConst `JanetCartan.AmplitudeBound.centeredTorusRepresentative) #[a[0]!,x]
      let leading ← withLocalDeclNoLocalInstanceUpdate `z .default pointType fun z => do
        let point ← mkAppM ``Prod.mk #[cx,z]
        mkLambdaFVars #[z] (mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.leading_physical) p[:51].toArray) point)
      let error := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.periodic) p
      let corrected := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalPeriodicBackground.actual_periodicH) p
      let sectionFn (H : Expr) : MetaM Expr :=
        withLocalDeclNoLocalInstanceUpdate `z .default pointType fun z => do
          let point ← mkAppM ``Prod.mk #[x,z]
          mkLambdaFVars #[p[51]!,z] (mkApp H point)
      let E ← sectionFn error
      let F ← sectionFn corrected
      let helper := ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.weighted_point_section_continuous
      let hE ← mkLambdaFVars #[p[51]!] (mkAppN (mkConst helper)
        #[a[0]!,g[6]!,error,mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.smooth) p,x])
      let hF ← mkLambdaFVars #[p[51]!] (mkAppN (mkConst helper)
        #[a[0]!,g[6]!,corrected,mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalPeriodicBackground.weighted_smooth) p,x])
      let hvalue ← withLocalDeclNoLocalInstanceUpdate `z .default pointType fun z => do
        let point ← mkAppM ``Prod.mk #[x,z]
        mkLambdaFVars #[p[51]!,z] (mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.periodic_difference) p) point)
      let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
      let oa := g[7]!.getAppArgs
      let B := mkAppN (mkConst (outer ++ `B)) oa[:22].toArray
      let hpatch := mkAppN (mkConst (outer ++ `patchBounds)) oa
      let rate := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Rate.to_mesh) p
      let h := (← inferType rate).getAppArgs[3]!
      let hTwo := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS) p[:44].toArray
      let facts ← mkAppM `JanetCartan.PhysicalMean.OriginalPeriodicBackground.original_scale_facts #[hTwo,p[45]!,p[46]!]
      let hh := Expr.proj ``And 0 (.proj ``And 1 facts)
      let hh1 := Expr.proj ``And 1 (.proj ``And 1 facts)
      let one ← mkNumeral (mkConst ``Real) 1
      let win := `JanetCartan.PhysicalSampling.OriginalWindow
      let generic := ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.original_colored_difference_identity
      let proof := mkAppN (mkConst generic)
        #[a[0]!,oa[2]!,mkConst (win ++ `mollifier),mkConst (win ++ `compact),mkConst (win ++ `smooth),
          mkConst (win ++ `mass),mkConst (win ++ `nonneg),mkConst (win ++ `support),p[43]!,g[6]!,g[8]!,
          B,one,h,hpatch,hh,hh1,leading,E,F,hE,hF,hvalue]
      let result ← inferType proof
      let lhs := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Row.continuum) p[:51].toArray) x
      let target ← mkEq lhs result.getAppArgs[2]!
      saveLeadingValue `row_value (p[:51].toArray.push x) proof target


/-! ## Checked value producer: GlobalRowIntegral -/
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open SeparatedSampling

private theorem original_measured_row_global {n : ℕ}
    (X : Set (Euclidean n)) (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (hCX : tsupport C ⊆ X) (ψ : Point → ℝ)
    (A : Euclidean n × Point → MetricTensor n) (M : Euclidean n → MetricTensor n)
    (hrow : ∀ x ∈ X, (∫ z, ψ z • C x (A (x,z))) = C x (M x)) :
    ∀ x, (∫ z, ψ z • C x (A (x,z))) = C x (M x) := by
  intro x
  by_cases hx : x ∈ X
  · exact hrow x hx
  · have hz : C x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hCX h))
    simp only [hz,zero_apply,smul_zero,integral_zero]

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def saveGlobalRow (name : Name) (p : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p value
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed global measured row {name}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking global measured row {name}"
  out.flush
  let pair := Lean.ShareCommon.shareCommon (type,value)
  addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed global measured row {name}"
  out.flush

run_meta do
  withWeightedParent fun p a g d => do
    let fixed := p[:51].toArray
    let some body := (← getConstInfo `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.leading_physical).value? | throwError "missing actual leading physical kernel"
    let physical := (body.beta fixed).headBeta
    let A ← lambdaTelescope physical fun w rhs => do
      unless w.size == 1 do throwError "changed original leading pair kernel"
      let raw := JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate.rootLets rhs
      mkLambdaFVars w raw.appArg!
    let M := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.row) fixed
    let hrow := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.on_measurement_support) fixed
    let globalProof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.original_measured_row_global)
      #[a[0]!,g[3]!,d[0]!,d[2]!,g[6]!,A,M,hrow]
    saveGlobalRow `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.global_original fixed globalProof (← inferType globalProof)

run_meta do
  withWeightedParent fun p _ _ d => do
    let fixed := p[:51].toArray
    let hrow := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.global_original) fixed
    let hC := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.C_eq_common) fixed
    let common := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.commonC) p[:50].toArray
    forallBoundedTelescope (← inferType hrow) (some 1) fun x eqType => do
      unless x.size == 1 && eqType.isAppOfArity ``Eq 3 do throwError "changed global measured row"
      let rhs := eqType.getAppArgs[2]!
      let mapper ← withLocalDeclNoLocalInstanceUpdate `C .default (← inferType d[0]!) fun C => do
        mkLambdaFVars #[C] (rhs.replace fun e => if e == d[0]! then some C else none)
      let rhsCommon := rhs.replace fun e => if e == d[0]! then some common else none
      unless rhsCommon != rhs do throwError "global row lost exact common measurement factor"
      let measured ← mkAppM ``congrArg #[mapper,hC]
      let proof ← mkEqTrans (mkAppN hrow x) measured
      saveGlobalRow `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.global (fixed ++ x) proof (← mkEq eqType.getAppArgs[1]! rhsCommon)


/-! ## Checked value producer: MeasuredPositiveMean -/
open Set Metric
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue

private theorem measured_positive_eq_affine {n : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (hC : tsupport C ⊆ closedBall 0 (4*μ))
    (H P : MetricField n) (heq : EqOn H P (ball 0 (5*μ))) :
    ∀ x, C x (P x) = C x (H x) := by
  intro x
  by_cases hx : x ∈ closedBall (0 : Euclidean n) (4*μ)
  · have h45 : 4*μ < 5*μ := by linarith
    rw [← heq (closedBall_subset_ball h45 hx)]
  · have hz : C x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hC h))
    simp only [hz,zero_apply]

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a _ _ => do
    let fixed := p[:50].toArray
    let commonName := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.commonC
    let some commonBody := (← getConstInfo commonName).value? | throwError "missing unchanged common measurement"
    let raw := (commonBody.beta fixed).headBeta
    unless raw.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do throwError "changed actual measurement4"
    let ca := raw.getAppArgs
    let C := mkAppN (mkConst commonName) fixed
    let hC := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.common_measurement_support) fixed
    let some labels := a[14]!.find? (·.isAppOfArity `JanetCartan.PhysicalBackground.NativeAdmission.labels 41) |
      throwError "lost SAME native39 positive initial"
    let native := labels.getAppArgs[:39].toArray
    let heq := mkAppN (mkConst `JanetCartan.PhysicalBackground.NativePositiveCancellation.affine_eq_positive) native
    let eqType ← inferType heq
    unless eqType.isAppOf ``Set.EqOn do throwError "positive equality lost its genuine physical window"
    let ea := eqType.getAppArgs
    let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.measured_positive_eq_affine)
      #[ca[0]!,ca[2]!,ca[3]!,C,hC,ea[ea.size-3]!,ea[ea.size-2]!,heq]
    let type ← mkForallFVars fixed (← inferType proof)
    let value ← mkLambdaFVars fixed proof
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed original measured positive equality50"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn "kernel checking exact native50 measured positive/physical equality"
    out.flush
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.MeasuredPositiveMean.identity,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    out.putStrLn "kernel passed exact native50 measured positive/physical equality"
    out.flush


/-! ## Checked value producer: NativeMeanSum -/
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a _ _ => do
    let some labels := a[14]!.find? (·.isAppOfArity `JanetCartan.PhysicalBackground.NativeAdmission.labels 41) | throwError "lost same native39"
    let native := labels.getAppArgs[:39].toArray
    let I ← inferType p[50]!
    let fi ← synthInstance (mkApp (mkConst ``Fintype [.zero]) I)
    let univ := mkAppN (mkConst ``Finset.univ [.zero]) #[I,fi]
    withLocalDeclNoLocalInstanceUpdate `x .default (mkApp (mkConst `JanetCartan.Euclidean) a[0]!) fun x => do
      let row := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.row) p[:51].toArray) x
      let rows ← mkLambdaFVars #[p[50]!] row
      let sum ← mkAppM ``Finset.sum #[univ,rows]
      let mean := mkApp (mkAppN (mkConst `JanetCartan.PhysicalBackground.NativePositiveCancellation.positiveMean) native) x
      let target ← mkEq sum mean
      let params := p[:50].toArray.push x
      let type ← mkForallFVars params target
      let value ← mkLambdaFVars params (← mkEqRefl sum)
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed exact native row mean sum"
      let pair := Lean.ShareCommon.shareCommon (type,value)
      let out ← IO.getStdout
      out.putStrLn "kernel checking exact native positive row sum"
      out.flush
      addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Total.native_row_sum,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
      out.putStrLn "kernel passed exact native positive row sum"
      out.flush


/-! ## Checked value producer: FullIdentity -/
open Set MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue

private theorem measured_signed_row_sum (n : ℕ) (I : Type) [Fintype I]
    (C : MetricTensor n →L[ℝ] Euclidean n)
    (E L B : I → Euclidean n) (M : I → MetricTensor n)
    (he : ∀ i, E i = L i - B i) (hl : ∀ i, L i = C (M i)) :
    (∑ i, E i) = C (∑ i, M i) - ∑ i, B i := by
  calc
    _ = ∑ i, (C (M i)-B i) := Finset.sum_congr rfl (fun i _ ↦ by rw [he i,hl i])
    _ = _ := by rw [Finset.sum_sub_distrib,map_sum]

private theorem residual_profile_from_signed_value (n : ℕ)
    (F : CurrentMean.SmoothResidual n) (f : Torus n → Euclidean n)
    (hvalue : ∀ x, f x = F.val x ()) (q : ℕ) (B : ℝ)
    (h : periodicSobolevNorm q f ≤ B) : residualSobolevSeminorm n q F ≤ B := by
  have hf : f = fun x ↦ F.val x () := funext hvalue
  rw [hf] at h
  simpa only [residualSobolevSeminorm,DensityDiscrepancy.densitySobolevSeminorm_eq_norm,
    DensityDiscrepancy.norm_densitySobolevRealization] using h

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def saveFullLeadingIdentity (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p proof
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then throwError "unclosed exact full leading identity {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking exact full leading identity {key}"
  out.flush
  addDecl (.thmDecl {name := if key == `comparison_source_profile then `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile ++ key else `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Total ++ key,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed exact full leading identity {key}"
  out.flush

run_meta do
  withWeightedParent fun p a _ _ => do
    let fixed := p[:50].toArray
    let I ← inferType p[50]!
    let fi ← synthInstance (mkApp (mkConst ``Fintype [.zero]) I)
    let selectedValue := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_leading_comparison_value) fixed
    forallBoundedTelescope (← inferType selectedValue) (some 1) fun x selectedType => do
      unless x.size == 1 && selectedType.isAppOfArity ``Eq 3 do throwError "changed literal selected comparison value50"
      let cx := mkAppN (mkConst `JanetCartan.AmplitudeBound.centeredTorusRepresentative) #[a[0]!,x[0]!]
      let hError := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.row_value) p[:51].toArray) x[0]!
      let et ← inferType hError
      let difference := et.getAppArgs[2]!
      unless difference.isAppOfArity ``HSub.hSub 6 do throwError "changed exact signed row value"
      let E ← mkLambdaFVars #[p[50]!] et.getAppArgs[1]!
      let L ← mkLambdaFVars #[p[50]!] difference.getAppArgs[4]!
      let B ← mkLambdaFVars #[p[50]!] difference.getAppArgs[5]!
      let M ← mkLambdaFVars #[p[50]!] (mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.row) p[:51].toArray) cx)
      let he ← mkLambdaFVars #[p[50]!] hError
      let hl ← mkLambdaFVars #[p[50]!] (mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.NativeRow.global) p[:51].toArray) cx)
      let C := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.commonC) fixed) cx
      let hSum := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.measured_signed_row_sum)
        #[a[0]!,I,fi,C,E,L,B,M,he,hl]
      let sumType ← inferType hSum
      let sumRHS := sumType.getAppArgs[2]!
      let hNative := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Total.native_row_sum) fixed) cx
      let hMeasured ← mkAppM ``congrArg #[sumRHS.getAppArgs[4]!.appFn!,hNative]
      let hPhysical := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.MeasuredPositiveMean.identity) fixed) cx
      let hMean ← mkEqTrans hMeasured hPhysical
      let mapper ← withLocalDeclNoLocalInstanceUpdate `v .default (← inferType sumRHS.getAppArgs[4]!) fun v => do
        mkLambdaFVars #[v] (← mkAppM ``HSub.hSub #[v,sumRHS.getAppArgs[5]!])
      let hDifference ← mkAppM ``congrArg #[mapper,hMean]
      let proof ← mkEqTrans hSum hDifference
      let lhs := mkApp (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.signedContinuum) fixed) x[0]!
      saveFullLeadingIdentity `signed_value (fixed ++ x) proof (← mkEq lhs selectedType.getAppArgs[2]!)

run_meta do
  withWeightedParent fun p _ _ _ => do
    let fixed := p[:50].toArray
    let selectedValue := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_leading_comparison_value) fixed
    forallBoundedTelescope (← inferType selectedValue) (some 1) fun x selectedType => do
      let hValue := mkAppN (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Total.signed_value) fixed) x
      let proof ← mkEqTrans hValue (← mkEqSymm (mkAppN selectedValue x))
      let lhs := (← inferType hValue).getAppArgs[1]!
      saveFullLeadingIdentity `selected_value (fixed ++ x) proof (← mkEq lhs selectedType.getAppArgs[1]!)

run_meta do
  withWeightedParent fun p a _ _ => do
    let fixed := p[:50].toArray
    let root := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile
    let F := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedLeadingComparison) fixed
    let f := mkAppN (mkConst (root ++ `signedContinuum)) fixed
    let hv := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Total.selected_value) fixed
    let profile := mkAppN (mkConst (root ++ `signedContinuum_source_profile)) fixed
    forallBoundedTelescope (← inferType profile) (some 1) fun q qt => do
      unless q.size == 1 && qt.isAppOfArity ``LE.le 4 do throwError "changed sharp actual native50 profile"
      let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileValue.residual_profile_from_signed_value)
        #[a[0]!,F,f,hv,q[0]!,qt.getAppArgs[3]!,mkAppN profile q]
      saveFullLeadingIdentity `comparison_source_profile fixed (← mkLambdaFVars q proof) (← mkForallFVars q (← inferType proof))

run_meta Lean.addDocStringCore `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Value.Total.selected_value "Exact actual signed full-row/full-color continuum equals the literal selected leading comparison in new:eq:mean-source; original measurement, positive current, carrier, outer square, and normalized masks."

run_meta Lean.addDocStringCore `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.comparison_source_profile "Actual native50 all-order profile for the literal selected leading-minus-corrected comparison (new:eq:mean-source): prehistory Ccomparison44(q) times the unchanged sharp h*T^(q-sourceOrder), with no supplied analytic comparison hypothesis and no early T-to-R replacement."

#print axioms JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.comparison_source_profile
end
