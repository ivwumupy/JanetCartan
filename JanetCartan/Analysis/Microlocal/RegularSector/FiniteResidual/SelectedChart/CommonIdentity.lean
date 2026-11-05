module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.SupportedIdentity
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.CommonOperators
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.CommonWeakDerivative
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev

/-!
# The tested equation on the common measurement region

Localize the supported-chart identity to the actual common output plateau
and identify the retained solver and all three residual terms. The original
physical algebraic gain and signed retarded estimate construct the same
solver's weak derivative for compact smooth inputs. The a.e. equation uses
that derivative and the literal L² representatives. All graph limits are
constructed in `SupportedIdentity`; no differential equation is assumed.

Consumer: the common-mask local solver equation before finite summation.
Source: `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`;
`paper.tex`, `app:ch_regular_base:prop:complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.AmplitudeBounds Characteristic.ConicPhase
open Characteristic.ConicAmplitude Characteristic.ResidualCoordinates Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.EvolutionIntegral.UncutTestAction
open FourierIntegral FourierIntegral.LowBounds FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution
open FiniteEvolution.PhysicalCutoff
open JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral.LowBounds.FrequencyCutoff
open Characteristic.PdoRealization Characteristic.RootFamily
open Pseudodifferential FourierIntegral.FullLowBounds
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- The SAME common-mask solver satisfies the complete tested identity on the
measurement ball. For each compact smooth input, its actual weak derivative
satisfies the a.e. equation. The physical algebraic gain is the positive `n=0`
output of `exists_finite_physical_algebraic_pdos`; all four PDO budgets and
retained primitive hypotheses have the producers named in `SupportedIdentity`.
No output weak derivative or differential equation is assumed. The source
multiplier precedes the Fourier multiplier, all three residuals are retained,
and `Op(α)-I` remains explicit (`energy-complete-residual`). -/
theorem completeResidual_of_common_selected_chart
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (L : ℝ) (hL : 1 ≤ L) (hLf : f.radialThreshold ≤ L) (angular : Euclidean d → ℝ)
    (hang : ContDiff ℝ ∞ angular)
    (hangpos : ∀ η ∈ tsupport angular, 0 < (f.chart p).radialSection η)
    (hangular : ∀ ζ ∈ tsupport (fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L)
      (physicalCoordinates (f.chart p).index ξ) : ℂ)),
      conicMask angular =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ)) :
    let c := f.chart p
    let z : Z := ((coordinateSplit c.index x).1,
      ((coordinateSplit c.index x).2, (coordinateSplit c.index p.val.val).2))
    ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat)
      (_hQ : ContDiffOn ℝ ∞ Q Ω) (_hB : ContDiffOn ℝ ∞ B Ω),
    ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph T T),
    closedBall (z.1, z) c.targetRadius ⊆ C.target →
    ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
    (∀ v ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C v) v) →
    (∀ v ∈ closedBall (z.1, z) c.targetRadius, ‖twoTimePhaseMixed C v - 1‖ ≤ 1/2) →
    (∀ m, cNorm (closedBall (z.1, z) c.targetRadius) m (twoTimePhase C) ≤
      c.phaseCost m * (1 + cNorm (closedBall x RQ) (m+1) Q)) →
    (∀ v ∈ C.target, (C.symm v).2.1 = v.2.1) →
    ∀ Fs : Fin 3 → T → CMat,
    (∀ j, ContDiff ℝ ∞ (Fs j)) →
    let W := fun j : Fin 3 ↦ collared c.radialSection (if j = 0 then 0 else 1) angular (Fs j)
    (∀ j, ContDiff ℝ ∞ (W j)) →
    (∀ j, tsupport (W j) ⊆ ConicPhase.domain c.radialSection
      (C.target ∩ C.symm ⁻¹' (ball z.1 (c.maskRadius/2) ×ˢ
        (ball z.1 (c.maskRadius/2) ×ˢ ball z.2 (c.maskRadius/2))))) →
    (∀ v : T, c.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → ∀ j : Fin (d+1),
      (fun k ↦ W 2 v k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit c.index) v.2.1 v.2.2.2 y) k j)
          ((coordinateSplit c.index).symm (v.1, v.2.2.1))) →
    ∀ G : T → ℝ,
    (∀ v ∈ tsupport (W 0) ∪ tsupport (W 1), G =ᶠ[𝓝 v] ConicPhase.phase c.radialSection C) →
    (∀ v : T, c.timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) → W 2 v ≠ 0 →
      G =ᶠ[𝓝 v] ConicPhase.phase c.radialSection C) →
    ContDiff ℝ ∞ G →
    (∀ t y η, G (t, (t, (y, η))) = inner ℝ y η) →
    let A : E → Fin (d+1) → CMat := fun y i ↦ (coefficient c.index Q y i).map Complex.ofReal
    let Bc : E → CMat := fun y ↦ (zeroth c.index B y).map Complex.ofReal
    let W₀ : TwoTimeAmplitude d (d+1) := curryCharacteristicMatrix (W 0)
    let W₁ : TwoTimeAmplitude d (d+1) := curryCharacteristicMatrix (W 1)
    let Ψ : TwoTimePhase d := fun t s y η ↦ G (t, (s, (y, η)))
    let β : E → ℂ := fun ξ ↦ (dilatedConicMask (f.angularMask p) (2*L)
      (physicalCoordinates c.index ξ) : ℂ)
    let bm : E → E → CMat := conicBminus c.radialSection c.index Q h c.row c.col
    let σ : E → Euclidean d → ℂ := conicSourceSymbol c.radialSection (conicMask angular) c.sourceMask
    let σf : E → Euclidean d → ℂ := conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask
    (∀ y : E, c.timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1) → ∀ s η j,
      WKB.firstOrderApply (fun y i ↦ (A y i).mulVecLin) (fun y ↦ (Bc y).mulVecLin)
        (fun y ↦ Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
          (fun i ↦ (W₀ + W₁) (y 0) s (spatialPart y) η i j)) y =
      Complex.exp (Complex.I * (Ψ (y 0) s (spatialPart y) η : ℂ)) •
        (fun i ↦ twoTimePhysicalApply A Bc W₁ (y 0) s (spatialPart y) η i j)) →
    (∀ y : E, c.timeMask (y 0) = 1 → ∀ η,
      A y 0 * W₀ (y 0) (y 0) (spatialPart y) η =
        σ y η • projector c.index Q h c.row c.col y ((c.radialSection η)⁻¹ • η)) →
    ContDiff ℝ ∞ (Function.uncurry (directAlgebraicSymbol bm σf β)) →
    (∀ ξ ∈ tsupport β, ∀ y ∈ physicalCoordinates c.index ⁻¹' Ω,
      (∑ a, (ξ a : ℂ) • A y a) * bm y ξ =
        1 - projector c.index Q h c.row c.col y
          ((c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ)) →
    ∀ (Rbox Mbound : Fin 4 → ℝ),
    (∀ k, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (directPDOSymbols A Bc W₁ bm σf β k)) (Rbox k) (Mbound k)) →
    let P : Fin 4 → H →L[ℂ] H := fun k ↦ maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (directPDOSymbols A Bc W₁ bm σf β k)
    let b : Bool → TwoTimeAmplitude d (d+1) := directRetardedAmplitudes A Bc W₀ W₁
    ∀ (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
      (retained : Bool → H →L[ℂ] H) (Cret : Bool → ℝ) (Cs : Bool → ℕ → ℝ),
    (∀ k, RetainedSignedRetardedBounds (closedBall x RQ) Q B (3*c.maskRadius/4)
      (z.1-c.maskRadius/2) Ψ (b k) χout χsource β hs (if k then 1 else 0)
      (Cret k) (Cs k) (retained k)) →
    ∀ (Cgain high : ℝ),
    (∀ v : H, MemVectorFourierSobolev 0 v →
      MemVectorFourierSobolev 1 (FiniteEvolution.physicalOperator c.index (P 0) v) ∧
      vectorFourierSobolevNorm 1 (FiniteEvolution.physicalOperator c.index (P 0) v) ≤
        Cgain * (vectorFourierSobolevNorm 0 v + high * ‖v‖)) →
    ∀ (output : E → ℝ) (r : ℝ)
      (houtput : ContDiff ℝ ∞ output) (_houtputCompact : HasCompactSupport output)
      (houtputBound : ∀ y, ‖output y‖ ≤ 1),
    tsupport output ⊆ ball x f.physicalRadius →
    closedBall x r ⊆ interior {y | output y = 1} →
    (∀ y, (output y : ℂ) * χout ((physicalCoordinates c.index).symm y) = (output y : ℂ)) →
    (∀ y, χsource ((physicalCoordinates c.index).symm y) * (f.inputMask y : ℂ) =
      (f.inputMask y : ℂ)) →
    let e := physicalCoordinates c.index
    let Mo : H →L[ℂ] H := sourceCutMultiplier (r := d+1) (fun y ↦ output (e y))
      (houtput.continuous.comp e.continuous) (fun y ↦ houtputBound (e y))
    let Mi : H →L[ℂ] H := sourceCutMultiplier (r := d+1) (fun y ↦ f.inputMask (e y))
      (f.inputMask_smooth.continuous.comp e.continuous) (fun y ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (f.inputMask_range (e y)).1]
          using (f.inputMask_range (e y)).2)
    let Pc : Fin 4 → H →L[ℂ] H := fun k ↦ maskedPhysicalPDO
      (fun y ↦ (output (e y) : ℂ)) (chartInputMask f p) (directPDOSymbols A Bc W₁ bm σf β k)
    let S := Mo.comp ((retained false).comp Mi) + (1 / Complex.I) • Pc 0
    let R := Pc 2 + Mo.comp ((retained true).comp Mi) + (1 / Complex.I) • Pc 3
    let V : Set E := e ⁻¹' ball x r
    (∀ u φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ j,
      physicalTestAction (coefficient c.index Q) (zeroth c.index B)
        (fun y ↦ (S u y).ofLp) φ j = ∫ y, φ y • ((Pc 1 + R) u) y j) ∧
    (∀ u : graphTestSpace (d+1) (d+1), ∃ du : E → E →L[ℝ] (Fin (d+1) → ℂ),
      Mollification.HasWeakFDerivOn volume (fun y ↦ (S (graphTestToLp u) y).ofLp) du univ ∧
      MemLp du 2 volume ∧
      physicalWeakApply (coefficient c.index Q) (zeroth c.index B)
        (fun y ↦ (S (graphTestToLp u) y).ofLp) du =ᵐ[volume.restrict V]
          fun y ↦ (((Pc 1 + R) (graphTestToLp u)) y).ofLp) ∧
    Pc 1 + R = ContinuousLinearMap.id ℂ H + ((Pc 1 - ContinuousLinearMap.id ℂ H) + R) := by
  classical
  intro c z Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear hphase hsourceTime Fs hFs W hWs
    hsupport hphysical G hG hGres hGs hGdiag A Bc W₀ W₁ Ψ β bm σ σf hcancel hlead
    hc hcomp Rbox Mbound hbudget P b χout χsource hs retained Cret Cs hret
    Cgain high hphysicalGain output r houtput houtputCompact houtputBound hout houtputPlateau
    hlocalout hlocalin e Mo Mi Pc S R V
  let U : Set E := e ⁻¹' ball x f.physicalRadius
  have hcanonical := @completeResidual_of_selected_supported_chart d Ω x RQ M A₀ K f p hρb hsrcρ hΩ hKΩ
    L hL hLf angular hang hangpos hangular Q B hQ hB h Φ C hbuffer hsmooth hdiff hnear
    hphase hsourceTime Fs hFs hWs hsupport hphysical G hG hGres hGs hGdiag hcancel hlead
    hc hcomp Rbox Mbound hbudget
  let Op : Bool → H →L[ℂ] H := hcanonical.choose
  have hdata := hcanonical.choose_spec
  have hoperators := selected_common_complete_operators f p Q B (3*c.maskRadius/4)
    (z.1-c.maskRadius/2) Ψ W₀ W₁ bm σf β χout χsource hs output houtput.continuous houtputBound hout
    hlocalout hlocalin Op retained Cret Cs hdata.2.2.1 hret Rbox Mbound hbudget
  have hSeq : S = Mo.comp (Op false + (1 / Complex.I) • P 0) := hoperators.1
  have hTeq : Pc 1 + R = Mo.comp (P 1 + (P 2 + Op true + (1 / Complex.I) • P 3)) :=
    hoperators.2.2.1
  have hV : IsOpen V := isOpen_ball.preimage e.continuous
  have hplateau (y : E) (hy : y ∈ V) : output (e y) = 1 :=
    (show e y ∈ {y | output y = 1} from
      interior_subset (houtputPlateau (ball_subset_closedBall hy)))
  have hVU : V ⊆ U := by
    intro y hy
    apply hout
    apply subset_tsupport output
    change output (e y) ≠ 0
    rw [hplateau y hy]
    exact one_ne_zero
  have htest := tested_equation_sourceCutMultiplier (coefficient c.index Q) (zeroth c.index B)
    (Op false + (1 / Complex.I) • P 0) (P 1 + (P 2 + Op true + (1 / Complex.I) • P 3))
    (fun y ↦ output (e y)) (houtput.continuous.comp e.continuous) (fun y ↦ houtputBound (e y)) hV.measurableSet hplateau
    (fun u φ hφ hcφ hφV j ↦ hdata.2.2.2.1 u φ hφ hcφ (hφV.trans hVU) j)
  have hgain (v : H) (hv : MemVectorFourierSobolev 0 v) :
      MemVectorFourierSobolev 1 (P 0 v) ∧ vectorFourierSobolevNorm 1 (P 0 v) ≤
        Cgain * (vectorFourierSobolevNorm 0 v + high * ‖v‖) := by
    have hh := hphysicalGain ((physicalPullbackL2 c.index).symm v)
      ((memVectorFourierSobolev_physicalPullbackL2_symm c.index 0 v).mpr hv)
    simpa only [physicalOperator_apply, LinearIsometryEquiv.apply_symm_apply,
      memVectorFourierSobolev_physicalPullbackL2_symm,
      vectorFourierSobolevNorm_physicalPullbackL2_symm, LinearIsometryEquiv.norm_map] using hh
  have hd := exists_common_solver_weakDerivative_of_original_algebraic_gain f p Q B
    (3*c.maskRadius/4) (z.1-c.maskRadius/2) Ψ (b false) χout χsource β hs
    (Cret false) (Cs false) (retained false) (hret false)
    (directPDOSymbols A Bc W₁ bm σf β 0) (Rbox 0) (Mbound 0) Cgain high (hbudget 0) hgain
    output houtput houtputCompact houtputBound hout
  obtain ⟨hψo, hψs, hψob, hψsb, hderiv⟩ := hd
  refine ⟨?_, ?_, hoperators.2.2.2⟩
  · intro u φ hφ hcφ hφV j
    exact (congrArg (fun op : H →L[ℂ] H ↦ physicalTestAction
      (coefficient c.index Q) (zeroth c.index B) (fun y ↦ (op u y).ofLp) φ j) hSeq).trans
      ((htest u φ hφ hcφ hφV j).trans
        (congrArg (fun op : H →L[ℂ] H ↦ ∫ y, φ y • (op u) y j) hTeq).symm)
  · intro u
    obtain ⟨du, hdu, hduLp⟩ := hderiv u
    change Mollification.HasWeakFDerivOn volume (fun y ↦ (S (graphTestToLp u) y).ofLp) du univ at hdu
    have hSlocal : (fun y ↦ (S (graphTestToLp u) y).ofLp) =ᵐ[volume.restrict V]
        fun y ↦ ((Op false + (1 / Complex.I) • P 0) (graphTestToLp u) y).ofLp := by
      exact (congrArg (fun op : H →L[ℂ] H ↦
        fun y ↦ (op (graphTestToLp u) y).ofLp) hSeq).eventuallyEq.trans
          (sourceCutMultiplier_ae_on_plateau (fun y ↦ output (e y))
            (houtput.continuous.comp e.continuous) (fun y ↦ houtputBound (e y))
            hV.measurableSet hplateau _)
    have hTlocal : (fun y ↦ ((Pc 1 + R) (graphTestToLp u) y).ofLp) =ᵐ[volume.restrict V]
        fun y ↦ ((P 1 + (P 2 + Op true + (1 / Complex.I) • P 3)) (graphTestToLp u) y).ofLp := by
      exact (congrArg (fun op : H →L[ℂ] H ↦
        fun y ↦ (op (graphTestToLp u) y).ofLp) hTeq).eventuallyEq.trans
          (sourceCutMultiplier_ae_on_plateau (fun y ↦ output (e y))
            (houtput.continuous.comp e.continuous) (fun y ↦ houtputBound (e y))
            hV.measurableSet hplateau _)
    have hcanonicalDu := (hdu.mono (subset_univ V)).congr_ae hSlocal Filter.EventuallyEq.rfl
    have heq := hdata.2.2.2.2.1 V hV hVU (graphTestToLp u) du hcanonicalDu
    refine ⟨du, hdu, hduLp, ?_⟩
    filter_upwards [heq, hSlocal, hTlocal] with y hy hsy hty
    funext j
    simpa only [physicalWeakApply, hsy, hty] using congrFun hy j

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
