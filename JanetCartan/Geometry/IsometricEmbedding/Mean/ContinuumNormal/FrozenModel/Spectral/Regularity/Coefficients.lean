module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Construction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Detector

/-!
# Regularity of the literal frozen seed coefficients

The spectator integrability proof for `app:ch_background:prop:bg-frame` uses
these coefficients, with no replacement of the seed normal or detector.
At zero position the normal-completion map is a fixed linear map; thus its
parameter regularity needs no additional immersion estimate. The retained
Hamilton family already contains the smooth current frame. The unit initial
amplitude is the choice in `new:lem:scaling`. The time-zero identity below
also records exactly what survives for nonconstant initial multipliers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol NullTransport LeadingWave AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)

/-- The original initial multiplier evaluated at the actual time-zero
footpoint, with the exponential transport factor computed rather than assumed
(`new:lem:scaling`). The retained flow producer supplies `Y (0,p) = p`
on its initial domain when this is reduced further to `initial (0,z)`. -/
theorem carrierScalarAmplitude_origin (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) :
    carrierScalarAmplitude T Q F row col Φ Y initial (0, z) =
      initial (Y (0, (0, z))) := by
  simp [carrierScalarAmplitude, transportFromFootpoint, characteristicTransport,
    FlowAmplitude.coordinates_apply, ActualFlow.adaptedCoordinates_apply]

/-- At zero the actual normal retains the fourth-power initial multiplier
in its normal density; the pointwise normal itself scales linearly
(`new:lem:scaling`, `app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenSeedNormal_initial_factor
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) (z : CarrierParameter) :
    normalField T Q F row col Φ Y initial 0 z =
      initial (Y (0, (0, parameter z))) • normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z := by
  rw [normalField_eq_scalar_smul, carrierScalarAmplitude_origin]
  simp only [normalField, carrierScalarAmplitude_origin_unit, one_smul]

variable {c C : ℝ} (hP : P.IsValid c C)
include hP

/-- Parameter smoothness of the actual seed gradient used by the frozen
normal and detector (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenSeedGradient_smooth :
    ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦ T.carrierGradient Q 0 (parameter z))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
  have hψ : ContDiff ℝ ∞ (fun z : CarrierParameter ↦ ((0 : Euclidean n), parameter z)) :=
    contDiff_const.prodMk parameter.contDiff
  exact (T.carrierGradient_smooth hP Q).comp
    (f := fun z : CarrierParameter ↦ ((0 : Euclidean n), parameter z))
    (s := parameter ⁻¹' parameterInterior (2 * P.radius)) hψ.contDiffOn
    (fun _ hz ↦ ⟨mem_ball_self T.physicalRadius_pos, hz⟩)

/-- The literal frozen detector is smooth on the original carrier buffer.
This instantiates the polynomial API used by `CanonicalBudgets.Detector`
(`app:ch_seed:eq:seed-frozen-detection`). -/
theorem frozenSeedDetector_smooth :
    ContDiffOn ℝ ∞
      (fun z : CarrierParameter ↦ quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter z)))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
  have hp : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦
      (Q.1 0, T.carrierGradient Q 0 (parameter z)))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    (contDiffOn_const (c := Q.1 0)).prodMk (frozenSeedGradient_smooth T Q hP)
  change ContDiffOn ℝ ∞ ((fun p : (Fin n → MetricTensor n) × Euclidean n ↦
    quadratic p.1 p.2) ∘ (fun z : CarrierParameter ↦ (Q.1 0, T.carrierGradient Q 0 (parameter z)))) _
  exact (contDiff_quadratic (n := n)).comp_contDiffOn hp

private def seedMatrixOfEntries (n : ℕ) :
    (Fin n → Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap LinearMap.id

/-- Smoothness of the actual unit-amplitude seed normal. The frozen
completion is a fixed linear map, while the cofactor column and symmetric
product are polynomial in the SAME carrier gradient and frame
(`new:lem:scaling`, `app:ch_background:eq:bg-Nsigma`). -/
theorem frozenSeedNormal_unit_smooth :
    ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦
      normalField T Q F row col Φ Y (fun _ ↦ 1) 0 z)
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
  have hξ := frozenSeedGradient_smooth T Q hP
  have hp : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦
      (Q.1 0, T.carrierGradient Q 0 (parameter z)))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := contDiffOn_const.prodMk hξ
  have hb : ContDiffOn ℝ ∞
      (fun z : CarrierParameter ↦ carrierNullvector T Q col (0, parameter z))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) :=
    by
      change ContDiffOn ℝ ∞ (CoefficientBounds.right col ∘
        (fun z : CarrierParameter ↦ (Q.1 0, T.carrierGradient Q 0 (parameter z)))) _
      exact (CoefficientBounds.smooth_right col).comp_contDiffOn hp
  have hs : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦
      symmetricProduct (T.carrierGradient Q 0 (parameter z))
        (carrierNullvector T Q col (0, parameter z)))
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    apply (seedMatrixOfEntries n).contDiff.comp_contDiffOn (f := fun z i j ↦
      ((T.carrierGradient Q 0 (parameter z)) i * (carrierNullvector T Q col (0, parameter z)) j +
        (carrierNullvector T Q col (0, parameter z)) i * (T.carrierGradient Q 0 (parameter z)) j) / 2)
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    have hx (i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hξ
    have hk (i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hb
    exact ((hx i |>.mul (hk j)).add (hk i |>.mul (hx j))).div_const 2
  have hn := (canonicalNormalCompletion F 0).toContinuousLinearMap.contDiff.comp_contDiffOn hs
  apply hn.congr
  intro z _
  simp only [normalField, carrierScalarAmplitude_origin_unit, one_smul, principalNormal]
  rfl

/-- For permitted initial multipliers the exact additional regularity is
smooth initial data and a smooth retained footpoint with image in their
initial domain. These are outputs/inputs of `ActualAmplitude.LocalConstruction`;
no regularity of the normal itself is assumed (`new:lem:scaling`). -/
theorem frozenSeedNormal_smooth
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {D : Set (Euclidean (n - 1) × Euclidean 3)}
    (hi : ContDiffOn ℝ ∞ initial D)
    {Z : Set CarrierParameter} (hZ : Z ⊆ parameter ⁻¹' parameterInterior (2 * P.radius))
    (hY : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦ Y (0, (0, parameter z))) Z)
    (hYD : MapsTo (fun z : CarrierParameter ↦ Y (0, (0, parameter z)))
      Z D) :
    ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦ normalField T Q F row col Φ Y initial 0 z) Z := by
  apply ((hi.comp hY hYD).smul ((frozenSeedNormal_unit_smooth T Q F row col Φ Y hP).mono hZ)).congr
  intro z _
  rw [normalField_eq_scalar_smul, carrierScalarAmplitude_origin]
  simp only [normalField, carrierScalarAmplitude_origin_unit, one_smul]
  rfl

end JanetCartan.ContinuumNormal.FrozenModel
