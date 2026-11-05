module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Transport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude

/-!
# Literal coefficients after matching the actual null flow

For `app:ch_background:eq:bg-Nsigma` and `app:ch_osc:prop:osc-normal`, Step 4'.
The matching equation produced by `exists_retained_seed_matched_unit_transport`
identifies the actual positive carrier's normal and reduced coefficients with
`normalizedCarrierData`. Consumer: `MatchedSeedCoefficients`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport HamiltonPhase NormalizedBackground.SourceGeometry SourceMatching
open ContinuumNormalReduction.TransportSymbol

/-- The actual positive-scale carrier has exactly the normalized primitive
coefficients on the common buffer. The null-amplitude matching premise is the
proved output of `exists_retained_seed_matched_unit_transport`; no coefficient
or inverse continuity is assumed. The canonical normal scaling and retained
Hamilton covector matching discharge both nonconstant fields.
Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem coefficientsOfCarrier_current_eq_normalized
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ v ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp v, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (row col : Fin n)
    (Φ Y Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {p : Euclidean n × CarrierParameter}
    (hx : p.1 ∈ ball (0 : Euclidean n) T.physicalRadius)
    (hz : parameter p.2 ∈ parameterInterior (2 * P.radius))
    (hb : carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
        (p.1, parameter p.2) • carrierNullvector T Qσ col (p.1, parameter p.2) =
      sourceAmplitude (fun w ↦ carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) w •
        carrierNullvector T Q₀ col w) σ (p.1, parameter p.2)) :
    let a := TransportKernel.coefficientsOfCarrier
      (data T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ) hr hcell angular high)
      (FixedCutoffs.physical hr 1)
    let b := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    a.normal p = b.normal p ∧ a.reduced p = b.reduced p := by
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hx ⟨hσ.le, hσ1⟩
  have hzC : parameter p.2 ∈ parameterCube (2 * P.radius) := fun i ↦ (hz i).le
  have hxU := (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
    (T.target_contains_closed hsx hzC)).1
  have hgrad := current_carrierGradient_source_dilation T Q₀ Qσ hF hrank hphysical
    hseed htrans hσ hσ1 hscaled hx hzC
  have hn := coefficientsOfCarrier_normalizedCarrierData_eq_source T Q₀ F row col Φ Y
    (fun _ ↦ 1) hr hcell angular high (FixedCutoffs.physical hr 1) hP hseed hsx hz
  have hs := normalizedSourceCoefficients_eq_sourceDilation hF
    (fun q ↦ T.carrierGradient Q₀ q.1 (parameter q.2))
    (fun q ↦ carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
      carrierNullvector T Q₀ col (q.1, parameter q.2))
    (FixedCutoffs.physical hr 1) (fun q ↦ angular q.1 q.2) high hσ p (hrank _ hxU)
  dsimp only
  constructor
  · rw [hn.1, hs.1]
    change normalField T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ) p.1 p.2 = _
    unfold normalField
    rw [hgrad, hb]
    rfl
  · rw [hn.2, hs.2, coefficientsOfCarrier_data]
    change (quadratic (Qσ.1 p.1) (T.carrierGradient Qσ p.1 (parameter p.2))).ofLp = _
    rw [hscaled, hgrad]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
