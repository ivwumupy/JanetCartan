module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.SourcePhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Normal

/-!
# Literal normalized carrier coefficients

The coefficient extension of `new:lem:scaling`, with the SAME seed Hamilton
chart and canonical null-transport amplitude as `CanonicalCarrier.data`.
The measurement chart, angular mask, high cutoff and initial Lebesgue spaces
are retained. At zero scale the normal and stress coefficients are independent
of position. These are function definitions and checked identifications;
spectral coercivity and the Euclidean Fourier energy identity remain separate
obligations of `app:ch_background:prop:bg-frame`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.FrozenModel

open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow
open CanonicalCarrier NullTransport NormalizedBackground LeadingWave AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The regular extension of the actual normal in `app:ch_background:eq:bg-Nsigma`.
Only its seed value is used at zero; no normal completion of the degenerate
map `G₀` is taken. -/
def normalizedNormal (σ : ℝ) (x : Euclidean n) (z : CarrierParameter) : Euclidean N :=
  normalizedPullback (fun p ↦ normalField T Q F row col Φ Y initial p.1 p.2) (σ, (x, z))

/-- Spatial independence of the actual normalized normal at zero scale
(`new:lem:scaling`). -/
theorem normalizedNormal_zero (x : Euclidean n) (z : CarrierParameter) :
    normalizedNormal T Q F row col Φ Y initial 0 x z =
      normalField T Q F row col Φ Y initial 0 z :=
  normalizedPullback_zero _ _ _

/-- For positive scale this is the canonical principal normal of the dilated
immersion, with the correctly scaled seed null amplitude
(`app:ch_background:eq:bg-Nsigma`). -/
theorem normalizedNormal_eq_sourceDilation {σ : ℝ} (hσ : 0 < σ)
    (hF : ContDiff ℝ ∞ F) (x : Euclidean n) (z : CarrierParameter)
    (hrank : Set.range (normalMap F (σ • x)) =
      (normalSpace F (σ • x) : Set (Euclidean N))) :
    normalizedNormal T Q F row col Φ Y initial σ x z =
      principalNormal (canonicalNormalCompletion (sourceDilation F σ) x)
        (T.carrierGradient Q (σ • x) (parameter z))
        (σ • (carrierScalarAmplitude T Q F row col Φ Y initial (σ • x, parameter z) •
          carrierNullvector T Q col (σ • x, parameter z))) :=
  (principalNormal_sourceDilation_scaled_amplitude hσ hF x hrank _ _).symm

/-- The actual exponential transport factor equals one at physical zero
for unit initial amplitude (`new:lem:scaling`). This follows from the literal
time-zero formula, independently of a bound on the transport potential. -/
theorem carrierScalarAmplitude_origin_unit (z : Euclidean 3) :
    carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1) (0, z) = 1 := by
  simp [carrierScalarAmplitude, transportFromFootpoint, characteristicTransport,
    FlowAmplitude.coordinates_apply, ActualFlow.adaptedCoordinates_apply]

/-- The frozen unit-amplitude normal is exactly the canonical seed null
normal. No arbitrary positive normal amplitude is introduced
(`new:lem:scaling`). -/
theorem normalizedNormal_zero_unit (x : Euclidean n) (z : CarrierParameter) :
    normalizedNormal T Q F row col Φ Y (fun _ ↦ 1) 0 x z =
      principalNormal (canonicalNormalCompletion F 0)
        (T.carrierGradient Q 0 (parameter z)) (carrierNullvector T Q col (0, parameter z)) := by
  rw [normalizedNormal_zero]
  simp only [normalField, carrierScalarAmplitude_origin_unit, one_smul]

variable {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

/-- The source-normalized carrier uses the same measurement chart and masks,
with the actual extended phase and pulled-back coefficients
(`new:lem:scaling`, `app:ch_background:defn:bg-row`). -/
def normalizedCarrierData (σ : ℝ) : CarrierData n N :=
  { data T Q F row col Φ Y initial hr hcell angular high with
    transportedPosition := fun x z ↦ normalizedTransportPosition T Q σ (x, z)
    covector := normalizedCovector T Q σ
    normalField := normalizedNormal T Q F row col Φ Y initial σ
    stressFrame := fun x ↦ Q.1 (σ • x) }

/-- The seed detector is precisely the carrier gradient shared with the
constructed incidence geometry (`app:ch_seed:eq:seed-frozen-detection`). -/
theorem seedCovector_spatialPatch (z : CarrierParameter) :
    seedCovector T Q (T.reference.spatialPatch (parameter z)) =
      T.carrierGradient Q 0 (parameter z) := rfl

/-- The frozen carrier covector is the actual seed carrier gradient at the
origin (`new:lem:scaling`). -/
theorem normalizedCarrierData_covector_zero (x : Euclidean n) (z : CarrierParameter) :
    (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high 0).covector x z =
      T.carrierGradient Q 0 (parameter z) :=
  normalizedCovector_zero T Q x z

/-- The primitive reduced entry is the actual seed stress contraction, with
no position dependence (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalizedCarrierData_reduced_zero (x : Euclidean n) (ξ : Euclidean n) :
    reducedCovector (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high 0)
      x ξ = ActualCarriers.quadratic (Q.1 0) ξ := by
  ext i
  change (∑ j, ∑ k, Q.1 ((0 : ℝ) • x) i j k * (ξ j * ξ k)) =
    ∑ j, ∑ k, ξ j * Q.1 0 i j k * ξ k
  simp only [zero_smul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit hr hcell in
/-- The frozen primitive coefficients with only the physical measurement
factor removed. The actual high and angular masks are retained, including
their possible asymmetry (`app:ch_background:prop:bg-frame`, frozen step). -/
def uncutFrozenCoefficients : ContinuumNormalReduction.TransportSymbol.Coefficients n N where
  measurement := fun _ ↦ 1
  angular := fun p ↦ angular p.1 p.2
  high := high
  normal := fun p ↦ normalField T Q F row col Φ Y initial 0 p.2
  reduced := fun p ↦ ActualCarriers.quadratic (Q.1 0) (T.carrierGradient Q 0 (parameter p.2))

/-- Exact primitive-coefficient identification for the normalized carrier
at scale zero, retaining both physical measurement factors in its normal
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem coefficientsOfCarrier_normalizedCarrierData_zero :
    TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high 0)
      (FixedCutoffs.physical hr 1) =
    { uncutFrozenCoefficients T Q F row col Φ Y initial angular high with
      measurement := FixedCutoffs.physical hr 1 } := by
  unfold TransportKernel.coefficientsOfCarrier
  simp only [normalizedCarrierData_covector_zero, normalizedCarrierData_reduced_zero]
  congr 1
  funext p
  exact normalizedNormal_zero T Q F row col Φ Y initial p.1 p.2

end JanetCartan.ContinuumNormal.FrozenModel
