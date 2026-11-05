module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.TameBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction

/-!
# The literal full-flow preparation matrix

The relative estimates for `app:ch_mean_pairs:eq:mean-density-lipschitz` use
these same supplied maps, with arbitrary signed initial data. No background,
new flow, or new initializer is selected. The consumer is the reserve-fourteen
estimate in `PreparationTransportPrimitives.OneHigh`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.CurrentMean.PreparationTransportPrimitives
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open LeadingWave LeadingWave.FullModulation AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))

/-- The unperiodized real principal matrix on the retained full flow,
`app:ch_waves:eq:arbitrary-b-amplitudes`. -/
def fullTransportPrincipalMatrix (u : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Matrix (Fin N) (Fin n) ℝ :=
  principalMatrix (principalNormal (canonicalNormalCompletion F w.1)
    (phaseGradient T Q w.1 w.2.2)
    (scalarAmplitude T Q F row col Φ Y u w • nullvector T Q col w))
    (phaseGradient T Q w.1 w.2.2)

/-- Linearity in the signed initial scalar, with the flow and immersion
unchanged (`app:ch_mean_pairs:eq:mean-density-lipschitz`). -/
theorem fullTransportPrincipalMatrix_smul (a : ℝ)
    (u : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    fullTransportPrincipalMatrix T Q F row col Φ Y (a • u) =
      a • fullTransportPrincipalMatrix T Q F row col Φ Y u := by
  have ha := (scalarAmplitudeLinearMap T Q F row col Φ Y).map_smul a u
  change scalarAmplitude T Q F row col Φ Y (a • u) =
    a • scalarAmplitude T Q F row col Φ Y u at ha
  funext w
  simp only [fullTransportPrincipalMatrix, ha, Pi.smul_apply, smul_eq_mul]
  rw [← smul_smul, principalNormal_smul]
  ext i j
  simp [principalMatrix, PiLp.smul_apply, Matrix.smul_apply]
  ring

/-- Entrywise complex conversion is a fixed real continuous linear map;
it therefore costs no derivatives in `app:ch_waves:eq:joint-tame`. -/
def preparationMatrixComplexification : Matrix (Fin N) (Fin n) ℝ →L[ℝ]
    Matrix (Fin N) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.map Complex.ofReal
      map_add' := by intros; ext i j; simp
      map_smul' := by intros; ext i j; simp [Complex.real_smul] }

/-- Signed characteristic data are smooth on the supplied full-flow domain.
The primitive smooth coefficients come from `exists_full_modulation_coefficient_bounds_before_geometry`,
and the maps and their ranges from the retained full-flow constructor.
Positivity is unnecessary (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem scalarAmplitude_contDiffOn_of_retained_flow
    {D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))))}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    {z : Euclidean 3 × Euclidean (n - 1)} {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ)
    (hphys : coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D ⊆ Ω)
    (hc : ContDiffOn ℝ ∞ (transportPotential T Q F row col) Ω)
    (hΦ : ContDiffOn ℝ ∞ Φ
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q))
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) D)
    (hY : ContDiffOn ℝ ∞ Y D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D
      (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)))
    {u : Euclidean (n - 1) × Euclidean 3 → ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball ((0 : Euclidean (n - 1)), z.1) (R / 4))) :
    ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y u)
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D) := by
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
    (adaptedCoordinates T.data.adapted)
  have hc' : ContDiffOn ℝ ∞ (transportPotential T Q F row col ∘ C.symm) D :=
    (hc.mono hphys).comp C.symm.contDiff.contDiffOn (by
      intro q hq
      change C (C.symm q) ∈ D
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  have hr := contDiffOn_initialScalar hu
    ((initialProjection_mapsTo_ball ((0 : Euclidean (n - 1)), z) (R / 4)).mono_left
      (ball_subset_ball (by linarith : R / 8 ≤ R / 4)))
  exact (contDiffOn_transportFromFootpoint isOpen_Ioo ordConnected_Ioo isOpen_ball
    (contDiffOn_flowTransportCoefficient hc' hΦ hΦD) hr
    (show (0 : ℝ) ∈ Ioo (-τ) τ by constructor <;> linarith) hY hYU).comp
      C.contDiff.contDiffOn (fun _ hw ↦ hw)

end JanetCartan.CurrentMean.PreparationTransportPrimitives
