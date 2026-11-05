module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.CarrierCompatibility.Flow

/-!
# Identification of the actual characteristic formula

The full modulation extension retains the SAME carrier scalar and null
amplitude in `app:ch_waves:thm:leading`. The maps need only satisfy their own
ODE and inverse identities; equality between the two constructions is proved.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius NNReal

namespace JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Equality of footpoints and of the literal scalar and null amplitudes,
from ODE uniqueness and the individual inverse identities. The point `q`
is in adapted coordinates. The parent instantiates the trajectory hypotheses
at the original footpoint `y q`, on a common buffered time interval. No
comparison of the maps or amplitudes is an assumption
(`app:ch_waves:thm:leading`). -/
theorem amplitudes_eq_on_carrier (F : Euclidean n → Euclidean N) (row col : Fin n)
    {Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))}
    {φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {q : ℝ × (Euclidean (n - 1) × Euclidean 3)} {a b : ℝ} {K : ℝ≥0}
    {S : ℝ → Set (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))}
    (h0 : (0 : ℝ) ∈ Ioo a b) (ht : q.1 ∈ Ioo a b)
    (hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (fullVelocity T Q row col t) (S t))
    (hΦ₀ : Φ (0, carrierLabel T (y q)) = carrierLabel T (y q))
    (hφ₀ : φ (0, y q) = y q)
    (hΦ : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ Φ (s, carrierLabel T (y q)))
      (fullVelocity T Q row col t (Φ (t, carrierLabel T (y q)))) t)
    (hφ : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ φ (s, y q))
      (carrierVelocity T Q row col t (φ (t, y q))) t)
    (hΦS : ∀ t ∈ Ioo a b, Φ (t, carrierLabel T (y q)) ∈ S t)
    (hφS : ∀ t ∈ Ioo a b, carrierLabel T (φ (t, y q)) ∈ S t)
    (hYΦ : Y (q.1, Φ (q.1, carrierLabel T (y q))) = carrierLabel T (y q))
    (hφy : φ (q.1, y q) = q.2) :
    Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
    ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y r (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y r w ∧
      scalarAmplitude T Q F row col Φ Y r (w.1, (w.2, T.reference.spatialPatch w.2)) •
          nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y r w • carrierNullvector T Q col w := by
  have heq := forward_eq_on_carrier T Q row col h0 hlip hΦ₀ hφ₀ hΦ hφ hΦS hφS
  have hYeq : Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) := by
    rw [heq q.1 ht, hφy] at hYΦ
    exact hYΦ
  refine ⟨hYeq, fun r ↦ ?_⟩
  let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
  have hscalar : scalarAmplitude T Q F row col Φ Y r
      (w.1, (w.2, T.reference.spatialPatch w.2)) =
      carrierScalarAmplitude T Q F row col φ y r w := by
    have hcw : coordinates (adaptedCoordinates T.data.adapted)
        (w.1, (w.2, T.reference.spatialPatch w.2)) = (q.1, carrierLabel T q.2) := by
      simp only [w, coordinates_symm_apply, coordinates_apply,
        ContinuousLinearEquiv.apply_symm_apply, carrierLabel]
    have hw : coordinates (adaptedCoordinates T.data.adapted) w = q :=
      ContinuousLinearEquiv.apply_symm_apply _ q
    unfold scalarAmplitude carrierScalarAmplitude
    rw [hcw, hw]
    simp only [transportFromFootpoint, characteristicTransport]
    rw [hYeq]
    simp only [initialScalar, carrierLabel]
    unfold scalarTransport transportFactor
    congr 2
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI := ordConnected_Ioo.uIcc_subset h0 ht hs
    change transportPotential T Q F row col
      ((coordinates (adaptedCoordinates T.data.adapted)).symm
        (s, Φ (s, carrierLabel T (y q)))) = _
    rw [heq s hsI]
    rfl
  exact ⟨hscalar, by rw [hscalar, nullvector_on_carrier]⟩

/-- The full formula has the exact original initial datum, using only the
initial forward identity and the full flow's own left inverse. This applies
for arbitrary full covectors as well as on the carrier graph
(`app:ch_waves:thm:leading`). -/
theorem scalarAmplitude_initial (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (hΦ₀ : Φ (0, p) = p) (hYΦ : Y (0, Φ (0, p)) = p) :
    scalarAmplitude T Q F row col Φ Y r (T.data.adapted.embedding p.1, p.2) =
      r (p.1, p.2.1) := by
  have hi : Y (0, p) = p := by simpa only [hΦ₀] using hYΦ
  have hc : coordinates (adaptedCoordinates T.data.adapted)
      (T.data.adapted.embedding p.1, p.2) = (0, p) := by
    have he : (adaptedCoordinates T.data.adapted).symm (0, p.1) =
        T.data.adapted.embedding p.1 := by simp
    rw [← he]
    simp only [coordinates_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [scalarAmplitude, hc, transportFromFootpoint, characteristicTransport,
    hi, scalarTransport_initial, initialScalar]

/-- On the carrier graph the initial null amplitude uses the SAME original
scalar and null column, with no change of sign or normalization
(`app:ch_waves:thm:leading`). -/
theorem nullAmplitude_initial_on_carrier (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (p : Euclidean (n - 1) × Euclidean 3)
    (hΦ₀ : Φ (0, carrierLabel T p) = carrierLabel T p)
    (hYΦ : Y (0, Φ (0, carrierLabel T p)) = carrierLabel T p) :
    scalarAmplitude T Q F row col Φ Y r
        (T.data.adapted.embedding p.1, (p.2, T.reference.spatialPatch p.2)) •
        nullvector T Q col
          (T.data.adapted.embedding p.1, (p.2, T.reference.spatialPatch p.2)) =
      r p • carrierNullvector T Q col (T.data.adapted.embedding p.1, p.2) := by
  have hi := scalarAmplitude_initial T Q F row col Φ Y r (carrierLabel T p) hΦ₀ hYΦ
  simp only [carrierLabel, Prod.eta] at hi
  rw [hi]
  rfl

end JanetCartan.LeadingWave.FullModulation.CarrierCompatibility
