module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.Amplitude

/-!
# Quantitative positivity of the actual scalar formula

The coefficient bound and initial lower bound give an explicit positive lower
bound on the entire constructed flow tube (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- A uniform bound for the literal potential yields the explicit lower
bound for the prescribed scalar on the whole tube. The actual local producer
discharges this bound using its reserve-five coefficient theorem
(`app:ch_waves:thm:leading`). -/
theorem scalarAmplitude_lower_bound (F : Euclidean n → Euclidean N) (row col : Fin n)
    {τ B m : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B) (hm : 0 ≤ m)
    {L : Set (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))}
    {D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))))}
    {Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) → Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))}
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (Ioo (-τ) τ ×ˢ L) D)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (Ioo (-τ) τ ×ˢ L))
    (hc : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      |transportPotential T Q F row col w| ≤ B)
    {r : Euclidean (n - 1) × Euclidean 3 → ℝ} (hr : ∀ p ∈ initialProjection '' L, m ≤ r p)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D) :
    m * Real.exp (-B * τ) ≤ scalarAmplitude T Q F row col Φ Y r w := by
  let C := coordinates (Z := (Euclidean 3 × Euclidean (n - 1))) (adaptedCoordinates T.data.adapted)
  have hy := hYU hw
  apply scalarTransport_lower_bound hB hm (hr _ (mem_image_of_mem initialProjection hy.2))
  · simpa only [sub_zero] using (abs_le.mpr ⟨hy.1.1.le, hy.1.2.le⟩)
  · intro s hs
    have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨neg_neg_of_pos hτ, hτ⟩
    have ht : s ∈ Ioo (-τ) τ :=
      ordConnected_Ioo.uIcc_subset h0 hy.1 (uIoc_subset_uIcc hs)
    apply hc (C.symm (s, Φ (s, Y (C w))))
    change C (C.symm (s, Φ (s, Y (C w)))) ∈ D
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hΦD (show (s, Y (C w)) ∈ Ioo (-τ) τ ×ˢ L from ⟨ht, hy.2⟩)

end JanetCartan.LeadingWave.FullModulation
