module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalInputCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap

/-!
# Canonical frequency gap in literal sampling input coordinates

The raw kernel uses `normalizedFullPhase` at `canonicalInputCoordinates T u`.
The original `UniformNormalData` stays in the literal Euclidean variable `u`.
Local physical phase equality identifies its averaged gradient with the
canonical one at that changed input; the actual radial gap then supplies the
lower frequency bound. No transformation of the analytic data or its budgets
is needed. The consumer is `LiteralMeanBound.exists_refinedKernelPrefix_mean_bound`
(`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.LiteralMeanBound
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison AmplitudeBound
open MeanNormalBound MeanNormalBound.CanonicalGap MeanNormalBound.NormalizedFullPhase RawKernel
open ContinuumRow.CanonicalConic

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The literal radial dilation fixes incidence and scales only the transverse
covector after the exact published input change. This is the coordinate law
for the compact radial support in `exists_uniformNormalData_supported_gap`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem canonicalInputCoordinates_radial (a : ℝ) (u : ℝ × Euclidean m) :
    canonicalInputCoordinates T (fullInputCoordinates m (u.1, a • u.2)) =
      radialInput T a (canonicalInputCoordinates T (fullInputCoordinates m u)) := by
  apply (adaptedSliceCoordinates T).equiv.injective
  simp only [adapted_canonicalInputCoordinates, radialInput,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

variable (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- Local physical phase agreement at a changed input transfers the averaged
gradient exactly. Only the physical variable is differentiated, so the SAME
phase and coefficient budgets can stay in the literal input coordinates.
Consumer: `exists_uniformNormalData_supported_gap`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem averagedGradient_eq_of_phase_eqOn (φ : Euclidean (m + 1) → Euclidean (m + 1) → ℝ)
    (v : Euclidean 2) (ε : ℝ) {s : ℝ} {x y u : Euclidean (m + 1)}
    (hx : x ∈ ball 0 s) (hy : y ∈ ball 0 s)
    (hφ : EqOn (fun z ↦ φ z u)
      (fun z ↦ normalizedFullPhase T Q v ε z (canonicalInputCoordinates T u))
      (ball 0 s)) :
    averagedGradient φ x y u =
      averagedGradient (normalizedFullPhase T Q v ε) x y (canonicalInputCoordinates T u) := by
  have h := MeanNormalBound.CanonicalGap.averagedGradient_eq_of_phase_eqOn T Q
    (fun z w ↦ φ z ((canonicalInputCoordinates T).symm w)) v ε
    (u := canonicalInputCoordinates T u) hx hy
    (by simpa only [MeasurableEquiv.symm_apply_apply] using hφ)
  simpa only [averagedGradient, averagedPhaseDifferential,
    MeasurableEquiv.symm_apply_apply] using h

omit Q in
/-- The actual chart produces the primitive support gap for the canonical
phase composed with the literal input change, uniformly before current data,
color/radial labels and frequency.
The remaining premises identify original supports and phases only. The second
conclusion is the literal lower Fourier support radius used in the sampling
mean estimate (`app:ch_seed:eq:seed-normal-annulus`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniformNormalData_supported_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean (m + 1)} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ), ∃ γ > (0 : ℝ),
    ∀ Q,
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress (m + 1)) < δ →
    ∀ (d : ℕ) (G : UniformNormalGeometry (m + 1) d) (Cjet : ℕ → ℝ)
      (F : UniformNormalData G Cjet) (v : Euclidean 2),
      v ∈ closedBall (spectatorCenter z₀) (s / 2) →
      G.X₀ ⊆ closedBall 0 (s / 2) →
      canonicalInputCoordinates T '' G.D₀ ⊆
        (fun q : ℝ × Euclidean (m + 1) ↦ radialInput T q.1 q.2) ''
          (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r) →
      G.ε₀ ≤ e →
      (∀ ε ∈ Icc 0 G.ε₀, ∀ u ∈ G.D₀,
        EqOn (fun x ↦ F.phase ε x u)
          (fun x ↦ normalizedFullPhase T Q v ε x (canonicalInputCoordinates T u))
          (ball 0 s)) →
      ∀ ε ∈ Icc 0 G.ε₀,
        (∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
          γ ≤ ‖averagedGradient (F.phase ε) x y u‖) ∧
        ∀ K > 0, ∀ ξ z,
          unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ z ≠ 0 →
            (γ / (2 * Real.pi)) * K ≤ ‖ξ‖ := by
  obtain ⟨r, hr, hrcap, s, hs, hsr, e, he, hecap, δ, hδ, γ, hγ, hall⟩ :=
    exists_radial_normalizedFullPhase_gap T hP hz₀ hk hinc hd hrmax hemax hamin ha
  refine ⟨r, hr, hrcap, s, hs, hsr, e, he, hecap, δ, hδ, γ, hγ, ?_⟩
  intro Q hQ d G Cjet F v hv hX hD heG hphase ε hε
  have hgap : ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
      γ ≤ ‖averagedGradient (F.phase ε) x y u‖ := by
    intro x hx y hy u hu
    rw [LiteralMeanBound.averagedGradient_eq_of_phase_eqOn T Q (F.phase ε) v ε
      (closedBall_subset_ball (show s / 2 < s by linarith) (hX hx))
      (closedBall_subset_ball (show s / 2 < s by linarith) (hX hy)) (hphase ε hε u hu)]
    obtain ⟨⟨a, w⟩, ⟨ha', hw⟩, hcoord⟩ := hD (Set.mem_image_of_mem _ hu)
    rw [← hcoord]
    exact hall Q hQ ε ⟨hε.1, hε.2.trans heG⟩ a ha' v hv x (hX hx) y (hX hy) w
      ⟨closedBall_subset_closedBall (by linarith) hw.1,
        closedBall_subset_closedBall (by linarith) hw.2⟩
  exact ⟨hgap, fun K hK ξ z hne ↦
    unitFrequencyAmplitude_frequency_lower F hε hK hgap hne⟩

end JanetCartan.Sampling.LiteralMeanBound
