module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap.RadialSupport

/-!
# Canonical supported frequency gap for the sampling mean normal

`exists_buffered_normalizedFullPhase_gap` constructs the positive gap from the
actual full-phase charts, before the current frame, frequency, radial and color
labels. `averagedGradient_normalizedFullPhase` proves the exact coordinate
identity for the full modulation at all epsilon, retaining both positions and
both spectators. The input core is compact and lies inside the buffered chart;
no unrestricted shell or inverse-amplitude gap is used.

The theorem below supplies exactly the primitive gap consumed by
`FrequencySupport.pairedInverseAmplitude_frequency_lower` and its `2π`-scaled
version, for any already constructed `UniformNormalData` with the following
primitive identifications:

* `G.X₀` lies in the chosen physical core and `G.D₀` lies in the compact radial
  dilation of the incidence/covector core. These must be proved for the SAME masks and
  normalized radial labels. `CanonicalConic.angularMask_tsupport`,
  `CanonicalConic.primitive_masks_mem_bandInputSupport` and the literal
  `RawInputDilation` changes of variables are the existing support producers;
  their radial/angular restrictions must actually fit this chosen chart.
  `closedDirections_mem_normalizedInputCore` proves containment at the frozen
  covector magnitude, and `radialInput_image_compact` retains compactness.
* The retained spectator lies in its closed core, and `G.ε₀ ≤ e`. The radial
  shift is `ε = τ K`, as proved in
  `RawInputDilation.rawPrimaryPhaseDifference_dilate`; every admissible value,
  including zero, is covered. This is not restricted to the transport phase.
* `F.phase` agrees on the physical open ball with `normalizedFullPhase`, at
  every supported input. `ActualPhase.modulation` is its literal producer;
  `exists_normalizedFullPhase_quotient_radius` identifies it with the SAME
  Hamilton difference quotient on a fixed neighborhood. A phase extension
  only needs this local equality, not global equality.

The parent's full `UniformNormalData` and `BandKernelData` construction must
still instantiate these support/phase inputs and the amplitude jets. Primitive
phase regularity/grades come from `ActualQuotient`/`ActualEstimates`, amplitude
grades from the raw WKB/leading construction, and buffered inverse geometry
from the retained actual chart theorem. No analytic-output record is built
here. The consuming estimate is the finite-overlap argument following
`app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound.CanonicalGap
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison AmplitudeBound

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual chart produces the primitive support gap for any same-phase
normal family, uniformly before current data, color/radial labels and frequency.
The remaining premises identify original supports and phases only. The second
conclusion is the literal lower Fourier support radius used in the sampling
mean estimate (`app:ch_seed:eq:seed-normal-annulus`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniformNormalData_supported_gap {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {rmax emax amin amax : ℝ} (hrmax : 0 < rmax) (hemax : 0 < emax)
    (hamin : 0 < amin) (ha : amin ≤ amax) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ s > (0 : ℝ), s ≤ r ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧ ∃ δ > (0 : ℝ), ∃ γ > (0 : ℝ),
    ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
    ∀ (d : ℕ) (G : UniformNormalGeometry n d) (Cjet : ℕ → ℝ)
      (F : UniformNormalData G Cjet) (v : Euclidean 2),
      v ∈ closedBall (spectatorCenter z₀) (s / 2) →
      G.X₀ ⊆ closedBall 0 (s / 2) →
      G.D₀ ⊆ (fun q : ℝ × Euclidean n ↦ radialInput T q.1 q.2) ''
        (Icc amin amax ×ˢ normalizedInputCore T z₀ ηb r) →
      G.ε₀ ≤ e →
      (∀ ε ∈ Icc 0 G.ε₀, ∀ u ∈ G.D₀,
        EqOn (fun x ↦ F.phase ε x u) (fun x ↦ normalizedFullPhase T Q v ε x u)
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
    rw [averagedGradient_eq_of_phase_eqOn T Q (F.phase ε) v ε
      (closedBall_subset_ball (show s / 2 < s by linarith) (hX hx))
      (closedBall_subset_ball (show s / 2 < s by linarith) (hX hy)) (hphase ε hε u hu)]
    obtain ⟨⟨a, w⟩, ⟨ha', hw⟩, rfl⟩ := hD hu
    exact hall Q hQ ε ⟨hε.1, hε.2.trans heG⟩ a ha' v hv x (hX hx) y (hX hy) w
      ⟨closedBall_subset_closedBall (by linarith) hw.1,
        closedBall_subset_closedBall (by linarith) hw.2⟩
  exact ⟨hgap, fun K hK ξ z hne ↦
    unitFrequencyAmplitude_frequency_lower F hε hK hgap hne⟩

end JanetCartan.Sampling.MeanNormalBound.CanonicalGap
