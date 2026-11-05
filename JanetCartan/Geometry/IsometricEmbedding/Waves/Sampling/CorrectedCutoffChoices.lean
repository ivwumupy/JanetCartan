module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.SupportChoices
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelExtensions
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicSupport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.PhysicalMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.DensityFootpoint

/-!
# Actual cutoffs for the corrected original-row sample

Construct the joint cutoff and one carrier plateau after the analytic radii
are known. A fixed cap places every smaller original mask, all three physical
cutoffs, and the entire density-coordinate image inside these same domains.
The original scalar center may differ from the incidence center.

Consumers: `exists_correctedColoredCrossBandData_sample_event_after_cutoff`
and `leadingCrossTransportPrefix_originalConic_normal_eq_original`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier CanonicalConic
open MeasuredAmplitude SeparatedSampling RawKernel FullPhaseCharts.ActualComparison
open FullPhaseCharts
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference

/-- Construct a compact joint cutoff after the analytic sampling radii are
known. Its full plateau contains the physical core and the original carrier
graph ball, and its two physical support bounds are simultaneous
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_corrected_sampling_joint_cutoff {n : ℕ}
    (z₀ : Euclidean 3) (ζ₀ : Euclidean (n - 1)) {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : 0 < s) :
    ∃ r > (0 : ℝ), ∃ κ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ,
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      (∀ w, 0 ≤ κ w ∧ κ w ≤ 1) ∧
      tsupport κ ⊆ closedBall ((0 : Euclidean n), (z₀, ζ₀)) ρ ∧
      Prod.fst '' tsupport κ ⊆ closedBall (0 : Euclidean n) (ρ / 2) ∧
      Prod.fst '' tsupport κ ⊆ closedBall (0 : Euclidean n) (s / 4) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) r,
        ∀ q ∈ closedBall (z₀, ζ₀) (ρ / 2), κ (x, q) = 1 := by
  obtain ⟨χ, hχρ, hχs, _, _⟩ := exists_retained_physical_cutoff (n := n) hρ hs
  let a := ((0 : Euclidean n), (z₀, ζ₀))
  let θ : ContDiffBump a := ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩
  let κ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ χ w.1 * θ w
  have hκ : ContDiff ℝ ∞ κ := (χ.contDiff.comp contDiff_fst).mul θ.contDiff
  have hκc : HasCompactSupport κ := θ.hasCompactSupport.mul_left
  have hκθ : tsupport κ ⊆ closedBall a (3 * ρ / 4) := by
    simpa only [θ.tsupport_eq] using (tsupport_mul_subset_right : tsupport κ ⊆ tsupport (θ : _ → ℝ))
  have hκχ : tsupport κ ⊆ Prod.fst ⁻¹' closedBall (0 : Euclidean n) χ.rOut := by
    apply closure_minimal _ (isClosed_closedBall.preimage continuous_fst)
    intro w hw
    have hx : χ w.1 ≠ 0 := (mul_ne_zero_iff.mp hw).1
    have hx' : w.1 ∈ Function.support (χ : Euclidean n → ℝ) := hx
    exact ball_subset_closedBall (by simpa only [χ.support_eq] using hx')
  have hproj : Prod.fst '' tsupport κ ⊆ closedBall (0 : Euclidean n) χ.rOut := by
    rintro _ ⟨w, hw, rfl⟩
    exact hκχ hw
  refine ⟨χ.rIn, χ.rIn_pos, κ, hκ, hκc, ?_,
    hκθ.trans (closedBall_subset_closedBall (by linarith)),
    hproj.trans (closedBall_subset_closedBall hχρ),
    hproj.trans (closedBall_subset_closedBall hχs), ?_⟩
  · intro w
    exact ⟨mul_nonneg χ.nonneg θ.nonneg,
      (mul_le_mul_of_nonneg_right χ.le_one θ.nonneg).trans (by simpa using θ.le_one)⟩
  · intro x hx q hq
    have hxr : χ.rIn ≤ ρ / 2 := χ.rIn_lt_rOut.le.trans hχρ
    have hw : (x, q) ∈ closedBall a (ρ / 2) := by
      rw [← closedBall_prod_same]
      exact ⟨closedBall_subset_closedBall hxr hx, hq⟩
    change χ x * θ (x, q) = 1
    rw [χ.one_of_mem_closedBall hx, θ.one_of_mem_closedBall hw, mul_one]

/-- Choose the actual compact amplitude and carrier cutoffs after the sampling
radii, then a cap for the original masks. Every smaller original radius has
all three physical cutoffs on the same amplitude plateau and inside the band
measurement core. Its full density-coordinate image stays in the supplied
original compatibility domain; scalar and incidence centers are not identified
(`app:ch_waves:thm:sampling`, `app:ch_mean_pairs:eq:mean-normal-comparison`). -/
theorem exists_originalConic_corrected_sampling_cutoffs
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {ρ radius s bandRadius : ℝ} (hρ : 0 < ρ) (hradius : 0 < radius)
    (hs : 0 < s) (hbandRadius : 0 < bandRadius)
    {V : Set (ℝ × (Euclidean (m + 1 - 1) × Euclidean 3))}
    (hV : IsOpen V) (hcenter : (0, (0, z₀)) ∈ V) :
    ∃ κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ,
    ∃ ψ : Point → ℝ, ∃ Bψ > (0 : ℝ), ∃ cap > (0 : ℝ),
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ (∀ w, 0 ≤ κ w ∧ κ w ≤ 1) ∧
      tsupport κ ⊆ closedBall ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀)) ρ ∧
      Prod.fst '' tsupport κ ⊆ closedBall (0 : Euclidean (m + 1)) (ρ / 2) ∧
      Prod.fst '' tsupport κ ⊆ closedBall (0 : Euclidean (m + 1)) (s / 4) ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ PatchBounds ψ Bψ 1 ∧
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) radius ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) ∧
      ∀ b : ℝ, ∀ hb : 0 < b, b ≤ cap →
        4 * b < 1 / 2 ∧
        MapsTo (densityCoordinates T)
          (closedBall (0 : Euclidean (m + 1)) (4 * b) ×ˢ carrierSupport z₀ (r := b)) V ∧
        (∀ i : Fin 3, tsupport (FixedCutoffs.physical (n := m + 1) hb i) ⊆
          closedBall (0 : Euclidean (m + 1)) (bandRadius / 8)) ∧
        (∀ z ∈ carrierSupport z₀ (r := b),
          (parameter z, T.reference.spatialPatch (parameter z)) ∈
            closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4)) ∧
        (∀ i : Fin 3, ∀ x ∈ tsupport (FixedCutoffs.physical (n := m + 1) hb i),
          ∀ z ∈ carrierSupport z₀ (r := b),
            ∀ shift : Euclidean (m + 1 - 1), ‖shift‖ ≤ ρ / 4 →
              κ (x, parameter z, T.reference.spatialPatch (parameter z) + shift) = 1) ∧
        ∀ z, originalConicCarrierWeight z₀ hb z ≠ 0 →
          ψ z = 1 ∧ WithLp.toLp 2 z ∈ parameterCube P.radius ∧
          (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
            ball (z₀, T.reference.spatialPatch z₀) (ρ / 4) := by
  obtain ⟨rκ, hrκ, κ, hκ, hκc, hκbound, hκsupport, hκρ, hκs, hκone⟩ :=
    exists_corrected_sampling_joint_cutoff z₀ (T.reference.spatialPatch z₀) hρ hs
  obtain ⟨d, hd, ψ, Bψ, hBψ, hψ, hψc, hψbounds, hψone, hψsupport, hψbuffer⟩ :=
    exists_retained_carrier_cutoff_buffered T hP hz₀ hρ hradius hs
  let cell := densityCoordinates T ⁻¹' V
  have hcell : IsOpen cell := hV.preimage (densityCoordinates T).continuous
  have hcellcenter : ((0 : Euclidean (m + 1)), (z₀ 0, spectatorCenter z₀)) ∈ cell := by
    change densityCoordinates T (0, (z₀ 0, spectatorCenter z₀)) ∈ V
    have he : parameter (z₀ 0, spectatorCenter z₀) = z₀ := by
      ext i
      fin_cases i <;> rfl
    change NullTransport.FlowAmplitude.coordinates
      (NullTransport.ActualFlow.adaptedCoordinates T.data.adapted) (0, parameter (z₀ 0, spectatorCenter z₀)) ∈ V
    simpa only [NullTransport.FlowAmplitude.coordinates_apply, map_zero,
      Prod.fst_zero, Prod.snd_zero, he] using hcenter
  obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hcell.mem_nhds hcellcenter)
  obtain ⟨cgraph, hcgraph, hgraph⟩ := exists_originalConic_sampling_support_cap
    T hP hz₀ hρ hcell hcellcenter
  obtain ⟨cψ, hcψ, _, hparameter⟩ :=
    NormalizedSelection.exists_carrierSupport_in_parameter_ball z₀ hd zero_lt_one
  let cap := min cgraph (min (ε / 8) (min (rκ / 8)
    (min (bandRadius / 32) (min cψ (1 / 16)))))
  have hcap : 0 < cap := by dsimp [cap]; positivity
  refine ⟨κ, ψ, Bψ, hBψ, cap, hcap, hκ, hκc, hκbound, hκsupport, hκρ, hκs,
    hψ, hψc, hψbounds, hψsupport, ?_⟩
  intro b hb hbcap
  have hbgraph : b ≤ cgraph := hbcap.trans (min_le_left _ _)
  have hbε : b ≤ ε / 8 := hbcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbκ : b ≤ rκ / 8 := hbcap.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbband : b ≤ bandRadius / 32 := hbcap.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hbψ : b ≤ cψ := hbcap.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbsmall : b ≤ 1 / 16 := hbcap.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    apply hεsub
    rw [← closedBall_prod_same]
    refine ⟨closedBall_subset_closedBall (by linarith) hp.1, ?_⟩
    rw [← closedBall_prod_same]
    exact ⟨closedBall_subset_closedBall (by linarith) hp.2.1,
      closedBall_subset_closedBall (by linarith) hp.2.2⟩
  · intro i
    exact (FixedCutoffs.physical_tsupport_four hb i).trans
      (closedBall_subset_closedBall (by linarith))
  · intro z hz
    exact (hgraph b hbgraph).1 (mem_image_of_mem parameter hz)
  · intro i x hx z hz shift hshift
    have hzg := (hgraph b hbgraph).1 (mem_image_of_mem parameter hz)
    have hpair := retained_shift_mem_plateau T
      ((0 : Euclidean (m + 1)), (z₀, T.reference.spatialPatch z₀))
      (mem_closedBall_self (by positivity : 0 ≤ ρ / 2)) hzg hshift
    rw [← closedBall_prod_same] at hpair
    exact hκone x (closedBall_subset_closedBall (by linarith)
      (FixedCutoffs.physical_tsupport_four hb i hx)) _ hpair.2
  · intro z hz
    have hsupport := originalConicCarrierWeight_support z₀ hb hz
    have hsupport' : carrierSamplingEquiv.symm z ∈ carrierSupport z₀ (r := cψ) :=
      ⟨closedBall_subset_closedBall (by linarith) hsupport.1,
        closedBall_subset_closedBall (by linarith) hsupport.2⟩
    have hpar : WithLp.toLp 2 z ∈ closedBall z₀ d := by
      have hp := ball_subset_closedBall (hparameter hsupport')
      have heq : parameter (carrierSamplingEquiv.symm z) = WithLp.toLp 2 z := by
        ext i
        fin_cases i <;> rfl
      rwa [heq] at hp
    have he : ψ z = 1 := hψone z hpar
    exact ⟨he, hψbuffer z (by rw [he]; exact one_ne_zero)⟩

end JanetCartan.Sampling
