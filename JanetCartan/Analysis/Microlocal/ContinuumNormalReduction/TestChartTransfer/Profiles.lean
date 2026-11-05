module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Compact physical profiles of smooth torus tests

For `app:ch_background:eq:bg-full-complex-amplitude`, localize the actual
periodic lift by a smooth chart cutoff. The resulting physical profile is
smooth and compactly supported. The exact source integral uses the existing
normalized Haar-to-cell measure identity; no measure identification is an input.
The consumers are the finite normal matching in `TestChartTransfer` and the
source Fourier estimates used by `TransportKernel.TestReduction`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumRow.TestChartTransfer
open PeriodicLocalL2 AmplitudeBound
variable {n : ℕ}

/-- The compact physical source obtained from a torus test and a physical
chart cutoff (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def physicalSourceProfile {F : Type*} [SMul ℝ F]
    (χ : Euclidean n → ℝ) (w : Torus n → F) (y : Euclidean n) : F :=
  χ y • periodicLift w y

/-- The physical source is smooth because the torus test has a smooth
periodic lift (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem physicalSourceProfile_contDiff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {χ : Euclidean n → ℝ} {w : Torus n → F}
    (hχ : ContDiff ℝ ∞ χ) (hw : IsSmoothPeriodic w) :
    ContDiff ℝ ∞ (physicalSourceProfile χ w) := hχ.smul hw.2

/-- Compact support is supplied by the actual chart cutoff, independently of
the periodic test (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem physicalSourceProfile_hasCompactSupport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {χ : Euclidean n → ℝ} (hχ : HasCompactSupport χ)
    (w : Torus n → F) : HasCompactSupport (physicalSourceProfile χ w) :=
  hχ.smul_right

/-- The physical source vanishes outside the cutoff chart
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem physicalSourceProfile_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {χ : Euclidean n → ℝ} {K : Set (Euclidean n)}
    (hχ : ∀ y ∉ K, χ y = 0) (w : Torus n → F) {y : Euclidean n}
    (hy : y ∉ K) : physicalSourceProfile χ w y = 0 := by
  simp [physicalSourceProfile, hχ y hy]

/-- At the chosen representative the profile is literally cutoff times the
original test, without any periodization sum or normalization factor
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem physicalSourceProfile_representative {F : Type*} [SMul ℝ F]
    (χ : Euclidean n → ℝ) (w : Torus n → F) (z : Torus n) :
    physicalSourceProfile χ w (centeredTorusRepresentative z) =
      χ (centeredTorusRepresentative z) • w z := by
  simp [physicalSourceProfile, periodicLift, torusQuotient_centeredTorusRepresentative]

/-- Source integration on normalized torus volume equals physical Lebesgue
integration against the constructed profile. The cutoff is one wherever the
kernel is nonzero; this is a support condition, not an integral identity.
Used for the literal finite normal kernels in
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem integral_source_eq_physicalSourceProfile
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (H : Euclidean n → ℂ) (hH : ∀ y, H y ≠ 0 → χ y = 1)
    (w : Torus n → ℂ) :
    (∫ z : Torus n, H (centeredTorusRepresentative z) * w z) =
      ∫ y, H y * physicalSourceProfile χ w y := by
  calc
    _ = ∫ z : Torus n, H (centeredTorusRepresentative z) *
        physicalSourceProfile χ w (centeredTorusRepresentative z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [physicalSourceProfile_representative]
      by_cases hz : H (centeredTorusRepresentative z) = 0
      · simp [hz]
      · rw [hH _ hz, one_smul]
    _ = _ := integral_representative_of_supported hcell
      (fun y ↦ H y * physicalSourceProfile χ w y) (fun y hy ↦ by
      rw [physicalSourceProfile_eq_zero hχ w hy, mul_zero])

/-- Scalar coordinates of a smooth torus vector test are smooth periodic
functions (`app:ch_background:eq:bg-real-symbol`). -/
theorem isSmoothPeriodic_coordinate
    {w : Torus n → EuclideanSpace ℂ (Fin n)} (hw : IsSmoothPeriodic w) (j : Fin n) :
    IsSmoothPeriodic (fun z ↦ w z j) := by
  constructor
  · exact (PiLp.continuous_apply 2 _ j).comp hw.1
  · exact (contDiff_piLp 2).mp hw.2 j

/-- The actual scalar profiles required by the finite matrix source action
are compact and smooth (`app:ch_background:eq:bg-real-symbol`). -/
theorem physicalSourceProfile_coordinate_regular
    {χ : Euclidean n → ℝ} {w : Torus n → EuclideanSpace ℂ (Fin n)}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hw : IsSmoothPeriodic w)
    (j : Fin n) :
    ContDiff ℝ ∞ (physicalSourceProfile χ (fun z ↦ w z j)) ∧
      HasCompactSupport (physicalSourceProfile χ (fun z ↦ w z j)) :=
  ⟨physicalSourceProfile_contDiff hχ (isSmoothPeriodic_coordinate hw j),
    physicalSourceProfile_hasCompactSupport hχc _⟩

/-- The profile agrees almost everywhere with cutoff multiplication of the
existing Euclidean chart lift of the torus L² class. Thus the smooth source is
a representative of the actual chart operation used by the continuum row
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem physicalSourceProfile_eq_chartToEuclidean_ae
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set (Euclidean n)} (hK : MeasurableSet K) (hcell : K ⊆ halfOpenCell n)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (w : PeriodicL2 n F) (w₀ : Torus n → F) (hw : w =ᵐ[volume] w₀) :
    (fun y ↦ χ y • chartToEuclidean (𝕜 := ℝ) hK w y) =ᵐ[volume]
      physicalSourceProfile χ w₀ := by
  have hp := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae hw)
  filter_upwards [chartToEuclidean_coe (𝕜 := ℝ) hK hcell w, hp] with y hy hyp
  by_cases hKy : y ∈ K
  · rw [hy, indicator_of_mem hKy]
    exact congrArg (fun t : F ↦ χ y • t) (hyp (hcell hKy))
  · simp [hχ y hKy, physicalSourceProfile]

end JanetCartan.ContinuumRow.TestChartTransfer
