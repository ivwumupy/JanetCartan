module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AngularPartition.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AngularNormals
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles.Detector

/-!
# Canonical angular square partitions preserve the original detector

The masks are constructed from the supplied finite geometric cover in
`AngularPartition.Masks`. Multiplying the SAME complex angular detector by
these real masks preserves its regularity and degree-zero homogeneity. The
original high-pass, including its entire transition region, is unchanged.

Consumers: `MeasuredAmplitude.exists_finite_retained_sampling_realization`
and `sum_angularLocalizedKernel_prefix_normal`
(`app:ch_waves:thm:sampling`, `app:ch_waves:eq:sampling-prefix-normal`).
The actual cone cover, retained raw family, carrier weights and event remain
inputs of the parent sampling construction.
-/

@[expose] public noncomputable section
open Set Metric NormedSpace
open scoped ContDiff

namespace JanetCartan.Sampling
open ContinuumRow.CanonicalConic RawPrimary.MaskProfiles
open SamplingKernelBounds RawInputRealization RawInputPartition

variable {n : ℕ} {I : Type*} [Fintype I]
local notation "E" => Euclidean (n - 1)

variable (ηb : I → Euclidean (n - 1)) (r : I → ℝ)
    (hηb : ∀ i, ηb i ≠ 0) (hr : ∀ i, 0 < r i)

/-- Localize the original complex detector by the constructed real square
mask, retaining its complex value and phase (`app:ch_waves:thm:sampling`). -/
def canonicalLocalizedAngularDetector (a : E → ℂ) (i : I) (η : E) : ℂ :=
  (canonicalAngularSquareMask ηb r hηb hr i η : ℂ) * a η

/-- The localized original detector is smooth away from zero, as required
by `MeasuredAmplitude.exists_finite_retained_sampling_realization`
(`app:ch_waves:thm:sampling`). -/
theorem canonicalLocalizedAngularDetector_contDiffAt (a : E → ℂ)
    (ha : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ a η) (i : I) {η : E} (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (canonicalLocalizedAngularDetector ηb r hηb hr a i) η :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp η
    (canonicalAngularSquareMask_contDiffAt ηb r hηb hr i hη)).mul (ha η hη)

/-- Positive-dilation homogeneity of the SAME localized detector; no
evenness is imposed (`app:ch_waves:thm:sampling`). -/
theorem canonicalLocalizedAngularDetector_homogeneous (a : E → ℂ)
    (hah : ∀ t : ℝ, 0 < t → ∀ η, a (t • η) = a η)
    (i : I) (t : ℝ) (ht : 0 < t) (η : E) :
    canonicalLocalizedAngularDetector ηb r hηb hr a i (t • η) =
      canonicalLocalizedAngularDetector ηb r hηb hr a i η := by
  simp only [canonicalLocalizedAngularDetector,
    canonicalAngularSquareMask_homogeneous ηb r hηb hr i t ht, hah t ht]

/-- Nonzero localized detectors lie in their actual canonical closed cones.
This is the angular-support premise of the finite retained realization
(`app:ch_waves:thm:sampling`). -/
theorem canonicalLocalizedAngularDetector_support (a : E → ℂ) (i : I) {η : E}
    (h : canonicalLocalizedAngularDetector ηb r hηb hr a i η ≠ 0) :
    η ≠ 0 ∧ normalize η ∈ closedDirections (ηb i) (r i) := by
  apply canonicalAngularSquareMask_support ηb r hηb hr i
  intro hz
  simp [canonicalLocalizedAngularDetector, hz] at h

/-- Angular localization multiplies the literal detector mask by the square
factor, with the original high-pass unchanged at EVERY frequency, including
`1 < ‖η‖ < 2` (`app:ch_waves:thm:sampling`). -/
theorem detectorMask_canonicalLocalizedAngularDetector (a : E → ℂ) (H : E → ℝ)
    (i : I) (η : E) :
    detectorMask (canonicalLocalizedAngularDetector ηb r hηb hr a i) H η =
      (canonicalAngularSquareMask ηb r hηb hr i η : ℂ) * detectorMask a H η := by
  simp only [detectorMask, canonicalLocalizedAngularDetector, mul_assoc]

/-- The SAME high-pass removes the origin singularity of every localized
detector (`app:ch_waves:thm:sampling`). -/
theorem contDiff_detectorMask_canonicalLocalizedAngularDetector (a : E → ℂ) (H : E → ℝ)
    (ha : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ a η)
    (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0) (i : I) :
    ContDiff ℝ ∞ (detectorMask (canonicalLocalizedAngularDetector ηb r hηb hr a i) H) :=
  contDiff_detectorMask _ H
    (fun _ hη ↦ canonicalLocalizedAngularDetector_contDiffAt ηb r hηb hr a ha i hη) hH hH₀

/-- The primitive angular cover supplies exactly the nonzero-mask partition
premise of `sum_angularLocalizedKernel_prefix_normal`. The support hypothesis
only concerns nonzero directions; the original angular detector's value at
zero is unrestricted (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem canonicalAngularSquareMask_partition_detectorMask {S : Set E}
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (a : E → ℂ) (H : E → ℝ)
    (hsupport : ∀ η : E, η ≠ 0 → a η ≠ 0 → normalize η ∈ S)
    (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0) {η : E} (hm : detectorMask a H η ≠ 0) :
    ∑ i, canonicalAngularSquareMask ηb r hηb hr i η ^ 2 = 1 := by
  have hη : η ≠ 0 := by
    rintro rfl
    simp [detectorMask, hH₀ 0 (by simp)] at hm
  have ha : a η ≠ 0 := (mul_ne_zero_iff.mp hm).1
  exact canonicalAngularSquareMask_sum_sq ηb r hηb hr hcover (hsupport η hη ha)

/-- Exact squared-norm preservation for the original detector/high-pass
product, at all frequencies. In particular the original transition region
is retained (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_norm_sq_detectorMask_canonicalLocalizedAngularDetector {S : Set E}
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (a : E → ℂ) (H : E → ℝ)
    (hsupport : ∀ η : E, η ≠ 0 → a η ≠ 0 → normalize η ∈ S)
    (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0) (η : E) :
    ∑ i, ‖detectorMask (canonicalLocalizedAngularDetector ηb r hηb hr a i) H η‖ ^ 2 =
      ‖detectorMask a H η‖ ^ 2 := by
  simp only [detectorMask_canonicalLocalizedAngularDetector, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Finset.sum_mul]
  by_cases hm : detectorMask a H η = 0
  · simp [hm]
  · rw [canonicalAngularSquareMask_partition_detectorMask ηb r hηb hr hcover a H
      hsupport hH₀ hm, one_mul]

/-- The same angular squared-norm identity holds before the high-pass at
every nonzero covector (`app:ch_waves:thm:sampling`). -/
theorem sum_norm_sq_canonicalLocalizedAngularDetector {S : Set E}
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (a : E → ℂ) (hsupport : ∀ η : E, η ≠ 0 → a η ≠ 0 → normalize η ∈ S)
    {η : E} (hη : η ≠ 0) :
    ∑ i, ‖canonicalLocalizedAngularDetector ηb r hηb hr a i η‖ ^ 2 = ‖a η‖ ^ 2 := by
  simp only [canonicalLocalizedAngularDetector, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Finset.sum_mul]
  by_cases ha : a η = 0
  · simp [ha]
  · rw [canonicalAngularSquareMask_sum_sq ηb r hηb hr hcover (hsupport η hη ha), one_mul]

variable {P : Type*} [TopologicalSpace P]

/-- The original high-pass proves the kernel floor used in angular normal
reassembly; no additional analytic premise is needed
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem mask_floor_of_eq_detectorMask (a : E → ℂ) (H : E → ℝ)
    (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (D : BandKernelData P n) (hmask : D.mask = detectorMask a H)
    (η : E) (hη : ‖η‖ ≤ 1) : D.mask η = 0 := by
  rw [hmask]
  simp only [detectorMask, hH₀ η hη, Complex.ofReal_zero, mul_zero]

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- Apply the existing annular reassembly theorem to the masks CONSTRUCTED
from the supplied cover. The original kernel, measure, phase and amplitudes
are retained (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_canonicalAngularSquareMask_normal {S : Set E}
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (a : E → ℂ) (H : E → ℝ)
    (hsupport : ∀ η : E, η ≠ 0 → a η ≠ 0 → normalize η ∈ S)
    (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (D : BandKernelData P n) (hmask : D.mask = detectorMask a H) (R : ℝ) (p : P) :
    ∑ i, atomNormal ((angularLocalizedKernel D (mask_floor_of_eq_detectorMask a H hH₀ D hmask)
      (canonicalAngularSquareMask ηb r hηb hr i)
      (canonicalAngularSquareMask_continuousOn ηb r hηb hr i)
      (canonicalAngularSquareMask_abs_le ηb r hηb hr i)).operator R p) =
      atomNormal (D.operator R p) := by
  apply sum_angularLocalizedKernel_normal
  intro η hm
  rw [hmask] at hm
  exact canonicalAngularSquareMask_partition_detectorMask ηb r hηb hr hcover a H
    hsupport hH₀ hm

/-- Apply the existing grouped-prefix reassembly theorem to the actual
constructed masks. Every original radial band remains unchanged
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_canonicalAngularSquareMask_prefix_normal {S : Set E} {J : ℕ}
    (hcover : ∀ θ ∈ S, ∃ i,
      θ ∈ ball (normalize (ηb i)) (angularWidth (ηb i) (r i) / 4))
    (a : E → ℂ) (H : E → ℝ)
    (hsupport : ∀ η : E, η ≠ 0 → a η ≠ 0 → normalize η ∈ S)
    (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
    (D : BandKernelData (Fin J × P) n) (hmask : D.mask = detectorMask a H) (L : ℕ) (p : P) :
    ∑ i, atomNormal (refinedKernelPrefix (angularLocalizedKernel D
      (mask_floor_of_eq_detectorMask a H hH₀ D hmask)
      (canonicalAngularSquareMask ηb r hηb hr i)
      (canonicalAngularSquareMask_continuousOn ηb r hηb hr i)
      (canonicalAngularSquareMask_abs_le ηb r hηb hr i)) L p) =
      atomNormal (refinedKernelPrefix D L p) := by
  apply sum_angularLocalizedKernel_prefix_normal
  intro η hm
  rw [hmask] at hm
  exact canonicalAngularSquareMask_partition_detectorMask ηb r hηb hr hcover a H
    hsupport hH₀ hm

end JanetCartan.Sampling
