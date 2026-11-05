module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicMasks
public import JanetCartan.Analysis.Fourier.SeparatedSampling.Counting

/-!
# Original inner normal weights and the supplied external mean weight

These identities distinguish the original conic normal-test mass from the
external positive-mean mass. They use the SAME window, mesh, shifts and nodes.
The external cutoff is supplied, not selected here. Its plateau identifies
only its product with the INNER carrier weight, never the two full weights or
baseline means. Consumers: the actual finite-family coupling of
`app:ch_background:eq:bg-affine-mean` and `app:ch_waves:eq:sampling-prefix-normal`.
No inverse sample weight, division, resampling, or whole-mean equality occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
namespace JanetCartan.PhysicalSampling.OriginalExternalWeights
open Sampling SeparatedSampling ContinuumRow ContinuumRow.CanonicalConic

variable (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z ∈ carrierSupport zRoot (r := r), χ z = 1)

include hχ

/-- The actual external plateau removes χ² ONLY in a product with the inner
conic mass. It does not identify the two weights
(`app:ch_background:eq:bg-density-row`). -/
theorem carrier_weight_mul_external_sq (z : Point) :
    originalConicCarrierWeight zRoot hr z * (χ (carrierSamplingEquiv.symm z)) ^ 2 =
      originalConicCarrierWeight zRoot hr z := by
  by_cases hz : originalConicCarrierWeight zRoot hr z = 0
  · rw [hz, zero_mul]
  · rw [hχ _ (originalConicCarrierWeight_support zRoot hr hz), one_pow, mul_one]

/-- Literal multiplicative relation on EVERY shared sample label, including
zero weights. No sampler or Gaussian/window factor is changed
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weight_eq_carrier_weight_mul_external (w : ℝ → ℝ) (h : ℝ)
    (U : Lattice → Point) (a : Sample) :
    weight (originalConicCarrierWeight zRoot hr) w h U a =
      originalConicCarrierWeight zRoot hr (node h U a) *
        weight (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) w h U a := by
  have he := carrier_weight_mul_external_sq zRoot hr χ hχ (node h U a)
  change h ^ 3 * originalConicCarrierWeight zRoot hr (node h U a) *
      blockWeight w h a.1 (node h U a) =
    originalConicCarrierWeight zRoot hr (node h U a) *
      (h ^ 3 * (χ (carrierSamplingEquiv.symm (node h U a))) ^ 2 *
        blockWeight w h a.1 (node h U a))
  calc
    _ = h ^ 3 * (originalConicCarrierWeight zRoot hr (node h U a) *
        (χ (carrierSamplingEquiv.symm (node h U a))) ^ 2) *
          blockWeight w h a.1 (node h U a) := by rw [he]
    _ = _ := by ring

/-- The native square-root sample factor is transferred by multiplication by
the original nonnegative incidence/spectator cutoff, never by division by μ
(`new:eq:amplitude-test`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sqrt_weight_eq_carrier_cutoff_mul_external (w : ℝ → ℝ) (h : ℝ)
    (U : Lattice → Point) (a : Sample) :
    Real.sqrt (weight (originalConicCarrierWeight zRoot hr) w h U a) =
      (incidenceMask zRoot hr (carrierSamplingEquiv.symm (node h U a)).1 *
        spectatorMask zRoot hr (carrierSamplingEquiv.symm (node h U a)).2) *
      Real.sqrt (weight (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) w h U a) := by
  rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ]
  change Real.sqrt ((incidenceMask zRoot hr (carrierSamplingEquiv.symm (node h U a)).1 *
      spectatorMask zRoot hr (carrierSamplingEquiv.symm (node h U a)).2) ^ 2 *
      weight (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) w h U a) = _
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
    (mul_nonneg (ContDiffBump.nonneg _) (ContDiffBump.nonneg _))]

/-- Inner normal-test weights are bounded by the supplied external background
weights on the SAME nodes. This is a scalar weight inequality, not an equality
of their full Hermitian means (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem weight_le_external {p : ℕ} {w : ℝ → ℝ} {W Binner Bouter Pouter h : ℝ}
    (hw : WindowBounds p w W)
    (hinner : PatchBounds (originalConicCarrierWeight zRoot hr) Binner 1)
    (houter : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) Bouter Pouter)
    (hh : 0 ≤ h) (U : Lattice → Point) (a : Sample) :
    weight (originalConicCarrierWeight zRoot hr) w h U a ≤
      weight (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) w h U a := by
  rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ]
  exact mul_le_of_le_one_left (weight_nonneg hw houter hh a) (hinner.le_bound _)

/-- The inner nonzero labels embed into the supplied external nonzero labels
on one admissible realization. Each weight may use its own valid bounding cube;
no node or original nonzero weight is discarded or created by a division
(`app:ch_waves:thm:sampling`). -/
theorem samples_subset_external {p : ℕ} {w : ℝ → ℝ} {W Binner Bouter Pouter h : ℝ}
    (hw : WindowBounds p w W)
    (hinner : PatchBounds (originalConicCarrierWeight zRoot hr) Binner 1)
    (houter : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) Bouter Pouter)
    (hh : 0 < h) (hh₁ : h ≤ 1) (U : Lattice → Point)
    (hU : ∀ q i, 0 ≤ U q i ∧ U q i < h) :
    samples p Binner (originalConicCarrierWeight zRoot hr) w h U ⊆
      samples p Bouter (fun z ↦ (χ (carrierSamplingEquiv.symm z)) ^ 2) w h U := by
  intro a ha
  apply (mem_samples_iff hw houter hh hh₁ hU).mpr
  have hnonzero := (mem_samples_iff hw hinner hh hh₁ hU).mp ha
  rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ] at hnonzero
  exact (mul_ne_zero_iff.mp hnonzero).2

end JanetCartan.PhysicalSampling.OriginalExternalWeights
