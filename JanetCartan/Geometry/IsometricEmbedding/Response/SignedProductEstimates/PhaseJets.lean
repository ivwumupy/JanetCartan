module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The short-chord phase retains its derivative scale

The segment formula in `app:ch_pairs:setup:pairs-lag` divides a same-group
phase difference by the parameter distance. Applying the original mixed phase
jet bound along the entire convex patch cancels that divisor. The resulting
constant has no inverse power of the sample separation. This supplies the phase
derivative field of `ResponseTransfer.SourceNegative.SourceGeometry` from the
primitive mixed phase derivatives; the actual phase producer still supplies
those derivatives on its retained patch.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace JanetCartan.SignedProductEstimates

/-- The normalized short-chord phase has the original `L^(r-1)` spatial
jet bound from a mixed phase-parameter derivative bound on the SAME convex
patch (`app:ch_pairs:setup:pairs-lag`). In particular its constants do not
contain the inverse beat. This is the phase input for the true-frequency
source substitution `cutoff_minusSource_eq_real_modulatedSource`. -/
theorem norm_iteratedFDeriv_divided_phase_le {n r : ℕ}
    {K : Set (Euclidean 3)} (hK : Convex ℝ K)
    (φ : Euclidean 3 → Euclidean n → ℝ)
    (D : Euclidean 3 → Euclidean 3 →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ Euclidean n) ℝ)
    {C L : ℝ} {x : Euclidean n}
    (hD : ∀ z ∈ K, HasFDerivWithinAt (fun w ↦ iteratedFDeriv ℝ r (φ w) x) (D z) K z)
    (hbound : ∀ z ∈ K, ‖D z‖ ≤ C * L ^ (r - 1))
    {z w : Euclidean 3} (hz : z ∈ K) (hw : w ∈ K) (hne : z ≠ w)
    (hφz : ContDiffAt ℝ r (φ z) x) (hφw : ContDiffAt ℝ r (φ w) x) :
    ‖iteratedFDeriv ℝ r (fun y ↦ (φ z y - φ w y) / ‖z - w‖) x‖ ≤
      C * L ^ (r - 1) := by
  have hbeat : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsegment := hK.norm_image_sub_le_of_norm_hasFDerivWithin_le hD hbound hw hz
  change ‖iteratedFDeriv ℝ r (φ z) x - iteratedFDeriv ℝ r (φ w) x‖ ≤
    C * L ^ (r - 1) * ‖z - w‖ at hsegment
  have hfun : (fun y ↦ (φ z y - φ w y) / ‖z - w‖) =
      ‖z - w‖⁻¹ • (φ z - φ w) := by
    funext y
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hdiff : ContDiffAt ℝ r (φ z - φ w) x := hφz.sub hφw
  rw [hfun, iteratedFDeriv_const_smul_apply hdiff,
    iteratedFDeriv_sub_apply hφz hφw, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hbeat)]
  calc
    _ ≤ ‖z - w‖⁻¹ * (C * L ^ (r - 1) * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left hsegment (inv_nonneg.mpr hbeat.le)
    _ = C * L ^ (r - 1) := by field_simp

end JanetCartan.SignedProductEstimates
