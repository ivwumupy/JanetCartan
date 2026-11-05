module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounding the original raw reference normal

The reference bound in `main:prop:canonical` follows from the SAME uncut row
and the original squared raw masks. All carrier quadratures and both auxiliary
components retain their Hilbert norms and measures. No estimate of the reference
normal is assumed, and no sample-count or smallest-weight factor occurs.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace JanetCartan.CanonicalChange
open ContinuumRow RawCutoffBounds

/-- The actual squared carrier mask is contractive
(`app:ch_background:defn:bg-mixed`). -/
private theorem norm_carrierSquaredCutoff_le_of_unit_mask {n : ℕ}
    (m : Lp ℝ ∞ (carrierMeasure n))
    (hm : ∀ᵐ x ∂carrierMeasure n, m x ∈ Set.Icc (0 : ℝ) 1) (v : CarrierL2 n) :
    ‖carrierSquaredCutoff m v‖ ≤ ‖v‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [carrierSquaredCutoff_coeFn m v, hm] with x hx hm
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs : m x ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans_eq (one_mul _)

/-- Contractivity on the full original Hilbert sum keeps both auxiliary
channels (`main:eq:linear-two-errors`). -/
private theorem norm_rawSquaredCutoff_le_of_unit_masks {n : ℕ} {ν : Type*} [Fintype ν]
    {K : ℝ} (hK : 1 ≤ K) (m : ν → Lp ℝ ∞ (carrierMeasure n))
    (hm : ∀ a, ∀ᵐ x ∂carrierMeasure n, m a x ∈ Set.Icc (0 : ℝ) 1)
    (v : AugmentedInput n ν) : ‖rawSquaredCutoff K m v‖ ≤ ‖v‖ := by
  have hi : ‖auxiliarySquaredCutoff K v.fst.fst‖ ≤ ‖v.fst.fst‖ := by
    simpa using auxiliarySquaredCutoff_band hK v.fst.fst 0
  have he : ‖auxiliarySquaredCutoff K v.snd‖ ≤ ‖v.snd‖ := by
    simpa using auxiliarySquaredCutoff_band hK v.snd 0
  have hc := Finset.sum_le_sum (s := Finset.univ) fun a _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_carrierSquaredCutoff_le_of_unit_mask (m a) (hm a) (v.fst.snd a)) 2
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa [rawSquaredCutoff, WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] using
    add_le_add (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hi 2) hc)
      (pow_le_pow_left₀ (norm_nonneg _) he 2)

/-- The original raw square has operator norm at most one, from its
literal masks (`app:ch_background:defn:bg-mixed`). -/
theorem norm_rawSquaredCutoffCLM_le_one {n : ℕ} {ν : Type*} [Fintype ν] {K : ℝ} (hK : 1 ≤ K)
    (m : ν → Lp ℝ ∞ (carrierMeasure n))
    (hm : ∀ a, ∀ᵐ x ∂carrierMeasure n, m a x ∈ Set.Icc (0 : ℝ) 1) :
    ‖rawSquaredCutoffCLM hK m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [rawSquaredCutoffCLM_apply, one_mul] using norm_rawSquaredCutoff_le_of_unit_masks hK m hm v

/-- The SAME raw reference normal is bounded by the squared uncut row
norm (`main:prop:canonical`). This discharges the reference-normal bound
from primitive row and mask bounds in the canonical residual construction. -/
theorem norm_rawReferenceNormal_le_rowNorm_sq {n : ℕ} {ν : Type*} [Fintype ν]
    (A : AugmentedInput n ν →L[ℝ] OutputL2 n) {K : ℝ} (hK : 1 ≤ K)
    (m : ν → Lp ℝ ∞ (carrierMeasure n))
    (hm : ∀ a, ∀ᵐ x ∂carrierMeasure n, m a x ∈ Set.Icc (0 : ℝ) 1) :
    ‖A.comp ((rawSquaredCutoffCLM hK m).comp A.adjoint)‖ ≤ ‖A‖ ^ 2 := by
  have hP := norm_rawSquaredCutoffCLM_le_one hK m hm
  calc
    _ ≤ ‖A‖ * (‖rawSquaredCutoffCLM hK m‖ * ‖A.adjoint‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖A‖ * (1 * ‖A.adjoint‖) := by gcongr
    _ = ‖A‖ ^ 2 := by rw [ContinuousLinearMap.adjoint.norm_map, one_mul]; ring

end JanetCartan.CanonicalChange
