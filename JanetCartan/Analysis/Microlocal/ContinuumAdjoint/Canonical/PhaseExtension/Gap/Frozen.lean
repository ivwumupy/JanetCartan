module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Supported
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Reference

/-!
# The frozen spatial reference for the global affine extension

The reference is the actual frozen transported position with its carrier
fixed at the center. Its transverse rank comes from the spatial inclusion
in the orthogonal adapted coordinates. These are the reference inputs to
the global extension gap in `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The frozen velocity at the literal carrier label, for the reference
in `app:ch_background:eq:bg-derivative-trade`. -/
def frozenVelocity (z : CarrierParameter) : Euclidean (n - 1) :=
  gradient (ActualPhase.dispersion T)
    (T.reference.spatialPatch (CanonicalCarrier.parameter z))

/-- The reference `y + t ∇H₀(ζ(z))` in the original physical coordinates.
The global affine extension freezes `z` at the carrier center
(`app:ch_background:eq:bg-derivative-trade`). -/
def frozenSpatialReference (z : CarrierParameter) : Euclidean n →L[ℝ] Euclidean (n - 1) :=
  ((WithLp.sndL 2 ℝ ℝ (Euclidean (n - 1))) +
    (WithLp.fstL 2 ℝ ℝ (Euclidean (n - 1))).smulRight (frozenVelocity T z)).comp
      (CanonicalCarrier.physicalCoordinates T).toContinuousLinearMap

/-- Evaluation of the fixed spatial reference used in the cutoff correction
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem frozenSpatialReference_apply (z : CarrierParameter) (x : Euclidean n) :
    frozenSpatialReference T z x =
      (CanonicalCarrier.physicalCoordinates T x).ofLp.2 +
        (CanonicalCarrier.physicalCoordinates T x).ofLp.1 • frozenVelocity T z := rfl

/-- Freezing the carrier costs only the variation of the frozen velocity.
The fixed product-cutoff construction uses this estimate after shrinking its
carrier buffer (`app:ch_background:eq:bg-derivative-trade`). -/
theorem norm_frozenSpatialReference_sub_le (z z₀ : CarrierParameter) :
    ‖frozenSpatialReference T z - frozenSpatialReference T z₀‖ ≤
      ‖frozenVelocity T z - frozenVelocity T z₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he : (frozenSpatialReference T z - frozenSpatialReference T z₀) x =
      (CanonicalCarrier.physicalCoordinates T x).ofLp.1 •
        (frozenVelocity T z - frozenVelocity T z₀) := by
    simp only [_root_.sub_apply, frozenSpatialReference_apply, smul_sub]
    abel
  rw [he, norm_smul]
  have ht : ‖(CanonicalCarrier.physicalCoordinates T x).ofLp.1‖ ≤ ‖x‖ := by
    simpa using WithLp.norm_fst_le ℝ (CanonicalCarrier.physicalCoordinates T x)
  exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The reference is the covector gradient of the actual affine frozen phase,
not an additional phase hypothesis (`app:ch_background:eq:bg-derivative-trade`). -/
theorem frozenSpatialReference_eq_gradient (z : CarrierParameter)
    (hz : T.reference.spatialPatch (CanonicalCarrier.parameter z) ∈
      ball (ActualPhase.covectorCenter T) (2 * T.family.radius)) (x : Euclidean n) :
    frozenSpatialReference T z x =
      gradient (fun ζ ↦ Comparison.referencePhase (ActualPhase.dispersion T)
        (CanonicalCarrier.physicalCoordinates T x, ζ))
        (T.reference.spatialPatch (CanonicalCarrier.parameter z)) := by
  rw [Comparison.gradient_referencePhase_covector
    (((ActualPhase.dispersion_smooth T).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt
      (by simp))]
  exact add_comm _ _

/-- The isometric spatial inclusion is a right inverse of the frozen
transported position (`app:ch_background:eq:bg-derivative-trade`). -/
theorem frozenSpatialReference_spatial_inclusion (z : CarrierParameter)
    (v : Euclidean (n - 1)) :
    frozenSpatialReference T z
      ((CanonicalCarrier.physicalCoordinates T).symm (WithLp.toLp 2 (0, v))) = v := by
  simp [frozenSpatialReference_apply]

/-- The adjoint of the frozen reference expands every covector. This is the
unit transverse rank bound behind `app:ch_background:eq:bg-derivative-trade`. -/
theorem norm_le_frozenSpatialReference_adjoint (z : CarrierParameter)
    (v : Euclidean (n - 1)) :
    ‖v‖ ≤ ‖(frozenSpatialReference T z).adjoint v‖ := by
  let w := (CanonicalCarrier.physicalCoordinates T).symm (WithLp.toLp 2 (0, v))
  have hw : ‖w‖ = ‖v‖ := by simp [w, WithLp.norm_toLp_snd]
  have hi : inner ℝ ((frozenSpatialReference T z).adjoint v) w = ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_left,
      frozenSpatialReference_spatial_inclusion, real_inner_self_eq_norm_sq]
  have hb := real_inner_le_norm ((frozenSpatialReference T z).adjoint v) w
  rw [hi, hw] at hb
  by_cases hv : v = 0
  · simp [hv]
  · have hp := norm_pos_iff.mpr hv
    nlinarith

/-- The matrix action in the endpoint API is precisely the Hilbert adjoint
of the spatial derivative (`app:ch_background:eq:bg-derivative-trade`). -/
theorem spatialMatrix_mulVec_eq_adjoint
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (z : CarrierParameter) (x : Euclidean n) (v : Euclidean (n - 1)) :
    WithLp.toLp 2 (spatialMatrix Y z x *ᵥ (fun j ↦ v j)) =
      (fderiv ℝ (fun y ↦ Y (y, z)) x).adjoint v := by
  ext i
  have hi := ContinuousLinearMap.adjoint_inner_left
    (fderiv ℝ (fun y ↦ Y (y, z)) x) (EuclideanSpace.single i 1) v
  simpa [EuclideanSpace.inner_single_right, EuclideanSpace.inner_eq_star_dotProduct,
    spatialMatrix, Matrix.mulVec, dotProduct] using hi.symm

/-- The actual fixed affine reference has unit squared transverse gap at
every physical point and every carrier label
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem frozenSpatialReference_transverseGap (z₀ z : CarrierParameter) (x : Euclidean n) :
    TransverseGap 1 (spatialMatrix (fun p ↦ frozenSpatialReference T z₀ p.1) z x) := by
  intro v
  let w : Euclidean (n - 1) := WithLp.toLp 2 v
  have hn := norm_le_frozenSpatialReference_adjoint T z₀ w
  have hm := spatialMatrix_mulVec_eq_adjoint
    (fun p ↦ frozenSpatialReference T z₀ p.1) z x w
  rw [ContinuousLinearMap.fderiv] at hm
  have hs : ‖w‖ ^ 2 ≤ ‖(frozenSpatialReference T z₀).adjoint w‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [← hm] at hs
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hs
  simpa [dotProduct, pow_two, w] using hs

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
