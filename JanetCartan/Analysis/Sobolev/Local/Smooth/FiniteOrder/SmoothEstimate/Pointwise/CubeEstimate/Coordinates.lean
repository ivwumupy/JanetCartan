module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate.Pointwise.Cube
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Coordinate averaging for the pointwise Sobolev estimate

The averaged fundamental theorem of calculus applies to each derivative tensor.
Contraction against a Euclidean coordinate vector has operator norm at most one,
so one coordinate step uses just two consecutive derivative orders. These are
the analytic inputs to cube averaging in `app:ch_regular:thm:exact-correction`,
with derivative norms as in `app:not:fourier`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem coordinateSlice_eq (z : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    WithLp.toLp 2 (Function.update z i t) =
      WithLp.toLp 2 (Function.update z i 0) + t • EuclideanSpace.single i 1 := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

private theorem enorm_deriv_coordinateSlice_le {u : EuclideanSpace ℝ (Fin n) → F}
    (hu : ContDiff ℝ 1 u) (z : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ‖deriv (fun s ↦ u (WithLp.toLp 2 (Function.update z i s))) t‖ₑ ≤
      ‖fderiv ℝ u (WithLp.toLp 2 (Function.update z i t))‖ₑ := by
  have hd := ((hu.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
      (WithLp.toLp 2 (Function.update z i 0)))
  simp only [Function.comp_def, id_eq, one_smul, ← coordinateSlice_eq] at hd
  rw [hd.deriv, enorm_le_iff_norm_le]
  simpa using (fderiv ℝ u (WithLp.toLp 2 (Function.update z i t))).le_opNorm
    (EuclideanSpace.single i 1)

/-- One coordinate of the averaged FTC estimate for
`app:ch_regular:thm:exact-correction`, valid for arbitrary normed real targets. -/
theorem enorm_le_coordinate_integrals {u : EuclideanSpace ℝ (Fin n) → F}
    (hu : ContDiff ℝ 1 u) (z : Fin n → ℝ) (i : Fin n) :
    ‖u (WithLp.toLp 2 z)‖ₑ ≤
      (∫⁻ t in Icc (z i) (z i + 1), ‖u (WithLp.toLp 2 (Function.update z i t))‖ₑ) +
      ∫⁻ t in Icc (z i) (z i + 1),
        ‖fderiv ℝ u (WithLp.toLp 2 (Function.update z i t))‖ₑ := by
  have hs : ContDiff ℝ 1 (fun t ↦ u (WithLp.toLp 2 (Function.update z i t))) := by
    have hs' : ContDiff ℝ 1 (fun t : ℝ ↦ u
        (WithLp.toLp 2 (Function.update z i 0) + t • EuclideanSpace.single i 1)) :=
      hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    convert hs' using 1
    funext t
    exact congrArg u (coordinateSlice_eq z i t)
  have h := enorm_le_lintegral_unitInterval_add_deriv hs (z i)
  simp only [Function.update_eq_self] at h
  exact h.trans (add_le_add_right (lintegral_mono (fun t ↦
    enorm_deriv_coordinateSlice_le hu z i t)) _)

/-- Averaging a derivative tensor over one coordinate uses only that tensor
and the next derivative. This is the iteration step for the Sobolev norms of
`app:not:fourier` used in `app:ch_regular:thm:exact-correction`. -/
theorem enorm_iteratedFDeriv_le_coordinate_integrals
    {u : EuclideanSpace ℝ (Fin n) → F} (hu : ContDiff ℝ ∞ u)
    (l : ℕ) (z : Fin n → ℝ) (i : Fin n) :
    ‖iteratedFDeriv ℝ l u (WithLp.toLp 2 z)‖ₑ ≤
      (∫⁻ t in Icc (z i) (z i + 1),
        ‖iteratedFDeriv ℝ l u (WithLp.toLp 2 (Function.update z i t))‖ₑ) +
      ∫⁻ t in Icc (z i) (z i + 1),
        ‖iteratedFDeriv ℝ (l + 1) u (WithLp.toLp 2 (Function.update z i t))‖ₑ := by
  have h := enorm_le_coordinate_integrals
    (hu.iteratedFDeriv_right (m := 1) (i := l) (by simp)) z i
  simpa only [← ofReal_norm, norm_fderiv_iteratedFDeriv] using h

/-- Express cube averaging in ordinary product coordinates for Tonelli's
theorem in `app:ch_regular:thm:exact-correction`. -/
theorem lintegral_pointwiseUnitCube_eq_pi
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hf : Measurable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y in pointwiseUnitCube x, f y) =
      ∫⁻ z in Icc (WithLp.ofLp x) (fun i ↦ x i + 1), f (WithLp.toLp 2 z) := by
  simpa only [pointwiseUnitCube, Function.comp_apply, WithLp.toLp_ofLp] using
    (PiLp.volume_preserving_ofLp (Fin n)).setLIntegral_comp_preimage
      measurableSet_Icc (hf.comp (PiLp.volume_preserving_toLp (Fin n)).measurable)

end JanetCartan.LocalSobolev.FiniteOrder
