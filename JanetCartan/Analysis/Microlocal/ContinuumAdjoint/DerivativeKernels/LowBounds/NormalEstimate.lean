module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Kernel
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Normal

/-!
# The matrix PDO estimate on the genuine carrier space

The Hilbert-space deduction used in `app:ch_background:prop:bg-adjoint`.
The two-position matrix PDO acts on Euclidean measurement data, while its
factor maps to the distinct carrier space with literal measure `dz dη`.
The complete normal identity and its primitive symbol bounds remain producer
obligations; these lemmas alone do not establish the modified carrier estimate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow FourierIntegral AmplitudeBound

variable {n r : ℕ}

/-- A complete matrix normal identity implies the carrier-adjoint estimate.
This uses the checked matrix PDO theorem and the C*-identity without identifying
initial data with measurement data (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_modifiedAdjoint_of_normal (hn : 0 < n) (R : ℝ)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : GraphNormalAmplitudeBounds b R M)
    (S : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) →L[ℂ]
      CarrierL2 n)
    (hN : S.adjoint.comp S = graphNormalL2Operator hn R b M hb) :
    ‖S‖ ≤ Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by
    have := fixedBoxAmplitudeConstant_nonneg n R
    positivity)).mpr
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self S, hN]
  exact norm_graphNormalL2Operator_le hn R b hM hb

/-- Data bound on the actual carrier measure once the exact matrix normal has
been identified (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_modifiedAdjoint_apply_of_normal (hn : 0 < n) (R : ℝ)
    (b : Euclidean n → Euclidean (2 * n) → Matrix (Fin r) (Fin r) ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hb : GraphNormalAmplitudeBounds b R M)
    (S : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) →L[ℂ]
      CarrierL2 n)
    (hN : S.adjoint.comp S = graphNormalL2Operator hn R b M hb)
    (v : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n))) :
    ‖S v‖ ≤ Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M)) * ‖v‖ :=
  (S.le_opNorm v).trans (mul_le_mul_of_nonneg_right
    (norm_modifiedAdjoint_of_normal hn R b hM hb S hN) (norm_nonneg v))

end JanetCartan.ContinuumAdjoint.DerivativeKernels
