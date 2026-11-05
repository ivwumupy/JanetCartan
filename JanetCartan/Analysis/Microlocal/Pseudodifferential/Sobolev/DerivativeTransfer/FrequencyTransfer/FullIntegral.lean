module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.SourceBounds

/-!
# Transfer algebra through the full frequency integral

For `app:ch_regular_base:eq:graph-derivative-transfer`, the source integration
identity survives the full frequency integral. Integrability is derived from
the original primitive physical budget, including for the modified amplitude.
Identifying this expression as the distributional output derivative additionally
requires the compact-frequency weak identity and the operator limit.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the actual full
frequency integral of the output-derivative amplitude splits into the transferred
operator and the original operator on the differentiated datum. The sole
amplitude bound is a finite primitive bound on the original amplitude. -/
theorem fullAmplitudeOperator_outputDerivativeAmplitude
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d)
    {N : ℕ} (hN : d + 1 ≤ N) {A : ℝ}
    (hA : HasAmplitudeDerivativeBound b (N + 1) A)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) (x : E) :
    fullAmplitudeOperator
        (fun x y ξ ↦ outputDerivativeAmplitude b i ξ (pairedPosition x y)) u x =
      fullAmplitudeOperator
        (fun x y ξ ↦ transferAmplitude b i ξ (pairedPosition x y)) u x +
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y))
        (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x := by
  have ht := integrable_sourceAmplitudeTransform_transferAmplitude b hb i hN hA
    u (hu.of_le (by simp)) hus x
  have hd : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hi := integrable_sourceAmplitudeTransform_of_physicalBudget b hb
    (hN.trans (Nat.le_succ N)) hA _ (hd.of_le (by simp))
    (hus.fderiv_apply ℝ (EuclideanSpace.single i 1)) x
  simp only [fullAmplitudeOperator, Real.fourierInv_eq_fourier_neg, Real.fourier_eq]
  simp_rw [sourceAmplitudeTransform_outputDerivativeAmplitude b
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i u hu hus, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff (-x)).mpr ht)
    ((Real.fourierIntegral_convergent_iff (-x)).mpr hi)

end JanetCartan.Pseudodifferential
