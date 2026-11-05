module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.TameGain

/-!
# Literal kernels in the Sobolev estimates

The actual full-integral identifications used with the integer estimates in
`app:ch_regular_base:eq:fio-input`. Finite physical budgets discharge every
source-integrability premise, also for the literal adjoint.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:fio-input`: the L² class of the literal full
integral is the bounded realization on compact smooth tests. This equality
transfers both Sobolev membership and the proved one-high bounds to the integral. -/
theorem fullAmplitudeOperator_toLp_eq_twoPositionL2Operator
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    (memLp_fullAmplitudeOperator_of_physicalBudget hd R b hb hs M hM u hu hus).toLp
      (fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u) =
      twoPositionL2Operator hd R b hb hs M hM
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget hd R b hb hs M hM
      u (hu.continuous.memLp_of_hasCompactSupport hus) (hu.of_le (by simp)) hus).symm

/-- `app:ch_regular_base:eq:fio-input`: the literal adjoint kernel is obtained
from the original primitive physical budget alone, with every mask retained. -/
theorem twoPositionL2Operator_adjoint_toLp_ae_fullAmplitudeOperator_of_physicalBudget
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (M : ℝ)
    (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M)
    (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    (twoPositionL2Operator hd R b hb hs M hM).adjoint
        ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ star (b ξ (pairedPosition y x))) u := by
  rw [twoPositionL2Operator_adjoint]
  simpa only [adjointAmplitude_pairedPosition] using
    twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget hd R
      (adjointAmplitude b) (contDiff_adjointAmplitude hb)
      (supportedInCenteredBox_adjointAmplitude hs) M
      (hasAmplitudeDerivativeBound_adjointAmplitude
        (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hM)
      u (hu.continuous.memLp_of_hasCompactSupport hus) (hu.of_le (by simp)) hus

end JanetCartan.Pseudodifferential
