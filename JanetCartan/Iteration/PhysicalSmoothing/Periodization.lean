module

public import JanetCartan.Iteration.PhysicalSmoothing.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Norms

/-!
# Exact auxiliary realization of the compact physical source

For `new:eq:mean-source`, only the finite-moment tensor source is realized on
its auxiliary torus.  The real Schwartz history is never periodized.  Every
Cartesian derivative energy below is literally the energy of that same
compact tensor, with physical Lebesgue measure, and the order is unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSmoothing

open LocalSobolev AmplitudeBound PeriodicLocalL2 DefectSmoothing

variable {n : ℕ} {r : ℝ} {f : MetricField n}

/-- Exact Cartesian jet identity for the compact tensor in
`new:eq:mean-source`, including the faces of the fixed cell. -/
theorem multiindexDeriv_tensorPeriodization (hr : r < 1 / 2)
    (hs : tsupport f ⊆ Metric.ball 0 r) (hf : ContDiff ℝ ∞ f)
    (α : Fin n → ℕ) (z : Torus n) :
    periodicMultiindexDeriv α (tensorPeriodization f) z =
      cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α
        (centeredTorusRepresentative z) := by
  calc
    _ = cartesianJetDerivative
        (fun j ↦ iteratedFDeriv ℝ j (periodicLift (tensorPeriodization f))) α
        (centeredTorusRepresentative z) := by
      rw [AuxiliaryRawBand.cartesianJetDerivative_periodicLift
        (isSmoothPeriodic_tensorPeriodization hr hs hf)]
      simp [periodicLift]
    _ = _ := by
      unfold cartesianJetDerivative
      dsimp only
      rw [((tensorPeriodization_eventuallyEq hr hs (centeredTorusRepresentative_mem z)).iteratedFDeriv
        ℝ (sobolevDerivativeList α).length).self_of_nhds]

private theorem tensor_cartesianJetDerivative_eq_zero_outside_cell
    (hr : r < 1 / 2) (hs : tsupport f ⊆ Metric.ball 0 r)
    (α : Fin n → ℕ) {x : Euclidean n} (hx : x ∉ halfOpenCell n) :
    cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α x = 0 := by
  have hbox : tsupport f ⊆ {x | ∀ i, |x i| ≤ r} := by
    intro y hy i
    have hn : ‖y‖ < r := by simpa using hs hy
    exact (PiLp.norm_apply_le y i).trans hn.le
  have hjet : iteratedFDeriv ℝ (sobolevDerivativeList α).length f x = 0 := by
    by_contra h
    exact hx (UniformStep.Periodization.support_subset_halfOpenCell hr
      ((tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (sobolevDerivativeList α).length).trans hbox) h)
  simp [cartesianJetDerivative, hjet]

/-- Exact Lebesgue/Haar identification for each derivative of the SAME tensor
in `new:eq:mean-source`; the support gap, not a periodic history, proves it. -/
theorem integral_multiindexDeriv_tensorPeriodization_sq (hr : r < 1 / 2)
    (hs : tsupport f ⊆ Metric.ball 0 r) (hf : ContDiff ℝ ∞ f)
    (α : Fin n → ℕ) :
    (∫ z, ‖periodicMultiindexDeriv α (tensorPeriodization f) z‖ ^ 2) =
      ∫ x, ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α x‖ ^ 2 := by
  simp_rw [multiindexDeriv_tensorPeriodization hr hs hf α]
  rw [integral_representative
    (fun x ↦ ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f) α x‖ ^ 2)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [tensor_cartesianJetDerivative_eq_zero_outside_cell hr hs α hx]

/-- No derivative-order or carrier loss in the auxiliary source realization
of `new:eq:mean-source`. -/
theorem periodicDerivativeL2Norm_tensorPeriodization (hr : r < 1 / 2)
    (hs : tsupport f ⊆ Metric.ball 0 r) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    periodicDerivativeL2Norm m (tensorPeriodization f) =
      cartesianJetNorm univ m (fun j ↦ iteratedFDeriv ℝ j f) := by
  unfold periodicDerivativeL2Norm cartesianJetNorm cartesianJetEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  rw [periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),
    integral_multiindexDeriv_tensorPeriodization_sq hr hs hf]
  simp

/-- The actual Fourier Sobolev norm of the compact tensor source is bounded
by its same-order physical Cartesian norm (`new:eq:mean-source`). -/
theorem periodicSobolevNorm_tensorPeriodization_le (hr : r < 1 / 2)
    (hs : tsupport f ⊆ Metric.ball 0 r) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    periodicSobolevNorm m (tensorPeriodization f) ≤
      Real.sqrt (m.factorial : ℝ) *
        cartesianJetNorm univ m (fun j ↦ iteratedFDeriv ℝ j f) := by
  simpa only [periodicDerivativeL2Norm_tensorPeriodization hr hs hf] using
    periodicSobolevNorm_le_factorial_mul_derivativeL2Norm
      (isSmoothPeriodic_tensorPeriodization hr hs hf) m

end JanetCartan.PhysicalSmoothing
