module

public import JanetCartan.Analysis.Microlocal.NormalComparison.ChannelBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.CompactFrequency.Kernel

/-!
# Bounded realization of compact-frequency matrix amplitudes

The compact-frequency specialization of `app:ch_osc:lem:osc-amplitude` used in
Step 1 of `app:ch_osc:prop:osc-normal`. A finite regularization whose frequency
ball contains the carrier already has the literal full kernel. Its bound
depends only on the physical box, dimension, matrix size and derivative budget.
The compact frequency carrier contributes no constant to the bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace JanetCartan.NormalComparison

open AmplitudeBound

variable {n r : ℕ}

/-- A compact-frequency matrix amplitude defines a bounded operator with its
literal full kernel on every L² input. This consumes the finite regularizations
of `app:ch_osc:lem:osc-amplitude` and supplies the full-kernel realization needed
to identify the actual normal operator in `app:ch_osc:prop:osc-normal`, Step 1.
The estimate is independent of the compact frequency carrier `Q`. -/
theorem exists_compactFrequencyMatrixAmplitudeOperator (hn : 0 < n) (R : ℝ)
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) →
      Matrix (Fin r) (Fin r) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (A : ℝ)
    (hbound : MatrixNormalAmplitudeBounds b R A)
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsCompact Q)
    (hfreq : ∀ ξ, ξ ∉ Q → ∀ z, b ξ z = 0) :
    ∃ N : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r,
      ‖N‖ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A) ∧
      ∀ f i, (N f) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y,
        (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
          b ξ (pairedPosition x y) i j) * f j y := by
  obtain ⟨ρ, _, hρ⟩ := hQ.isBounded.exists_pos_norm_le
  have hfreq' (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ∉ Metric.closedBall 0 ρ)
      (z) : b ξ z = 0 := by
    apply hfreq ξ
    intro hξQ
    exact hξ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hρ ξ hξQ)
  obtain ⟨_, Nρ, _, hNρ, hker, _, _⟩ :=
    exists_matrixTwoPositionAmplitudeOperator hn R b hb hbound.support A hbound.derivative
  refine ⟨Nρ ρ, by simpa only [Fintype.card_fin] using hNρ ρ, ?_⟩
  intro f i
  apply (hker ρ f i).trans
  apply Filter.Eventually.of_forall
  intro x
  apply Finset.sum_congr rfl
  intro j _
  have hm : StronglyMeasurable (Function.uncurry (fun ξ z ↦ b ξ z i j)) :=
    (matrixEntryEvaluation i j).continuous.comp_stronglyMeasurable hbound.measurable
  have hz : ∀ ξ z, ‖b ξ z i j‖ ≤ A := by
    intro ξ z
    exact (norm_matrixEntry_le_frobenius _ i j).trans
      (hbound.derivative ξ [] (by simp) z)
  exact boxScalarAmplitudeKernel_eq_full_of_frequency_support
    (fun ξ z ↦ b ξ z i j) hm (fun ξ ↦ hbound.support ξ i j) hz
    (fun ξ hξ z ↦ congrArg (fun M ↦ M i j) (hfreq' ξ hξ z)) (f j) x

/-- The literal compact-frequency kernel determines any bounded realization
uniquely in L², so the estimate applies to the actual normal operator after
its kernel has been identified (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem norm_compactFrequencyMatrixAmplitudeOperator_le (hn : 0 < n) (R : ℝ)
    (b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) →
      Matrix (Fin r) (Fin r) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (A : ℝ)
    (hbound : MatrixNormalAmplitudeBounds b R A)
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsCompact Q)
    (hfreq : ∀ ξ, ξ ∉ Q → ∀ z, b ξ z = 0)
    (N : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r)
    (hN : ∀ f i, (N f) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y,
      (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        b ξ (pairedPosition x y) i j) * f j y) :
    ‖N‖ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A) := by
  obtain ⟨B, hB, hker⟩ :=
    exists_compactFrequencyMatrixAmplitudeOperator hn R b hb A hbound hQ hfreq
  have heq : N = B := by
    ext f i
    exact (hN f i).trans (hker f i).symm
  rw [heq]
  exact hB

end JanetCartan.NormalComparison
