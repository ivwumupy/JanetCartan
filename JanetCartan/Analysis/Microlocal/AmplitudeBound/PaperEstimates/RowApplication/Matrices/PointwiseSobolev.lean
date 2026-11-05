module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowApplication.Kernel

/-!
# Pointwise domination for the original Sobolev matrix rows

The original continuous `H^ell` representative in
`app:ch_osc:eq:amplitude-row` is bounded by its actual cutoff Fourier
series. This supplies integrable domination when the original scalar
row kernels are combined into a matrix, without any additional physical
derivative or supremum-norm premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter

namespace JanetCartan.AmplitudeBound.PaperEstimates

open Pseudodifferential

variable {d : ℕ} {X : Type*}

/-- The continuous representative of the original compact `H^ell` row
has its pointwise bound from the proved Fourier reconstruction, with
no added derivative assumption (`app:ch_osc:eq:amplitude-row`). -/
theorem norm_rowAmplitude_le_of_sobolev
    (R : ℝ) (b : X → EuclideanSpace ℝ (Fin d) → ℂ)
    (hc : ∀ u, Continuous (b u)) (hs : ∀ u, SupportedInCenteredBox R (b u))
    (hm : ∀ u, MemLp (b u) 2 volume)
    (hHs : ∀ u, MemFourierSobolev (d / 2 + 1 : ℕ) ((hm u).toLp (b u)))
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ u, fourierSobolevNorm (d / 2 + 1 : ℕ) ((hm u).toLp (b u)) ≤ A)
    (u : X) (x : EuclideanSpace ℝ (Fin d)) :
    ‖b u x‖ ≤ rowAmplitudeConstant d R * A := by
  let v : (Fin d → ℤ) → ℂ := fun k ↦ boxCellCutoff (amplitudeBoxScale R) x *
    UnitAddTorus.mFourier k (scaledTorusChart (amplitudeBoxScale R) x) * rowFourierCoefficient R b k u
  have hv : HasSum v (b u x) := rowFourierCoefficient_hasSum R b hc hs hm hHs u x
  have habs := rowFourierCoefficient_absolute_sum_bound R b hs hm hHs A hA hbound u
  have hn (k : Fin d → ℤ) : ‖v k‖ ≤ ‖rowFourierCoefficient R b k u‖ := by
    dsimp only [v]
    rw [norm_mul, norm_mul]
    have hchar := norm_mFourier_apply_le_one k (scaledTorusChart (amplitudeBoxScale R) x)
    have hcut := norm_boxCellCutoff_le (amplitudeBoxScale R) x
    exact (mul_le_mul_of_nonneg_right
      ((mul_le_mul hcut hchar (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
        (norm_nonneg _)).trans_eq (one_mul _)
  have hnorm : Summable (fun k ↦ ‖v k‖) := habs.1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hn
  calc
    ‖b u x‖ = ‖∑' k, v k‖ := congrArg norm hv.tsum_eq.symm
    _ ≤ ∑' k, ‖v k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, ‖rowFourierCoefficient R b k u‖ := hnorm.tsum_le_tsum hn habs.1
    _ ≤ _ := habs.2

end JanetCartan.AmplitudeBound.PaperEstimates
