module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives.Estimates

/-!
# First derivatives in Euclidean Fourier Sobolev spaces

The representation bridge identifies the weighted Fourier L² space with
Mathlib's Bessel-potential space at every real order. For `s ≥ 0`, membership
at order `s + 1` is equivalent to membership at order `s` together with actual
L² representatives of the distributional coordinate derivatives at order `s`.
The two norm comparisons have constants `1` and `1 + 2πd`.

These results supply the gain-one argument after
`app:ch_regular_base:eq:graph-derivative-transfer` for the norms in
`app:ch_regular_base:eq:fio-input`. The derivative convention is `2π i ξⱼ`,
and the statements include dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}

/-- With actual L² representatives of the coordinate derivatives, order `s + 1`
is equivalent to order `s` of the input and every representative. This is the
gain-one criterion after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem memFourierSobolev_add_one_iff_of_coordinateDerivatives {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    {v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hderiv : ∀ i, HasEuclideanL2CoordinateDerivative i u (v i)) :
    MemFourierSobolev (s + 1) u ↔
      MemFourierSobolev s u ∧ ∀ i, MemFourierSobolev s (v i) := by
  constructor
  · intro hu
    exact ⟨hu.mono (by linarith), fun i ↦ (hderiv i).memFourierSobolev hs hu⟩
  · rintro ⟨hu, hv⟩
    exact hu.of_coordinateDerivatives hs hv hderiv

/-- First-derivative characterization of the Euclidean Fourier Sobolev space,
including existence of actual L² derivative representatives. This supplies both
membership directions in the gain-one argument after
`app:ch_regular_base:eq:graph-derivative-transfer`, also in dimension zero. -/
theorem memFourierSobolev_add_one_iff {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2} :
    MemFourierSobolev (s + 1) u ↔
      MemFourierSobolev s u ∧
        ∃ v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2,
          ∀ i, HasEuclideanL2CoordinateDerivative i u (v i) ∧ MemFourierSobolev s (v i) := by
  constructor
  · intro hu
    exact ⟨hu.mono (by linarith), hu.exists_coordinateDerivatives hs⟩
  · rintro ⟨hu, v, hv⟩
    exact (memFourierSobolev_add_one_iff_of_coordinateDerivatives hs
      (fun i ↦ (hv i).1)).mpr ⟨hu, fun i ↦ (hv i).2⟩

set_option maxHeartbeats 800000 in
/-- Actual first derivatives and both quantitative norm comparisons, obtained
from order `s + 1` membership alone. The constants `1` and `1 + 2πd` retain
the Fourier convention in `app:ch_regular_base:eq:fio-input`, and implement
the gain-one argument after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem MemFourierSobolev.exists_coordinateDerivatives_norm_bounds {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev (s + 1) u) :
    MemFourierSobolev s u ∧
      ∃ v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2,
        (∀ i, HasEuclideanL2CoordinateDerivative i u (v i) ∧ MemFourierSobolev s (v i)) ∧
        (fourierSobolevNorm (s + 1) u ≤
          fourierSobolevNorm s u + ∑ i, fourierSobolevNorm s (v i)) ∧
        fourierSobolevNorm s u + ∑ i, fourierSobolevNorm s (v i) ≤
          (1 + 2 * Real.pi * d) * fourierSobolevNorm (s + 1) u := by
  obtain ⟨hu₀, v, hv⟩ := (memFourierSobolev_add_one_iff (u := u) hs).mp hu
  refine ⟨hu₀, v, hv, ?_, ?_⟩
  · exact fourierSobolevNorm_le_coordinateDerivatives hs hu₀
      (fun i ↦ (hv i).2) (fun i ↦ (hv i).1)
  · exact fourierSobolevNorm_coordinateDerivatives_le hs hu (fun i ↦ (hv i).1)

end JanetCartan.Pseudodifferential
