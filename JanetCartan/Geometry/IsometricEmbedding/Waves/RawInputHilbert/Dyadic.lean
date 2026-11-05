module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Synthesis
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization.Bounds

/-!
# Dyadic synthesis norm

The raw input map used by `app:ch_waves:eq:individual-raw-slice` costs only a
half power of the ceiling. The constant is independent of the scale count.
-/

@[expose] public noncomputable section

open MeasureTheory
namespace JanetCartan.RawInputHilbert
open RawInputRealization

/-- Dyadic annuli give a square-root ceiling bound, independent of their count
(`app:ch_waves:eq:B-bounds`, `app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_synthesis_dyadic_le {n J : ℕ} {M : ℝ}
    {β : Fin J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n ((2 : ℝ) ^ i.val)))
    (hM : 0 ≤ M)
    (hb : ∀ i, ∀ᵐ η ∂annularMeasure n ((2 : ℝ) ^ i.val), ‖β i η‖ ≤ M) :
    ‖synthesis hβ (fun _ ↦ hM) hb‖ ≤ M * Real.sqrt ((2 : ℝ) ^ J) := by
  have hs : (∑ i : Fin J, (2 : ℝ) ^ i.val * M ^ 2) ≤ (2 : ℝ) ^ J * M ^ 2 := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa using sum_dyadic_radii_pow_le (n := 1) le_rfl J
  calc
    _ ≤ Real.sqrt (∑ i : Fin J, (2 : ℝ) ^ i.val * M ^ 2) :=
      norm_synthesis_le (fun _ ↦ by positivity) hβ (fun _ ↦ hM) hb
    _ ≤ Real.sqrt ((2 : ℝ) ^ J * M ^ 2) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM, mul_comm]

/-- A geometric ceiling at most `C K` gives a constant independent of the
number of scales (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_synthesis_dyadic_ceiling_le {n J : ℕ} {M C K : ℝ}
    {β : Fin J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, AEStronglyMeasurable (β i) (annularMeasure n ((2 : ℝ) ^ i.val)))
    (hM : 0 ≤ M)
    (hb : ∀ i, ∀ᵐ η ∂annularMeasure n ((2 : ℝ) ^ i.val), ‖β i η‖ ≤ M)
    (hC : 0 ≤ C) (hceiling : (2 : ℝ) ^ J ≤ C * K) :
    ‖synthesis hβ (fun _ ↦ hM) hb‖ ≤ (M * Real.sqrt C) * Real.sqrt K := by
  calc
    _ ≤ M * Real.sqrt ((2 : ℝ) ^ J) := norm_synthesis_dyadic_le hβ hM hb
    _ ≤ M * Real.sqrt (C * K) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hceiling) hM
    _ = _ := by rw [Real.sqrt_mul hC, mul_assoc]

end JanetCartan.RawInputHilbert
