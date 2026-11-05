module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandOperator

/-!
# Summing the constructed wide-band operators

The Cauchy--Schwarz step of `app:ch_waves:eq:individual-raw-slice` uses the
original `WideInput` norm and the geometric sum of the actual frequencies
`2^j`. This leaf is the algebraic assembly step after
`exists_rawSliceBandOperator` has constructed each channel. Its band estimates
are explicit premises here; it does not assert their analytic production.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition RawInputRealization

variable {n J : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Sum on the original wide-band Hilbert input, used after constructing
each actual channel (`app:ch_waves:eq:individual-raw-slice`). -/
def wideBandOperatorSum (T : (j : Fin J) → WideBandL2 n j.val →L[ℂ] E) :
    WideInput n J →L[ℂ] E :=
  ∑ j : Fin J, (T j).comp (PiLp.proj 2 _ j)

/-- The sum evaluates on the original wide data, with no remaining sharp
components (`app:ch_waves:eq:individual-raw-slice`). -/
theorem wideBandOperatorSum_apply
    (T : (j : Fin J) → WideBandL2 n j.val →L[ℂ] E) (v : WideInput n J) :
    wideBandOperatorSum T v = ∑ j : Fin J, T j (v j) := by
  simp [wideBandOperatorSum, PiLp.proj_apply]

/-- Dyadic Cauchy--Schwarz uses the literal Hilbert norm. This is the
finite-sum step in `app:ch_waves:eq:individual-raw-slice`; its actual band
premises are produced by `exists_rawSliceBandOperator`. -/
theorem norm_wideBandOperatorSum_sq_le
    (T : (j : Fin J) → WideBandL2 n j.val →L[ℂ] E) {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ j, ‖T j‖ ^ 2 ≤ B * (2 : ℝ) ^ j.val) :
    ‖wideBandOperatorSum T‖ ^ 2 ≤ B * (2 : ℝ) ^ J := by
  have hbound : ‖wideBandOperatorSum T‖ ≤ Real.sqrt (B * (2 : ℝ) ^ J) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hcs : (∑ j : Fin J, Real.sqrt (B * (2 : ℝ) ^ j.val) * ‖v j‖) ≤
        Real.sqrt (∑ j : Fin J, B * (2 : ℝ) ^ j.val) * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by positivity)]
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j : Fin J ↦ Real.sqrt (B * (2 : ℝ) ^ j.val)) (fun j ↦ ‖v j‖)
      have hsq (j : Fin J) : Real.sqrt (B * (2 : ℝ) ^ j.val) ^ 2 = B * (2 : ℝ) ^ j.val :=
        Real.sq_sqrt (by positivity)
      simpa only [hsq, PiLp.norm_sq_eq_of_L2] using h
    rw [wideBandOperatorSum_apply]
    calc
      _ ≤ ∑ j : Fin J, ‖T j (v j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin J, Real.sqrt (B * (2 : ℝ) ^ j.val) * ‖v j‖ := by
        apply Finset.sum_le_sum
        intro j _
        apply ((T j).le_opNorm _).trans
        exact mul_le_mul_of_nonneg_right
          ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (hT j)) (norm_nonneg _)
      _ ≤ Real.sqrt (∑ j : Fin J, B * (2 : ℝ) ^ j.val) * ‖v‖ := hcs
      _ ≤ Real.sqrt (B * (2 : ℝ) ^ J) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.sqrt_le_sqrt
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ hB
        simpa only [pow_one] using sum_dyadic_radii_pow_le (n := 1) le_rfl J
  calc
    _ ≤ Real.sqrt (B * (2 : ℝ) ^ J) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = _ := Real.sq_sqrt (by positivity)

/-- The literal rounded prefix has a fixed squared constant four, with no
dependence on band count or sample count (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_wideBandOperatorSum_rounded_sq_le {K B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (T : (j : Fin (cutoffCount K)) → WideBandL2 n j.val →L[ℂ] E)
    (hT : ∀ j, ‖T j‖ ^ 2 ≤ B * (2 : ℝ) ^ j.val) :
    ‖wideBandOperatorSum T‖ ^ 2 ≤ (4 * B) * K := by
  apply (norm_wideBandOperatorSum_sq_le T hB hT).trans
  calc
    B * (2 : ℝ) ^ cutoffCount K ≤ B * (4 * K) :=
      mul_le_mul_of_nonneg_left (cutoffCount_ceiling hK) hB
    _ = _ := by ring

/-- Each physical derivative term retains `κ^q L^(s-q)` before using
`K ≥ L`. The scale `κ ≤ cK` allows the fixed dyadic ceiling constant, and
does not replace the fixed slice-seminorm reserve by an order-dependent
low budget (`app:ch_waves:eq:individual-raw-slice`). -/
theorem phaseAmplitudeGrade_le_ceiling {κ K L c : ℝ}
    (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hc : 1 ≤ c) (hLK : L ≤ K) (hκK : κ ≤ c * K)
    {s q : ℕ} (hq : q ≤ s) : κ ^ q * L ^ (s - q) ≤ c ^ s * K ^ s := by
  have hK : 0 ≤ K := hL.trans hLK
  calc
    κ ^ q * L ^ (s - q) ≤ (c * K) ^ q * (c * K) ^ (s - q) := by
      exact mul_le_mul (pow_le_pow_left₀ hκ hκK q)
        (pow_le_pow_left₀ hL (hLK.trans (by nlinarith)) (s - q))
        (by positivity) (by positivity)
    _ = c ^ s * K ^ s := by rw [← pow_add, Nat.add_sub_of_le hq, mul_pow]

end JanetCartan.RawPrimary.SliceBounds
