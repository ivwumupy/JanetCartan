module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DyadicSum
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.IntegralSum

/-!
# Order-zero construction on the original wide input

For `app:ch_waves:eq:individual-raw-slice`, apply the completed SingleChannel
producer to each reassembled smooth band and sum on the original Hilbert
input. All analytic inputs below are primitive buffered chart data,
continuity, support, and literal phase/amplitude identities. No raw operator
bound or integral realization is assumed. The constant precedes the rounded
prefix, history, and datum. Physical-coordinate transfer is supplied separately
by `PhysicalOutput`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition NormalComparison SingleChannel

variable {d r : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Construction of the normalized entire slice operator on the original
smooth wide input for every `K ≥ 1`. The full Lebesgue output includes time,
the exact Fourier normalization is displayed, and the real channel retains
both quadratures. The bound uses the literal `cutoffCount K` and its `4K`
ceiling, with no band-count or sample-count loss
(`app:ch_waves:eq:individual-raw-slice`).

The actual raw-family parent supplies `F` from its same buffered phase charts
and canonical derivative amplitude. It must also instantiate the support and
continuity premises; this theorem constructs all band and sum operators. -/
theorem exists_normalizedRawSliceOperator
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B > 0, ∀ (K : ℝ), 1 ≤ K → ∀ (τ : ℝ), τ ≠ 0 →
      ∀ (F : (j : Fin (cutoffCount K)) →
        (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
      (∀ j : Fin (cutoffCount K), τ * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      ∀ (S : X → Y → ℝ) (A : X → Y → V) (χ : X → ℝ) (ζ : Y)
        (m : Y → ℂ) (M : ℝ), Measurable m → (∀ η, ‖m η‖ ≤ M) →
      let amp := fun j : Fin (cutoffCount K) ↦
        rawSliceBandAmplitude (n := d + 1) A χ ζ τ (weightedRadialBand (n := d + 1) m j.val) j.val
      (∀ j, Continuous (Function.uncurry (amp j))) →
      (∀ j, HasCompactSupport (Function.uncurry (amp j))) →
      (∀ j, ∀ p ∈ tsupport (Function.uncurry (amp j)), ContinuousAt
        (Function.uncurry (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j.val))) p) →
      (∀ j, ∀ t ∉ Ioo a b, ∀ y u, amp j (t, y) u = 0) →
      (∀ j t (ht : t ∈ Ioo a b) y u,
        rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j.val) (t, y) u =
          (F j t ht).phase (τ * (2 : ℝ) ^ j.val) y u) →
      (∀ j t (ht : t ∈ Ioo a b) y u i,
        amp j (t, y) u i = (F j t ht).amplitude (τ * (2 : ℝ) ^ j.val) y u i) →
      (∀ x, χ x ≠ 0 → ∀ j : Fin (cutoffCount K), ContinuousOn
        (fun η ↦ Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) •
          A x (ζ + τ • η)) (wideBand (d + 1) j.val)) →
      ∃ T : WideInput (d + 1) (cutoffCount K) →L[ℂ] Lp V 2 (volume : Measure X),
        (∀ v, T v =ᵐ[volume] fun x ↦
          (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
            ((χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
              (weightedWideDensity (n := d + 1) m v) x)) ∧
        ‖T‖ ^ 2 ≤ B * K ∧ ‖realQuadratureChannel T‖ ^ 2 ≤ 4 * (B * K) := by
  obtain ⟨B, hB, hband⟩ := exists_rawSliceBandOperator G C a b hab
  refine ⟨4 * B, by positivity, ?_⟩
  intro K hK τ hτ F hε S A χ ζ m M hm hmb amp ha hs hφ ht hp hA hc
  have hb (j : Fin (cutoffCount K)) := hband j.val τ hτ (F j) (hε j)
    S A χ ζ (weightedRadialBand (n := d + 1) m j.val)
    (fun η hη ↦ weightedRadialBand_eq_zero_off_wideBand (n := d + 1) m hη)
    (ha j) (hs j) (hφ j) (ht j) (hp j) (hA j)
  choose T hT hnorm hreal using hb
  have hsum := norm_wideBandOperatorSum_rounded_sq_le hK hB.le T hnorm
  refine ⟨wideBandOperatorSum T, ?_, hsum,
    (realQuadratureChannel_norm_sq_le _).trans
      (mul_le_mul_of_nonneg_left hsum (by norm_num))⟩
  intro v
  rw [wideBandOperatorSum_apply]
  refine (Lp.coeFn_finsetSum Finset.univ (fun j ↦ T j (v j))).trans ?_
  have he := eventuallyEq_sum (s := Finset.univ) (fun j _ ↦ hT j (v j))
  refine he.trans (Filter.Eventually.of_forall ?_)
  intro x
  simp only [Finset.sum_apply]
  rw [← Finset.smul_sum, sum_rawSliceBandIntegral_eq_weightedWideDensity (n := d + 1)
    S A χ ζ τ hm hmb v x (hc x)]

end JanetCartan.RawPrimary.SliceBounds
