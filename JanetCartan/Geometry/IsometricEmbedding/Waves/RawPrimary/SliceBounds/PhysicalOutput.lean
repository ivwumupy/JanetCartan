module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.OrderZero
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer

/-!
# Physical Frobenius output of the constructed slice operator

This assembles the actual product/Euclidean volume identity and complex
Frobenius component isometry with the order-zero construction for
`app:ch_waves:eq:individual-raw-slice`. The normalization is undone explicitly
to obtain the literal integral used by the raw wave construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition NormalComparison SingleChannel ActualCarriers.FrozenPhaseReference

variable {n m : ℕ}

/-- Frobenius flattening commutes with the actual raw integral, even with
Mathlib's nonintegrable-integral convention. No new kernel is introduced
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawPrimaryDemodulatedIntegral_matrixChannelEquiv
    {X : Type*} (S : X → Euclidean (n - 1) → ℝ)
    (A : X → Euclidean (n - 1) → Matrix (Fin m) (Fin n) ℂ)
    (ζ : Euclidean (n - 1)) (τ : ℝ) (f : Euclidean (n - 1) → ℂ) (x : X) :
    rawPrimaryDemodulatedIntegral S (fun y η ↦ matrixChannelEquiv m n (A y η))
      ζ τ volume f x =
        matrixChannelEquiv m n (rawPrimaryDemodulatedIntegral S A ζ τ volume f x) := by
  simp only [rawPrimaryDemodulatedIntegral, matrixChannelEquiv_apply]
  rw [← integral_matrixChannelComponents]
  apply integral_congr_ae
  filter_upwards [] with η
  change _ = (matrixChannelEquiv m n) (_ • (_ • _))
  rw [map_smul, map_smul]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ξ : Euclidean n} (a : AdaptedSection ξ)

/-- Transfer the normalized slice output to the literal physical matrix
integral. The scalar is the inverse of the explicitly retained Fourier
normalization (`app:ch_waves:eq:individual-raw-slice`). -/
def physicalRawSliceOperator
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1)))) :
    E →L[ℂ] Lp (Matrix (Fin m) (Fin n) ℂ) 2 (volume : Measure (Euclidean n)) :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) •
    (physicalMatrixL2Equiv a m).toContinuousLinearEquiv.toContinuousLinearMap.comp T

/-- The only norm factor is the explicit physical Fourier scalar. Actual
coordinate transport and Frobenius conversion are isometries
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_physicalRawSliceOperator
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1)))) :
    ‖physicalRawSliceOperator a T‖ = (2 * Real.pi) ^ ((n : ℝ) / 2) * ‖T‖ := by
  rw [physicalRawSliceOperator, norm_smul,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]

/-- Representative of the actual physical output, using the proved measure
identity and component integral compatibility. This lemma is used with the
operator constructed by `exists_normalizedRawSliceOperator`; it assumes no
bound (`app:ch_waves:eq:individual-raw-slice`). -/
theorem physicalRawSliceOperator_coeFn
    (T : E →L[ℂ] Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1))))
    (S : Euclidean n → Euclidean (n - 1) → ℝ)
    (A : Euclidean n → Euclidean (n - 1) → Matrix (Fin m) (Fin n) ℂ)
    (χ : Euclidean n → ℝ) (ζ : Euclidean (n - 1)) (τ : ℝ)
    (v : E) (f : Euclidean (n - 1) → ℂ)
    (hT : T v =ᵐ[volume] fun q ↦
      (2 * Real.pi) ^ (-(n : ℝ) / 2) • ((χ (adaptedPhysicalCoordinates a q) : ℂ) •
        rawPrimaryDemodulatedIntegral
          (fun q η ↦ S (adaptedPhysicalCoordinates a q) η)
          (fun q η ↦ matrixChannelEquiv m n (A (adaptedPhysicalCoordinates a q) η))
          ζ τ volume f q)) :
    physicalRawSliceOperator a T v =ᵐ[volume] fun x ↦
      (χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume f x := by
  have hc : (2 * Real.pi) ^ ((n : ℝ) / 2) *
      (2 * Real.pi) ^ (-(n : ℝ) / 2) = 1 := by
    rw [neg_div, Real.rpow_neg (by positivity)]
    exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))
  change ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) • physicalMatrixL2Equiv a m (T v)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)
      (physicalMatrixL2Equiv a m (T v)), physicalMatrixL2Equiv_coeFn a m (T v),
    (adaptedPhysicalCoordinates_symm_measurePreserving a).quasiMeasurePreserving.ae hT]
    with x hx hy hz
  rw [hx]
  change (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) •
    physicalMatrixL2Equiv a m (T v) x = _
  rw [hy, hz, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_smul]
  simp only [MeasurableEquiv.apply_symm_apply]
  have hi := rawPrimaryDemodulatedIntegral_matrixChannelEquiv
    (fun q η ↦ S (adaptedPhysicalCoordinates a q) η)
    (fun q η ↦ A (adaptedPhysicalCoordinates a q) η) ζ τ f
    ((adaptedPhysicalCoordinates a).symm x)
  rw [hi, LinearIsometryEquiv.symm_apply_apply]
  simp only [rawPrimaryDemodulatedIntegral, rawPrimaryPhaseDifference,
    MeasurableEquiv.apply_symm_apply]
  change (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ) •
    ((((2 * Real.pi) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) •
      ((χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume f x)) = _
  rw [smul_smul, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_smul]
  rfl

/-- The actual physical Frobenius L² operator for every `K ≥ 1`, obtained
from primitive buffered slice charts. The representative is the original
unnormalized integral, with both quadratures, actual Euclidean volume, and
no count-dependent constant (`app:ch_waves:eq:individual-raw-slice`).

The canonical raw-family producer must instantiate `F`, the original detector
and cutoff, and their displayed chart identities. This proves the slice
deduction from those primitive data, not the actual WKB family construction. -/
theorem exists_rawPhysicalSliceOperator {d : ℕ} {ξ : Euclidean (d + 1)}
    (sec : AdaptedSection ξ)
    (G : UniformNormalGeometry d (m * (d + 1))) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ B > 0, ∀ (K : ℝ), 1 ≤ K → ∀ (τ : ℝ), τ ≠ 0 →
      ∀ (F : (j : Fin (cutoffCount K)) →
        (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
      (∀ j : Fin (cutoffCount K), τ * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀) →
      ∀ (S : Euclidean (d + 1) → Euclidean d → ℝ)
        (A : Euclidean (d + 1) → Euclidean d → Matrix (Fin m) (Fin (d + 1)) ℂ)
        (χ : Euclidean (d + 1) → ℝ) (ζ : Euclidean d)
        (mask : Euclidean d → ℂ) (M : ℝ), Measurable mask → (∀ η, ‖mask η‖ ≤ M) →
      let S₀ := fun q η ↦ S (adaptedPhysicalCoordinates sec q) η
      let A₀ := fun q η ↦ matrixChannelEquiv m (d + 1) (A (adaptedPhysicalCoordinates sec q) η)
      let χ₀ := fun q ↦ χ (adaptedPhysicalCoordinates sec q)
      let amp := fun j : Fin (cutoffCount K) ↦
        rawSliceBandAmplitude (n := d + 1) A₀ χ₀ ζ τ (weightedRadialBand (n := d + 1) mask j.val) j.val
      (∀ j, Continuous (Function.uncurry (amp j))) →
      (∀ j, HasCompactSupport (Function.uncurry (amp j))) →
      (∀ j, ∀ p ∈ tsupport (Function.uncurry (amp j)), ContinuousAt
        (Function.uncurry (rawPrimaryPhaseDifference S₀ ζ (τ * (2 : ℝ) ^ j.val))) p) →
      (∀ j, ∀ t ∉ Ioo a b, ∀ y u, amp j (t, y) u = 0) →
      (∀ j t (ht : t ∈ Ioo a b) y u,
        rawPrimaryPhaseDifference S₀ ζ (τ * (2 : ℝ) ^ j.val) (t, y) u =
          (F j t ht).phase (τ * (2 : ℝ) ^ j.val) y u) →
      (∀ j t (ht : t ∈ Ioo a b) y u i,
        amp j (t, y) u i = (F j t ht).amplitude (τ * (2 : ℝ) ^ j.val) y u i) →
      (∀ x, χ₀ x ≠ 0 → ∀ j : Fin (cutoffCount K), ContinuousOn
        (fun η ↦ Complex.exp (Complex.I * (rawPrimaryPhaseDifference S₀ ζ τ x η : ℂ)) •
          A₀ x (ζ + τ • η)) (wideBand (d + 1) j.val)) →
      ∃ T : WideInput (d + 1) (cutoffCount K) →L[ℂ]
          Lp (Matrix (Fin m) (Fin (d + 1)) ℂ) 2 (volume : Measure (Euclidean (d + 1))),
        (∀ v, T v =ᵐ[volume] fun x ↦
          (χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
            (weightedWideDensity (n := d + 1) mask v) x) ∧
        ‖T‖ ^ 2 ≤ B * K ∧
        ‖realQuadratureChannel
          ((matrixChannelL2Equiv volume m (d + 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp T)‖ ^ 2
            ≤ 4 * (B * K) ∧
        ∀ v, ‖T v‖ ≤ Real.sqrt B * Real.sqrt K * ‖v‖ := by
  obtain ⟨B, hB, hconstruct⟩ := exists_normalizedRawSliceOperator G C a b hab
  let c : ℝ := (2 * Real.pi) ^ (((d + 1 : ℕ) : ℝ) / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨c ^ 2 * B, by positivity, ?_⟩
  intro K hK τ hτ F hε S A χ ζ mask M hm hmb S₀ A₀ χ₀ amp ha hs hφ ht hp hA hcont
  obtain ⟨T, hT, hnorm, _⟩ := hconstruct K hK τ hτ F hε S₀ A₀ χ₀ ζ mask M hm hmb
    ha hs hφ ht hp hA hcont
  let P := physicalRawSliceOperator sec T
  have hP : ‖P‖ ^ 2 ≤ (c ^ 2 * B) * K := by
    rw [show ‖P‖ = c * ‖T‖ from norm_physicalRawSliceOperator sec T, mul_pow]
    calc
      c ^ 2 * ‖T‖ ^ 2 ≤ c ^ 2 * (B * K) := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
      _ = _ := by ring
  refine ⟨P, fun v ↦ physicalRawSliceOperator_coeFn sec T S A χ ζ τ v
    (weightedWideDensity (n := d + 1) mask v) (hT v), hP, ?_, ?_⟩
  · apply (realQuadratureChannel_norm_sq_le _).trans
    rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]
    exact mul_le_mul_of_nonneg_left hP (by norm_num)
  · intro v
    apply (P.le_opNorm v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← Real.sqrt_mul (by positivity)]
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hP

end JanetCartan.RawPrimary.SliceBounds
