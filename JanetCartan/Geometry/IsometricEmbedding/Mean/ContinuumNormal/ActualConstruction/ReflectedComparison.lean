module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.OperatorDifference.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ImagePerturbation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Restriction

/-!
# The retained reflected normals in the local and global lower bounds

This applies the published full-amplitude difference estimate to the literal
normal identities exported by the initialized row. The same common measurement
cutoff sandwiches both operators. Reflection already includes factor four.
The local frozen image is identified only on the test support; the periodic
coefficient extension need not be globally constant. Exterior completion keeps
the original square `(1 - ψ)^2` and a common bound for the physical row.

The actual producers are `RetainedFrozen.exists_initialized_retained_frozen_row`
for realizations and the density-weighted frozen gap, and `CarrierVariation`
for full-amplitude differences. Instantiation of the latter on the same
initialized family remains necessary. These deductions do not assert that
the actual comparison data have been constructed.
Sources: `app:ch_background:prop:bg-frame`, `bg-local-bound`, `bg-global-bound`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction

open ContinuumRow CommonMeasurement CarrierVariation
open AmplitudeBound Pseudodifferential PeriodicLocalL2

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Apply the full reflected amplitude comparison to the SAME two realized
carriers and then their common measurement restriction. The original reserve
and matrix factor are retained; reflection already includes the real-quadrature
factor four (`app:ch_background:eq:bg-full-complex-amplitude`, `bg-realification`). -/
theorem norm_restricted_carrierNormal_sub_le_full_amplitudes
    (hn : 0 < n) (R : ℝ)
    (b : Bool → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (b t)))
    (hs : ∀ t ξ i j, SupportedInCenteredBox R (fun z ↦ b t ξ z i j))
    (B : Bool → ℝ)
    (hB : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b t ξ z i j)
      (2 * (n + 1)) (B t))
    (U : Bool → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hnormal : ∀ t, carrierChannel (U t) ∘L (carrierChannel (U t)).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn R (b t) (hb t) (hs t) (B t) (hB t))))
    (χ : C(Torus n, ℝ)) (hχ : ‖χ‖ ≤ 1)
    (s : ℕ) (hreserve : 2 * (n + 1) ≤ s) (D : ℝ)
    (hD : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ (b true - b false) ξ z i j) s D) :
    ‖carrierChannel (restrictCarrier χ (U true)) ∘L
          (carrierChannel (restrictCarrier χ (U true))).adjoint -
        carrierChannel (restrictCarrier χ (U false)) ∘L
          (carrierChannel (restrictCarrier χ (U false))).adjoint‖ ≤
      (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n R * D) := by
  have hsub : ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ (b true - b false) ξ z i j) := by
    intro ξ i j z hz
    by_cases hzero : b true ξ z i j = 0
    · exact hs false ξ i j z (by simpa only [Pi.sub_apply, Matrix.sub_apply,
        hzero, zero_sub, neg_ne_zero] using hz)
    · exact hs true ξ i j z hzero
  have hdiff := (vectorTwoPositionL2Operator_sub_bounds hn R (b true) (b false)
    (hb true) (hb false) ((hb true).sub (hb false)) (hs true) (hs false) hsub
    (B true) (B false) D (hB true) (hB false) s hreserve hD).2.2
  rw [← hnormal true, ← hnormal false] at hdiff
  rw [carrierChannel_restrictCarrier_normal, carrierChannel_restrictCarrier_normal,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp,
    ← ContinuousLinearMap.comp_assoc]
  have hm : ‖cutoffMultiplier χ‖ ≤ 1 := (cutoffMultiplier_norm_le χ).trans hχ
  calc
    _ ≤ ‖cutoffMultiplier χ‖ *
        ‖carrierChannel (U true) ∘L (carrierChannel (U true)).adjoint -
          carrierChannel (U false) ∘L (carrierChannel (U false)).adjoint‖ *
        ‖cutoffMultiplier χ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 *
        ‖carrierChannel (U true) ∘L (carrierChannel (U true)).adjoint -
          carrierChannel (U false) ∘L (carrierChannel (U false)).adjoint‖ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) hm
        (norm_nonneg _) (by positivity)
    _ ≤ _ := by simpa only [one_mul, mul_one] using hdiff

/-- Sum the literal reflected PDO comparisons for the retained physical row.
This is the full-normal, rather than oscillatory-row, perturbation used in
`app:ch_background:prop:bg-frame`. The same image/source and measurement masks
occur on both sides. The amplitude inputs are the outputs of `CarrierVariation`. -/
theorem norm_physicalNormal_sub_le_image_and_full_amplitudes
    (hn : 0 < n) (R : ι → ℝ)
    (b : ι → Bool → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ i t, ContDiff ℝ ∞ (Function.uncurry (b i t)))
    (hs : ∀ i t ξ j k, SupportedInCenteredBox (R i) (fun z ↦ b i t ξ z j k))
    (B : ι → Bool → ℝ)
    (hB : ∀ i t j k, HasAmplitudeDerivativeBound (fun ξ z ↦ b i t ξ z j k)
      (2 * (n + 1)) (B i t))
    (U : ι → Bool → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hnormal : ∀ i t, carrierChannel (U i t) ∘L (carrierChannel (U i t)).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator hn (R i) (b i t) (hb i t) (hs i t)
          (B i t) (hB i t))))
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χ χsrc : C(Torus n, ℝ)) (hχ : ‖χ‖ ≤ 1)
    (s : ℕ) (hreserve : 2 * (n + 1) ≤ s) (D : ι → ℝ)
    (hD : ∀ i j k, HasAmplitudeDerivativeBound
      (fun ξ z ↦ (b i true - b i false) ξ z j k) s (D i)) :
    ‖NormalPerturbation.normal
        (physicalRow (imageChannel c χ χsrc) (fun i ↦ restrictCarrier χ (U i true))) -
      NormalPerturbation.normal
        (physicalRow (imageChannel d χ χsrc) (fun i ↦ restrictCarrier χ (U i false)))‖ ≤
      ‖NormalPerturbation.normal (imageChannel c χ χsrc) -
        NormalPerturbation.normal (imageChannel d χ χsrc)‖ +
        ∑ i, (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (R i) * D i) := by
  simp only [NormalPerturbation.normal, physicalRow_normal]
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
    norm_restricted_carrierNormal_sub_le_full_amplitudes hn (R i) (b i) (hb i)
      (hs i) (B i) (hB i) (U i) (hnormal i) χ hχ s hreserve (D i) (hD i))

end JanetCartan.ContinuumNormal.ActualConstruction
