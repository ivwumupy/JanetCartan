module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Multiplier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FiniteNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension

/-!
# Restrict the same constructed carrier

The hypotheses below are precisely the literal test and adjoint conclusions
of `CarrierNormalRealization.exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
They refer to a single `U`. Its common measurement restriction is constructed
here; its new normal is proved, rather than assumed. Actual geometric
instantiation remains with `jc-continuum-row`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ContinuumRow.CommonMeasurement
variable {n N : ℕ}

/-- Restrict the output of the SAME complex carrier
(`app:ch_background:eq:bg-T`). -/
def restrictCarrier (χ : C(Torus n, ℝ)) (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    CarrierL2 n →L[ℂ] ComplexOutputL2 n := complexMultiplier χ ∘L U

/-- The inherited operator bound (`app:ch_background:prop:bg-frame`). -/
theorem restrictCarrier_norm_le (χ : C(Torus n, ℝ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) : ‖restrictCarrier χ U‖ ≤ ‖χ‖ * ‖U‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (complexMultiplier_norm_le χ) (norm_nonneg U))

/-- Literal test realization after restriction. The supported producer supplies
`hU` for this same `U` (`app:ch_background:eq:bg-T`). -/
theorem restrictCarrier_test (χ : C(Torus n, ℝ)) (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val)
    (v : carrierInitialTestSpace n) :
    restrictCarrier χ U (carrierInitialTestToLp v) =ᵐ[volume]
      carrierTestIntegral (restrictData d χ) v.val := by
  filter_upwards [complexMultiplier_coeFn χ (U (carrierInitialTestToLp v)), hU v] with x hm hu
  change complexMultiplier χ (U (carrierInitialTestToLp v)) x = _
  rw [hm, hu, carrierTestIntegral_restrictData,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Full-output support after restriction, for every carrier L² input
(`app:ch_background:defn:bg-row`). -/
theorem restrictCarrier_support (χ : C(Torus n, ℝ)) (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val)
    (f : CarrierL2 n) :
    ∀ᵐ x ∂volume, x ∉ d.outputChart ∩ Function.support χ → restrictCarrier χ U f x = 0 := by
  filter_upwards [complexMultiplier_coeFn χ (U f),
    carrierRealization_eq_zero_outside d U hU f] with x hm hs hx
  change complexMultiplier χ (U f) x = _
  rw [hm]
  by_cases hc : x ∈ d.outputChart
  · have hz : χ x = 0 := by
      by_contra hn
      exact hx ⟨hc, hn⟩
    simp [hz]
  · simp [hs hc]

/-- The literal complex adjoint of restriction
(`app:ch_background:eq:bg-realification`). -/
theorem restrictCarrier_adjoint (χ : C(Torus n, ℝ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    (restrictCarrier χ U).adjoint = U.adjoint ∘L complexMultiplier χ := by
  rw [restrictCarrier, ContinuousLinearMap.adjoint_comp, complexMultiplier_adjoint]

/-- The adjoint integral for the new data belongs to the original carrier L²,
and represents the SAME restricted operator's adjoint. The sole analytic input
is the supported producer's adjoint conclusion for `U`
(`app:ch_background:eq:bg-realification`). -/
theorem restrictCarrier_literal_adjoint (χ : C(Torus n, ℝ)) (d : CarrierData n N)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hUadj : ∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
      U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w)
    (w : ComplexOutputL2 n) :
    MemLp (carrierAdjointIntegral (restrictData d χ) w) 2 (carrierMeasure n) ∧
      (restrictCarrier χ U).adjoint w =ᵐ[carrierMeasure n]
        carrierAdjointIntegral (restrictData d χ) w := by
  have he : carrierAdjointIntegral d (complexMultiplier χ w) =
      carrierAdjointIntegral (restrictData d χ) w := by
    funext u
    rw [carrierAdjointIntegral_restrictData]
    apply integral_congr_ae
    filter_upwards [complexMultiplier_coeFn χ w] with x hx
    rw [hx, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [restrictCarrier_adjoint]
  simpa only [ContinuousLinearMap.comp_apply, he] using hUadj (complexMultiplier χ w)

/-- The complex normal is the proved sandwich, without any additional normal
hypothesis (`app:ch_background:eq:bg-T`). -/
theorem restrictCarrier_normal (χ : C(Torus n, ℝ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    restrictCarrier χ U ∘L (restrictCarrier χ U).adjoint =
      complexMultiplier χ ∘L (U ∘L U.adjoint) ∘L complexMultiplier χ := by
  rw [restrictCarrier_adjoint, restrictCarrier]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Restriction retains BOTH real quadratures (`app:ch_background:eq:bg-realification`). -/
theorem carrierChannel_restrictCarrier (χ : C(Torus n, ℝ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    carrierChannel (restrictCarrier χ U) = cutoffMultiplier χ ∘L carrierChannel U := by
  ext1 f
  change (2 : ℝ) • l2RealPart volume (complexMultiplier χ (U f)) =
    cutoffMultiplier χ ((2 : ℝ) • l2RealPart volume (U f))
  rw [realPart_complexMultiplier, map_smul]

/-- The real carrier normal has the SAME sandwich. A reflected amplitude
already containing factor four is substituted here without a second factor
(`app:ch_background:eq:bg-realification`). -/
theorem carrierChannel_restrictCarrier_normal (χ : C(Torus n, ℝ))
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n) :
    carrierChannel (restrictCarrier χ U) ∘L (carrierChannel (restrictCarrier χ U)).adjoint =
      cutoffMultiplier χ ∘L (carrierChannel U ∘L (carrierChannel U).adjoint) ∘L
        cutoffMultiplier χ := by
  rw [carrierChannel_restrictCarrier, ContinuousLinearMap.adjoint_comp, cutoffMultiplier_adjoint]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Real compression commutes with the two cutoff factors
(`app:ch_background:eq:bg-realification`). -/
theorem realOutputCompression_sandwich (χ : C(Torus n, ℝ))
    (A : ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) :
    realOutputCompression (complexMultiplier χ ∘L A ∘L complexMultiplier χ) =
      cutoffMultiplier χ ∘L realOutputCompression A ∘L cutoffMultiplier χ := by
  ext1 f
  change l2RealPart volume (complexMultiplier χ (A (complexMultiplier χ
    (l2ComplexInclusion volume f)))) =
      cutoffMultiplier χ (l2RealPart volume (A (l2ComplexInclusion volume (cutoffMultiplier χ f))))
  rw [complexMultiplier_inclusion, realPart_complexMultiplier]

end JanetCartan.ContinuumRow.CommonMeasurement
