module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.WeightedTests

/-!
# Literal carrier realization on weighted raw inputs

For `app:ch_background:eq:bg-density-twice`, Hölder pairing and the constructed
weighted test approximation identify the bounded carrier with its literal
uncut integral. The hypotheses concern the raw weighted input and the reciprocal
weighted kernel, never a transported mean identity. The latter membership must
be obtained from the geometric compact carrier support and frequency decay.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.UncutDensity
open ContinuumRow RawCutoffBounds ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

private theorem cancel_weight_smul (w : ℝ) (hw : w ≠ 0) (a : ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    (w • a) • (w⁻¹ • v) = a • v := by
  rw [smul_assoc, smul_comm a, ← mul_smul, mul_inv_cancel₀ hw, one_smul]

/-- Absolute convergence of the actual kernel follows by Hölder from the
existing weighted raw domain (`app:ch_background:eq:bg-density-twice`). -/
theorem integrable_carrierKernel_of_weighted (d : CarrierData n N) (s : ℕ)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight s) f)
    (x : Torus n)
    (hk : MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
      2 (carrierMeasure n)) :
    Integrable (fun p ↦ f p • carrierKernel d x p) (carrierMeasure n) := by
  have hi : MemLp (fun p ↦ (etaBesselWeight s p • f p) •
      ((etaBesselWeight s p)⁻¹ • carrierKernel d x p)) 1 (carrierMeasure n) :=
    hf.smul hk
  apply (memLp_one_iff_integrable.mp hi).congr
  exact Eventually.of_forall fun p ↦
    cancel_weight_smul _ (ne_of_gt (etaBesselWeight_pos s p)) _ _

private theorem pairing_weighted_input (d : CarrierData n N) (s : ℕ)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight s) f)
    (x : Torus n)
    (hk : MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
      2 (carrierMeasure n)) :
    (ContinuousLinearMap.lsmul ℂ ℂ).lpPairing (carrierMeasure n) 2 2
        (hf.toLp _) (hk.toLp _) = carrierTestIntegral d f x := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hk.coeFn_toLp] with p hp hq
  simp only [ContinuousLinearMap.lsmul_apply, hp, hq]
  exact cancel_weight_smul _ (ne_of_gt (etaBesselWeight_pos s p)) _ _

private theorem pairing_divided_test (d : CarrierData n N) (s : ℕ)
    (u : carrierInitialTestSpace n) (x : Torus n)
    (hk : MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
      2 (carrierMeasure n)) :
    (ContinuousLinearMap.lsmul ℂ ℂ).lpPairing (carrierMeasure n) 2 2
        (carrierInitialTestToLp u) (hk.toLp _) =
      carrierTestIntegral d (divideWeightTest s u).val x := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(carrierInitialTest_memLp u).coeFn_toLp, hk.coeFn_toLp] with p hp hq
  change carrierInitialTestToLp u p = u.val p at hp
  simp only [ContinuousLinearMap.lsmul_apply, hp, hq, divideWeightTest]
  exact (smul_comm _ _ _).trans (smul_assoc _ _ _).symm

/-- The literal carrier integral is the pointwise limit of the constructed
weighted tests, including the original phase and footpoint
(`app:ch_background:eq:bg-density-twice`). -/
theorem carrierTestIntegral_divideWeight_tendsto (d : CarrierData n N) (s : ℕ)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight s) f)
    (u : ℕ → carrierInitialTestSpace n)
    (hu : Tendsto (fun k ↦ carrierInitialTestToLp (u k)) atTop (𝓝 (hf.toLp _)))
    (x : Torus n)
    (hk : MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
      2 (carrierMeasure n)) :
    Tendsto (fun k ↦ carrierTestIntegral d (divideWeightTest s (u k)).val x)
      atTop (𝓝 (carrierTestIntegral d f x)) := by
  let L : CarrierL2 n →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((ContinuousLinearMap.lsmul ℂ ℂ).lpPairing (carrierMeasure n) 2 2).flip (hk.toLp _)
  have ht := L.continuous.tendsto (hf.toLp _) |>.comp hu
  change Tendsto (fun k ↦ L (carrierInitialTestToLp (u k))) atTop (𝓝 (L (hf.toLp _))) at ht
  have he : L (hf.toLp _) = carrierTestIntegral d f x :=
    pairing_weighted_input d s f hf x hk
  rw [he] at ht
  exact ht.congr (fun k ↦ pairing_divided_test d s (u k) x hk)

/-- Passage from the bounded literal test realization to actual weighted raw
inputs. This derives the representative from test density and Hölder continuity;
it does not assume realization away from tests
(`app:ch_background:eq:bg-density-twice`). -/
theorem carrierRealization_weighted (d : CarrierData n N) (s : ℕ)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (hk : ∀ᵐ x ∂volume,
      MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
        2 (carrierMeasure n))
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight s) f) :
    U f =ᵐ[volume] carrierTestIntegral d f := by
  obtain ⟨u, hu, hv⟩ := exists_weighted_test_approximation s f hf
  obtain ⟨ks, hks, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (U.continuous.tendsto f |>.comp hv)).exists_seq_tendsto_ae
  filter_upwards [hlim, hk, ae_all_iff.mpr (fun k ↦ hU (divideWeightTest s (u k)))]
    with x hx hkx htest
  have ht := (carrierTestIntegral_divideWeight_tendsto d s f hf u hu x hkx).comp
    hks.tendsto_atTop
  exact tendsto_nhds_unique hx (ht.congr (fun k ↦ (htest (ks k)).symm))

/-- The factor-four identity on raw weighted inputs, for
`app:ch_background:eq:bg-density-twice`. Geometric plateau and reciprocal-kernel
membership are explicit remaining inputs; bounded realization is required only
on the existing smooth test domain. -/
theorem measuredIncrement_four_weighted (d : CarrierData n N) (s : ℕ)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (hk : ∀ᵐ x ∂volume,
      MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
        2 (carrierMeasure n))
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight s) f) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d 4 f) =ᵐ[volume]
      fun x ↦ (2 : ℝ) • carrierChannel U f x := by
  filter_upwards [carrierRealization_weighted d s U hU hk f hf,
    carrierChannel_coeFn U f, hk] with x hx hy hkx
  rw [hy, hx]
  exact measuredIncrement_four d χ hχ f x
    (integrable_carrierKernel_of_weighted d s f hf x hkx)

/-- The negative-twice identity on raw weighted inputs, for
`app:ch_mean_pairs:eq:mean-density-recursion`, on the same literal domain. -/
theorem measuredIncrement_neg_two_weighted (d : CarrierData n N) (s : ℕ)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (hk : ∀ᵐ x ∂volume,
      MemLp (fun p ↦ (etaBesselWeight s p)⁻¹ • carrierKernel d x p)
        2 (carrierMeasure n))
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight s) f) :
    measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d (-2) f) =ᵐ[volume]
      fun x ↦ -(carrierChannel U f x) := by
  filter_upwards [carrierRealization_weighted d s U hU hk f hf,
    carrierChannel_coeFn U f, hk] with x hx hy hkx
  rw [hy, hx]
  exact measuredIncrement_neg_two d χ hχ f x
    (integrable_carrierKernel_of_weighted d s f hf x hkx)

end JanetCartan.UncutDensity
