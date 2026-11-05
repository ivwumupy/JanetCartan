module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.UncutDensity.KernelDecay

/-!
# Literal uncut synthesis for regular raw data

For `app:ch_background:eq:bg-density-four`, weighted raw membership proves
both L² multiplier output and integrable frequency slices. Consequently the
literal density agrees with the partial unitary inverse with the exact existing
`synthesisFactor`; slice integrability is no longer an extra analytic premise.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.UncutDensity
open ContinuumRow CarrierSobolev RawCutoffBounds ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- The half-order output is in the existing weighted L² domain, directly
from the original cutoff bounds (`app:ch_background:eq:bg-density-four`). -/
theorem memLp_weighted_densitySymbol (d : CarrierData n N) (s : ℕ)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hhm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    MemLp (fun p ↦ etaBesselWeight s p • (carrierDensitySymbol d p * f p))
      2 (carrierMeasure n) := by
  apply memLp_weighted_halfOrder_mul s
    (measurable_angularHighMask hρm hhm).aestronglyMeasurable (mul_nonneg hA hB) _ f hf
  filter_upwards [] with p
  simp only [angularHighMask, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ B * A := mul_le_mul (hhi _) (hρ _ _) (abs_nonneg _) hB
    _ = A * B := mul_comm _ _

/-- Forgetting a positive transverse weight preserves L² membership; this is
used only on the density multiplier output (`app:ch_background:eq:bg-density-four`). -/
theorem memLp_of_weighted_density (s : ℕ) {g : CarrierVariable n → ℂ}
    (hg : AEStronglyMeasurable g (carrierMeasure n))
    (hw : MemLp (fun p ↦ etaBesselWeight s p • g p) 2 (carrierMeasure n)) :
    MemLp g 2 (carrierMeasure n) := by
  apply hw.mono hg
  filter_upwards [] with p
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (etaBesselWeight_pos s p)]
  apply le_mul_of_one_le_left (norm_nonneg _)
  simpa [etaBesselWeight] using etaBesselWeight_mono (n := n) (Nat.zero_le s) p

/-- Sufficient transverse raw regularity gives absolutely integrable frequency
slices. The conclusion holds at almost every carrier parameter and all spatial
points, so no almost-everywhere evaluation on a footpoint graph is used
(`app:ch_background:eq:bg-density-four`). -/
theorem integrable_slice_of_weighted_density (s : ℕ) (hs : n - 1 < 2 * s)
    {g : CarrierVariable n → ℂ}
    (hw : MemLp (fun p ↦ etaBesselWeight s p • g p) 2 (carrierMeasure n)) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (fun η ↦ g (z, η)) := by
  filter_upwards [Fubini.memLp_slice_ae hw] with z hz
  have hi : MemLp (fun η ↦ (Real.sqrt (1 + ‖η‖ ^ 2) ^ s)⁻¹ •
      (etaBesselWeight s (z, η) • g (z, η))) 1 volume :=
    (memLp_inverse_transverse_weight s hs).smul hz
  apply (memLp_one_iff_integrable.mp hi).congr
  exact Eventually.of_forall fun η ↦ by
    change (etaBesselWeight s (z, η))⁻¹ • (etaBesselWeight s (z, η) • g (z, η)) = _
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (etaBesselWeight_pos s (z, η))), one_smul]

/-- Full agreement of literal uncut synthesis with the actual partial unitary
inverse on weighted raw inputs. Output L² membership and integrable slices are
proved, with the exact radian normalization from `realSynthesisL2`
(`app:ch_background:eq:bg-density-four`). -/
theorem realSynthesisL2_raw_coeFn (d : CarrierData n N) (s : ℕ)
    (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hhm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)
    (c : ℝ) (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    ∃ hg : MemLp (fun p ↦ carrierDensitySymbol d p * f p) 2 (carrierMeasure n),
      realSynthesisL2 c (hg.toLp _) =ᵐ[carrierMeasure n] initialDensity d c f := by
  have hm : StronglyMeasurable (fun p ↦ carrierDensitySymbol d p * f p) := by
    apply StronglyMeasurable.mul _ (Lp.stronglyMeasurable f)
    exact (((Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_snd.norm)).measurable).mul
      (measurable_angularHighMask hρm hhm)).stronglyMeasurable
  have hw := memLp_weighted_densitySymbol d s hρm hhm hA hB hρ hhi f hf
  have hg := memLp_of_weighted_density s hm.aestronglyMeasurable hw
  exact ⟨hg, realSynthesisL2_coeFn d c f hm hg
    (integrable_slice_of_weighted_density s hs hw)⟩

/-- Both paper coefficients on actual raw inputs, using only original geometric
support and cutoff data, weighted membership, and bounded realization on tests.
This instantiates the reciprocal-kernel hypothesis rather than asking the
consumer for an extra integral estimate (`app:ch_background:eq:bg-density-twice`,
`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem measuredIncrement_raw (d : CarrierData n N) (s : ℕ) (hs : n - 1 < 2 * s)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ u : carrierInitialTestSpace n,
      U (carrierInitialTestToLp u) =ᵐ[volume] carrierTestIntegral d u.val)
    (hk : ∀ x, AEStronglyMeasurable (carrierKernel d x) (carrierMeasure n))
    {K : Set CarrierParameter} (hK : IsCompact K)
    (hsupp : ∀ z ∉ K, ∀ θ, d.angularCutoff z θ = 0)
    (hst : ∀ x, ContinuousOn (measuredStress d x) K)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z θ, |d.angularCutoff z θ| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)
    (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f) :
    (measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d 4 f) =ᵐ[volume]
      fun x ↦ (2 : ℝ) • carrierChannel U f x) ∧
    (measuredIncrement d (fun z ↦ χ z ^ 2) (initialDensity d (-2) f) =ᵐ[volume]
      fun x ↦ -(carrierChannel U f x)) := by
  have hkernel : ∀ᵐ x ∂volume,
      MemLp (fun p ↦ (etaBesselWeight (s + 1) p)⁻¹ • carrierKernel d x p)
        2 (carrierMeasure n) := Eventually.of_forall fun x ↦
    memLp_inverseWeight_carrierKernel d s hs x (hk x) hK hsupp (hst x) hA hB hρ hhi
  exact ⟨measuredIncrement_four_weighted d (s + 1) χ hχ U hU hkernel f hf,
    measuredIncrement_neg_two_weighted d (s + 1) χ hχ U hU hkernel f hf⟩

end JanetCartan.UncutDensity
