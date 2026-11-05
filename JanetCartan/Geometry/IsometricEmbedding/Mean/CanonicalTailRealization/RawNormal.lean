module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.InverseTail
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Output

/-!
# The finite reference normal on the original augmented row

The actual carrier input multiplier is self-adjoint on the original complex
L² space regarded as real. Its cut channel normal is therefore the squared
raw input multiplier. Assembling these carrier normals with the existing
`cutAuxiliaryNormal` identifies the complete reference output with the SAME
augmented row applied to `rawSquaredCutoff` and its original adjoint.

This supplies the algebraic cutoff identification in `main:eq:linear-two-errors`
for the finite raw reference normal. Identifying the sampled corrected row's
comparison target with this expression remains with `CanonicalRowComparison`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal

namespace JanetCartan.CanonicalTailRealization
open ContinuumRow RawCutoffBounds AuxiliaryRawBand

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The literal real input multiplier is self-adjoint, with both complex
quadratures retained (`app:ch_background:defn:bg-mixed`). -/
theorem carrierMultiplier_adjoint (m : Lp ℝ ∞ (carrierMeasure n)) :
    (carrierMultiplier m).adjoint = carrierMultiplier m := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [carrierMultiplier_coeFn m u, carrierMultiplier_coeFn m v] with x hu hv
  rw [hu, hv, real_inner_smul_left, inner_smul_right]

/-- The normal of the SAME carrier with a raw input cutoff is exactly the
carrier composed with the squared multiplier and its uncut adjoint
(`app:ch_background:defn:bg-mixed`). -/
theorem cutCarrier_normal_apply
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (m : Lp ℝ ∞ (carrierMeasure n)) (q : OutputL2 n) :
    ((carrierChannel T).comp (carrierMultiplier m))
      (((carrierChannel T).comp (carrierMultiplier m)).adjoint q) =
      carrierChannel T (carrierSquaredCutoff m ((carrierChannel T).adjoint q)) := by
  rw [ContinuousLinearMap.adjoint_comp, carrierMultiplier_adjoint]
  rfl

/-- Exact expansion of the raw reference output, retaining both auxiliary
slots and every carrier slot of the original adjoint
(`main:eq:linear-two-errors`). -/
theorem augmentedRow_rawSquaredCutoff_apply
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    (K : ℝ) (m : ι → Lp ℝ ∞ (carrierMeasure n)) (q : OutputL2 n) :
    augmentedRow image T ψ
      (rawSquaredCutoff K m ((augmentedRow image T ψ).adjoint q)) =
      image (auxiliarySquaredCutoff K (image.adjoint q)) +
      (∑ i, carrierChannel (T i) (carrierSquaredCutoff (m i) ((carrierChannel (T i)).adjoint q))) +
      exteriorChannel ψ (auxiliarySquaredCutoff K (exteriorChannel ψ q)) := by
  simp only [augmentedRow_adjoint_apply, physicalRow_adjoint_apply, carrierRow_adjoint_apply,
    rawSquaredCutoff, augmentedRow_apply, physicalRow_apply, carrierRow_apply]
  rfl

/-- The already constructed auxiliary normal plus the actual finite carrier
normals is the raw square on the SAME augmented row. This identifies the
reference operator before applying the tail estimate; it is not a hypothesis
about that reference (`app:ch_background:defn:bg-mixed`). -/
theorem cutAuxiliaryNormal_add_cutCarrierNormals_eq_rawSquaredCutoff
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {K : ℝ} (hK : 1 ≤ K) (m : ι → Lp ℝ ∞ (carrierMeasure n)) :
    cutAuxiliaryNormal coeff χmeas χsrc ψ hK +
      (∑ i, ((carrierChannel (T i)).comp (carrierMultiplier (m i))).comp
        ((carrierChannel (T i)).comp (carrierMultiplier (m i))).adjoint) =
      (augmentedRow (imageChannel coeff χmeas χsrc) T ψ).comp
        ((rawSquaredCutoffCLM hK m).comp
          (augmentedRow (imageChannel coeff χmeas χsrc) T ψ).adjoint) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, rawSquaredCutoffCLM_apply,
    ContinuousLinearMap.adjoint_comp, carrierMultiplier_adjoint,
    augmentedRow_rawSquaredCutoff_apply,
    cutAuxiliaryNormal_apply, auxiliaryOutput, imageOutput_eq_imageChannel, exteriorOutput]
  change _ + ∑ i, carrierChannel (T i)
    (carrierSquaredCutoff (m i) ((carrierChannel (T i)).adjoint q)) = _
  abel

/-- The squared-multiplier form of the original normal used by
`exists_finite_prepared_sampled_normal_comparison` is the SAME augmented raw
square. The auxiliary cutoff and carrier masks remain independent here
(`app:ch_mean_pairs:eq:mean-normal-comparison`, `main:eq:linear-two-errors`). -/
theorem cutAuxiliaryNormal_add_carrierSquaredCutoffs_eq_rawSquaredCutoff
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {K : ℝ} (hK : 1 ≤ K) (m : ι → Lp ℝ ∞ (carrierMeasure n)) :
    cutAuxiliaryNormal coeff χmeas χsrc ψ hK +
      (∑ i, (carrierChannel (T i)).comp
        ((carrierSquaredCutoff (m i)).comp (carrierChannel (T i)).adjoint)) =
      (augmentedRow (imageChannel coeff χmeas χsrc) T ψ).comp
        ((rawSquaredCutoffCLM hK m).comp
          (augmentedRow (imageChannel coeff χmeas χsrc) T ψ).adjoint) := by
  rw [← cutAuxiliaryNormal_add_cutCarrierNormals_eq_rawSquaredCutoff]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ext1 q
  exact (cutCarrier_normal_apply (T i) (m i) q).symm

/-- The reference tail now applies to the literal auxiliary-plus-carrier
normal, on the same residual and original inverse. The carrier cutoff is
`c*K`, both auxiliary cutoffs are `K`, and the exact plateau loss remains
visible (`main:eq:linear-two-errors`). -/
theorem cutAuxiliaryNormal_add_cutCarrierNormals_inverse_error_le
    (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {γ c K : ℝ} (hγ : 0 < γ)
    (hgap : ∀ q, γ * ‖q‖ ^ 2 ≤
      ‖(augmentedRow (imageChannel coeff χmeas χsrc) T ψ).adjoint q‖ ^ 2)
    (hc : 0 < c) (hK : 1 ≤ K) (hcK : 1 ≤ c * K) {s : ℕ} (r : OutputL2 n)
    (hmem : CoerciveInverse.rightInverse
      (augmentedRow (imageChannel coeff χmeas χsrc) T ψ) r ∈
        (CarrierSobolev.augmentedInputSobolevScale n ι).level s) :
    let A := augmentedRow (imageChannel coeff χmeas χsrc) T ψ
    let M := carrierMultiplier (RawInputPartition.roundedCarrierMask n (c * K))
    ‖r - (cutAuxiliaryNormal coeff χmeas χsrc ψ hK +
      ∑ i, ((carrierChannel (T i)).comp M).comp ((carrierChannel (T i)).comp M).adjoint)
        ((CoerciveInverse.normalOperator A).inverse r)‖ ≤
      (‖A‖ * max 1 (c ^ (-(s : ℝ)))) * K ^ (-(s : ℝ)) *
        (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s
          (CoerciveInverse.rightInverse A r) := by
  dsimp only
  rw [cutAuxiliaryNormal_add_cutCarrierNormals_eq_rawSquaredCutoff]
  exact reference_error_scaled_rounded_le_raw_norm _ hγ hgap hc hK hcK r hmem

end JanetCartan.CanonicalTailRealization
