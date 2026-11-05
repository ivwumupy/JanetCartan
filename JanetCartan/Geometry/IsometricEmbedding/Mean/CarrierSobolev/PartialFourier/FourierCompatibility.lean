module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Transverse
/-!
# Fourier compatibility of the transverse radian dilation

For `app:ch_background:prop:bg-adjoint`, the initial Sobolev norm requires
control of the transverse Fourier variable. We prove that the L² Fourier
transform conjugates `transverseDilation` to its inverse. Consequently the
Fourier transform of `transverseUnitaryInverse` is exactly the inverse dilation,
with representative `synthesisFactor n • f ((2π) • ξ)`.

The integral change of variables proves the identity on integrable L² data;
Schwartz density and continuity extend it to all L² data. These results supply
the transverse compatibility used by the carrier partial unitary transform.
They allow arbitrary complete complex Hilbert fibers and dimension zero.
-/

open MeasureTheory FourierTransform
open scoped ComplexInnerProductSpace
@[expose] public noncomputable section
namespace JanetCartan.CarrierSobolev
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
/-- The Fourier integral exchanges the radian coordinate dilation with its
inverse, including the exact amplitude in `app:ch_background:prop:bg-adjoint`.
This change of variables is the integral input to `fourier_transverseDilation`;
it does not require integrability. -/
theorem fourierIntegral_transverseDilation (f : Euclidean (n - 1) → F) (ξ : Euclidean (n - 1)) :
    𝓕 (fun y => (synthesisFactor n)⁻¹ • f ((2 * Real.pi)⁻¹ • y)) ξ =
      synthesisFactor n • 𝓕 f ((2 * Real.pi) • ξ) := by
  have hi (y : Euclidean (n - 1)) :
      inner ℝ ((2 * Real.pi)⁻¹ • y) ((2 * Real.pi) • ξ) = inner ℝ y ξ := by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_mul]
  simp only [Real.fourier_eq, smul_comm (Real.fourierChar _) ((synthesisFactor n)⁻¹),
    integral_smul]
  conv_lhs => arg 2; arg 2; ext y; rw [← hi y]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun y : Euclidean (n - 1) => Real.fourierChar (-inner ℝ y ((2 * Real.pi) • ξ)) • f y)
    (by positivity : 0 ≤ 2 * Real.pi)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul]
  rw [← synthesisFactor_sq]
  congr 1
  field_simp [ne_of_gt (synthesisFactor_pos n)]

/-- Representative of the inverse radian dilation, used to identify the
transverse frequency variable in `app:ch_background:prop:bg-adjoint`. -/
theorem transverseDilation_symm_coeFn
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    (transverseDilation n F).symm f =ᵐ[volume]
      fun ξ => synthesisFactor n • f ((2 * Real.pi) • ξ) :=
  transverseScale_coeFn _ _ (by positivity) f

private theorem fourier_transverseDilation_of_integrable
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1))))
    (hf : Integrable (f : Euclidean (n - 1) → F)) :
    𝓕 (transverseDilation n F f) = (transverseDilation n F).symm (𝓕 f) := by
  have hD : Integrable (transverseDilation n F f : Euclidean (n - 1) → F) :=
    ((hf.comp_smul (by positivity : (2 * Real.pi : ℝ)⁻¹ ≠ 0)).smul
      (synthesisFactor n)⁻¹).congr (transverseDilation_coeFn f).symm
  have he := (Measure.quasiMeasurePreserving_smul (volume : Measure (Euclidean (n - 1)))
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)).ae
    (Localization.fourierTransform_coeFn_ae_integral_hilbert f hf)
  apply Lp.ext
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hD,
    transverseDilation_symm_coeFn (𝓕 f), he] with ξ h1 h2 h3
  rw [h1, Real.fourier_congr_ae (transverseDilation_coeFn f) ξ,
    fourierIntegral_transverseDilation, h2, h3]

/-- The actual L² Fourier-dilation conjugacy for the transverse frequency
control in `app:ch_background:prop:bg-adjoint`. The identity holds for every L²
class, without any extra integrability hypothesis. -/
theorem fourier_transverseDilation
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    𝓕 (transverseDilation n F f) = (transverseDilation n F).symm (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun f : Lp F 2 (volume : Measure (Euclidean (n - 1))) =>
      𝓕 (transverseDilation n F f) = (transverseDilation n F).symm (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := Euclidean (n - 1)) (F := F)
      (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      (continuous_fourier.comp (transverseDilation n F).continuous)
      ((transverseDilation n F).symm.continuous.comp continuous_fourier)
  intro g
  exact fourier_transverseDilation_of_integrable _
    (g.integrable.congr (g.coeFn_toLp 2).symm)

/-- The Fourier transform of the unitary radian inverse is the inverse
dilation. This is the transverse identity consumed by the partial carrier
transform for `app:ch_background:prop:bg-adjoint`. -/
theorem fourier_transverseUnitaryInverse
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    𝓕 (transverseUnitaryInverse n F f) = (transverseDilation n F).symm f := by
  change 𝓕 (transverseDilation n F (𝓕⁻ f)) = _
  rw [fourier_transverseDilation, fourier_fourierInv_eq]

/-- Explicit transverse frequency representative after unitary radian
synthesis, supplying the frequency rescaling in the initial Sobolev estimate
of `app:ch_background:prop:bg-adjoint`. -/
theorem fourier_transverseUnitaryInverse_coeFn
    (f : Lp F 2 (volume : Measure (Euclidean (n - 1)))) :
    (𝓕 (transverseUnitaryInverse n F f) : Lp F 2 volume) =ᵐ[volume]
      fun ξ => synthesisFactor n • f ((2 * Real.pi) • ξ) := by
  rw [fourier_transverseUnitaryInverse]
  exact transverseDilation_symm_coeFn f

end JanetCartan.CarrierSobolev
