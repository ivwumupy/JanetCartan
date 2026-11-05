module
public import JanetCartan.Iteration.PhysicalPairs.SampledMask
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ComplexFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSources
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Strain
public import JanetCartan.Iteration.PhysicalHistory
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryAmplitude
public import JanetCartan.Iteration.PhysicalPairs.OriginalMaskRows
public meta import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfilesTemplate
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import Mathlib.Tactic.Module
public meta import Lean

/-!
# Original primary full-strain first-mask data

Consumer: `PhysicalPairs.SampledMask.first_mask.hA/hAj/he` for the original
pre-response primary source (`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`).
The full strain and original solver half force A = 2J_F. The chi2 cutoff occurs
once, the broad source cutoff is unchanged, and neither quadrature doubles the
carrier. The actual compact smooth admission and zero extension provide he.

`Native.sourceF` is extracted verbatim from the checked raw13[7] of the SAME
original amplitude. Its stored expression is the history map of the original
extended/dilated source reference. It is NOT globally relabeled as the unextended
physical finiteMap. `Native.C` depends only on the prehistory44 prefix; `Native.jets`
bounds this SAME twice-Jacobian on the entire original source chart at the true
current coefficient scale. The existing `OriginalMaskRows.row_jets` supplies Q.

The original raw annular derivative factorization and true-scale D-profile remain
separate actual producers (raw native fullDerivativeAmplitude + forward source
field + commonD_N). No hFirstMask, residual-output bound or chain-success premise
is added here. These source data alone do not close the primary strain or Main.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData
open CorrectedAtoms ResponseSourceExtension Sampling.BackgroundModulation
open PhysicalPairs.SampledMask ResponseTransfer.SourceNegative

/-- The complexified Jacobian of the LITERAL original raw source field, with ambient row and physical column (main:eq:primary-strain). -/
noncomputable def sourceJacobian {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  fun k i ↦ (partialDeriv F x i k : ℂ)

/-- The derivative matrix of the unchanged pre-response primary wave. Its annular carrier factorization is supplied separately by the original raw producer (app:ch_waves:eq:individual-representation). -/
noncomputable def rawJacobian {n N : ℕ} (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  fun k i ↦ partialDeriv Z x i k

/-- The first-mask coefficient is exactly twice the SAME source Jacobian. The factor two compensates only the half in symmetricBilinearTensor, not the carrier phase (main:eq:primary-strain). -/
noncomputable def twiceSourceJacobian {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ := (2 : ℂ) • sourceJacobian F x

/-- The full complex linearized metric is the symmetric bilinear tensor with 2J_F, not J_F. No differentiation of a cutoff occurs (app:ch_waves:eq:exact-half-strain). -/
theorem full_strain_eq_symmetric {n N : ℕ}
    (F : Euclidean n → Euclidean N) (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (x : Euclidean n) : WKB.complexLinearizedMetric F Z x =
      symmetricBilinearTensor (twiceSourceJacobian F x) (rawJacobian Z x) := by
  ext i j
  simp only [WKB.complexLinearizedMetric,symmetricBilinearTensor_apply,
    twiceSourceJacobian,sourceJacobian,rawJacobian,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact complex source for SampledMask.first_mask: the original solver half, stress frame and source multiplier remain, chi2 occurs ONCE, and the original phase and frequency do not change. The only wave input is the actual raw derivative factorization on tsupport chi2 (app:ch_regular:eq:source-tail). -/
theorem half_stress_eq_reduced_wave {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ₂ χsrc φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (hfactor : ∀ x ∈ tsupport χ₂,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    (x : Euclidean (d+1)) :
    χsrc x • ((1/2 : ℝ) • complexStressContraction (Q x) (complexAtomicSource F χ₂ Z x)) =
      reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) D false φ ρ x := by
  by_cases hx : x ∈ tsupport χ₂
  · rw [complexAtomicSource,full_strain_eq_symmetric,hfactor x hx,
      symmetricBilinearTensor_smul_right]
    simp only [ContinuousLinearMap.map_smul_of_tower,map_smul,reduced_wave,Bool.false_eq_true,ite_false,
      modulatedSource,ResponseTransfer.carrier]
    module
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp [complexAtomicSource,reduced_wave,modulatedSource,hz]

/-- Rotate only the complete second amplitude in the PLUS reduced source; the phase is unchanged. The imaginary quadrature uses -I (app:ch_response:eq:response-graded-reduced). -/
theorem reduced_wave_smul_amplitude {d N : ℕ}
    (χ ψ φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (A D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ)
    (ρ : ℝ) (ζ : ℂ) (x : Euclidean (d+1)) :
    reduced_wave χ ψ Q A (ζ • D) false φ ρ x =
      ζ • reduced_wave χ ψ Q A D false φ ρ x := by
  simp only [reduced_wave,Bool.false_eq_true,ite_false,Pi.smul_apply,
    symmetricBilinearTensor_smul_right,map_smul,modulatedSource]
  module

/-- The actual real cutoffStressSmoothSource vector is the real part of the original complex half-stress vector (app:ch_response:eq:response-full-map). -/
theorem cutoff_stress_realPart {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (χsrc : Euclidean n → ℝ)
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ) (x : Euclidean n) :
    euclideanCutoffStressSource Q χsrc (tensorFieldRealPart H) x =
      euclideanRealPart (χsrc x • ((1/2 : ℝ) • complexStressContraction (Q x) (H x))) := by
  change χsrc x • WithLp.toLp 2 (AmbientResponse.stressSource Q (tensorFieldRealPart H) x) = _
  rw [congrFun (SignedProductEstimates.stressSource_realPart_eq Q H) x]
  simp only [map_smul]

/-- Every scalar quadrature of the original FULL strain has the exact once-chi2 first-mask representation, with the rotation confined to D (app:ch_regular:eq:source-tail). -/
theorem cutoff_stress_quadrature_eq {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ₂ χsrc φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (hfactor : ∀ x ∈ tsupport χ₂,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    (ζ : ℂ) (x : Euclidean (d+1)) :
    euclideanCutoffStressSource Q χsrc (tensorFieldRealPart (ζ • complexAtomicSource F χ₂ Z)) x =
      euclideanRealPart (reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) (ζ • D) false φ ρ x) := by
  rw [cutoff_stress_realPart,reduced_wave_smul_amplitude,
    ← half_stress_eq_reduced_wave F Z χ₂ χsrc φ Q D ρ hfactor x]
  congr 1
  simp only [Pi.smul_apply,map_smul]
  module

/-- For an already admitted literal tensor quadrature, the genuine inverse-domain zero-extension theorem supplies SampledMask.first_mask.he; no localization-success premise is used (app:ch_regular:eq:exact-physical). -/
theorem zeroExtend_quadrature_eq {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ₂ χsrc φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (hfactor : ∀ x ∈ tsupport χ₂,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    {U W : Set (Euclidean (d+1))} (hU : IsOpen U) (hW : MeasurableSet W)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hχsrc : ContDiff ℝ ∞ χsrc) (hSU : tsupport χ₂ ⊆ U) (hSW : tsupport χ₂ ⊆ W)
    (ζ : ℂ) (hadmit : tensorFieldRealPart (ζ • complexAtomicSource F χ₂ Z) ∈
      PrimarySourceAdmission.compactSmoothSources (tsupport χ₂)) :
    SmallSupport.zeroExtend hW
      (cutoffStressSmoothSource (W := W) Q χsrc hU hQ hχsrc hSU ⟨_,hadmit⟩ :
        LocalSobolev.LocalL2 W (Euclidean (d+1))) =ᵐ[volume]
      fun x ↦ euclideanRealPart
        (reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) (ζ • D) false φ ρ x) := by
  exact (zeroExtend_cutoffStressSmoothSource_coeFn Q χsrc hU hQ hχsrc hSU hW hSW
    ⟨_,hadmit⟩).trans (Eventually.of_forall (cutoff_stress_quadrature_eq F Z χ₂ χsrc φ Q D ρ hfactor ζ))

/-- The real quadrature uses exactly D and the undoubled original carrier (main:eq:primary-strain). -/
theorem cutoff_stress_real_eq {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ₂ χsrc φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (hfactor : ∀ x ∈ tsupport χ₂,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    (x : Euclidean (d+1)) :
    euclideanCutoffStressSource Q χsrc (tensorFieldRealPart (complexAtomicSource F χ₂ Z)) x =
      euclideanRealPart (reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) D false φ ρ x) := by
  simpa only [one_smul] using cutoff_stress_quadrature_eq F Z χ₂ χsrc φ Q D ρ hfactor 1 x

/-- The imaginary quadrature uses exactly -I times D, with the SAME undoubled phase and frequency (main:eq:primary-strain). -/
theorem cutoff_stress_imag_eq {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ₂ χsrc φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (hfactor : ∀ x ∈ tsupport χ₂,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    (x : Euclidean (d+1)) :
    euclideanCutoffStressSource Q χsrc (tensorFieldImagPart (complexAtomicSource F χ₂ Z)) x =
      euclideanRealPart
        (reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) (-Complex.I • D) false φ ρ x) := by
  have hi : tensorFieldImagPart (complexAtomicSource F χ₂ Z) =
      tensorFieldRealPart (-Complex.I • complexAtomicSource F χ₂ Z) := by
    ext y i j
    change (complexAtomicSource F χ₂ Z y i j).im = (-Complex.I * complexAtomicSource F χ₂ Z y i j).re
    simp
  rw [hi]
  exact cutoff_stress_quadrature_eq F Z χ₂ χsrc φ Q D ρ hfactor (-Complex.I) x

/-- Construct both actual compact tensor admissions from local smoothness of the literal F and raw wave, then prove BOTH first-mask he identities for the existing cutoffStressSmoothSource and zeroExtend. This is conditional only on the explicit raw factorization and ordinary source geometry/smoothness; it is not an unconditional primary-strain estimate (app:ch_regular:eq:source-tail). -/
theorem admitted_quadratures_zeroExtend {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Z : Euclidean (d+1) → EuclideanSpace ℂ (Fin N))
    (χ₂ χsrc φ : Euclidean (d+1) → ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (D : Euclidean (d+1) → Matrix (Fin N) (Fin (d+1)) ℂ) (ρ : ℝ)
    (hfactor : ∀ x ∈ tsupport χ₂,
      rawJacobian Z x = Complex.exp (Complex.I * (ρ * φ x : ℝ)) • D x)
    {U W : Set (Euclidean (d+1))} (hU : IsOpen U) (hW : MeasurableSet W)
    (hF : ContDiffOn ℝ ∞ F U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hc : HasCompactSupport χ₂)
    (hχsrc : ContDiff ℝ ∞ χsrc) (hSU : tsupport χ₂ ⊆ U) (hSW : tsupport χ₂ ⊆ W) :
    ∃ (hre : tensorFieldRealPart (complexAtomicSource F χ₂ Z) ∈
          PrimarySourceAdmission.compactSmoothSources (tsupport χ₂))
      (him : tensorFieldImagPart (complexAtomicSource F χ₂ Z) ∈
          PrimarySourceAdmission.compactSmoothSources (tsupport χ₂)),
      (SmallSupport.zeroExtend hW
        (cutoffStressSmoothSource (W := W) Q χsrc hU hQ hχsrc hSU ⟨_,hre⟩ :
          LocalSobolev.LocalL2 W (Euclidean (d+1))) =ᵐ[volume]
        fun x ↦ euclideanRealPart
          (reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) D false φ ρ x)) ∧
      (SmallSupport.zeroExtend hW
        (cutoffStressSmoothSource (W := W) Q χsrc hU hQ hχsrc hSU ⟨_,him⟩ :
          LocalSobolev.LocalL2 W (Euclidean (d+1))) =ᵐ[volume]
        fun x ↦ euclideanRealPart
          (reduced_wave χ₂ χsrc Q (twiceSourceJacobian F) (-Complex.I • D) false φ ρ x)) := by
  obtain ⟨hre,him⟩ := PrimarySourceAdmission.cutoff_strain_quadratures_mem hχ₂ hc hU hF hZ hSU
  refine ⟨hre,him,?_,?_⟩
  · exact (zeroExtend_cutoffStressSmoothSource_coeFn Q χsrc hU hQ hχsrc hSU hW hSW
      ⟨_,hre⟩).trans (Eventually.of_forall (cutoff_stress_real_eq F Z χ₂ χsrc φ Q D ρ hfactor))
  · exact (zeroExtend_cutoffStressSmoothSource_coeFn Q χsrc hU hQ hχsrc hSU hW hSW
      ⟨_,him⟩).trans (Eventually.of_forall (cutoff_stress_imag_eq F Z χ₂ χsrc φ Q D ρ hfactor))


/-- The fixed real-linear Frobenius conversion from DF to 2J_F. Its operator norm is a dimension-only coefficient cost (main:eq:primary-strain). -/
def twiceJacobianLinear (n N : ℕ) :
    (Euclidean n →L[ℝ] Euclidean N) →L[ℝ] Matrix (Fin N) (Fin n) ℂ :=
  let L : (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ :=
    { toFun := fun A k i ↦ (2 : ℂ) * (A (EuclideanSpace.single i (1 : ℝ)) k : ℂ)
      map_add' := by intro A B; ext k i; simp [mul_add]
      map_smul' := by intro a A; ext k i; simp [mul_left_comm] }
  ⟨L,L.continuous_of_finiteDimensional⟩

/-- The coefficient is literally the fixed linear conversion of the SAME full source derivative (main:eq:primary-strain). -/
theorem twiceSourceJacobian_eq_comp {n N : ℕ} (F : Euclidean n → Euclidean N) :
    twiceSourceJacobian F = twiceJacobianLinear n N ∘ fderiv ℝ F := rfl

/-- Smoothness of the actual twice-Jacobian coefficient comes from the original source field, not a physical-frequency wave profile (app:ch_regular:eq:source-tail). -/
theorem contDiff_twiceSourceJacobian {n N : ℕ} {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (twiceSourceJacobian F) := by
  rw [twiceSourceJacobian_eq_comp]
  exact (twiceJacobianLinear n N).contDiff.comp (hF.fderiv_right (by simp))

/-- A q-jet of 2J_F spends exactly one source-field derivative and only the fixed conversion norm (main:eq:primary-strain). -/
theorem norm_iteratedFDeriv_twiceSourceJacobian_le {n N : ℕ}
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (q : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ q (twiceSourceJacobian F) x‖ ≤
      ‖twiceJacobianLinear n N‖ * ‖iteratedFDeriv ℝ (q+1) F x‖ := by
  rw [twiceSourceJacobian_eq_comp]
  have h := (twiceJacobianLinear n N).norm_iteratedFDeriv_comp_left
    (hF.fderiv_right (m := ∞) (by simp)).contDiffAt (n := q) (x := x) (by simp)
  simpa only [norm_iteratedFDeriv_fderiv] using h

/-- The actual history derivative producer gives all q-jets of the SAME 2J_F at the TRUE coefficient scale: q+1-rStar <= q. The fixed reference may already contain the original extension/dilation. C is selected before R0 and every history; no lambda-jet estimate is used (main:eq:primary-strain; app:ch_regular:eq:source-tail). -/
theorem exists_history_twiceJacobian_profiles {n : ℕ} (G : FlatReference n) (radius : ℝ)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ} (hStar : 1 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧ ∀ R₀, 2 ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      ContDiff ℝ ∞ (twiceSourceJacobian (RevisedGlobal.finiteMap G.map u)) ∧
      ∀ x ∈ closedBall (0 : Euclidean n) radius, ∀ q,
        ‖iteratedFDeriv ℝ q (twiceSourceJacobian (RevisedGlobal.finiteMap G.map u)) x‖ ≤
          C q * currentCoefficientScale R₀ j ^ q := by
  obtain ⟨A,hA,hp⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) radius) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  refine ⟨fun q ↦ ‖twiceJacobianLinear n (embeddingDimension n)‖ * A (q+1),
    fun q ↦ mul_nonneg ((twiceJacobianLinear n (embeddingDimension n)).opNorm_nonneg) (hA _),?_⟩
  intro R₀ hR₀ j u ell hu
  have hF : ContDiff ℝ ∞ (RevisedGlobal.finiteMap G.map u) :=
    G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  refine ⟨contDiff_twiceSourceJacobian hF,?_⟩
  intro x hx q
  have hT := one_le_currentCoefficientScale (by linarith : (1 : ℝ) ≤ R₀) j
  have hjet := (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall (0 : Euclidean n) radius)
    (hF.of_le (by simp)) hx (le_refl (q+1))).trans (hp R₀ hR₀ j u ell hu _ Subset.rfl (q+1))
  apply (norm_iteratedFDeriv_twiceSourceJacobian_le hF q x).trans
  apply (mul_le_mul_of_nonneg_left hjet ((twiceJacobianLinear n (embeddingDimension n)).opNorm_nonneg)).trans
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega : q+1-rStar ≤ q))
    (mul_nonneg ((twiceJacobianLinear n (embeddingDimension n)).opNorm_nonneg) (hA _))


end JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData
end

meta section
namespace JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication
open Lean Meta Elab Command
open PhysicalMean.OriginalParentCorrectedProfilesTemplate (withActualParent)
private def root := `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native
private def helper := `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData
private def graded := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (n : Name) (a : Array Expr) := mkAppN (mkConst n) a
private def left (h : Expr) := Expr.proj ``And 0 h
private def right (h : Expr) := Expr.proj ``And 1 h
private def save (key : Name) (p : Array Expr) (value : Expr) (target : Expr)
    (data := false) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "primary source coefficient: open/late/unchecked operand in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"checking original primary strain coefficient {key}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The literal raw13[7] sourceF and its SAME twice-Jacobian on the original whole source chart. Static coefficient cost precedes all histories; the true current coefficient scale is unchanged (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  return app name p
private def publish (mode : Nat) : MetaM Unit := withActualParent fun d => do
  unless mode < 7 do throwError "primary source coefficient: unknown declaration"
  let p := d.params52
  let static := p[:44].toArray
  let native := p[:50].toArray
  let F := d.raw13[7]!
  unless F.isAppOfArity `JanetCartan.RevisedGlobal.finiteMap 5 do
    throwError "primary source coefficient: saved raw source is not the checked literal history map"
  let fa := F.getAppArgs
  unless fa[3]!.isAppOfArity `JanetCartan.FlatReference.map 2 do
    throwError "primary source coefficient: original source reference map changed"
  let G := fa[3]!.appArg!
  let n := d.raw13[0]!
  let radius := app `JanetCartan.PhysicalSeed.OriginalBoundary.b #[n,p[1]!]
  let A := app (helper ++ `twiceSourceJacobian) #[n,d.raw13[1]!,F]
  let namedA := app (root ++ `A) native
  if mode == 2 then
    discard <| save `sourceF native F (← inferType F) true
    return
  if mode == 3 then
    discard <| save `A native A (← inferType A) true
    return
  if mode == 4 then
    let sourceF := app (root ++ `sourceF) native
    let namedSrcA := app (helper ++ `twiceSourceJacobian) #[n,d.raw13[1]!,sourceF]
    discard <| save `A_eq_twiceSourceJacobian native (← mkEqRefl A) (← mkEq namedA namedSrcA)
    return
  let hStar ← Term.TermElabM.run' <| PhysicalBackground.NativeReferenceSourceTemplate.termWith
    [(`rStar,p[31]!),(`hStar,p[33]!)] "(show 1 ≤ rStar from by omega)"
  let ex := app (helper ++ `exists_history_twiceJacobian_profiles)
    #[n,G,radius,p[29]!,p[30]!,p[31]!,p[32]!,hStar,p[35]!]
  let C ← mkAppM ``Classical.choose #[ex]
  if mode == 0 then
    discard <| save `C static C (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true
    return
  let spec ← mkAppM ``Classical.choose_spec #[ex]
  let namedC := app (root ++ `C) static
  if mode == 1 then
    let nonneg ← withLocalDeclD `q (mkConst ``Nat) fun q => do
      let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real,mkNatLit 0,none]
      mkForallFVars #[q] (← mkAppM ``LE.le #[zero,mkApp namedC q])
    discard <| save `C_nonneg static (left spec) nonneg
    return
  let hTwo ← mkAppM ``le_trans #[app (graded ++ `hS) static,p[45]!]
  let actual := mkAppN (right spec) #[p[44]!,hTwo,p[46]!,p[47]!,p[48]!,p[49]!]
  let named (e : Expr) : Expr := e.replace fun a =>
    if a == A then some namedA else if a == C then some namedC else none
  if mode == 5 then
    discard <| save `smooth native (left actual) (named (← inferType (left actual)))
    return
  let source23 := d.source53[:23].toArray
  let chart := app (masks ++ `chart) source23
  let hchart := app (masks ++ `chart_in_coefficient_ball) source23
  let E := (← inferType chart).appArg!
  withLocalDeclD `x E fun x => do
    withLocalDeclD `hx (← mkAppM `Membership.mem #[chart,x]) fun hx => do
      let hxball := mkAppN hchart #[x,hx]
      let hxclosed ← mkAppM `Metric.ball_subset_closedBall #[hxball]
      let bound := mkAppN (right actual) #[x,hxclosed]
      let pf ← mkLambdaFVars #[x,hx] bound
      discard <| save `jets native pf (named (← inferType pf))
end JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication
end
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 0
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 1
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 2
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 3
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 4
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 5
run_meta JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskDataApplication.publish 6
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.C
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.C_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.sourceF
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.A
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.A_eq_twiceSourceJacobian
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native.jets

#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.full_strain_eq_symmetric
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.half_stress_eq_reduced_wave
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.cutoff_stress_imag_eq
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.admitted_quadratures_zeroExtend
#print axioms JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.exists_history_twiceJacobian_profiles
