module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.RepresentativeAdmission
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSources
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledObserved

/-!
# The native inverse input has only one inner measurement bump

`main:prop:pairs`, `app:ch_pairs:eq:pairs-exact-offself`,
`app:ch_regular:eq:source-tail`.  Put the *uncut* reduced datum of
`q = χsrc · Qoff` in the original inverse's smooth subspace.  Applying its
actual `bumpL2 χ₂` THEN yields the measured quadrature.  We never need χ₂ to
equal one on its own shoulder.  Smooth admission comes from the complete
Schwartz derivatives, not from any quantitative primary amplitude assumption.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 480000
open Set Metric MeasureTheory
open scoped NNReal ENNReal ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.SampledInput
open PrimarySourceAdmission CorrectedAtoms ResponseSourceExtension SignedProductEstimates UniformStep
open AmbientResponse SmallSupport LocalSobolev FixedDomainInverse
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The literal real tensor of a single ordered pair of complete waves. -/
def tensor {I : Type} {n N : ℕ} (Z : I → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (θ : I → Euclidean n → ℝ) (minus : Bool) (i j : I) : MetricField n :=
  let A := sampledDerivativeAmplitude (fun k ↦ (Z k : Euclidean n → EuclideanSpace ℂ (Fin N))) θ
  fun x ↦ if minus then ProductSum.minusSource θ A i j x else ProductSum.plusSource θ A i j x

/-- No phase smoothness outside the physical carrier chart is needed. The
exponentials cancel in each individual complete tensor, including the
conjugated second derivative of a difference. -/
theorem tensor_formula {I : Type} {n N : ℕ} (Z : I → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (θ : I → Euclidean n → ℝ) (minus : Bool) (i j : I) :
    let dZ := sampledDerivative (fun k ↦ (Z k : Euclidean n → EuclideanSpace ℂ (Fin N)))
    tensor Z θ minus i j = fun x ↦ (symmetricBilinearTensor (dZ i x)
      (if minus then (dZ j x).map conj else dZ j x)).map Complex.re := by
  intro dZ
  funext x
  cases minus <;> simp only [tensor, Bool.false_eq_true, ↓reduceIte, ProductSum.plusSource,
    ProductSum.minusSource,signedPairPlus_eq,signedPairMinus_eq,←sampledDerivative_eq_phase_smul_amplitude] <;> rfl

/-- The actual broad original source cutoff admits this tensor even when the
inner measurement bump is NOT one throughout its support. -/
theorem tensor_admitted {I : Type} {n N : ℕ} (Z : I → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
    (θ : I → Euclidean n → ℝ) (minus : Bool) (i j : I) {η : Euclidean n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    (fun x ↦ η x • tensor Z θ minus i j x) ∈ compactSmoothSources (tsupport η) := by
  let dZ := sampledDerivative (fun k ↦ (Z k : Euclidean n → EuclideanSpace ℂ (Fin N)))
  have hd (k : I) : ContDiffOn ℝ ∞ (dZ k) univ := by
    let L : (Fin N → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ := LinearMap.id
    let J : (Fin N → Fin n → ℂ) →L[ℝ] Matrix (Fin N) (Fin n) ℂ := ⟨L,L.continuous_of_finiteDimensional⟩
    apply J.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro a
    apply contDiffOn_pi.mpr
    intro b
    exact (contDiffOn_piLp 2).mp (((Z k).smooth'.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single b (1:ℝ)))) a
  obtain ⟨hp,hm⟩ := contDiffOn_signed_tensor_amplitudes (hd i) (hd j)
  apply cutoff_mem_compactSmoothSources hη hc isOpen_univ _ (subset_univ _)
  rw [tensor_formula]
  cases minus
  · exact contDiffOn_tensorFieldRealPart hp
  · exact contDiffOn_tensorFieldRealPart hm

/-- The stress on the original uncut tensor `χsrc·q` pays the inner χ₂ only
once upon measurement. No new cutoff or plateau assumption is used. -/
theorem exchange_stress {n : ℕ} (Q : Euclidean n → Fin n → MetricTensor n)
    (χ η : Euclidean n → ℝ) (q : MetricField n) (y : Euclidean n) :
    χ y • WithLp.toLp 2 (stressSource Q (fun x ↦ η x • q x) y) =
      WithLp.toLp 2 (cutoffSource η (stressSource Q (fun x ↦ χ x • q x)) y) := by
  ext j
  change χ y * ((1 / 2 : ℝ) * tensorPairing (Q y j) (η y • q y)) =
    η y * ((1 / 2 : ℝ) * tensorPairing (Q y j) (χ y • q y))
  have he (b : ℝ) : tensorPairing (Q y j) (b • q y) = b * tensorPairing (Q y j) (q y) := by
    simp [tensorPairing, Finset.mul_sum, mul_left_comm]
  rw [he,he]
  ring

variable {n N : ℕ} {I : Type} (Z : I → SchwartzMap (Euclidean n) (EuclideanSpace ℂ (Fin N)))
  (θ : I → Euclidean n → ℝ) (minus : Bool) (i j : I)
  {U W : Set (Euclidean n)} {η : Euclidean n → ℝ} (hU : IsOpen U)
  (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ∀ a, ContDiffOn ℝ ∞ (fun x ↦ Q x a) U)
  (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηU : tsupport η ⊆ U)

/-- Original smooth local datum, BEFORE the `bumpL2` in `Current.Corr`. -/
def uncut : smoothSource W (Euclidean n) :=
  cutoffStressSmoothSource Q (fun _ ↦ 1) hU hQ contDiff_const hηU
    ⟨_,tensor_admitted Z θ minus i j hη hc⟩

/-- The actual real `zeroExtend` fed to `complexSource` represents the exact
ONCE measured stress quadrature on all of space, not just the final core. -/
theorem zeroExtend_measured (hW : MeasurableSet W) {c : Euclidean n} (χ₂ : ContDiffBump c)
    (hχ : tsupport (χ₂ : Euclidean n → ℝ) ⊆ W) :
    zeroExtend hW (bumpL2 (p := 2) le_rfl χ₂
      (uncut (W := W) Z θ minus i j hU Q hQ hη hc hηU : LocalL2 W (Euclidean n))) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (cutoffSource η
        (stressSource Q (fun x ↦ χ₂ x • tensor Z θ minus i j x)) y) := by
  let v : LocalL2 W (Euclidean n) := (uncut (W := W) Z θ minus i j hU Q hQ hη hc hηU).val
  let q := tensor Z θ minus i j
  have hv := (ae_restrict_iff' hW).mp (cutoffStressSmoothSource_coeFn (W := W) Q (fun _ ↦ 1)
    hU hQ contDiff_const hηU ⟨_, tensor_admitted Z θ minus i j hη hc⟩)
  have hb := (ae_restrict_iff' hW).mp (bumpL2_coeFn (p := 2) le_rfl χ₂ v)
  filter_upwards [zeroExtend_coeFn hW (bumpL2 (p := 2) le_rfl χ₂ v),hv,hb] with y he hv hb
  rw [← exchange_stress Q (χ₂ : Euclidean n → ℝ) η q y]
  change zeroExtend hW (bumpL2 (p := 2) le_rfl χ₂ v) y = _
  rw [he]
  by_cases hw : y ∈ W
  · rw [indicator_of_mem hw,hb hw]
    congr 1
    simpa only [v,uncut,q,euclideanCutoffStressSource,cutoffSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul] using hv hw
  · rw [indicator_of_notMem hw,show χ₂ y = 0 from image_eq_zero_of_notMem_tsupport (fun h ↦ hw (hχ h)),zero_smul]
end JanetCartan.PhysicalPairs.SampledInput
end
