module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange.ComponentOperator
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure
public import Mathlib.Tactic.Abel

/-!
# Actual-current inverse and the uncut sampled mean frontend

Consume the original current augmented-normal inverse and its all-order raw
regularity (producer: `StrongCurrent.source_continuation`, completed with the
actual leading data by the parent). Reuse `PhysicalMean.fixedSourceLinear`,
whose auxiliary part is UNCUT, and the same full corrected raw derivative G.

The global complete source operator is the sampled complete normal followed by
THIS current inverse. The physical strain identity holds ONLY on the common
original plateau, as in `new:lem:mean-source-identity`; the exterior summand is
never identified globally with physical strain. Consumer:
`PhysicalMean.sourceResidual_localized_eq_weightedHermitian_defect`.

The exact `I−E` decomposition preserves the leading-carrier tail on sources
separately from finite-rate corrected-normal transport and sampling. The
transport producer is `CorrectedTransport.FullComparison`, with error
`Ccompare * lam⁻¹ * K / h` and a `τ K` buffer, NOT a `τ K²` hypothesis.
The middle term retains the producer's literal colored expectation, including
its deterministic quadrature; it is not called a sampling-only error.
No claim is made that `I−E` is small on all L² (`new:sec:mean-source-equation`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalNormalInverse.MeanFrontend
open CurrentMean SmoothPeriodicFamily ContinuumRow CanonicalChange PhysicalMean AmplitudeBound

variable {n N : ℕ} {ι ν m : Type*} [Fintype ι] [Fintype ν] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]

/-- The literal current coefficient formula becomes the geometric coefficient
on the original coefficient plateau; no equality of raw/extended stresses
outside their common domain is used (`app:ch_background:defn:bg-mixed`). -/
theorem coefficient_formula_on_core
    (F : Euclidean n → Euclidean N)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χcoeff : Euclidean n → ℝ) {core : Set (Euclidean n)}
    (hformula : ∀ a y, c a y = χcoeff (centeredTorusRepresentative y) *
      GeometricProfile.geometricReducedCoefficients F (centeredTorusRepresentative y) a)
    (hcell : core ⊆ PeriodicLocalL2.halfOpenCell n)
    (hplateau : ∀ x ∈ core, χcoeff x = 1) :
    ∀ x ∈ core, ∀ a, c a (torusQuotient x) =
      GeometricProfile.geometricReducedCoefficients F x a := by
  intro x hx a
  rw [hformula, PeriodicLocalL2.centeredTorusRepresentative_quotient (hcell hx),
    hplateau x hx, one_mul]

variable (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n)

attribute [local irreducible] ContinuousLinearMap.inverse augmentedNormal imageChannel
  augmentedRow fixedSourceLinear smoothCanonicalResponse

variable (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)) ∈
        CarrierSobolev.augmentedInputLevel n ν s)
    (μ : ι → ℝ)
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))

include hreg in
/-- The image raw component of this current inverse has every actual Sobolev
order (`app:ch_background:prop:bg-inverse`), by projection of its proved hreg. -/
theorem current_image_mem (e : SmoothResidual n) (s : ℕ) :
    (imageChannel c χmeas χsrc).adjoint (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
  rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ]
  exact ((CarrierSobolev.mem_augmentedInputLevel_iff s _).mp (hreg e s)).1

include hreg in
/-- The unchanged exterior raw component is retained globally, not dropped
from the current normal (`app:ch_background:prop:bg-inverse`). -/
theorem current_exterior_mem (e : SmoothResidual n) (s : ℕ) :
    exteriorChannel ψ (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
  rw [← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
  exact ((CarrierSobolev.mem_augmentedInputLevel_iff s _).mp (hreg e s)).2.2

/-- The complete sampled normal is followed by the literal uncut CURRENT
normal inverse. The raw action premise is the exact corrected-kernel identity
from `DirectCorrectedRow`, not a desired mean-response estimate. -/
theorem current_fixedSourceLinear_toL2 (hμ : ∀ i, 0 ≤ μ i)
    (hraw : ∀ i v, smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v) = A i v)
    (e : SmoothResidual n) :
    smoothResidualToL2 n
      (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) hreg μ base C hC A G e) =
      uncutSampledNormal c χmeas χsrc ψ μ A (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)) :=
  fixedSourceLinear_toL2 c hc χmeas χsrc ψ hm hs hψ U ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) hreg μ base C hC A G hμ hraw e

/-- For the actual raw cross operator construction, the raw action is closed
by definition. The primitive hG is produced by
`exists_directSmoothCanonicalPrefix_L2_bound` for the SAME full corrected G;
this leaves no mean-response identity as an assumption. -/
theorem current_fixedSourceLinear_toL2_of_rawDerivative
    (CG : ι → ℝ)
    (hG : ∀ i v, periodicL2Norm (fun x ↦ (G i v).val x ()) ≤ CG i * ‖v‖)
    (hμ : ∀ i, 0 ≤ μ i) (e : SmoothResidual n) :
    let Aactual := smoothRawCrossOperator base C hC G CG hG
    smoothResidualToL2 n
      (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) hreg μ base C hC Aactual G e) =
      uncutSampledNormal c χmeas χsrc ψ μ Aactual (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)) := by
  apply current_fixedSourceLinear_toL2
  · exact hμ
  · intro i v
    rfl

/-- The physical linear mean on the original core, with no global physical
interpretation of the exterior channel (`new:lem:mean-source-identity`). This
closes the localized hlinear consumer using the literal uncut auxiliary field
and full corrected sampled-adjoint derivative, not principal replacements. -/
theorem current_fixedSourceLinear_eq_strain_on_core
    {F : Euclidean n → Euclidean N} {W core : Set (Euclidean n)}
    (hW : IsOpen W) (hcore : IsOpen core) (hsub : core ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    {χout : Euclidean n → ℝ} (hplateau : EqOn χout (fun _ ↦ 1) core)
    (hcoeff : ∀ x ∈ core, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (hmeas : ∀ x ∈ core, χmeas (torusQuotient x) = 1)
    (hext : ∀ x ∈ core, ψ (torusQuotient x) = 1)
    (hCgeom : ∀ x ∈ core, ∀ T i, (C (torusQuotient x) T) i =
      tensorPairing (StressFrame.geometricCubeStress F x i).val T)
    (e : SmoothResidual n) {x : Euclidean n} (hx : x ∈ core) (i : Fin n) :
    (fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) hreg μ base C hC A G e).val
        (torusQuotient x) () i =
      tensorPairing (StressFrame.geometricCubeStress F x i).val
        (linearizedMetric F
          (preparationAuxiliaryField χsrc ((imageChannel c χmeas χsrc).adjoint (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e))) F χout) x +
        (2 : ℝ) • weightedHermitianBilinear μ
          (fun y j ↦ base.val (torusQuotient y) j)
          (fun y j ↦ (fixedSourceDerivative A G ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e).val (torusQuotient y) j) x) := by
  have haux := uncutAuxiliaryRepresentative_eq_strain_on_core
    c hc χmeas χsrc ψ hm hs hψ
    ((imageChannel c χmeas χsrc).adjoint (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)))
    (exteriorChannel ψ (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) (smoothResidualToL2 n e)))
    (current_image_mem c χmeas χsrc ψ U hreg e)
    (current_exterior_mem c χmeas χsrc ψ U hreg e)
    hW hcore hsub hF himm hplateau hcoeff hmeas hext hx i
  rw [fixedSourceLinear, LinearMap.add_apply, LinearMap.comp_apply,
    smoothCanonicalResponse_eq_measured_cross]
  change _ + (C (torusQuotient x)
    ((2 : ℝ) • weightedHermitianBilinear μ
      (fun y j ↦ base.val (torusQuotient y) j)
      (fun y j ↦ (fixedSourceDerivative A G ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e).val (torusQuotient y) j) x)) i = _
  simp only [preparationAuxiliaryCorrection, LinearMap.coe_mk, AddHom.coe_mk,
    preparationAuxiliaryRepresentative, Equiv.toFun_as_coe, WithLp.equiv_apply]
  rw [haux, hCgeom x hx]
  simp only [tensorPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- The exact v2 two-term decomposition, with NK the SAME continuous LEADING
carrier-input cutoff normal. Its second summand includes corrected-normal
transport AND sampling; neither analytic bound follows from this algebra
(`new:sec:mean-source-equation`). -/
theorem current_mean_defect_split (NK : OutputL2 n →L[ℝ] OutputL2 n)
    (hN : ((augmentedNormal (imageChannel c χmeas χsrc) U ψ)).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) = ContinuousLinearMap.id ℝ (OutputL2 n)) :
    ContinuousLinearMap.id ℝ (OutputL2 n) -
        (uncutSampledNormal c χmeas χsrc ψ μ A).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) =
      ((augmentedNormal (imageChannel c χmeas χsrc) U ψ) - NK).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) +
        (NK - uncutSampledNormal c χmeas χsrc ψ μ A).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) := by
  calc
    _ = ((augmentedNormal (imageChannel c χmeas χsrc) U ψ)).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) - (uncutSampledNormal c χmeas χsrc ψ μ A).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) := by rw [hN]
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro e
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply]
      abel

/-- The leading-carrier tail is evaluated on THIS source. Corrected transport
and sampling are retained together in the second operator norm; their distinct
analytic producers must still be applied (`app:ch_background:eq:bg-carrier-tail`). -/
theorem current_mean_defect_le_split (NK : OutputL2 n →L[ℝ] OutputL2 n)
    (hN : ((augmentedNormal (imageChannel c χmeas χsrc) U ψ)).comp ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) = ContinuousLinearMap.id ℝ (OutputL2 n)) (e : OutputL2 n) :
    ‖e - uncutSampledNormal c χmeas χsrc ψ μ A (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e)‖ ≤
      ‖((augmentedNormal (imageChannel c χmeas χsrc) U ψ) - NK) (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e)‖ +
        ‖NK - uncutSampledNormal c χmeas χsrc ψ μ A‖ * ‖((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e‖ := by
  have h := congrArg (fun T : OutputL2 n →L[ℝ] OutputL2 n ↦ T e)
    (current_mean_defect_split c χmeas χsrc ψ U μ A NK hN)
  change e - uncutSampledNormal c χmeas χsrc ψ μ A (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e) =
    ((augmentedNormal (imageChannel c χmeas χsrc) U ψ) - NK) (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e) + (NK - uncutSampledNormal c χmeas χsrc ψ μ A) (((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse) e) at h
  rw [h]
  exact (norm_add_le
    (((augmentedNormal (imageChannel c χmeas χsrc) U ψ) - NK)
      ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e))
    ((NK - uncutSampledNormal c χmeas χsrc ψ μ A)
      ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e))).trans
    (add_le_add le_rfl
      ((NK - uncutSampledNormal c χmeas χsrc ψ μ A).le_opNorm
        ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e)))

/-- The fully separated v2 operator identity: source-only leading carrier
truncation, finite-rate corrected transport, then sampling. The two cutoff
normals use the SAME input cutoff (`new:sec:mean-source-equation`). -/
theorem current_mean_defect_split_three
    (N0K NcorrK : OutputL2 n →L[ℝ] OutputL2 n)
    (hN : (augmentedNormal (imageChannel c χmeas χsrc) U ψ).comp
      (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse =
        ContinuousLinearMap.id ℝ (OutputL2 n)) :
    ContinuousLinearMap.id ℝ (OutputL2 n) -
      (uncutSampledNormal c χmeas χsrc ψ μ A).comp
        (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse =
      (augmentedNormal (imageChannel c χmeas χsrc) U ψ - N0K).comp
        (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse +
      (N0K - NcorrK).comp (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse +
      (NcorrK - uncutSampledNormal c χmeas χsrc ψ μ A).comp
        (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse := by
  rw [current_mean_defect_split c χmeas χsrc ψ U μ A N0K hN]
  apply ContinuousLinearMap.ext
  intro e
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- Apply the normal-composition and sampling estimates only to their own
operator differences. The leading tail is NOT replaced by an all-L² bound.
The current inverse remains identical in every summand. -/
theorem current_mean_defect_le_three_terms
    (N0K NcorrK : OutputL2 n →L[ℝ] OutputL2 n)
    (hN : (augmentedNormal (imageChannel c χmeas χsrc) U ψ).comp
      (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse =
        ContinuousLinearMap.id ℝ (OutputL2 n)) (e : OutputL2 n) :
    ‖e - uncutSampledNormal c χmeas χsrc ψ μ A
      ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e)‖ ≤
      ‖(augmentedNormal (imageChannel c χmeas χsrc) U ψ - N0K)
        ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e)‖ +
      (‖N0K - NcorrK‖ + ‖NcorrK - uncutSampledNormal c χmeas χsrc ψ μ A‖) *
        ‖(augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse e‖ := by
  have hnorm : ‖N0K - uncutSampledNormal c χmeas χsrc ψ μ A‖ ≤
      ‖N0K - NcorrK‖ + ‖NcorrK - uncutSampledNormal c χmeas χsrc ψ μ A‖ := by
    calc
      _ = ‖(N0K - NcorrK) + (NcorrK - uncutSampledNormal c χmeas χsrc ψ μ A)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
  exact (current_mean_defect_le_split c χmeas χsrc ψ U μ A N0K hN e).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)))

end JanetCartan.PhysicalNormalInverse.MeanFrontend
