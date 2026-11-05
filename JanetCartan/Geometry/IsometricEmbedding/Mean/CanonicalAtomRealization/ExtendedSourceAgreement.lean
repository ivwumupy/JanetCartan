module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.AdmittedResponse
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FrameExtension

/-!
# The full-source coefficient extension on admitted canonical sources

The fixed inverse uses `extendedProjectedStress` while the canonical atoms
use the physical history's projected stress. The original affine extension
agrees on the fixed coefficient ball. Consequently the cutoff stress fields,
their all-order local Lebesgue classes, and the SAME completed smooth response
agree on admitted sources, both quadratures and every tensor-response jet.
No comparison of ambient extensions off the admitted submodule is needed.

Consumers: the full-source direct solver application in the canonical smooth
map and `CorrectedAtoms.exists_fixedSmoothSolver_tensorComponent_bounds`.
Sources: `app:ch_regular:eq:coefficient-extension`,
`app:ch_response:eq:response-full-map`, `app:ch_response:prop:response-graded`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open CorrectedAtoms PrimarySourceAdmission FixedDomainInverse LocalSobolev ResponseSourceExtension
open AmbientResponse ProtectedFlow ResponseSmoothParameters RetardedSobolev.Spaces

/-- Only the stress frame on the admitted tensor support enters the full
cutoff source (`app:ch_response:eq:response-full-map`). -/
theorem euclideanCutoffStressSource_eq_of_eqOn
    {n : ℕ} (Q Q' : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S : Set (Euclidean n)} (hQ : EqOn Q Q' S) (h : compactSmoothSources S) :
    euclideanCutoffStressSource Q η h = euclideanCutoffStressSource Q' η h := by
  funext x
  by_cases hx : x ∈ S
  · simp only [euclideanCutoffStressSource, LinearMap.coe_mk, AddHom.coe_mk,
      cutoffSource, stressSource, hQ hx]
  · have hh : (h : MetricField n) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (h.property.2.2 ht))
    simp [euclideanCutoffStressSource, cutoffSource, stressSource, hh, tensorPairing]

/-- The two coefficient extensions give the identical all-order local L²
source, retaining the original Lebesgue restriction and cutoff
(`app:ch_regular:eq:coefficient-extension`, `app:ch_response:eq:response-full-map`). -/
theorem cutoffStressSmoothSource_eq_of_eqOn
    {n : ℕ} (Q Q' : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U U' W : Set (Euclidean n)} (hU : IsOpen U) (hU' : IsOpen U')
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hQ' : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q' x i) U')
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U) (hSU' : S ⊆ U') (heq : EqOn Q Q' S)
    (h : compactSmoothSources S) :
    cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h =
      cutoffStressSmoothSource (W := W) Q' η hU' hQ' hη hSU' h := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [cutoffStressSmoothSource_coeFn (W := W) Q η hU hQ hη hSU h,
    cutoffStressSmoothSource_coeFn (W := W) Q' η hU' hQ' hη hSU' h] with x hx hx'
  rw [hx, hx', euclideanCutoffStressSource_eq_of_eqOn Q Q' η heq h]

/-- Applying the SAME fixed solution and output cutoff to equal admitted
sources gives identical global completed fields. Values of the ambient
extensions off the source submodule are not compared
(`app:ch_response:eq:response-full-map`). -/
theorem fixedSmoothSolverAmbientExtension_eq_of_eqOn
    {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q Q' : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U U' W core chart : Set (Euclidean n)} (hU : IsOpen U) (hU' : IsOpen U')
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hQ' : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q' x i) U')
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U) (hSU' : S ⊆ U') (heq : EqOn Q Q' S)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (h : compactSmoothSources S) :
    fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h =
      fixedSmoothSolverAmbientExtension F Q' η hU' hQ' hη hSU' solver hsolver Ξ h := by
  rw [fixedSmoothSolverAmbientExtension_eq_cutoff, fixedSmoothSolverAmbientExtension_eq_cutoff,
    cutoffStressSmoothSource_eq_of_eqOn Q Q' η hU hU' hQ hQ' hη hSU hSU' heq h]

/-- Both original quadratures of an admitted complex tensor source use the
same completed field under supported coefficient agreement
(`app:ch_response:cor:current-atoms`). -/
theorem complexify_fixedSmoothSolverAmbientExtension_eq_of_eqOn
    {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q Q' : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U U' W core chart : Set (Euclidean n)} (hU : IsOpen U) (hU' : IsOpen U')
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hQ' : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q' x i) U')
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U) (hSU' : S ⊆ U') (heq : EqOn Q Q' S)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart H ∈ compactSmoothSources S)
    (hi : tensorFieldImagPart H ∈ compactSmoothSources S) :
    complexifyResponse (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) H =
      complexifyResponse (fixedSmoothSolverAmbientExtension F Q' η hU' hQ' hη hSU' solver hsolver Ξ) H := by
  have hr' := fixedSmoothSolverAmbientExtension_eq_of_eqOn F Q Q' η hU hU' hQ hQ' hη
    hSU hSU' heq solver hsolver Ξ ⟨_, hr⟩
  have hi' := fixedSmoothSolverAmbientExtension_eq_of_eqOn F Q Q' η hU hU' hQ hQ' hη
    hSU hSU' heq solver hsolver Ξ ⟨_, hi⟩
  simp only [complexifyResponse, LinearMap.coe_mk, AddHom.coe_mk, hr', hi']

variable {n N : ℕ} (p : BallExtension.Parameters (Euclidean n))
    (F : Euclidean n → Euclidean N) {U S W core chart : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U) (hpU : Metric.closedBall p.center p.radius ⊆ U)
    (hSp : S ⊆ Metric.closedBall p.center p.radius)
    (η : Euclidean n → ℝ) (hη : ContDiff ℝ ∞ η)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)

local notation "Qraw" => ProjectedStressFrame.projectedStress F
local notation "Qext" => extendedProjectedStress p F
local notation "hraw" => ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank
set_option quotPrecheck false in
local notation "hext" => (contDiff_affineFrameExtension p
  ((contDiffOn_pi.mpr hraw).mono hpU)).contDiffOn

/-- The actual affine extension used by the full-source inverse has the
same admitted stress as the physical history, with the original source
support wholly retained (`app:ch_regular:eq:coefficient-extension`). -/
theorem cutoffStressSmoothSource_extendedProjectedStress_eq (h : compactSmoothSources S) :
    cutoffStressSmoothSource (W := W) Qext η isOpen_univ
      (fun i ↦ contDiffOn_pi.mp hext i) hη (subset_univ S) h =
      cutoffStressSmoothSource (W := W) Qraw η hU hraw hη (hSp.trans hpU) h :=
  cutoffStressSmoothSource_eq_of_eqOn Qext Qraw η isOpen_univ hU
    (fun i ↦ contDiffOn_pi.mp hext i) hraw hη (subset_univ S) (hSp.trans hpU)
    ((affineFrameExtension_eqOn p Qraw).mono hSp) h

/-- The canonical response built with the full-source inverse's extended
coefficients is exactly the original completed physical response on every
admitted tensor source (`app:ch_response:eq:response-full-map`). -/
theorem fixedSmoothSolverAmbientExtension_extendedProjectedStress_eq (h : compactSmoothSources S) :
    fixedSmoothSolverAmbientExtension F Qext η isOpen_univ
      (fun i ↦ contDiffOn_pi.mp hext i) hη (subset_univ S) solver hsolver Ξ h =
      fixedSmoothSolverAmbientExtension F Qraw η hU hraw hη (hSp.trans hpU) solver hsolver Ξ h :=
  fixedSmoothSolverAmbientExtension_eq_of_eqOn F Qext Qraw η isOpen_univ hU
    (fun i ↦ contDiffOn_pi.mp hext i) hraw hη (subset_univ S) (hSp.trans hpU)
    ((affineFrameExtension_eqOn p Qraw).mono hSp) solver hsolver Ξ h

/-- Every tensor-test jet agrees for the actual coefficient extension and
physical stress frame. This identifies the full-source solver's response
with the canonical atom consumer without identifying extensions off the
admitted submodule (`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_tensorComponentResponse_extendedProjectedStress_eq
    {d : ℕ} (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) (hS : IsCompact S)
    (i j : Fin n) (u : supportedTests (e ⁻¹' S)) (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (tensorComponentResponse e S
      (fixedSmoothSolverAmbientExtension F Qext η isOpen_univ
        (fun i ↦ contDiffOn_pi.mp hext i) hη (subset_univ S) solver hsolver Ξ) i j u) x =
      iteratedFDeriv ℝ q (tensorComponentResponse e S
        (fixedSmoothSolverAmbientExtension F Qraw η hU hraw hη (hSp.trans hpU)
          solver hsolver Ξ) i j u) x := by
  obtain ⟨hr, him⟩ := tensorTestSource_quadratures_mem e hS i j u
  exact congrArg (fun g ↦ iteratedFDeriv ℝ q g x)
    (complexify_fixedSmoothSolverAmbientExtension_eq_of_eqOn F Qext Qraw η isOpen_univ hU
      (fun i ↦ contDiffOn_pi.mp hext i) hraw hη (subset_univ S) (hSp.trans hpU)
      ((affineFrameExtension_eqOn p Qraw).mono hSp) solver hsolver Ξ _ hr him)

end JanetCartan.CanonicalAtomRealization
