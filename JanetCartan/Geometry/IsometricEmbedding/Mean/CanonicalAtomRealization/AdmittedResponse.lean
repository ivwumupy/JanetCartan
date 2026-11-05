module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.DirectFactors

/-!
# Agreement of the two ambient constructors on admitted sources

In `app:ch_response:eq:response-full-map` the ambient completion uses one
reduced solution and one output cutoff. The direct factors yield precisely
that solution on each admitted real source. Hence the complexifications
agree on both genuine quadratures and on every jet of the same tensor test.
No claim on sources outside the original compact smooth submodule is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open CorrectedAtoms FixedDomainInverse LocalSobolev PrimarySourceAdmission ResponseSourceExtension
open AmbientResponse ResponseSmoothParameters RetardedSobolev.Spaces

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)}
    (hU : IsOpen U) (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (Z solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hW : MeasurableSet W) (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (Pphys : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ] Lp (Euclidean n) 2 volume)
    (hZ : ∀ v : smoothSource W (Euclidean n), Z v =ᵐ[volume] SmallSupport.zeroExtend hW (Corr v))
    (hphysical : ∀ v : smoothSource W (Euclidean n), solver v =ᵐ[volume]
      Pphys (SmallSupport.zeroExtend hW (Corr v)))
    (Ξ : OutputCutoff core chart)

local notation "Tdirect" => directStressCorrectionFactor Q η hU hQ hη hSU Z
local notation "Sdirect" => directPhysicalSolveFactor Z solver hsolver hW Corr Pphys hZ hphysical

/-- The smoothness input of `WholeSource` is supplied by the SAME reduced
solver, for all original sources (`app:ch_response:prop:response-ambient`). -/
theorem contDiff_directPhysicalSolveFactor_correctedStressSource (h : compactSmoothSources S) :
    ContDiff ℝ ∞ (Sdirect (correctedStressSource Q η Tdirect h)) := by
  rw [directPhysicalSolveFactor_correctedStressSource]
  exact hsolver _

/-- The existing `ambientExtension` on the actual correction and solve factors,
using the supplied output cutoff (`app:ch_response:eq:response-full-map`). -/
abbrev directFactoredAmbientExtension : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  ambientExtension F Q η Tdirect Sdirect (compactSmoothSources S) Ξ
    (fun h y _ ↦ (contDiff_directPhysicalSolveFactor_correctedStressSource Q η hU hQ hη hSU
      Z solver hsolver hW Corr Pphys hZ hphysical h).differentiable (by simp) y)

local notation "Bdirect" => directFactoredAmbientExtension F Q η hU hQ hη hSU Z solver hsolver
  hW Corr Pphys hZ hphysical Ξ
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ

/-- The two existing ambient constructors agree as global fields on every
admitted tensor source: the completed reduced solution and the output cutoff
are identical (`app:ch_response:eq:response-full-map`). -/
theorem directFactoredAmbientExtension_eq_fixedSmoothSolver_on_source
    (h : compactSmoothSources S) : Bdirect h = Bfixed h := by
  unfold directFactoredAmbientExtension
  rw [ambientExtension_eq_cutoff, fixedSmoothSolverAmbientExtension_eq_cutoff]
  simp only [ambientResponse, directPhysicalSolveFactor_correctedStressSource]

/-- Agreement for both original quadratures of a complex source, without
identifying values of algebraic extensions off the admitted domain
(`app:ch_response:cor:current-atoms`). -/
theorem complexify_directFactoredAmbientExtension_eq_fixedSmoothSolver
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart H ∈ compactSmoothSources S)
    (hi : tensorFieldImagPart H ∈ compactSmoothSources S) :
    complexifyResponse Bdirect H = complexifyResponse Bfixed H := by
  have hr' := directFactoredAmbientExtension_eq_fixedSmoothSolver_on_source F Q η hU hQ hη hSU
    Z solver hsolver hW Corr Pphys hZ hphysical Ξ ⟨_, hr⟩
  have hi' := directFactoredAmbientExtension_eq_fixedSmoothSolver_on_source F Q η hU hQ hη hSU
    Z solver hsolver hW Corr Pphys hZ hphysical Ξ ⟨_, hi⟩
  change Bdirect (tensorFieldRealPart H) = Bfixed (tensorFieldRealPart H) at hr'
  change Bdirect (tensorFieldImagPart H) = Bfixed (tensorFieldImagPart H) at hi'
  simp only [complexifyResponse, LinearMap.coe_mk, AddHom.coe_mk, hr', hi']

/-- Every spatial jet of a supported tensor test uses the identical fixed
response. This transports the actual finite source bound to the constructor
used by `WholeSource` (`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_tensorComponentResponse_directFactored_eq_fixedSmoothSolver
    {d : ℕ} (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) (hS : IsCompact S)
    (i j : Fin n) (u : supportedTests (e ⁻¹' S)) (q : ℕ) (x : Euclidean n) :
    iteratedFDeriv ℝ q (tensorComponentResponse e S Bdirect i j u) x =
      iteratedFDeriv ℝ q (tensorComponentResponse e S Bfixed i j u) x := by
  obtain ⟨hr, hi⟩ := tensorTestSource_quadratures_mem e hS i j u
  exact congrArg (fun g ↦ iteratedFDeriv ℝ q g x)
    (complexify_directFactoredAmbientExtension_eq_fixedSmoothSolver F Q η hU hQ hη hSU
      Z solver hsolver hW Corr Pphys hZ hphysical Ξ _ hr hi)

end JanetCartan.CanonicalAtomRealization
