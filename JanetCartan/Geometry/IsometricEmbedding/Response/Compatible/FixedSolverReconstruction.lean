module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverAtoms
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Complex

/-!
# The fixed smooth response is the literal complex ambient reconstruction

Apply the same real smooth solver to both original tensor admissions. Their
complex sum is the reduced field used by `completedVariationComplex`; the
existing algebraic extension is exactly its original output cutoff. On the
output core, all physical derivatives agree. This connects the reconstruction
estimates to the fixed response used by the corrected atoms without choosing
another solver, source, phase, or response.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CompatibleResponse
open CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse
open ResponseTransfer
variable {n N : ℕ}
variable (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hre : tensorFieldRealPart h ∈ compactSmoothSources S)
    (him : tensorFieldImagPart h ∈ compactSmoothSources S)

/-- The original reduced solver acts on both admitted quadratures, with the
full stress contraction and source cutoff unchanged
(`app:ch_response:eq:response-actual-solver-formula`). -/
def fixedSmoothSolverComplexSolution : Euclidean n → EuclideanSpace ℂ (Fin n) :=
  fun x ↦ euclideanComplexInclusion
    (solver (cutoffStressSmoothSource Q η hU hQ hη hSU ⟨_,hre⟩) x) +
      Complex.I • euclideanComplexInclusion
        (solver (cutoffStressSmoothSource Q η hU hQ hη hSU ⟨_,him⟩) x)

include hsolver in
/-- Smoothness of the same complex reduced solution follows from the supplied
fixed solver, before ambient completion
(`app:ch_response:prop:response-ambient`). -/
theorem contDiff_fixedSmoothSolverComplexSolution :
    ContDiff ℝ ∞ (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him) :=
  (euclideanComplexInclusion.contDiff.comp (hsolver _)).add
    ((euclideanComplexInclusion.contDiff.comp (hsolver _)).const_smul Complex.I)

variable (F : Euclidean n → Euclidean N) {core chart : Set (Euclidean n)}
    (Ξ : OutputCutoff core chart)

/-- The actual whole-source ambient extension is the original output cutoff
of the literal complex completion of its two reduced solutions. The identity
holds globally and retains both independent quadratures
(`app:ch_response:eq:response-full-map`,
`app:ch_response:eq:response-two-envelopes`). -/
theorem complexify_fixedSmoothSolverAmbientExtension_eq_completedVariation :
    complexifyResponse
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) h =
      fun x ↦ (Ξ.toFun x : ℂ) • completedVariationComplex F
        (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him) h x := by
  have hv := contDiff_fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver hsolver h hre him
  have hvre : (fun y ↦ WithLp.toLp 2 (fun j ↦
      (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him y j).re)) =
      solver (cutoffStressSmoothSource Q η hU hQ hη hSU ⟨_,hre⟩) := by
    ext y j
    simp [fixedSmoothSolverComplexSolution]
  have hvim : (fun y ↦ WithLp.toLp 2 (fun j ↦
      (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him y j).im)) =
      solver (cutoffStressSmoothSource Q η hU hQ hη hSU ⟨_,him⟩) := by
    ext y j
    simp [fixedSmoothSolverComplexSolution]
  have hreal := fixedSmoothSolverAmbientExtension_eq_cutoff
    F Q η hU hQ hη hSU solver hsolver Ξ ⟨_,hre⟩
  have himag := fixedSmoothSolverAmbientExtension_eq_cutoff
    F Q η hU hQ hη hSU solver hsolver Ξ ⟨_,him⟩
  ext x j
  apply Complex.ext
  · rw [complexifyResponse_re]
    change (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
      (⟨_,hre⟩ : compactSmoothSources S) x) j = _
    rw [hreal]
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [completedVariationComplex_re F h (hv.differentiable (by simp) x) j, hvre]
    rfl
  · rw [complexifyResponse_im]
    change (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
      (⟨_,him⟩ : compactSmoothSources S) x) j = _
    rw [himag]
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [completedVariationComplex_im F h (hv.differentiable (by simp) x) j, hvim]
    rfl

/-- On the original output core the same fixed response agrees locally with
its literal complex reconstruction, so no derivative of the output cutoff
enters the observed physical derivative (`app:ch_response:eq:response-two-envelopes`). -/
theorem complexify_fixedSmoothSolverAmbientExtension_eventuallyEq_completedVariation
    {x : Euclidean n} (hx : x ∈ core) :
    complexifyResponse
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) h =ᶠ[𝓝 x]
      completedVariationComplex F
        (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him) h := by
  rw [complexify_fixedSmoothSolverAmbientExtension_eq_completedVariation
    Q η hU hQ hη hSU solver hsolver h hre him F Ξ]
  filter_upwards [isOpen_interior.mem_nhds (Ξ.plateau hx)] with y hy
  have he : Ξ.toFun y = 1 := (interior_subset : interior {x | Ξ.toFun x = 1} ⊆ {x | Ξ.toFun x = 1}) hy
  simp only [he, Complex.ofReal_one, one_smul]

/-- Every jet on the output core belongs to the same fixed response and the
same reduced solution (`app:ch_response:prop:response-graded`). -/
theorem iteratedFDeriv_complexify_fixedSmoothSolverAmbientExtension_eq_completedVariation
    {x : Euclidean n} (hx : x ∈ core) (k : ℕ) :
    iteratedFDeriv ℝ k (complexifyResponse
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ) h) x =
      iteratedFDeriv ℝ k (completedVariationComplex F
        (fixedSmoothSolverComplexSolution Q η hU hQ hη hSU solver h hre him) h) x :=
  ((complexify_fixedSmoothSolverAmbientExtension_eventuallyEq_completedVariation
    Q η hU hQ hη hSU solver hsolver h hre him F Ξ hx).iteratedFDeriv ℝ k).self_of_nhds

end JanetCartan.CompatibleResponse
