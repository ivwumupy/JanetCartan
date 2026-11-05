module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutReconstruction
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ExtendedSourceAgreement

/-! # Admitted comparison with the proof-only localization
The original whole-space response is not recut. Comparison is on the actual
compact tensor submodule and the same supported smooth solver. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalComparisonResponse
open PhysicalInitialization PhysicalSeed ResponseSourceExtension CorrectedAtoms FixedDomainInverse
  PrimarySourceAdmission OriginalAmbientResponse CanonicalAtomRealization

/-- A proof-only output cutoff, equal to one on the *whole* protected source
including the support of the output, not merely on the smaller defect core. -/
def proofCutoff {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    OutputCutoff (OriginalProtected.Xsrc hn a) (ball 0 (OriginalBoundary.b hn)) := by
  let hex := CompatibleResponse.exists_compact_family_cutoff (OriginalProtected.source_domains hn a).1
    isOpen_ball (closedBall_subset_ball (OriginalProtected.sourceRadius_lt_b hn))
  exact ⟨hex.choose,hex.choose_spec.1,hex.choose_spec.2.2.1,hex.choose_spec.2.2.2.1,
    hex.choose_spec.2.2.2.2⟩

/-- Agreement of the same admitted full tensor under both the proof-only
cutoff and the frame change on its compact support. This is NOT a statement
about the arbitrary algebraic extensions off the admitted submodule. -/
theorem admitted_eq {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Qext Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S Ue U W core chart : Set (Euclidean n)} (hUe : IsOpen Ue) (hU : IsOpen U)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Qext x i) Ue) (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSe : S ⊆ Ue) (hS : S ⊆ U) (hframes : EqOn Qext Q S)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hsol : ∀ v, tsupport (solver v) ⊆ core) (hSc : S ⊆ core) (t : compactSmoothSources S) :
    uncutAmbientExtension F Qext η hUe he hη hSe solver hsolver t =
      fixedSmoothSolverAmbientExtension F Q η hU hQ hη hS solver hsolver Ξ t :=
  (OriginalUncutReconstruction.uncutAmbientExtension_eq_fixedSmoothSolverAmbientExtension_of_native_support
    F Qext η hUe he hη hSe solver hsolver Ξ hsol hSc t).trans
    (fixedSmoothSolverAmbientExtension_eq_of_eqOn F Qext Q η hUe hU he hQ hη hSe hS hframes solver hsolver Ξ t)

/-- A single equality on the admitted real submodule gives the two actual
complex responses, including every physical derivative of them. -/
theorem complex_agreement {n N : ℕ} {S : Set (Euclidean n)}
    (B B' : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (he : ∀ h : compactSmoothSources S, B h = B' h)
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hr : tensorFieldRealPart h ∈ compactSmoothSources S) (hi : tensorFieldImagPart h ∈ compactSmoothSources S) :
    complexifyResponse B h = complexifyResponse B' h := by
  funext x
  ext j
  simp only [complexifyResponse, LinearMap.coe_mk, AddHom.coe_mk]
  rw [he ⟨_,hr⟩,he ⟨_,hi⟩]

end JanetCartan.PhysicalPrimary.OriginalComparisonResponse
end
