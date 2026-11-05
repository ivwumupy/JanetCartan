module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolver

/-!
# The uncut ambient completion of the same full physical inverse

The vector solver is the original full Neumann inverse followed by its fixed
chi3 SOURCE cutoff and globally uncut paired solver. The parent specializes
this algebraic construction to the actual original solver getter. Unlike the
chart-cutoff adapter, no output cutoff is applied here. The original chi2
belongs only to the incoming atomic tensor source; it is not applied a second
time. Consumers are `fullPrimaryResponse` and its derivative amplitude on the
entire original comparison set (`app:ch_response:eq:response-full-map`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalAmbientResponse
open CorrectedAtoms PrimarySourceAdmission AmbientResponse FixedDomainInverse

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))

/-- Evaluate the existing full-space chart completion at every physical point.
There is no output mask, restriction of values or new response selection. -/
def uncutTensorResponse : compactSmoothSources S →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  (LinearMap.pi fun x : Euclidean n ↦
    (LinearMap.proj (⟨x,mem_univ x⟩ : (univ : Set (Euclidean n))) :
      (↥(univ : Set (Euclidean n)) → Euclidean N) →ₗ[ℝ] Euclidean N)).comp
    (fixedSmoothSolverChartResponse (chart := univ) F Q η hU hQ hη hSU solver hsolver)

/-- The single whole-function-space algebraic extension is made before any
atom, scalar or oscillation rate. It has no hidden source or output cutoff. -/
def uncutAmbientExtension : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  (uncutTensorResponse F Q η hU hQ hη hSU solver hsolver).exists_extend.choose

/-- Every admitted tensor source gives exactly the globally uncut canonical
completion of the SAME vector solution, not merely agreement on an output core. -/
theorem uncutAmbientExtension_apply (h : compactSmoothSources S) :
    uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h =
      completedVariation F (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h := by
  have he := DFunLike.congr_fun
    (uncutTensorResponse F Q η hU hQ hη hSU solver hsolver).exists_extend.choose_spec h
  exact he

/-- Smoothness on any actual immersion/full-normal-rank comparison chart.
No compact support or smoothness outside that geometric chart is asserted. -/
theorem uncutAmbientExtension_contDiffOn {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    (hi : IsImmersionOn F Ω) (hrank : HasFullNormalRankOn F Ω)
    (h : compactSmoothSources S) :
    ContDiffOn ℝ ∞ (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h) Ω := by
  rw [uncutAmbientExtension_apply]
  exact contDiffOn_completedVariation hΩ hF (hsolver _).contDiffOn
    h.property.1.contDiffOn hi hrank

/-- The full strain identity sees the literal uncut completion everywhere;
no plateau or identity of independently selected masks is used. -/
theorem uncutAmbientExtension_linearizedMetric (h : compactSmoothSources S) :
    linearizedMetric F (uncutAmbientExtension F Q η hU hQ hη hSU solver hsolver h) =
      linearizedMetric F
        (completedVariation F (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h) := by
  rw [uncutAmbientExtension_apply]

end JanetCartan.PhysicalPrimary.OriginalAmbientResponse
