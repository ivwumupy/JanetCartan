module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSources

/-!
# Ambient completion of the supplied fixed smooth solver

`FixedDomainInverse.DirectSmooth` exports one linear smooth solver on its
original all-order local L² source space. We apply it to the actual cutoff
stress sources and use the existing `completedVariation` and `extendResponse`.
This instantiates the smooth-source domain of the ambient construction; no
regularity of a completed response is a premise.

The supplied solver already includes the original corrected-source operator.
It is neither replaced by a new inverse nor factored using an identity inverse.
Its selection on the initialized stationary source family, and its quantitative
response estimates, remain obligations of the corresponding producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.CorrectedAtoms
open PrimarySourceAdmission AmbientResponse FixedDomainInverse ResponseSourceExtension

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))

/-- Canonical tangent-normal completion of the SAME supplied smooth solver on
the actual tensor-source submodule. This is the chart map consumed by the
existing algebraic extension (`app:ch_response:eq:response-full-map`). -/
def fixedSmoothSolverChartResponse : compactSmoothSources S →ₗ[ℝ] (chart → Euclidean N) where
  toFun h x := completedVariation F
    (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h x
  map_add' h k := by
    funext x
    change completedVariation F
      (solver (cutoffStressSmoothSource Q η hU hQ hη hSU (h + k)))
      ((h : MetricField n) + k) x = _
    rw [map_add, map_add]
    exact completedVariation_add_apply F h k
      ((hsolver _).differentiable (by simp) x) ((hsolver _).differentiable (by simp) x)
  map_smul' a h := by
    funext x
    change completedVariation F
      (solver (cutoffStressSmoothSource Q η hU hQ hη hSU (a • h)))
      (a • (h : MetricField n)) x = _
    rw [map_smul, map_smul]
    exact completedVariation_smul_apply F h ((hsolver _).differentiable (by simp) x) a

/-- One whole-source response obtained from the original smooth solver by the
existing algebraic extension and the supplied output cutoff. The operator has
no scalar, carrier, frequency or accuracy parameter
(`app:ch_response:cor:current-atoms`). -/
def fixedSmoothSolverAmbientExtension (Ξ : OutputCutoff core chart) :
    MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  extendResponse Ξ (fixedSmoothSolverChartResponse F Q η hU hQ hη hSU solver hsolver)

/-- Exact identification on every admitted tensor source; both the supplied
solver and the source cutoff remain literal
(`app:ch_response:eq:response-full-map`). -/
theorem fixedSmoothSolverAmbientExtension_eq_cutoff (Ξ : OutputCutoff core chart)
    (h : compactSmoothSources S) :
    fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h =
      fun x ↦ Ξ.toFun x • completedVariation F
        (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h x :=
  extendResponse_eq_cutoff Ξ _ h _ rfl

/-- On the unchanged output core every jet is that of the original canonical
completion of the fixed solver (`app:ch_response:prop:response-graded`). -/
theorem fixedSmoothSolverAmbientExtension_eventuallyEq (Ξ : OutputCutoff core chart)
    (h : compactSmoothSources S) {x : Euclidean n} (hx : x ∈ core) :
    fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h =ᶠ[𝓝 x]
      completedVariation F (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h :=
  extendResponse_eventuallyEq Ξ _ h _ rfl hx

/-- The accepted fixed solver's all-order regularity supplies the ambient
regularity needed by the actual corrected atoms. The tensor and geometric
inputs supply every other regularity obligation
(`app:ch_response:prop:response-ambient`). -/
theorem contDiff_fixedSmoothSolverAmbientExtension (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
    (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
    (h : compactSmoothSources S) :
    ContDiff ℝ ∞
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h) :=
  contDiff_extendResponse Ξ _ h hchart _ rfl
    (contDiffOn_completedVariation hchart hF (hsolver _).contDiffOn
      h.property.1.contDiffOn hi hrank)

/-- The same physical output cutoff supports every response, including finite
synthesis by the actual sampling consumer
(`app:ch_response:cor:current-atoms`). -/
theorem hasCompactSupport_fixedSmoothSolverAmbientExtension (Ξ : OutputCutoff core chart)
    (h : MetricField n) : HasCompactSupport
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h) :=
  hasCompactSupport_extendResponse Ξ _ h

/-- The full strain of the extension is the strain of the literal completed
fixed solution on the output core. This retains the complete reduced residual
for subsequent inverse-Gram reconstruction
(`app:ch_response:eq:response-full-identity`). -/
theorem linearizedMetric_fixedSmoothSolverAmbientExtension_eq
    (Ξ : OutputCutoff core chart) (h : compactSmoothSources S)
    {x : Euclidean n} (hx : x ∈ core) :
    linearizedMetric F
      (fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ h) x =
      linearizedMetric F
        (completedVariation F (solver (cutoffStressSmoothSource Q η hU hQ hη hSU h)) h) x := by
  have he := (fixedSmoothSolverAmbientExtension_eventuallyEq
    F Q η hU hQ hη hSU solver hsolver Ξ h hx).fderiv_eq (𝕜 := ℝ)
  ext i j
  simp only [linearizedMetric, partialDeriv, he]

end JanetCartan.CorrectedAtoms
