module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Differential
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Homogeneity and normalized covectors

The degree-zero mixed Hessian obtained from the degree-one phase, as used in
`app:ch_response:thm:response-literal-transfer`. Homogeneity is required only
on the physical and normalized covector charts; no smoothness at the origin
is required.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace JanetCartan.ResponseTransfer

/-- Differentiating the primitive degree-one phase in physical position
preserves degree one (`app:ch_response:thm:response-literal-transfer`). -/
theorem partialDeriv_smul_covector {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {U : Set (Euclidean n)}
    (hU : IsOpen U) {x : Euclidean n} (hx : x ∈ U)
    {ρ : ℝ} {η : Euclidean n}
    (hh : ∀ z ∈ U, S z (ρ • η) = ρ * S z η)
    (hd : DifferentiableAt ℝ (fun z ↦ S z η) x) (i : Fin n) :
    partialDeriv (fun z ↦ S z (ρ • η)) x i =
      ρ * partialDeriv (fun z ↦ S z η) x i := by
  have he : (fun z ↦ S z (ρ • η)) =ᶠ[𝓝 x] (fun z ↦ ρ • S z η) :=
    eventuallyEq_of_mem (hU.mem_nhds hx) hh
  have hd' := hd.hasFDerivAt.const_smul ρ
  have hf := (hd'.congr_of_eventuallyEq he).fderiv
  exact congrArg (fun T : Euclidean n →L[ℝ] ℝ ↦ T (EuclideanSpace.single i 1)) hf

/-- The mixed phase matrix is homogeneous of degree zero, derived by
successively differentiating the degree-one phase identity. These are local
primitive differentiability hypotheses, not a mixed-matrix scaling assumption
(`app:ch_response:thm:response-literal-transfer`). -/
theorem mixedPhaseMatrix_smul_covector {n : ℕ}
    {S : Euclidean n → Euclidean n → ℝ} {U D : Set (Euclidean n)}
    (hU : IsOpen U) (hD : IsOpen D) {x η : Euclidean n}
    (hx : x ∈ U) (hη : η ∈ D) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hh : ∀ z ∈ U, ∀ ξ ∈ D, S z (ρ • ξ) = ρ * S z ξ)
    (hDx : ∀ ξ ∈ D, DifferentiableAt ℝ (fun z ↦ S z ξ) x)
    (hDξ : ∀ i : Fin n,
      DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η)
    (hDρξ : ∀ i : Fin n,
      DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) (ρ • η)) :
    FourierIntegral.mixedPhaseMatrix S x (ρ • η) =
      FourierIntegral.mixedPhaseMatrix S x η := by
  ext i j
  let f : Euclidean n → ℝ := fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i
  have he : (fun ξ ↦ f (ρ • ξ)) =ᶠ[𝓝 η] (fun ξ ↦ ρ • f ξ) := by
    apply eventuallyEq_of_mem (hD.mem_nhds hη)
    intro ξ hξ
    exact partialDeriv_smul_covector hU hx (fun z hz ↦ hh z hz ξ hξ) (hDx ξ hξ) i
  have hleft := (hDρξ i).hasFDerivAt.comp η ((hasFDerivAt_id η).const_smul ρ)
  have hright := (hDξ i).hasFDerivAt.const_smul ρ
  have heq := (hleft.congr_of_eventuallyEq he.symm).unique hright
  have hev := congrArg (fun T : Euclidean n →L[ℝ] ℝ ↦ T (EuclideanSpace.single j 1)) heq
  apply mul_left_cancel₀ hρ
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, f,
    FourierIntegral.mixedPhaseMatrix, partialDeriv] using hev

end JanetCartan.ResponseTransfer
