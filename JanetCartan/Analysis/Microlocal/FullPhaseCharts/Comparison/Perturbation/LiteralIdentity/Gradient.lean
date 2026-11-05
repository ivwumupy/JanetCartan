module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.IntegralCalculus
/-!
# Physical derivative of the literal phase quotient

The physical derivative under `app:ch_seed:eq:seed-quotient-integral` is the
mixed Hessian kernel. These local identities feed `modulationChart_eq_phaseChartKernelIntegral`
and hence the comparison in `app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.FullPhaseCharts.Comparison
variable {X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance literalGradientNormedSpaceX : NormedSpace ℝ X := InnerProductSpace.toNormedSpace
local instance literalGradientNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
set_option backward.isDefEq.respectTransparency false
omit [CompleteSpace X] in
private theorem inner_covectorGradient_eq_jointFDeriv {S : X × E → ℝ} {x : X} {ξ η : E}
    (hS : DifferentiableAt ℝ S (x, ξ)) :
    inner ℝ (gradient (fun z ↦ S (x,z)) ξ) η = fderiv ℝ S (x,ξ) (0,η) := by
  rw [inner_gradient_left]
  have hd := hS.hasFDerivAt.comp ξ ((hasFDerivAt_const x ξ).prodMk (hasFDerivAt_id ξ))
  dsimp only [Function.comp_def] at hd
  rw [hd.fderiv]
  rfl
omit [CompleteSpace E] in
private theorem fderiv_covectorIntegrand {S : X × E → ℝ} {x : X} {ξ η : E}
    (hS : ContDiffAt ℝ ∞ S (x, ξ)) :
    fderiv ℝ (fun y ↦ fderiv ℝ S (y,ξ) (0,η)) x =
      (InnerProductSpace.toDual ℝ X) (phaseMixedKernel S (x,ξ) η) := by
  have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ S) (x,ξ) := hS.fderiv_right (by simp)
  have hd := (h₁.differentiableAt (by simp)).hasFDerivAt
  have hc : HasFDerivAt (fun y : X ↦ fderiv ℝ S (y,ξ))
      ((fderiv ℝ (fderiv ℝ S) (x,ξ)).comp (ContinuousLinearMap.inl ℝ X E)) x :=
    hd.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const ξ x))
  have hh := hc.clm_apply (hasFDerivAt_const ((0 : X),η) x)
  rw [hh.fderiv]
  ext v
  change _ = inner ℝ (phaseMixedKernel S (x,ξ) η) v
  rw [inner_phaseMixedKernel]
  simp

variable [FiniteDimensional ℝ X]

/-- Differentiating the literal integral quotient in the physical variable gives
its mixed-Hessian integral (`app:ch_seed:eq:seed-quotient-integral`). Only an open
physical buffer and phase smoothness on `Ω` are required. This is the integrand
identity for `modulationChart_eq_phaseChartKernelIntegral`. -/
theorem gradient_phaseShiftQuotient_eq_integral_phaseMixedKernel
    {S : X × E → ℝ} {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (ξ η : E) (ε : ℝ)
    (hmem : ∀ y ∈ B, ∀ s ∈ W, (y, ξ + (s * ε) • η) ∈ Ω)
    {x : X} (hx : x ∈ B) :
    gradient (fun y ↦ phaseShiftQuotient (fun y z ↦ S (y,z)) y ξ η ε) x =
      ∫ s in (0 : ℝ)..1, phaseMixedKernel S (x, ξ + (s * ε) • η) η := by
  let F : X × ℝ → ℝ := fun a ↦ fderiv ℝ S (a.1, ξ + (a.2 * ε) • η) (0,η)
  have hF : ContDiffOn ℝ ∞ F (B ×ˢ W) := by
    intro a ha
    have h₁ : ContDiffAt ℝ ∞ (fderiv ℝ S) (a.1, ξ + (a.2 * ε) • η) :=
      (hS.contDiffAt (hΩ.mem_nhds (hmem a.1 ha.1 a.2 ha.2))).fderiv_right (by simp)
    exact ((h₁.comp a (by fun_prop)).clm_apply contDiffAt_const).contDiffWithinAt
  have hd := hasFDerivAt_unitIntervalParameterIntegral hB hW hIW hF hx
  have he : (fun y ↦ phaseShiftQuotient (fun y z ↦ S (y,z)) y ξ η ε) =ᶠ[𝓝 x]
      (fun y ↦ ∫ s in (0 : ℝ)..1, F (y,s)) := by
    filter_upwards [hB.mem_nhds hx] with y hy
    apply intervalIntegral.integral_congr
    intro s hs
    exact inner_covectorGradient_eq_jointFDeriv
      ((hS.contDiffAt (hΩ.mem_nhds (hmem y hy s (hIW (by simpa using hs))))).differentiableAt
        (by simp))
  change (InnerProductSpace.toDual ℝ X).symm (fderiv ℝ _ x) = _
  rw [he.fderiv_eq, hd.fderiv]
  refine ((InnerProductSpace.toDual ℝ X).symm.toLinearIsometry.intervalIntegral_comp_comm
    (fun s ↦ fderiv ℝ (fun y ↦ F (y,s)) x)).symm.trans ?_
  apply intervalIntegral.integral_congr
  intro s hs
  change (InnerProductSpace.toDual ℝ X).symm
    (fderiv ℝ (fun y ↦ fderiv ℝ S (y, ξ + (s * ε) • η) (0,η)) x) = _
  rw [fderiv_covectorIntegrand
    (hS.contDiffAt (hΩ.mem_nhds (hmem x hx s (hIW (by simpa using hs)))))]
  exact (InnerProductSpace.toDual ℝ X).symm_apply_apply _

end JanetCartan.FullPhaseCharts.Comparison
