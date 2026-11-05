module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.Differential
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Parameter phase trade on a buffered chart

Instantiates the segment calculus for the parameter identity in
`app:ch_response:thm:response-literal-transfer` using only smoothness on an open
convex normalized chart and positive homogeneity. No smoothness at the zero
covector is required. The geometry producer must supply the chart and its two
endpoint inclusions.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer

private theorem homogeneousPhase_differentiableAt_smul {n : ℕ}
    {f : Euclidean n → ℝ} (hhom : PosHomogeneousOne f)
    {η : Euclidean n} (hne : η ≠ 0) (hf : DifferentiableAt ℝ f η)
    {ρ : ℝ} (hρ : 0 < ρ) : DifferentiableAt ℝ f (ρ • η) := by
  have he : (fun ξ ↦ f (ρ • ξ)) =ᶠ[𝓝 η] (fun ξ ↦ ρ • f ξ) :=
    (eventually_ne_nhds hne).mono fun ξ hξ ↦ hhom ρ hρ ξ hξ
  have hd := (hf.const_smul ρ).congr_of_eventuallyEq he
  exact (ContinuousLinearEquiv.smulLeft (Units.mk0 ρ hρ.ne') :
    Euclidean n ≃L[ℝ] Euclidean n).comp_right_differentiableAt_iff.mp hd

/-- The exact parameter phase trade from a smooth buffered convex chart away
from zero (`app:ch_response:thm:response-literal-transfer`). Homogeneity supplies
physical-covector differentiability; the chart supplies every segment hypothesis
of `hasFDerivAt_phaseIncrement_parameter`. Frequency and the operator phase stay
fixed while the carrier parameter varies. -/
theorem hasFDerivAt_phaseIncrement_parameter_of_chart {n : ℕ}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {S : Euclidean n → Euclidean n → ℝ} {ζ : P → Euclidean n}
    {D : Set (Euclidean n)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hD0 : (0 : Euclidean n) ∉ D) {x : Euclidean n}
    (hS : ContDiffOn ℝ ∞ (S x) D) (hhom : PosHomogeneousOne (S x))
    {c : P} (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : Euclidean n} (hend : ζ c + ρ⁻¹ • δ ∈ D) :
    HasFDerivAt (fun d ↦ phaseIncrement S (ζ d) ρ x δ)
      (parameterPhaseCoefficient S ζ x (ρ⁻¹ • δ) c δ) c := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ζ c + t • (ρ⁻¹ • δ) ∈ D :=
    fun _ ht ↦ hcD.add_smul_mem hζD hend ht
  have hne : ∀ η ∈ D, η ≠ (0 : Euclidean n) := by
    intro η hη he
    exact hD0 (he ▸ hη)
  have hd : ∀ η ∈ D, DifferentiableAt ℝ (S x) η :=
    fun η hη ↦ (hS.contDiffAt (hD.mem_nhds hη)).differentiableAt (by simp)
  have hdS : ContDiffOn ℝ ∞ (fderiv ℝ (S x)) D :=
    hS.fderiv_of_isOpen hD (by simp)
  have hddS : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (S x))) D :=
    hdS.fderiv_of_isOpen hD (by simp)
  apply hasFDerivAt_phaseIncrement_parameter S ζ c (fderiv ℝ ζ c) ρ hρ x δ
    hζ.hasFDerivAt hhom (fun t ht ↦ hne _ (hseg t ht)) (fun t ht ↦ hd _ (hseg t ht))
  · have he : ρ • ζ c + δ = ρ • (ζ c + ρ⁻¹ • δ) := by
      simp [smul_add, smul_smul, hρ.ne']
    exact ⟨he ▸ homogeneousPhase_differentiableAt_smul hhom (hne _ hend) (hd _ hend) hρ,
      homogeneousPhase_differentiableAt_smul hhom (hne _ hζD) (hd _ hζD) hρ⟩
  · intro t ht
    exact (hdS.contDiffAt (hD.mem_nhds (hseg t ht))).differentiableAt (by simp)
  · intro t ht
    exact ((hddS.contDiffAt (hD.mem_nhds (hseg t ht))).continuousAt.comp
      (f := fun s : ℝ ↦ ζ c + s • (ρ⁻¹ • δ))
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const))).continuousWithinAt

end JanetCartan.ResponseTransfer
