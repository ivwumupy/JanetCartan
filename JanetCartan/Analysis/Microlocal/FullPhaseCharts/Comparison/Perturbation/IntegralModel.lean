module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.Kernel

/-!
# The double-integral model for the perturbed chart

Shared definitions for the comparison paragraph after
`app:ch_seed:eq:seed-quotient-integral`. They retain all spectators, both physical
endpoints, the carrier coordinate, and the direction. Equality with the literal
`modulationChart` is a separate calculus obligation, not part of these definitions.
The model's value estimate below is consumed by the full chart perturbation bound.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedSpace ℝ X := InnerProductSpace.toNormedSpace

/-- The joint phase point under the physical and covector integrals of
`app:ch_seed:prop:seed-phase-charts`. A data tuple is `(p, (x, x'), (z, η))`. -/
def phaseChartPoint (ζ : P × ℝ → E) (ε : ℝ)
    (q : P × (X × X) × (ℝ × E)) (r s : ℝ) : X × E :=
  (q.2.1.2 + r • (q.2.1.1 - q.2.1.2), ζ (q.1, q.2.2.1) + (s * ε) • q.2.2.2)

/-- Mixed-Hessian integrand for the two segment averages in
`app:ch_seed:prop:seed-phase-charts`. -/
def phaseChartKernel (S : X × E → ℝ) (ζ : P × ℝ → E) (ε : ℝ)
    (q : P × (X × X) × (ℝ × E)) (r s : ℝ) : X :=
  phaseMixedKernel S (phaseChartPoint ζ ε q r s) q.2.2.2

/-- Double-integral model for the physical modulation chart in
`app:ch_seed:prop:seed-phase-charts`. The literal quotient and gradient remain
those in `Comparison.Basic`; their equality to this expression requires proof. -/
def phaseChartKernelIntegral (S : X × E → ℝ) (ζ : P × ℝ → E) (ε : ℝ)
    (q : P × (X × X) × (ℝ × E)) : X :=
  ∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, phaseChartKernel S ζ ε q r s

/-- The value bound for the double-integral model uses only phase jets along
the two segments (`app:ch_seed:prop:seed-phase-charts`). In the application
`S` is the phase error, and `‖η‖` is bounded on the fixed direction set. -/
theorem norm_phaseChartKernelIntegral_le_cNorm_four
    {K : Set (X × E)} {S : X × E → ℝ} (hK : IsCompact K)
    (hS : ∀ q ∈ K, ContDiffAt ℝ 4 S q)
    (ζ : P × ℝ → E) (ε : ℝ) (q : P × (X × X) × (ℝ × E))
    (hmem : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      phaseChartPoint ζ ε q r s ∈ K) :
    ‖phaseChartKernelIntegral S ζ ε q‖ ≤ cNorm K 4 S * ‖q.2.2.2‖ := by
  unfold phaseChartKernelIntegral
  have bound (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ‖∫ s in (0 : ℝ)..1, phaseChartKernel S ζ ε q r s‖ ≤ cNorm K 4 S * ‖q.2.2.2‖ := by
    simpa [phaseChartKernel] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := cNorm K 4 S * ‖q.2.2.2‖)
      (fun s hs ↦ norm_phaseMixedKernel_apply_le_cNorm_four hK hS
        (hmem r hr s (by simpa using Ioc_subset_Icc_self hs)) q.2.2.2)
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := cNorm K 4 S * ‖q.2.2.2‖)
    (fun r hr ↦ bound r (by simpa using Ioc_subset_Icc_self hr))

end JanetCartan.FullPhaseCharts.Comparison
