module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.LiteralIdentity.Gradient
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Comparison.Perturbation.LiteralIdentity.Subtraction

/-!
# Literal modulation charts are mixed-Hessian integrals

The integral quotient `app:ch_seed:eq:seed-quotient-integral` and its physical
averaged gradient equal the checked double-integral model. The identity holds on
open data neighborhoods, so it transfers actual joint derivatives in the
comparison of `app:ch_seed:prop:seed-phase-charts`. Subtraction is justified by
local smoothness, which supplies the integrability of both segment averages.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance literalChartNormedSpaceX : NormedSpace ℝ X := InnerProductSpace.toNormedSpace
local instance literalChartNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

variable [FiniteDimensional ℝ X]

/-- The literal chart is the double mixed-Hessian integral in
`app:ch_seed:prop:seed-phase-charts`, including at zero shift. The physical box
is an open buffer for differentiation of the literal quotient. -/
theorem modulationChart_eq_phaseChartKernelIntegral
    {S : X × E → ℝ} (ζ : P × ℝ → E) (ε : ℝ) (p : P)
    (x x' : X) (z : ℝ) (η : E) {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hphys : ∀ r ∈ Icc (0 : ℝ) 1, x' + r • (x - x') ∈ B)
    (hshift : ∀ y ∈ B, ∀ s ∈ W, (y, ζ (p,z) + (s * ε) • η) ∈ Ω) :
    modulationChart S ζ ε p x x' (z,η) =
      phaseChartKernelIntegral S ζ ε (p,(x,x'),(z,η)) := by
  apply intervalIntegral.integral_congr
  intro r hr
  exact gradient_phaseShiftQuotient_eq_integral_phaseMixedKernel hB hΩ hW hIW hS
    (ζ (p,z)) η ε hshift (hphys r (by simpa using hr))

/-- The literal and model charts agree throughout the given data set, preserving
all spectators and both endpoints (`app:ch_seed:prop:seed-phase-charts`). -/
theorem modulationChart_eqOn_phaseChartKernelIntegral
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
    {U : Set (P × (X × X) × (ℝ × E))} {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hphys : ∀ q ∈ U, ∀ r ∈ Icc (0 : ℝ) 1, q.2.1.2 + r • (q.2.1.1 - q.2.1.2) ∈ B)
    (hshift : ∀ q ∈ U, ∀ y ∈ B, ∀ s ∈ W,
      (y, ζ (q.1,q.2.2.1) + (s * ε) • q.2.2.2) ∈ Ω) :
    EqOn (fun q ↦ modulationChart S ζ ε q.1 q.2.1.1 q.2.1.2 q.2.2)
      (phaseChartKernelIntegral S ζ ε) U := by
  intro q hq
  exact modulationChart_eq_phaseChartKernelIntegral ζ ε q.1 q.2.1.1 q.2.1.2
    q.2.2.1 q.2.2.2 hB hΩ hW hIW hS (hphys q hq) (hshift q hq)

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
/-- Equality on the open buffered data domain transfers the actual full joint
Fréchet derivative to the model (`app:ch_seed:prop:seed-phase-charts`). Composing
this neighborhood identity with data slices also transfers their derivatives. -/
theorem modulationChart_eventuallyEq_phaseChartKernelIntegral
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
    {U : Set (P × (X × X) × (ℝ × E))} {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hU : IsOpen U) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hphys : ∀ q ∈ U, ∀ r ∈ Icc (0 : ℝ) 1, q.2.1.2 + r • (q.2.1.1 - q.2.1.2) ∈ B)
    (hshift : ∀ q ∈ U, ∀ y ∈ B, ∀ s ∈ W,
      (y, ζ (q.1,q.2.2.1) + (s * ε) • q.2.2.2) ∈ Ω)
    {q : P × (X × X) × (ℝ × E)} (hq : q ∈ U) :
    (fun a ↦ modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) =ᶠ[𝓝 q]
      phaseChartKernelIntegral S ζ ε := by
  filter_upwards [hU.mem_nhds hq] with a ha
  exact modulationChart_eqOn_phaseChartKernelIntegral hB hΩ hW hIW hS hphys hshift ha

/-- The full joint derivative equality used to transfer the model's `C⁴` phase
error estimate to the literal chart (`app:ch_seed:prop:seed-phase-charts`). -/
theorem fderiv_modulationChart_eq_phaseChartKernelIntegral
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
    {U : Set (P × (X × X) × (ℝ × E))} {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hU : IsOpen U) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S Ω)
    (hphys : ∀ q ∈ U, ∀ r ∈ Icc (0 : ℝ) 1, q.2.1.2 + r • (q.2.1.1 - q.2.1.2) ∈ B)
    (hshift : ∀ q ∈ U, ∀ y ∈ B, ∀ s ∈ W,
      (y, ζ (q.1,q.2.2.1) + (s * ε) • q.2.2.2) ∈ Ω)
    {q : P × (X × X) × (ℝ × E)} (hq : q ∈ U) :
    fderiv ℝ (fun a ↦ modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2) q =
      fderiv ℝ (phaseChartKernelIntegral S ζ ε) q :=
  (modulationChart_eventuallyEq_phaseChartKernelIntegral hU hB hΩ hW hIW hS
    hphys hshift hq).fderiv_eq

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

/-- Differentiate the literal chart jointly in spectators, endpoints, carrier
coordinate and direction, under the two integrals. Every hypothesis concerns
phase/carrier smoothness or geometric containment on open boxes; the model is
identified by proof (`app:ch_seed:prop:seed-phase-charts`). -/
theorem hasFDerivAt_modulationChart
    {S : X × E → ℝ} {ζ : P × ℝ → E} {ε : ℝ}
    {U : Set (P × (X × X) × (ℝ × E))} {V : Set (P × ℝ)}
    {B : Set X} {Ω : Set (X × E)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hB : IsOpen B) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ S Ω) (hζ : ContDiffOn ℝ ∞ ζ V)
    (hproj : ∀ q ∈ U, (q.1,q.2.2.1) ∈ V)
    (hphys : ∀ q ∈ U, ∀ r ∈ W, q.2.1.2 + r • (q.2.1.1 - q.2.1.2) ∈ B)
    (hshift : ∀ q ∈ U, ∀ y ∈ B, ∀ s ∈ W,
      (y, ζ (q.1,q.2.2.1) + (s * ε) • q.2.2.2) ∈ Ω)
    {q : P × (X × X) × (ℝ × E)} (hq : q ∈ U) :
    HasFDerivAt (fun a ↦ modulationChart S ζ ε a.1 a.2.1.1 a.2.1.2 a.2.2)
      (∫ r in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        fderiv ℝ (fun a ↦ phaseChartKernel S ζ ε a r s) q) q := by
  have hm : ∀ a ∈ U, ∀ r ∈ W, ∀ s ∈ W, phaseChartPoint ζ ε a r s ∈ Ω :=
    fun a ha r hr s hs ↦ hshift a ha _ (hphys a ha r hr) s hs
  apply (hasFDerivAt_phaseChartKernelIntegral hU hV hΩ hW hIW hS hζ hproj hm hq).congr_of_eventuallyEq
  exact modulationChart_eventuallyEq_phaseChartKernelIntegral
      hU hB hΩ hW hIW hS (fun a ha r hr ↦ hphys a ha r (hIW hr)) hshift hq

end JanetCartan.FullPhaseCharts.Comparison
