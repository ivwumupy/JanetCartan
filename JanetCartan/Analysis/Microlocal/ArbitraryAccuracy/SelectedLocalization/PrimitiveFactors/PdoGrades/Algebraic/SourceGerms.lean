module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.Carriers
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SourceAgreement
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.AlgebraicSums

/-!
# The entire source product on the actual output plateau

The source factor is one on a neighborhood of every endpoint output point.
The equalities below are germs of the entire original product, and hence
account for all source derivatives before applying the physical operator.
The zeroth-order coefficient is retained. Consumer: the algebraic joint
profile in `CompleteFactor` (`energy-complete-residual`, `high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The complete source--inverse product agrees on the common output ball
with the same inverse times the original doubled multiplier. This equality
does not alter the symbol away from the plateau (`energy-complete-residual`). -/
theorem selected_algebraic_source_product_on_common_ball
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold) (Q : E → Coeff)
    {y : E} (hy : physicalCoordinates (f.chart p).index y ∈ closedBall x (4*f.physicalRadius))
    (ξ : E) :
    directAlgebraicSymbol
      (conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold) y ξ =
      selectedEndpointMultiplier f p threshold ξ •
        conicBminus (f.chart p).radialSection (f.chart p).index Q
          (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
          (f.chart p).row (f.chart p).col y ξ := by
  by_cases hβ : selectedEndpointMultiplier f p threshold ξ = 0
  · simp only [directAlgebraicSymbol, hβ, mul_zero, zero_smul]
  rw [directAlgebraicSymbol, f.conicSourceSymbol_eq_one p hy
    (selectedEndpointMultiplier_tsupport_subset f p ht (subset_tsupport _ hβ)), one_mul]

/-- Differentiating the original entire source product on the open common
ball gives the physical action of that same inverse product. All source
derivatives are discharged by local equality, and the full `B` remains
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_algebraic_physical_action_on_common_ball
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    (Q : E → Coeff) (B : E → Mat)
    {y : E} (hy : physicalCoordinates (f.chart p).index y ∈ ball x (4*f.physicalRadius))
    (ξ : E) :
    selectedAlgebraicSymbol f p (2*threshold) Q B 1 y ξ =
      physicalSymbolApply
        (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
        (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal)
        (fun y ξ ↦ selectedEndpointMultiplier f p threshold ξ •
          conicBminus (f.chart p).radialSection (f.chart p).index Q
            (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
            (f.chart p).row (f.chart p).col y ξ) y ξ := by
  let b := directAlgebraicSymbol
    (conicBminus (f.chart p).radialSection (f.chart p).index Q
      (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
      (f.chart p).row (f.chart p).col)
    (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
      (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold)
  have he : (fun z ↦ b z ξ) =ᶠ[𝓝 y] (fun z ↦ selectedEndpointMultiplier f p threshold ξ •
      conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col z ξ) := by
    filter_upwards [(physicalCoordinates (f.chart p).index).continuous.continuousAt.eventually
      (isOpen_ball.mem_nhds hy)] with z hz
    exact selected_algebraic_source_product_on_common_ball f p ht Q (ball_subset_closedBall hz) ξ
  change physicalSymbolApply
    (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
    (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal) b y ξ = _
  simp only [physicalSymbolApply, partialDeriv, he.fderiv_eq, he.eq_of_nhds]

/-- The preceding identity holds as a JOINT germ in position and full
covector, so it rewrites every mixed derivative of the literal selected
physical action (`app:ch_regular:eq:high-amplitude`). -/
theorem selected_algebraic_physical_action_eventuallyEq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    (Q : E → Coeff) (B : E → Mat)
    {v : E × E} (hv : physicalCoordinates (f.chart p).index v.1 ∈ ball x (4*f.physicalRadius)) :
    (fun w : E × E ↦ selectedAlgebraicSymbol f p (2*threshold) Q B 1 w.1 w.2) =ᶠ[𝓝 v]
      fun w : E × E ↦ physicalSymbolApply
        (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
        (fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal)
        (fun y ξ ↦ selectedEndpointMultiplier f p threshold ξ •
          conicBminus (f.chart p).radialSection (f.chart p).index Q
            (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
            (f.chart p).row (f.chart p).col y ξ) w.1 w.2 := by
  filter_upwards [((physicalCoordinates (f.chart p).index).continuous.comp continuous_fst).continuousAt.eventually
    (isOpen_ball.mem_nhds hv)] with w hw
  exact selected_algebraic_physical_action_on_common_ball f p ht Q B hw w.2

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
