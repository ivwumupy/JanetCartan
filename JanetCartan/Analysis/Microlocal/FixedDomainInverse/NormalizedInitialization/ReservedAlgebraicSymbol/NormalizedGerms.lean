module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedAlgebraicSymbol.CoefficientAction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.NormalizedGerms

/-!
# Exact normalized germs of both selected algebraic symbols

The solver and its complete physical residual use the original source
product. On the output plateau that product equals the original multiplier
times the SAME conic inverse. The frequency normalization is exact before
any mixed derivative is taken (`energy-complete-residual`, `high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol

open ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.FinitePdo RegularSector.FiniteAssembly
open CharacteristicTransport.CompleteResidual

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Both literal selected algebraic symbols agree, as joint germs, with
their retained coefficient operations and the original normalized multiplier.
The entire source product is included in this equality; in particular all
its differentiated terms in the residual are accounted for
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_algebraic_normalized_eventuallyEq_selectedCoefficientAction
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (o : Fin 2)
    {threshold ρ : ℝ} (ht : f.radialThreshold ≤ threshold) (hρ : 0 < ρ)
    (Q : E → Coeff) (B : E → Mat) (v : E × E)
    (hv : physicalCoordinates (f.chart p).index v.1 ∈ ball x (4*f.physicalRadius))
    (hQ : ContDiffAt ℝ ∞ Q (physicalCoordinates (f.chart p).index v.1))
    (hG : ContDiffAt ℝ ∞ (coefficientConicBminus (f.chart p).radialSection
      (f.chart p).index (f.chart p).row (f.chart p).col (f.chart p).root)
      (Q (physicalCoordinates (f.chart p).index v.1), v.2)) :
    (fun w : E × E ↦ selectedAlgebraicSymbol f p (2*threshold) Q B o w.1 (ρ • w.2)) =ᶠ[𝓝 v]
      fun w : E × E ↦ ρ⁻¹ • (selectedEndpointMultiplier f p threshold (ρ • w.2) •
        selectedCoefficientAlgebraicAction f p o
          ((Q (physicalCoordinates (f.chart p).index w.1),
            (fderiv ℝ Q (physicalCoordinates (f.chart p).index w.1),
              B (physicalCoordinates (f.chart p).index w.1))), w.2)) := by
  fin_cases o
  · have hπ : Continuous (fun w : E × E ↦ physicalCoordinates (f.chart p).index w.1) :=
      (physicalCoordinates (f.chart p).index).continuous.comp continuous_fst
    filter_upwards [hπ.continuousAt.eventually (isOpen_ball.mem_nhds hv)] with w hw
    change directAlgebraicSymbol
      (conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold) w.1 (ρ • w.2) =
      ρ⁻¹ • (selectedEndpointMultiplier f p threshold (ρ • w.2) •
        coefficientConicBminus (f.chart p).radialSection (f.chart p).index
          (f.chart p).row (f.chart p).col (f.chart p).root
          (Q (physicalCoordinates (f.chart p).index w.1), w.2))
    rw [selected_algebraic_source_product_on_common_ball f p ht Q (ball_subset_closedBall hw),
      conicBminus_fieldRoot_eq_coefficientConicBminus,
      coefficientConicBminus_smul _ _ _ _ _ hρ.ne']
    exact smul_comm _ _ _
  · exact selected_algebraic_normalized_eventuallyEq_coefficient_action
      f p ht hρ Q B v hv hQ hG

/-- Either complete algebraic symbol is zero where its literal multiplier
is zero, before taking any source derivative (`high-amplitude`). -/
theorem selected_algebraic_symbol_zero_of_original_multiplier_zero
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (o : Fin 2)
    (threshold : ℝ) (Q : E → Coeff) (B : E → Mat) (y ξ : E)
    (hβ : selectedEndpointMultiplier f p threshold ξ = 0) :
    selectedAlgebraicSymbol f p (2*threshold) Q B o y ξ = 0 := by
  fin_cases o
  · change directAlgebraicSymbol
      (conicBminus (f.chart p).radialSection (f.chart p).index Q
        (fieldRoot (coordinateSplit (f.chart p).index) Q (f.chart p).root)
        (f.chart p).row (f.chart p).col)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask) (selectedEndpointMultiplier f p threshold) y ξ = 0
    simp only [directAlgebraicSymbol, hβ, mul_zero, zero_smul]
  · exact selected_algebraic_symbol_zero_of_multiplier_zero f p threshold Q B y ξ hβ

/-- Substitution of the actual smooth fields into either coefficient
operation preserves the retained local inverse germ. This is the local
smoothness used in the reserved mask Leibniz rule (`direct-envelope-profile`). -/
theorem contDiffAt_selectedCoefficientAlgebraicAction_of_fields
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (o : Fin 2)
    (Q : E → Coeff) (B : E → Mat) (v : E × E)
    (hQ : ContDiffAt ℝ ∞ Q (physicalCoordinates (f.chart p).index v.1))
    (hB : ContDiffAt ℝ ∞ B (physicalCoordinates (f.chart p).index v.1))
    (hG : ContDiffAt ℝ ∞ (coefficientConicBminus (f.chart p).radialSection
      (f.chart p).index (f.chart p).row (f.chart p).col (f.chart p).root)
      (Q (physicalCoordinates (f.chart p).index v.1), v.2)) :
    ContDiffAt ℝ ∞ (fun w : E × E ↦ selectedCoefficientAlgebraicAction f p o
      ((Q (physicalCoordinates (f.chart p).index w.1),
        (fderiv ℝ Q (physicalCoordinates (f.chart p).index w.1),
          B (physicalCoordinates (f.chart p).index w.1))), w.2)) v := by
  have hP : ContDiff ℝ ∞ (fun w : E × E ↦ physicalCoordinates (f.chart p).index w.1) :=
    (physicalCoordinates (f.chart p).index).contDiff.comp contDiff_fst
  apply (contDiffAt_selectedCoefficientAlgebraicAction f p o _ hG).comp v
  exact ((hQ.comp v hP.contDiffAt).prodMk
    (((hQ.fderiv_right (m := ∞) (by simp)).comp v hP.contDiffAt).prodMk
      (hB.comp v hP.contDiffAt))).prodMk contDiffAt_snd

end JanetCartan.FixedDomainInverse.ReservedAlgebraicSymbol
