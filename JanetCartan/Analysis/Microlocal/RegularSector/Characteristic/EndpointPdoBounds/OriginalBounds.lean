module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Coefficients
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ConicConstruction

/-!
# Original-coefficient budgets for the actual supported endpoint

The input amplitude bounds below have exactly the joint normalized signature
published by `UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes`:
reserve ten in `Q`, nine in `B`, on the same compact `J`. The coefficient
multiplier is `ResidualCoordinates.coefficient`, with its bound proved in
`Coefficients`. Consequently only one high original coefficient quantity
occurs in the PDO position budgets. Source:
`paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets NormalComparison AmplitudeBound PdoRealization
open ResidualCoordinates AmplitudeBounds ConicAmplitude UniformAmplitudes
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "T" => EvolutionIntegral.SymbolBudgets.TwoTimePoint d
local notation "Z" => RootState (Euclidean d)
local notation "CT" => Characteristic.TwoTimePoint (Euclidean d)
local notation "QValue" => Fin (d + 1) → MetricTensor (d + 1)

/-- Original-coefficient, single-high position budgets for the endpoint.
The only amplitude estimates assumed are the exact normalized estimates
already produced by `exists_uniform_supported_conic_pencilAmplitudes` on
the SAME `J`. Fixed original low orders ten and nine fix the tame product
constant. The common high reserve is ten, independent of derivative order.
Consumer: the literal supported specialization below, followed by
`PdoRealization.IntegerBounds` (`energy-complete-residual`). -/
theorem exists_endpoint_originalCoefficient_constants
    (i : Fin (d + 1)) {KQ Ω : Set E} (hKQ : IsCompact KQ)
    (hΩ : IsOpen Ω) (hKΩ : KQ ⊆ Ω)
    (x₀ : E) {r : ℝ} (hr : 0 < r)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x₀ r) KQ)
    (J : Set T) (hJ : IsCompact J) (amplitudeCost : ℕ → ℝ)
    (hcost : ∀ m, 0 < amplitudeCost m) {M : ℝ} (_hM : 0 ≤ M)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hso : tsupport χout ⊆ closedBall x₀ r) (hcs : HasCompactSupport χsource)
    {Bβ Ccone : ℝ} (hBβ : 0 ≤ Bβ) (hCcone : 0 ≤ Ccone) (hβ : ∀ ζ, ‖β ζ‖ ≤ Bβ)
    (hcone : ∀ ζ ∈ tsupport β, |ζ 0| ≤ Ccone * ‖spatialPart ζ‖)
    (hcover : ∀ ζ ∈ tsupport β, ∃ R : ℝ, 1 ≤ R ∧ ∃ η : Euclidean d,
      spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R ∧
      MapsTo (diagonalPoint η) (closedBall x₀ r) J) :
    ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
      ∀ Q : E → QValue, ContDiffOn ℝ ∞ Q Ω → cNorm KQ 10 Q ≤ M →
      ∀ B : E → MetricTensor (d + 1), cNorm KQ 9 B ≤ M →
      ∀ W : TwoTimeAmplitude d (d + 1), ContDiff ℝ ∞ (jointAmplitude W) →
        (∀ m, BoundedTwoTimeOrderSeminorm 1 J m W ∧
          twoTimeOrderSeminorm 1 J m W ≤
            amplitudeCost m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B)) →
      ∀ m, ∀ ξ : E, ∀ is : List (Fin (2 * (d + 1))), is.length ≤ m → ∀ z : P,
        (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource
            (fun x ζ ↦ β ζ • ((coefficient i Q x 0).map Complex.ofReal *
              W (x 0) (x 0) (spatialPart x) (spatialPart ζ))) ξ) z‖ ≤
        C m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 10) B) := by
  obtain ⟨D, hD, hend⟩ := exists_endpoint_weighted_position_constants
    (q := d + 1) x₀ hr (timeCoefficientCost i 0 * M) (amplitudeCost 0 * (1 + M + M))
    J hJ χout χsource β ho hs hso hcs hBβ hCcone hβ hcone hcover
  let C := fun m ↦ 1 + D m * (1 + timeCoefficientCost i m + amplitudeCost m)
  have hC m : 1 ≤ C m := by
    have := hD m
    have := timeCoefficientCost_pos i m
    have := hcost m
    dsimp [C]
    have hp : 0 ≤ D m * (1 + timeCoefficientCost i m + amplitudeCost m) := by positivity
    linarith
  refine ⟨C, hC, ?_⟩
  intro Q hQ hQlow B hBlow W hW hnorm m ξ is hi z
  let U := (physicalCoordinates i) ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (physicalCoordinates i).continuous
  have hKU : closedBall x₀ r ⊆ U := fun _ hx ↦ hKΩ (hphysical hx)
  have hA := contDiffOn_timeCoefficient i hQ
  have hAb m := cNorm_timeCoefficient_le i (isCompact_closedBall x₀ r) hKQ hΩ hKΩ hphysical hQ m
  have hA0 : cNorm (closedBall x₀ r) 0 (fun x ↦ (coefficient i Q x 0).map Complex.ofReal) ≤
      timeCoefficientCost i 0 * M := by
    exact (hAb 0).trans (mul_le_mul_of_nonneg_left
      ((cNorm_mono_order (by omega : 0 ≤ 10)).trans hQlow) (timeCoefficientCost_pos i 0).le)
  have hW0 : twoTimeOrderSeminorm 1 J 0 W ≤ amplitudeCost 0 * (1 + M + M) := by
    exact (hnorm 0).2.trans (mul_le_mul_of_nonneg_left (by simpa only [zero_add] using (show
      1 + cNorm KQ 10 Q + cNorm KQ 9 B ≤ 1 + M + M by linarith))
      (hcost 0).le)
  have hb := hend U hU hKU (fun x a ↦ (coefficient i Q x a).map Complex.ofReal)
    hA hA0 W hW (hnorm 0).1 hW0 m (hnorm m).1 ξ is hi z
  have hq := cNorm_nonneg KQ (m + 10) Q
  have hb' := cNorm_nonneg KQ (m + 10) B
  have hcostA := (timeCoefficientCost_pos i m).le
  have hcostW := (hcost m).le
  have hAQ : cNorm (closedBall x₀ r) m (fun x ↦ (coefficient i Q x 0).map Complex.ofReal) ≤
      timeCoefficientCost i m * cNorm KQ (m + 10) Q :=
    (hAb m).trans (mul_le_mul_of_nonneg_left (cNorm_mono_order (by omega : m ≤ m + 10)) hcostA)
  have hWB : twoTimeOrderSeminorm 1 J m W ≤
      amplitudeCost m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 10) B) :=
    (hnorm m).2.trans (mul_le_mul_of_nonneg_left (by
      have hBm : cNorm KQ (m + 9) B ≤ cNorm KQ (m + 10) B := cNorm_mono_order (by omega)
      linarith) hcostW)
  apply hb.trans
  have hadd : 1 + cNorm (closedBall x₀ r) m (fun x ↦ (coefficient i Q x 0).map Complex.ofReal) +
      twoTimeOrderSeminorm 1 J m W ≤ (1 + timeCoefficientCost i m + amplitudeCost m) *
        (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 10) B) := by
    nlinarith [mul_nonneg hcostA hb']
  have h := mul_le_mul_of_nonneg_left hadd (hD m).le
  dsimp [C]
  nlinarith

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
