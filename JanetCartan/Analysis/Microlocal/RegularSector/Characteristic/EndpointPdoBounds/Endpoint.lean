module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.MaskJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.TameProduct

/-!
# Full-frequency weighted jets of the literal upper-endpoint PDO

The normalized two-time amplitude budgets imply every weighted position
derivative estimate for `β(ξ) A_t(x) W₁(t,t,y,η)`, with both masks and the
exact physical/cycle covector conversion. The only geometric input is an
explicit inclusion of the normalized diagonal into the SAME amplitude
buffer. This is the endpoint in `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets NormalComparison AmplitudeBound PdoRealization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "T" => EvolutionIntegral.SymbolBudgets.TwoTimePoint d
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The exact order-minus-one position budgets from the original joint
normalized amplitude bounds. The fixed masks and constants precede `A` and
`W₁`; the high physical coefficient and high amplitude norms are ADDITIVE.
The cone is required only on the original multiplier support. Consumers:
`PdoRealization.directPDOSymbols_regularizations` at index two, and the
forward/literal-adjoint gain estimates in `PdoRealization.IntegerBounds`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_endpoint_weighted_position_constants
    (x₀ : E) {r : ℝ} (hr : 0 < r) (MA MW : ℝ)
    (J : Set T) (hJ : IsCompact J)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hso : tsupport χout ⊆ closedBall x₀ r) (hcs : HasCompactSupport χsource)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hβ : ∀ ζ, ‖β ζ‖ ≤ B)
    (hcone : ∀ ζ ∈ tsupport β, |ζ 0| ≤ C * ‖spatialPart ζ‖)
    (hcover : ∀ ζ ∈ tsupport β, ∃ R : ℝ, 1 ≤ R ∧ ∃ η : Euclidean d,
      spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R ∧
      MapsTo (diagonalPoint η) (closedBall x₀ r) J) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ U : Set E, IsOpen U → closedBall x₀ r ⊆ U →
      ∀ A : E → Fin (d + 1) → Mat,
        ContDiffOn ℝ ∞ (fun x ↦ A x 0) U → cNorm (closedBall x₀ r) 0 (fun x ↦ A x 0) ≤ MA →
      ∀ W : TwoTimeAmplitude d q, ContDiff ℝ ∞ (jointAmplitude W) →
        BoundedTwoTimeOrderSeminorm 1 J 0 W → twoTimeOrderSeminorm 1 J 0 W ≤ MW →
      ∀ m, BoundedTwoTimeOrderSeminorm 1 J m W →
      ∀ ξ : E, ∀ is : List (Fin (2 * (d + 1))), is.length ≤ m → ∀ z : P,
        (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource
            (fun x ζ ↦ β ζ • (A x 0 * W (x 0) (x 0) (spatialPart x) (spatialPart ζ))) ξ) z‖ ≤
        D m * (1 + cNorm (closedBall x₀ r) m (fun x ↦ A x 0) + twoTimeOrderSeminorm 1 J m W) := by
  obtain ⟨Pcost, hPcost, hprod⟩ := exists_diagonal_matrixProduct_cNorm_bounds (q := q) x₀ hr MA MW
  choose Mcost hMcost hmask using fun m ↦ exists_masked_position_derivative_constant
    (q := q) (isCompact_closedBall x₀ r) χout χsource ho hs hso hcs m
  let D := fun m ↦ 1 + (2 * (C + 1)) * Mcost m * B * Pcost m
  have hD m : 0 < D m := by
    dsimp [D]
    have := hMcost m
    have := hPcost m
    positivity
  refine ⟨D, hD, ?_⟩
  intro U hU hKU A hA hA0 W hW hW0 hMW m hWm ξ is hi z
  let ζ := (2 * Real.pi) • ξ
  let f : E → Mat := fun x ↦ A x 0 * W (x 0) (x 0) (spatialPart x) (spatialPart ζ)
  have hw : ContDiff ℝ ∞ (fun x : E ↦ W (x 0) (x 0) (spatialPart x) (spatialPart ζ)) := by
    have hp : ContDiff ℝ ∞ (diagonalPoint (spatialPart ζ)) :=
      diagonalLinear.contDiff.add contDiff_const
    simpa only [Function.comp_def, diagonalPoint_eq, jointAmplitude] using hW.comp hp
  have hf : ContDiffOn ℝ ∞ f U := hA.mul hw.contDiffOn
  have hm := hmask m U hU hKU (fun x ↦ β ζ • f x) (hf.const_smul _) is hi z
  rw [cNorm_complex_smul_on_open hU hKU hf] at hm
  let H := 1 + cNorm (closedBall x₀ r) m (fun x ↦ A x 0) + twoTimeOrderSeminorm 1 J m W
  have hH : 0 ≤ H := by
    have := cNorm_nonneg (closedBall x₀ r) m (fun x ↦ A x 0)
    have := twoTimeOrderSeminorm_nonneg 1 J m W
    dsimp [H]
    positivity
  have hc := cNorm_nonneg (closedBall x₀ r) m f
  change (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
    (fun p ↦ (χout (splitPhysicalPositions p).1 * χsource (splitPhysicalPositions p).2) •
      (β ζ • f (splitPhysicalPositions p).1)) z‖ ≤ D m * H
  by_cases hz : β ζ = 0
  · have hm0 : ‖matrixAmplitudeCoordinateDerivList is
        (fun p ↦ (χout (splitPhysicalPositions p).1 * χsource (splitPhysicalPositions p).2) •
          (β ζ • f (splitPhysicalPositions p).1)) z‖ ≤ 0 := by
      simpa only [hz, norm_zero, zero_mul, mul_zero] using hm
    have hn := norm_nonneg (matrixAmplitudeCoordinateDerivList is
      (fun p ↦ (χout (splitPhysicalPositions p).1 * χsource (splitPhysicalPositions p).2) •
        (β ζ • f (splitPhysicalPositions p).1)) z)
    have he := le_antisymm hm0 hn
    rw [he, mul_zero]
    exact mul_nonneg (hD m).le hH
  · have hζ := subset_tsupport β hz
    obtain ⟨R, hR, η, hη, hnorm, hmap⟩ := hcover ζ hζ
    have hp := hprod U hU hKU (fun x ↦ A x 0) hA hA0 J hJ W hW hW0 hMW R hR η hmap m hWm
    have he : (fun x : E ↦ R • (A x 0 * W (x 0) (x 0) (spatialPart x) (R • η))) = R • f := by
      funext x
      simp only [Pi.smul_apply, f, hη]
    rw [he, cNorm_smul_of_contDiffAt R (fun x hx ↦
      (hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp)),
      Real.norm_of_nonneg (zero_le_one.trans hR)] at hp
    have hweight := cycle_bracket_le_shell_of_cone hC hR ξ (hcone ζ hζ) hnorm
    have hmc : 0 ≤ Mcost m := (hMcost m).le
    calc
      _ ≤ (1 + ‖ξ‖) * (Mcost m * (‖β ζ‖ * cNorm (closedBall x₀ r) m f)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ ((2 * (C + 1)) * R) * (Mcost m * (B * cNorm (closedBall x₀ r) m f)) := by
        exact mul_le_mul hweight (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hβ ζ) hc) hmc) (by positivity) (by positivity)
      _ = ((2 * (C + 1)) * Mcost m * B) * (R * cNorm (closedBall x₀ r) m f) := by ring
      _ ≤ ((2 * (C + 1)) * Mcost m * B) * (Pcost m * H) :=
        mul_le_mul_of_nonneg_left hp (by have := (hMcost m).le; positivity)
      _ ≤ D m * H := by dsimp [D]; nlinarith

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
