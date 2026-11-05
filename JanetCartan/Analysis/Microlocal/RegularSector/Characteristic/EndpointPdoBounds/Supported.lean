module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.OriginalBounds

/-!
# PDO budgets for the literal supported amplitude from the uniform constructor

This specialization retains the exact `collared` / `bufferedMatrix` /
`pencilAmplitudeFamily ... 1` expression. Its only analytic inputs are the
joint smoothness and normalized bounds returned by
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes` on the
same `J`. The parent still instantiates the physical and normalized support
inclusions for its finite family. No PDO or endpoint-operator bound is an
input. Source: `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets NormalComparison AmplitudeBound PdoRealization
open ResidualCoordinates AmplitudeBounds ConicAmplitude UniformAmplitudes FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "T" => EvolutionIntegral.SymbolBudgets.TwoTimePoint d
local notation "Z" => RootState (Euclidean d)
local notation "CT" => Characteristic.TwoTimePoint (Euclidean d)
local notation "QValue" => Fin (d + 1) → MetricTensor (d + 1)

/-- The actual upper endpoint supplies `GraphNormalAmplitudeBounds` and all
weighted low/high inputs for both forward and literal-adjoint integer gain.
The required fixed ORIGINAL low order is `2 * (d + 2) + 11`. Position
derivatives have reserve ten; therefore order-`n` gain uses the one fixed
original reserve `2 * (d + 2) + 11`, independently of `n`.

All constants precede the varying coefficients. The amplitude smoothness and
joint shell bounds are precisely the outputs of the published supported
constructor, applied to its literal `W₁`. Consumers:
`PdoRealization.directPDOSymbols_regularizations` at index two and
`PdoRealization.IntegerBounds` (`energy-complete-residual`). -/
theorem exists_supported_endpoint_pdo_budgets
    (i : Fin (d + 1)) {KQ Ω : Set E} (hKQ : IsCompact KQ)
    (hΩ : IsOpen Ω) (hKΩ : KQ ⊆ Ω)
    (x₀ : E) {r : ℝ} (hr : 0 < r)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x₀ r) KQ)
    (J : Set T) (hJ : IsCompact J) (amplitudeCost : ℕ → ℝ)
    (hcost : ∀ m, 0 < amplitudeCost m) {M : ℝ} (hM : 0 ≤ M)
    (χout χsource β : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) (hβs : ContDiff ℝ ∞ β)
    (hso : tsupport χout ⊆ closedBall x₀ r) (hcs : HasCompactSupport χsource)
    (Rbox : ℝ) (hoR : ∀ x ∈ tsupport χout, ‖x‖ ≤ Rbox)
    (hsR : ∀ x ∈ tsupport χsource, ‖x‖ ≤ Rbox)
    {Bβ Ccone : ℝ} (hBβ : 0 ≤ Bβ) (hCcone : 0 ≤ Ccone) (hβ : ∀ ζ, ‖β ζ‖ ≤ Bβ)
    (hcone : ∀ ζ ∈ tsupport β, |ζ 0| ≤ Ccone * ‖spatialPart ζ‖)
    (hcover : ∀ ζ ∈ tsupport β, ∃ R : ℝ, 1 ≤ R ∧ ∃ η : Euclidean d,
      spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R ∧
      MapsTo (diagonalPoint η) (closedBall x₀ r) J) :
    ∃ D : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧
      ∀ Q : E → QValue, ContDiffOn ℝ ∞ Q Ω → cNorm KQ (2 * (d + 2) + 11) Q ≤ M →
      ∀ B : E → MetricTensor (d + 1), cNorm KQ (2 * (d + 2) + 11) B ≤ M →
      ∀ (h : Z → ℝ) (Φ : Z × ℝ → Z) (chart : OpenPartialHomeomorph CT CT)
        (V : Set CT) (κ : ℝ → ℝ) (ℓ : Euclidean d →L[ℝ] ℝ) (angular : Euclidean d → ℝ)
        (rminor cminor : Fin (d + 1)) (σ : Z → ℝ),
      let F := collared ℓ 1 angular
        (bufferedMatrix V κ (pencilAmplitudeFamily i Q B h Φ chart rminor cminor σ 1))
      let W := curryCharacteristicMatrix F
      let c := fun x ζ ↦ β ζ • ((coefficient i Q x 0).map Complex.ofReal *
        W (x 0) (x 0) (spatialPart x) (spatialPart ζ))
      ContDiff ℝ ∞ F →
      (∀ m, BoundedTwoTimeOrderSeminorm 1 J m W ∧
        twoTimeOrderSeminorm 1 J m W ≤
          amplitudeCost m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B)) →
      GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) Rbox
        (D (2 * (d + 2) + 1) * (1 + M + M)) ∧
      (∀ ξ is, is.length ≤ 2 * (d + 2) + 1 → ∀ z,
        (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
          D (2 * (d + 2) + 1) * (1 + M + M)) ∧
      (∀ m ξ is, is.length ≤ m → ∀ z,
        (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
          D m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 10) B)) := by
  obtain ⟨D, hD, hb⟩ := exists_endpoint_originalCoefficient_constants i hKQ hΩ hKΩ
    x₀ hr hphysical J hJ amplitudeCost hcost hM χout χsource β ho hs hso hcs
    hBβ hCcone hβ hcone hcover
  refine ⟨D, hD, ?_⟩
  intro Q hQ hQlow B hBlow h Φ chart V κ ℓ angular rminor cminor σ F W c hF hnorm
  have hW : ContDiff ℝ ∞ (jointAmplitude W) := by
    rw [show W = curryCharacteristicMatrix F from rfl, jointAmplitude_curryCharacteristicMatrix]
    exact hF.comp evolutionToCharacteristicPoint.contDiff
  have hQ10 : cNorm KQ 10 Q ≤ M := (cNorm_mono_order (by omega)).trans hQlow
  have hB9 : cNorm KQ 9 B ≤ M := (cNorm_mono_order (by omega)).trans hBlow
  have hall := hb Q hQ hQ10 B hB9 W hW hnorm
  have hlow ξ is (hi : is.length ≤ 2 * (d + 2) + 1) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
        D (2 * (d + 2) + 1) * (1 + M + M) := by
    apply (hall (2 * (d + 2) + 1) ξ is hi z).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (hD _))
    have hQn : cNorm KQ (2 * (d + 2) + 1 + 10) Q ≤ M := by
      simpa only [Nat.add_assoc] using hQlow
    have hBn : cNorm KQ (2 * (d + 2) + 1 + 10) B ≤ M := by
      simpa only [Nat.add_assoc] using hBlow
    linarith
  refine ⟨⟨?_, ?_, ?_⟩, hlow, hall⟩
  · exact contDiff_endpointPDOCycleSymbol (hΩ.preimage (physicalCoordinates i).continuous)
      (fun x a ↦ (coefficient i Q x a).map Complex.ofReal) (contDiffOn_timeCoefficient i hQ)
      W hW β χout χsource hβs ho hs (hso.trans fun _ hx ↦ hKΩ (hphysical hx))
  · exact maskedPhysicalPDOCycleSymbol_supportedInCenteredBox χout χsource c hoR hsR
  · intro ξ is hi z
    have hl := hlow ξ is (by omega) z
    have hn := norm_nonneg (matrixAmplitudeCoordinateDerivList is
      (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z)
    nlinarith [norm_nonneg ξ]

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
