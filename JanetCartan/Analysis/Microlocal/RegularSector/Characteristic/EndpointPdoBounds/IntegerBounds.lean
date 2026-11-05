module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Supported

/-!
# Forward and literal-adjoint gain for the actual endpoint PDO

Apply the existing matrix operator estimates to the position budgets proved
from the normalized amplitude. The operator and its literal Hilbert adjoint
use the SAME masks and symbol. No operator or PDO derivative budget is an
input. `Supported` specializes these identical primitive amplitude inputs to
the literal supported `W₁` constructed by `UniformAmplitudes`.
Source: `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets AmplitudeBound PdoRealization
open ResidualCoordinates FourierIntegral Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "TPoint" => EvolutionIntegral.SymbolBudgets.TwoTimePoint d
local notation "QValue" => Fin (d + 1) → MetricTensor (d + 1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin (d + 1))) 2 (volume : Measure E)

/-- Uniform gain-one estimates for the SAME endpoint and its literal adjoint,
deduced from the original normalized amplitude budgets. All constants precede
the varying `Q,B,W₁`. The fixed original low order and high reserve are both
`2 * (d + 2) + 11`; only the additive original high coefficient norms occur.
Consumer: the complete residual's forward and adjoint inputs to the fixed
inverse and arbitrary-accuracy constructions (`energy-complete-residual`). -/
theorem exists_endpoint_integer_gain_constants
    (i : Fin (d + 1)) {KQ Ω : Set E} (hKQ : IsCompact KQ)
    (hΩ : IsOpen Ω) (hKΩ : KQ ⊆ Ω)
    (x₀ : E) {r : ℝ} (hr : 0 < r)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x₀ r) KQ)
    (J : Set TPoint) (hJ : IsCompact J) (amplitudeCost : ℕ → ℝ)
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
    ∃ D G : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧ (∀ n, 0 ≤ G n) ∧
      ∀ Q : E → QValue, ContDiffOn ℝ ∞ Q Ω → cNorm KQ (2 * (d + 2) + 11) Q ≤ M →
      ∀ B : E → MetricTensor (d + 1), cNorm KQ (2 * (d + 2) + 11) B ≤ M →
      ∀ W : TwoTimeAmplitude d (d + 1), ContDiff ℝ ∞ (jointAmplitude W) →
        (∀ m, BoundedTwoTimeOrderSeminorm 1 J m W ∧
          twoTimeOrderSeminorm 1 J m W ≤
            amplitudeCost m * (1 + cNorm KQ (m + 10) Q + cNorm KQ (m + 9) B)) →
      ∀ n : ℕ, ∀ f : H, MemVectorFourierSobolev (n : ℝ) f →
      let T := maskedPhysicalPDO χout χsource
        (fun x ζ ↦ β ζ • ((coefficient i Q x 0).map Complex.ofReal *
          W (x 0) (x 0) (spatialPart x) (spatialPart ζ)))
      let high := D (2 * (d + 2) + (n + 1)) *
        (1 + cNorm KQ (n + (2 * (d + 2) + 11)) Q + cNorm KQ (n + (2 * (d + 2) + 11)) B)
      (MemVectorFourierSobolev ((n : ℝ) + 1) (T f) ∧
        vectorFourierSobolevNorm ((n : ℝ) + 1) (T f) ≤
          ((d + 1 : ℝ) * (d + 1) * G n) *
            (vectorFourierSobolevNorm (n : ℝ) f + high * ‖f‖)) ∧
      (MemVectorFourierSobolev ((n : ℝ) + 1) (T.adjoint f) ∧
        vectorFourierSobolevNorm ((n : ℝ) + 1) (T.adjoint f) ≤
          ((d + 1 : ℝ) * (d + 1) * G n) *
            (vectorFourierSobolevNorm (n : ℝ) f + high * ‖f‖)) := by
  obtain ⟨D, hD, hb⟩ := exists_endpoint_originalCoefficient_constants i hKQ hΩ hKΩ
    x₀ hr hphysical J hJ amplitudeCost hcost hM χout χsource β ho hs hso hcs
    hBβ hCcone hβ hcone hcover
  let low := D (2 * (d + 2) + 1) * (1 + M + M)
  choose Cf hCf hforward using fun n ↦
    exists_canonicalGraph_integer_gain_tame_constant_all_data (d := d + 1) (r := d + 1)
      (Nat.succ_pos d) Rbox n low
  choose Ca hCa hadjoint using fun n ↦
    exists_canonicalGraph_adjoint_integer_gain_tame_constant_all_data (d := d + 1) (r := d + 1)
      (Nat.succ_pos d) Rbox n low
  refine ⟨D, fun n ↦ Cf n + Ca n, hD, fun n ↦ add_nonneg (hCf n) (hCa n), ?_⟩
  intro Q hQ hQlow B hBlow W hW hnorm n f hf T high
  have hall := hb Q hQ ((cNorm_mono_order (by omega)).trans hQlow)
    B ((cNorm_mono_order (by omega)).trans hBlow) W hW hnorm
  let c := fun x ζ ↦ β ζ • ((coefficient i Q x 0).map Complex.ofReal *
    W (x 0) (x 0) (spatialPart x) (spatialPart ζ))
  let Amp := fun x z ζ ↦ (χout x * χsource z) • c x ζ
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol Amp)) :=
    contDiff_endpointPDOCycleSymbol (hΩ.preimage (physicalCoordinates i).continuous)
      (fun x a ↦ (coefficient i Q x a).map Complex.ofReal) (contDiffOn_timeCoefficient i hQ)
      W hW β χout χsource hβs ho hs (hso.trans fun _ hx ↦ hKΩ (hphysical hx))
  have hsupp := maskedPhysicalPDOCycleSymbol_supportedInCenteredBox χout χsource c hoR hsR
  have hlow ξ is (hi : is.length ≤ 2 * ((d + 1) + 1) + 1) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol Amp ξ) z‖ ≤ low := by
    apply (hall (2 * (d + 2) + 1) ξ is hi z).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (hD _))
    have hQn : cNorm KQ (2 * (d + 2) + 1 + 10) Q ≤ M := by
      simpa only [Nat.add_assoc] using hQlow
    have hBn : cNorm KQ (2 * (d + 2) + 1 + 10) B ≤ M := by
      simpa only [Nat.add_assoc] using hBlow
    linarith
  have hhigh ξ is (hi : is.length ≤ 2 * ((d + 1) + 1) + (n + 1)) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol Amp ξ) z‖ ≤ high := by
    have h := hall (2 * (d + 2) + (n + 1)) ξ is hi z
    change (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol Amp ξ) z‖ ≤
      D (2 * (d + 2) + (n + 1)) *
        (1 + cNorm KQ (2 * (d + 2) + (n + 1) + 10) Q + cNorm KQ (2 * (d + 2) + (n + 1) + 10) B) at h
    rw [show 2 * (d + 2) + (n + 1) + 10 = n + (2 * (d + 2) + 11) by omega] at h
    exact h
  have hhigh1 : 1 ≤ high := by
    have hq := cNorm_nonneg KQ (n + (2 * (d + 2) + 11)) Q
    have hb' := cNorm_nonneg KQ (n + (2 * (d + 2) + 11)) B
    have hp : 1 ≤ 1 + cNorm KQ (n + (2 * (d + 2) + 11)) Q +
        cNorm KQ (n + (2 * (d + 2) + 11)) B := by linarith
    exact one_le_mul_of_one_le_of_one_le (hD (2 * (d + 2) + (n + 1))) hp
  have hfor := hforward n Amp hsmooth hsupp high hlow hhigh f hf
  have hadj := hadjoint n Amp hsmooth hsupp high hlow hhigh f hf
  rw [max_eq_right hhigh1] at hfor hadj
  have hS : 0 ≤ vectorFourierSobolevNorm (n : ℝ) f + high * ‖f‖ := by
    have hn : 0 ≤ vectorFourierSobolevNorm (n : ℝ) f := by
      unfold vectorFourierSobolevNorm matrixFourierSobolevNorm
      positivity
    exact add_nonneg hn (mul_nonneg (zero_le_one.trans hhigh1) (norm_nonneg _))
  refine ⟨⟨hfor.1, hfor.2.trans ?_⟩, ⟨hadj.1, hadj.2.trans ?_⟩⟩
  · apply mul_le_mul_of_nonneg_right _ hS
    simp only [Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hCa n)) (by positivity)
  · apply mul_le_mul_of_nonneg_right _ hS
    simp only [Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hCf n)) (by positivity)

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
