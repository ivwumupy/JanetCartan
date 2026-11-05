module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SupportedBudgets.SymbolBounds

/-!
# Actual algebraic PDO gains on the retained finite family

The supported budgets are instantiated with the existing natural-order PDO
calculus, including the literal Hilbert adjoint and the exact frequency change
`η = 2 * π * ξ`. Consumer: the finite solver and complete residual, indices zero
and three of `directPDOSymbols`, followed by `FixedDomainInverse.LocalL2`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral Characteristic.PdoRealization
open Characteristic.AmplitudeBounds FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound FourierIntegral Pseudodifferential
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin (d + 1))) 2 (volume : Measure E)
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Gain one derivative at every natural Sobolev order, forward and for the
literal adjoint, for the SAME algebraic symbol and its full physical action.
All constants precede the varying original fields and radial enlargement.
The low order and total original high reserve are `2 * (d + 2) + 2`, and the
high quantity is additive in `Q,B`. The only local analytic inputs are the
retained inverse constructor's outputs, instantiated through the supported
budget theorem in this proof; no operator estimate is assumed.
Source: `app:ch_regular_base:eq:energy-complete-residual` and `fio-input`. -/
theorem exists_selected_algebraicSymbols_integer_gain_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hΩ : IsOpen Ω) (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : RootBuffer (f.chart p).index (f.chart p).row (f.chart p).col A₀ p.val.val
      (f.chart p).root (f.chart p).coefficientRadius (f.chart p).rootRadius
      (f.chart p).minorGap (f.chart p).transportGap)
    (hsource : MapsTo (rootPhysicalPosition (coordinateSplit (f.chart p).index))
      (tsupport (f.chart p).sourceMask) (closedBall x RQ))
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : tsupport ρ ⊆ {η | 0 < (f.chart p).radialSection η})
    (hρrange : ∀ η, ρ η ∈ Icc (0 : ℝ) 1)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (hcarrier : tsupport χout ⊆ closedBall ((physicalCoordinates (f.chart p).index).symm x) RQ)
    (Mlow : ℝ) (hMlow : 0 ≤ Mlow) (D : ℕ → ℝ) (hD : ∀ m, 0 < D m) :
    let c := f.chart p
    let x' := (physicalCoordinates c.index).symm x
    ∃ C G : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧ (∀ n, 0 ≤ G n) ∧
      ∀ (L : ℝ) (Q : E → Coeff) (B : E → Mat),
        ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
        MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
        cNorm (closedBall x RQ) (2 * (d + 2) + 2) Q ≤ Mlow →
        cNorm (closedBall x RQ) (2 * (d + 2) + 2) B ≤ Mlow →
        let h := fieldRoot (coordinateSplit c.index) Q c.root
        let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ)
        ((physicalCoordinates c.index ⁻¹' Ω) ×ˢ
          (normalizeCovector c.radialSection '' tsupport β) ⊆
          complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) →
        (∀ ζ ∈ tsupport β,
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) y) ∧
          ∀ m, (1 + ‖ζ‖) * cNorm (closedBall x' RQ) m
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) ≤
              D m * (1 + cNorm (closedBall x RQ) m Q)) →
        let b := directAlgebraicSymbol
          (conicBminus c.radialSection c.index Q h c.row c.col)
          (conicSourceSymbol c.radialSection ρ c.sourceMask) β
        let p := physicalSymbolApply
          (fun y a ↦ (coefficient c.index Q y a).map Complex.ofReal)
          (fun y ↦ (zeroth c.index B y).map Complex.ofReal) b
        ∀ s ∈ ({b, p} : Set (E → E → CMat)),
          ∀ n : ℕ, ∀ u : H, MemVectorFourierSobolev (n : ℝ) u →
          let T := maskedPhysicalPDO χout χsource s
          let high := C (2 * (d + 2) + (n + 1)) *
            (1 + cNorm (closedBall x RQ) (n + (2 * (d + 2) + 2)) Q +
              cNorm (closedBall x RQ) (n + (2 * (d + 2) + 2)) B)
          (MemVectorFourierSobolev ((n : ℝ) + 1) (T u) ∧
            vectorFourierSobolevNorm ((n : ℝ) + 1) (T u) ≤
              ((d + 1 : ℝ) * (d + 1) * G n) *
                (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖)) ∧
          (MemVectorFourierSobolev ((n : ℝ) + 1) (T.adjoint u) ∧
            vectorFourierSobolevNorm ((n : ℝ) + 1) (T.adjoint u) ≤
              ((d + 1 : ℝ) * (d + 1) * G n) *
                (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖)) := by
  intro c x'
  obtain ⟨Rbox, _, C₀, Mbound, _, hC₀, hbudgets⟩ :=
    exists_selected_algebraicSymbols_supported_budgets f p hΩ hRQ hKΩ hc hsource
      ρ hρ hsρ hρrange χout χsource ho hs hco hcs hcarrier Mlow hMlow D hD
  let C : ℕ → ℝ := fun m ↦ 1 + C₀ m
  have hC m : 1 ≤ C m := by dsimp [C]; linarith [hC₀ m]
  choose Cf hCf hforward using fun n ↦
    exists_canonicalGraph_integer_gain_tame_constant_all_data (d := d + 1) (r := d + 1)
      (Nat.succ_pos d) Rbox n Mbound
  choose Ca hCa hadjoint using fun n ↦
    exists_canonicalGraph_adjoint_integer_gain_tame_constant_all_data (d := d + 1) (r := d + 1)
      (Nat.succ_pos d) Rbox n Mbound
  refine ⟨C, fun n ↦ Cf n + Ca n, hC, fun n ↦ add_nonneg (hCf n) (hCa n), ?_⟩
  intro radial Q B hQ hB hQrange hQlow hBlow h β hdom hinverse b p' s hs' n u hu T high
  have hall := hbudgets radial Q B hQ hB hQrange hQlow hBlow hdom hinverse s hs'
  let Amp := fun y z ζ ↦ (χout y * χsource z) • s y ζ
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry (physicalPDOCycleSymbol Amp)) := hall.2.1.smooth
  have hsupp := hall.2.1.support
  have hlow := hall.2.2.1
  have hhigh ξ is (hi : is.length ≤ 2 * ((d + 1) + 1) + (n + 1)) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (physicalPDOCycleSymbol Amp ξ) z‖ ≤ high := by
    have hb := hall.2.2.2 (2 * (d + 2) + (n + 1)) ξ is hi z
    rw [show 2 * (d + 2) + (n + 1) + 1 = n + (2 * (d + 2) + 2) by omega] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
      (by linarith [cNorm_nonneg (closedBall x RQ) (n + (2 * (d + 2) + 2)) Q,
        cNorm_nonneg (closedBall x RQ) (n + (2 * (d + 2) + 2)) B]))
  have hhigh1 : 1 ≤ high := by
    apply one_le_mul_of_one_le_of_one_le (hC _)
    linarith [cNorm_nonneg (closedBall x RQ) (n + (2 * (d + 2) + 2)) Q,
      cNorm_nonneg (closedBall x RQ) (n + (2 * (d + 2) + 2)) B]
  have hfor := hforward n Amp hsmooth hsupp high hlow hhigh u hu
  have hadj := hadjoint n Amp hsmooth hsupp high hlow hhigh u hu
  rw [max_eq_right hhigh1] at hfor hadj
  have hS : 0 ≤ vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖ := by
    have hn : 0 ≤ vectorFourierSobolevNorm (n : ℝ) u := by
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

end JanetCartan.RegularSector.FiniteAlgebraic
