module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencyRealization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.ScalarFourier

/-!
# Identifying the terminal physical PDO

The scalar angular operator with the original source and output masks is
identified with the existing `maskedPhysicalPDO` by its literal test action.
The source multiplier remains before Fourier transformation, and adjunction
reverses both masks. Consumer: the full terminal defect in
`app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform Filter
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral LowBounds LowBounds.FrequencyCutoff FullLowBounds
open FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
open CharacteristicTransport.CompleteResidual

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The physical frequency multiplier has exactly the scalar canonical
graph action, with the manuscript's normalization. Consumer: bounded
terminal identification (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem leftLocalizer_scalarFrequency_eq_physicalMultiplier
    (b : E → ℝ) (ht : (fun ξ ↦ (b ξ : ℂ)).HasTemperateGrowth)
    (g : SchwartzMap E (Fin r → ℂ)) (x : E) :
    leftLocalizer 1 (fun p ↦ b p.2) g x =
      physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) g x := by
  simp only [leftLocalizer, inv_one, one_smul]
  rw [graphOperator_eq_sourceFourierIntegral, physicalMultiplier_eq_integral _ ht]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Construct the literal uncut scalar graph on the existing dense graph
test space. Schwartz regularity is proved for the actual finite masks by
`actualFamily_angularSymbol_hasTemperateGrowth`; boundedness follows from
their pointwise range. Consumer: terminal PDO identification in
`app:ch_regular:eq:chain-tail`. -/
theorem scalarPhysicalFrequencyOperator_graphTestToLp
    (b : E → ℝ) (hb : Continuous b) (hbound : ∀ ξ, ‖b ξ‖ ≤ 1)
    (ht : (fun ξ ↦ (b ξ : ℂ)).HasTemperateGrowth)
    (u : graphTestSpace (d + 1) r) :
    scalarPhysicalFrequencyOperator b hb hbound (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator (fun y ξ ↦ inner ℝ y ξ)
        (fun _ _ ξ ↦ (b ξ : ℂ) • (1 : Mat)) (graphTestToSchwartz u) x) := by
  rw [← schwartzVectorToLp_graphTestToSchwartz u,
    schwartzVectorToLp_eq_toEuclideanSchwartz_toLp,
    scalarPhysicalFrequencyOperator_toEuclideanSchwartz b hb hbound ht]
  refine ((toEuclideanSchwartz
    (physicalMultiplier (fun ξ ↦ (b ξ : ℂ)) (graphTestToSchwartz u))).coeFn_toLp 2).trans ?_
  apply Eventually.of_forall
  intro x
  apply congrArg (WithLp.toLp 2)
  simpa only [leftLocalizer, inv_one, one_smul] using
    (leftLocalizer_scalarFrequency_eq_physicalMultiplier b ht (graphTestToSchwartz u) x).symm

/-- The original masked scalar PDO is the literal bounded Fourier
composition, proved by dense test realization. No sector operator is silently
identified with this expression: the parent's finite chart sum must still be
matched to the same scalar symbol. Consumer: terminal `AΓ-I` in
`app:ch_regular:eq:resolved-angular-tail`. -/
theorem maskedPhysicalPDO_scalarFrequency_eq
    (b : E → ℝ) (hb : Continuous b) (hbound : ∀ ξ, ‖b ξ‖ ≤ 1)
    (ht : (fun ξ ↦ (b ξ : ℂ)).HasTemperateGrowth)
    (χout χsource : E → ℝ) (ho : Continuous χout)
    (hs : ContDiff ℝ ∞ χsource)
    (hob : ∀ x, ‖χout x‖ ≤ 1) (hsb : ∀ x, ‖χsource x‖ ≤ 1) :
    maskedPhysicalPDO (fun x ↦ (χout x : ℂ)) (fun x ↦ (χsource x : ℂ))
      (fun _ ξ ↦ (b ξ : ℂ) • (1 : Mat)) =
        (sourceCutMultiplier χout ho hob).comp
          ((scalarPhysicalFrequencyOperator b hb hbound).comp
            (sourceCutMultiplier χsource hs.continuous hsb)) := by
  apply fullGraphOperator_eq_of_realizes
  intro u
  have hsource := sourceCutGraph_ae_graphOperator
    (fun x ξ : E ↦ inner ℝ x ξ) (fun _ ξ ↦ (b ξ : ℂ) • (1 : Mat))
    (scalarPhysicalFrequencyOperator b hb hbound)
    (scalarPhysicalFrequencyOperator_graphTestToLp b hb hbound ht)
    χsource hs hsb u
  filter_upwards [sourceCutMultiplier_coeFn χout ho hob
    (((scalarPhysicalFrequencyOperator b hb hbound).comp
      (sourceCutMultiplier χsource hs.continuous hsb)) (graphTestToLp u)), hsource]
    with x ho' hs'
  refine ho'.trans ?_
  rw [hs']
  change WithLp.toLp 2 ((χout x : ℂ) • _) = _
  apply congrArg (WithLp.toLp 2)
  change (χout x : ℂ) • graphOperator (fun y ξ : E ↦ inner ℝ y ξ)
    (fun _ y ξ ↦ (χsource y : ℂ) • (b ξ : ℂ) • (1 : Mat))
    (graphTestToSchwartz u) x =
      graphOperator (fun y ξ : E ↦ inner ℝ y ξ)
        (fun y z ξ ↦ ((χout y : ℂ) * (χsource z : ℂ)) • (b ξ : ℂ) • (1 : Mat))
        (graphTestToSchwartz u) x
  rw [← graphOperator_target_mul (fun y ξ : E ↦ inner ℝ y ξ)
    (fun _ y ξ ↦ (χsource y : ℂ) • (b ξ : ℂ) • (1 : Mat))
    (fun y ↦ (χout y : ℂ)) (graphTestToSchwartz u) x]
  congr 1
  funext y z ξ
  simp only [smul_smul, mul_assoc]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
