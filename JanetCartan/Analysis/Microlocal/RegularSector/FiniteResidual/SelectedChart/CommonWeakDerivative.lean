module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.WeakDerivative.Localization

/-!
# The common solver's derivative from the original algebraic gain

Use the original chart-mask PDO's positive order-zero gain and its normal
budget, both exported by the algebraic construction. Literal multiplication
identifies the common-output PDO, so no new inverse estimates or symbol budget
for that smaller output is required. The retarded positive estimate is applied
only to compact smooth inputs. Consumer: the same-output a.e. equation in
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.UniformEvolution Characteristic.EvolutionIntegral
open Characteristic.ResidualCoordinates Characteristic.PdoRealization
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The original algebraic PDO gain constructs a whole-space weak derivative
of the SAME common-mask retarded-plus-algebraic solver for compact smooth
inputs. `hgain` is the positive `n=0` estimate of the algebraic producer in
chart coordinates; `hOp` is the order-zero retained signed solver output.
No derivative of an output is assumed, and arbitrary L² inputs are not
asserted to give H¹ solver outputs (`energy-complete-residual`). -/
theorem exists_common_solver_weakDerivative_of_original_algebraic_gain
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (Δ a : ℝ)
    (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d (d+1))
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (A : ℝ) (As : ℕ → ℝ) (Op : H →L[ℂ] H)
    (hOp : RetainedSignedRetardedBounds (closedBall x RQ) Q B Δ a Ψ W
      χout χsource β hs 0 A As Op)
    (b : E → E → CMat) (Rbox Mbound C high : ℝ)
    (hbudget : GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) b) Rbox Mbound)
    (hgain : ∀ v : H, MemVectorFourierSobolev 0 v →
      MemVectorFourierSobolev 1 (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) b v) ∧
      vectorFourierSobolevNorm 1 (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p) b v) ≤
        C * (vectorFourierSobolevNorm 0 v + high * ‖v‖))
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hout : tsupport output ⊆ ball x f.physicalRadius) :
    let e := physicalCoordinates (f.chart p).index
    let ψout := output ∘ e
    let ψsource := f.inputMask ∘ e
    ∃ (hψout : ContDiff ℝ ∞ ψout) (hψsource : ContDiff ℝ ∞ ψsource)
      (hψob : ∀ y, ‖ψout y‖ ≤ 1) (hψsb : ∀ y, ‖ψsource y‖ ≤ 1),
    let S := (sourceCutMultiplier ψout hψout.continuous hψob).comp
        (Op.comp (sourceCutMultiplier ψsource hψsource.continuous hψsb)) +
      (1 / Complex.I) • maskedPhysicalPDO
        (fun y ↦ (ψout y : ℂ)) (fun y ↦ (ψsource y : ℂ)) b
    ∀ u : graphTestSpace (d+1) (d+1), ∃ D : E → E →L[ℝ] (Fin (d+1) → ℂ),
      Mollification.HasWeakFDerivOn volume (fun y ↦ (S (graphTestToLp u) y).ofLp) D univ ∧
        MemLp D 2 volume := by
  intro e ψout ψsource
  have hψout : ContDiff ℝ ∞ ψout := ho.comp e.contDiff
  have hψsource : ContDiff ℝ ∞ ψsource := f.inputMask_smooth.comp e.contDiff
  have hψob : ∀ y, ‖ψout y‖ ≤ 1 := fun y ↦ hob (e y)
  have hψsb (y : E) : ‖ψsource y‖ ≤ 1 := by
    change ‖f.inputMask (e y)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (f.inputMask_range _).1]
    exact (f.inputMask_range _).2
  have hψoc : HasCompactSupport ψout := hoc.comp_homeomorph e.toHomeomorph
  obtain ⟨Cm, hCm, hmul⟩ := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) ψout hψout hψoc hψob 1
  simp only [Nat.cast_one] at hmul
  have heq := sourceCutMultiplier_maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
    b Rbox Mbound hbudget ψout hψout.continuous hψob (commonOutput_mul_chartOutputMask f p output hout)
  refine ⟨hψout, hψsource, hψob, hψsb, ?_⟩
  apply exists_localized_retarded_algebraic_weakDerivative (closedBall x RQ) Q B Δ a Ψ W
    χout χsource β hs A As Op hOp ψout ψsource hψout hψoc hψsource hψob hψsb b (Cm*C) high
  intro v hv
  have hg := hgain v hv
  have hm := hmul _ hg.1
  change _ = maskedPhysicalPDO (fun y ↦ (ψout y : ℂ)) (fun y ↦ (ψsource y : ℂ)) b at heq
  rw [← heq]
  refine ⟨hm.1, hm.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hg.2 hCm).trans_eq (mul_assoc _ _ _).symm

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
