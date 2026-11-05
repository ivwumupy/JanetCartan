module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SourceAgreement.Collars
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.AlgebraicExtension

/-!
# Exact agreement of selected and retarded source symbols

At the enlarged physical threshold the selected spatial collar and the angular
collar retained by `SelectedChartEvolutionAt` both equal one on the same right
multiplier. Thus the entire source symbols agree at every physical position,
with the original source mask and multiplier order preserved. The common-ball
source partition retains both its angular and low-frequency complements.

Consumers: the parent endpoint assembly and index one of `directPDOSymbols` in
`paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`; the measured
residual of `paper.tex`, `sector-theorem-residual` and `measured-adjoint`.
The parent instantiates the SAME retained evolution witnesses and the bound
`f.radialThreshold ≤ L` from its finite threshold construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- Equality of the entire selected source symbol and the source symbol of
the SAME retained retarded evolution. The angular plateau is extracted from
`SelectedChartEvolutionAt`, whose producer is the selected physical evolution
constructor. The multiplier stays pointwise on the right for every position;
no Fourier multiplier is commuted through a physical source mask.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selectedSourceSymbol_eq_retainedSourceSymbol
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {L₀ L : ℝ} {angular : Euclidean d → ℝ} {χout χsource : E → ℂ}
    {hs : ContDiff ℝ ∞ χsource}
    (hevolution : SelectedChartEvolutionAt (f.chart p) (selectedEndpointMultiplier f p)
      L₀ angular χout χsource hs)
    (hL₀ : L₀ ≤ L) (hL : f.radialThreshold ≤ L) :
    selectedSourceSymbol f p (2 * L) =
      fun y ζ ↦ (conicSourceSymbol (f.chart p).radialSection (conicMask angular)
        (f.chart p).sourceMask y (spatialPart ζ) * selectedEndpointMultiplier f p L ζ) •
          (1 : CMat) := by
  have hsp : ∀ ζ, selectedEndpointMultiplier f p L ζ ≠ 0 →
      conicMask (f.spatialMask p) (spatialPart ζ) = 1 := fun ζ hζ ↦
    (selectedEndpointMultiplier_spatialMask_plateau f p hL (subset_tsupport _ hζ)).eq_of_nhds
  have ha : ∀ ζ, selectedEndpointMultiplier f p L ζ ≠ 0 →
      conicMask angular (spatialPart ζ) = 1 := fun ζ hζ ↦
    ((hevolution L hL₀).1 ζ (subset_tsupport _ hζ)).eq_of_nhds
  funext y ζ
  change (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
    (f.chart p).sourceMask y (spatialPart ζ) * selectedEndpointMultiplier f p L ζ) •
      (1 : CMat) = _
  rw [conicSourceSymbol_mul_right_multiplier _ _ _ _ hsp,
    conicSourceSymbol_mul_right_multiplier _ _ _ _ ha]

/-- Index one of the complete residual is literally the selected source
symbol at the enlarged threshold. The other direct PDO inputs can be the
parent's actual coefficients and amplitudes without changing this identity.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selectedSourceSymbol_eq_directPDOSymbols_one
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {L₀ L : ℝ} {angular : Euclidean d → ℝ} {χout χsource : E → ℂ}
    {hs : ContDiff ℝ ∞ χsource}
    (hevolution : SelectedChartEvolutionAt (f.chart p) (selectedEndpointMultiplier f p)
      L₀ angular χout χsource hs)
    (hL₀ : L₀ ≤ L) (hL : f.radialThreshold ≤ L)
    (A : E → Fin (d+1) → CMat) (B : E → CMat)
    (W₁ : TwoTimeAmplitude d (d+1)) (bminus : E → E → CMat) :
    selectedSourceSymbol f p (2 * L) =
      directPDOSymbols A B W₁ bminus
        (conicSourceSymbol (f.chart p).radialSection (conicMask angular)
          (f.chart p).sourceMask) (selectedEndpointMultiplier f p L) 1 := by
  exact selectedSourceSymbol_eq_retainedSourceSymbol f p hevolution hL₀ hL

/-- Literal equality of the masked source PDOs follows from symbol equality,
with arbitrary SAME physical masks on both sides. This preserves the source
mask order required by `app:ch_regular_base:eq:measured-adjoint` and the source
term in `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selectedSourceSymbol_maskedPhysicalPDO_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {L₀ L : ℝ} {angular : Euclidean d → ℝ} {χout χsource : E → ℂ}
    {hs : ContDiff ℝ ∞ χsource}
    (hevolution : SelectedChartEvolutionAt (f.chart p) (selectedEndpointMultiplier f p)
      L₀ angular χout χsource hs)
    (hL₀ : L₀ ≤ L) (hL : f.radialThreshold ≤ L) (output input : E → ℂ) :
    maskedPhysicalPDO output input (selectedSourceSymbol f p (2 * L)) =
      maskedPhysicalPDO output input
        (fun y ζ ↦ (conicSourceSymbol (f.chart p).radialSection (conicMask angular)
          (f.chart p).sourceMask y (spatialPart ζ) * selectedEndpointMultiplier f p L ζ) •
            (1 : CMat)) := by
  rw [selectedSourceSymbol_eq_retainedSourceSymbol f p hevolution hL₀ hL]

/-- The original source-mask diagonal geometry and selected spatial collar
also give the exact common-ball source identity at every doubled enlarged
threshold. Consumer: the complete source partition for
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem selectedSourceSymbol_on_common_ball_enlarged
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {L : ℝ}
    (hL : f.radialThreshold ≤ L) {y : E}
    (hy : y ∈ closedBall x (4 * f.physicalRadius)) (ζ : E) :
    selectedSourceSymbol f p (2 * L)
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ζ) =
      (dilatedConicMask (f.angularMask p) (2 * L) ζ : ℂ) • (1 : CMat) := by
  let e := physicalCoordinates (f.chart p).index
  by_cases hz : dilatedConicMask (f.angularMask p) (2 * L) ζ = 0
  · simp only [selectedSourceSymbol, ContinuousLinearEquiv.apply_symm_apply,
      hz, Complex.ofReal_zero, mul_zero, zero_smul]
  have hζ : e.symm ζ ∈ tsupport (selectedEndpointMultiplier f p L) := by
    apply subset_tsupport
    change (dilatedConicMask (f.angularMask p) (2 * L) (e (e.symm ζ)) : ℂ) ≠ 0
    rw [e.apply_symm_apply]
    exact_mod_cast hz
  have hsource := f.conicSourceSymbol_eq_one p
    (y := e.symm y) (by
      change e (e.symm y) ∈ closedBall x (4 * f.physicalRadius)
      rwa [e.apply_symm_apply])
    (selectedEndpointMultiplier_tsupport_subset f p hL hζ)
  dsimp only [e] at hsource
  simp only [selectedSourceSymbol, hsource, one_mul,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Exact finite source partition at the actual enlarged threshold. Both
the angular complement and the SAME literal low-frequency complement remain
as summands. Consumer: the source discrepancy in `prop:complete-residual`,
`energy-complete-residual`, and `sector-theorem-residual`. -/
theorem selectedSourceSymbols_complete_partition_enlarged
    (f : ActualMaskFamily Ω x RQ A₀ K M) {L : ℝ} (hL : f.radialThreshold ≤ L)
    {y : E} (hy : y ∈ closedBall x (4 * f.physicalRadius)) (ζ : E) :
    (∑ p, selectedSourceSymbol f p (2 * L)
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ζ)) +
      (dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2 * L) ζ : ℂ) •
        (1 : CMat) +
      (FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
        ((2 * L)⁻¹ • ζ) : ℂ) • (1 : CMat) = 1 := by
  classical
  simp_rw [selectedSourceSymbol_on_common_ball_enlarged f _ hL hy]
  rw [← Finset.sum_smul, ← add_smul, ← add_smul]
  have h := congrArg (fun a : ℝ ↦ (a : ℂ))
    (dilatedConicMask_complete_partition f.angularMask (2 * L) ζ)
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_one] at h
  rw [h, one_smul]

end JanetCartan.RegularSector.FinitePdo
