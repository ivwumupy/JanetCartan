module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Masks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.MaskJets

/-!
# The original selected masks in the full PDO tail

The original input mask is one at the selected center and throughout the
smaller output support. Absorbing that output into the symbol therefore
preserves the literal cycle symbol and bounded operator. Fixed compact masks
also turn the derived global physical jets into the normal certificate used
by the full-frequency complementary estimate
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.ResidualCoordinates RegularSector.Characteristic.EndpointPdoBounds
open CharacteristicTransport.CompleteResidual FourierIntegral AmplitudeBound

variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The original chart input mask is one at its fixed physical center.
This supplies the source slice used to recover the full masked symbol from
its actual cycle certificate (`fixed-time-representation`). -/
theorem chartInputMask_eq_one_at_center
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    chartInputMask f p ((physicalCoordinates (f.chart p).index).symm x) = 1 := by
  have hx : x ∈ closedBall x (2*f.physicalRadius) :=
    mem_closedBall_self (by linarith [f.physicalRadius_pos])
  have he : f.inputMask x = 1 := interior_subset (s := {y | f.inputMask y = 1})
    (f.inputMask_plateau hx)
  simp only [chartInputMask, ContinuousLinearEquiv.apply_symm_apply, he, Complex.ofReal_one]

/-- The supplied smaller output is absorbed by the ORIGINAL input plateau;
no new mask is selected (`energy-complete-residual`). -/
theorem endpointOutputMask_mul_chartInputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hos : tsupport output ⊆ ball x f.physicalRadius) (y : E) :
    endpointOutputMask f p output y * chartInputMask f p y = endpointOutputMask f p output y := by
  by_cases hy : output (physicalCoordinates (f.chart p).index y) = 0
  · simp only [endpointOutputMask, hy, Complex.ofReal_zero, zero_mul]
  · have hpos := hos (subset_tsupport output hy)
    have hball : physicalCoordinates (f.chart p).index y ∈ closedBall x (2*f.physicalRadius) :=
      ball_subset_closedBall (ball_subset_ball (by linarith [f.physicalRadius_pos]) hpos)
    have he : f.inputMask (physicalCoordinates (f.chart p).index y) = 1 :=
      interior_subset (s := {z | f.inputMask z = 1}) (f.inputMask_plateau hball)
    simp only [chartInputMask, he, Complex.ofReal_one, mul_one]

/-- Absorbing the actual output into the symbol preserves the full physical
amplitude, before any cutoff or operator realization
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem absorbed_selected_amplitude_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (σ : E → E → CMat) (y z ξ : E) :
    (chartInputMask f p y * chartInputMask f p z) •
        (endpointOutputMask f p output y • σ y ξ) =
      (endpointOutputMask f p output y * chartInputMask f p z) • σ y ξ := by
  simp only [smul_smul]
  congr 1
  calc
    _ = (endpointOutputMask f p output y * chartInputMask f p y) * chartInputMask f p z := by ring
    _ = _ := by rw [endpointOutputMask_mul_chartInputMask f p output hos]

/-- The exact original cycle symbol survives output absorption. In the
endpoint case this transports the retained normal certificate unchanged
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem absorbed_selected_cycleSymbol_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (σ : E → E → CMat) :
    maskedPhysicalPDOCycleSymbol (chartInputMask f p) (chartInputMask f p)
        (fun y ξ ↦ endpointOutputMask f p output y • σ y ξ) =
      maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p) σ := by
  unfold maskedPhysicalPDOCycleSymbol
  congr 1
  funext y z ξ
  exact absorbed_selected_amplitude_eq f p output hos σ y z ξ

/-- Literal bounded PDO equality, retaining both original masks and the full
frequency symbol (`app:ch_response:eq:direct-envelope-profile`). -/
theorem maskedPhysicalPDO_chartInput_output_absorption
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (hos : tsupport output ⊆ ball x f.physicalRadius)
    (σ : E → E → CMat) :
    maskedPhysicalPDO (chartInputMask f p) (chartInputMask f p)
        (fun y ξ ↦ endpointOutputMask f p output y • σ y ξ) =
      maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p) σ := by
  unfold maskedPhysicalPDO
  congr 1
  funext y z ξ
  exact absorbed_selected_amplitude_eq f p output hos σ y z ξ

/-- The original compact chart input mask and the DERIVED global physical
jets give an actual normal certificate for the full absorbed symbol. Its
numerical bound may depend on the supplied symbol, as allowed by
`completeDiagonalAnnularComplement_sobolev`; the tail constants are supplied
separately by the uniform jet profile (`direct-envelope-profile`). -/
theorem exists_chartInput_normal_certificate_of_physical_jets
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (σ : E → E → CMat) (hσ : ContDiff ℝ ∞ (Function.uncurry σ))
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j)
    (hjet : ∀ j ξ y, ‖iteratedFDeriv ℝ j (fun z ↦ σ z ξ) y‖ ≤ D j) :
    ∃ R N, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartInputMask f p) (chartInputMask f p) σ) R N := by
  let χ := chartInputMask f p
  have hχ : ContDiff ℝ ∞ χ := (chartPhysicalMasks_properties f p).2.1
  have hcχ : HasCompactSupport χ := (chartPhysicalMasks_properties f p).2.2.2.1
  obtain ⟨R, _hR, hoR, _hsR, hsupport⟩ :=
    exists_maskedPhysicalPDOCycleSymbol_support_box (q := q) χ χ hcχ hcχ
  have hcarrier : tsupport χ ⊆ closedBall 0 R := by
    intro y hy
    simpa only [mem_closedBall, dist_zero_right] using hoR y hy
  let m := 2*(d+2)
  obtain ⟨Cmask, hCmask, hmask⟩ := exists_masked_position_derivative_constant (q := q)
    (isCompact_closedBall (0 : E) R) χ χ hχ hχ hcarrier hcχ m
  refine ⟨R, Cmask * ∑ j ∈ Finset.range (m+1), D j, ?_⟩
  refine ⟨EndpointPdoBounds.contDiff_maskedPhysicalPDOCycleSymbol isOpen_univ χ χ hχ hχ
    (subset_univ _) σ hσ.contDiffOn, hsupport σ, ?_⟩
  intro ξ is his z
  have hs : ContDiff ℝ ∞ (fun y ↦ σ y ((2*Real.pi) • ξ)) :=
    hσ.comp (contDiff_id.prodMk contDiff_const)
  have hb := hmask univ isOpen_univ (subset_univ _) (fun y ↦ σ y ((2*Real.pi) • ξ))
    hs.contDiffOn is his z
  have hcn : cNorm (closedBall 0 R) m (fun y ↦ σ y ((2*Real.pi) • ξ)) ≤
      ∑ j ∈ Finset.range (m+1), D j :=
    cNorm_le_sum_of_bounds (fun j _ ↦ hD j) (fun j _ y _ ↦ hjet j _ y)
  exact hb.trans (mul_le_mul_of_nonneg_left hcn hCmask.le)

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
