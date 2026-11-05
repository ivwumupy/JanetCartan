module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification.Fourier

/-!
# Literal identification of the finite source PDO

The actual chart symbols reduce to scalar frequency symbols on the output
support. Their bounded Fourier realizations are transported through the same
physical pullbacks and summed on Lebesgue L². The original input and the
entire enlarged radial shoulder remain unchanged.

Consumer: the source in `selectedFiniteCompleteError`
(`energy-complete-residual`, `prop:complete-residual`, `measured-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.PdoRealization FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

private theorem mask_norm_le_one {a : E → ℝ} (ha : ∀ y, a y ∈ Icc (0 : ℝ) 1) :
    ∀ y, ‖a y‖ ≤ 1 := fun y ↦ (Real.norm_of_nonneg (ha y).1).trans_le (ha y).2

private theorem angular_norm_le_one (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) (L : ℝ) : ∀ ξ, ‖dilatedConicMask (f.angularMask p) L ξ‖ ≤ 1 :=
  fun ξ ↦ mask_norm_le_one (conicMask_mem_Icc (f.angularMask_range p)) (L⁻¹ • ξ)

/-- On the actual output support, the chart source has its scalar Fourier
realization. This is equality of the SAME canonical PDO, using the concrete
smooth angular symbol and original masks. Consumer: finite source summation
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selectedSourcePDO_physical_eq_fourier
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (hL : f.radialThreshold ≤ L) :
    physicalOperator (f.chart p).index
      (maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L))) =
      (sourceCutMultiplier f.outputMask f.outputMask_smooth.continuous
        (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)).comp
        ((scalarPhysicalFrequencyOperator (dilatedConicMask (f.angularMask p) (2*L))
          (contDiff_dilatedConicMask (f.angularMask_smooth p) (2*L)).continuous
          (fun ξ ↦ (Real.norm_of_nonneg
            (conicMask_mem_Icc (f.angularMask_range p) ((2*L)⁻¹ • ξ)).1).trans_le
              (conicMask_mem_Icc (f.angularMask_range p) ((2*L)⁻¹ • ξ)).2)).comp
          (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous
            (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2))) := by
  let e := physicalCoordinates (f.chart p).index
  have he : maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (selectedSourceSymbol f p (2*L)) =
      maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
        (fun _ ξ ↦ (dilatedConicMask (f.angularMask p) (2*L) (e ξ) : ℂ) • (1 : CMat)) := by
    unfold maskedPhysicalPDO
    congr 1
    funext y z ξ
    by_cases hy : f.outputMask (e y) = 0
    · change ((f.outputMask (e y) : ℂ) * chartInputMask f p z) • _ =
        ((f.outputMask (e y) : ℂ) * chartInputMask f p z) • _
      simp only [hy, Complex.ofReal_zero, zero_mul, zero_smul]
    · have hyball : e y ∈ closedBall x (4*f.physicalRadius) :=
        ball_subset_closedBall ((ball_subset_ball (by linarith [f.physicalRadius_pos] :
          2*f.physicalRadius ≤ 4*f.physicalRadius)) (f.outputMask_support (subset_tsupport _ hy)))
      have h := selectedSourceSymbol_on_common_ball_enlarged f p hL hyball (e ξ)
      simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using
        congrArg (fun c : CMat ↦ (chartOutputMask f p y * chartInputMask f p z) • c) h
  rw [he]
  have hscalar := maskedPhysicalPDO_scalarFrequency_eq (r := d+1)
    (dilatedConicMask (f.angularMask p) (2*L) ∘ e)
    ((contDiff_dilatedConicMask (f.angularMask_smooth p) (2*L)).continuous.comp e.continuous)
    (fun ξ ↦ angular_norm_le_one f p (2*L) (e ξ))
    ((hasTemperateGrowth_complex_dilatedConicMask (f.angularMask_smooth p) (2*L)).comp
      e.toContinuousLinearMap.hasTemperateGrowth)
    (f.outputMask ∘ e) (f.inputMask ∘ e)
    (f.outputMask_smooth.continuous.comp e.continuous) (f.inputMask_smooth.comp e.contDiff)
    (fun y ↦ mask_norm_le_one f.outputMask_range (e y))
    (fun y ↦ mask_norm_le_one f.inputMask_range (e y))
  rw [show maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
      (fun _ ξ ↦ (dilatedConicMask (f.angularMask p) (2*L) (e ξ) : ℂ) • (1 : CMat)) = _
      from hscalar]
  exact physicalOperator_scalarFourier_masks (f.chart p).index _ _ _ _ _ _ _ _ _

/-- The finite sum of the actual source chart PDOs is the canonical original
coordinate source PDO. Coordinate transport and Fourier multiplication prove
this identity; the pointwise partition is not used as a substitute for operator
realization (`prop:complete-residual`). -/
theorem finitePhysicalOperator_selectedSource_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L) :
    finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ maskedPhysicalPDO (chartOutputMask f p) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L))) = selectedFiniteSourcePDO f L := by
  classical
  let b := fun p : f.centers ↦ dilatedConicMask (f.angularMask p) (2*L)
  let hb := fun p : f.centers ↦ (contDiff_dilatedConicMask (f.angularMask_smooth p) (2*L)).continuous
  let hbb := fun p : f.centers ↦ angular_norm_le_one f p (2*L)
  let hsum : ∀ ξ, ‖∑ p, b p ξ‖ ≤ 1 :=
    mask_norm_le_one (actualFamily_sum_dilatedConicMask_mem_Icc (withEnlargedThreshold f L hL))
  rw [selectedFiniteSourcePDO_eq_actualAngularPDO f L hL,
    (actualAngularPDO_eq_fourier_composition (r := d+1) (withEnlargedThreshold f L hL)).2.2.1]
  change finitePhysicalOperator _ _ =
    (sourceCutMultiplier f.outputMask f.outputMask_smooth.continuous
      (mask_norm_le_one f.outputMask_range)).comp
      ((scalarPhysicalFrequencyOperator (fun ξ ↦ ∑ p, b p ξ)
        (continuous_finsetSum _ fun p _ ↦ hb p) hsum).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous
          (mask_norm_le_one f.inputMask_range)))
  rw [← scalarPhysicalFrequencyOperator_sum b hb hbb hsum]
  unfold finitePhysicalOperator
  simp_rw [selectedSourcePDO_physical_eq_fourier f _ L hL]
  ext1 u
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  rfl

/-- The literal source sum with the common output is exactly the output
multiplier composed with the SAME finite source PDO at threshold `2*L`.
All source realization budgets are constructed from `ActualMaskFamily` by
`exists_selected_source_pdo_budgets`. Consumer: `selectedFiniteCompleteError`
(`energy-complete-residual`, `prop:complete-residual`). -/
theorem selectedFiniteSourcePDO_commonOutput
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) :
    finitePhysicalOperator (fun p ↦ (f.chart p).index)
      (fun p ↦ maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2*L))) =
      (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L) := by
  classical
  rw [← finitePhysicalOperator_selectedSource_eq f L hL]
  ext1 u
  simp only [finitePhysicalOperator, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  obtain ⟨R, _, C, _, hb, _⟩ := exists_selected_source_pdo_budgets f p (2*L)
  exact (DFunLike.congr_fun (commonOutput_comp_chartPDO f p output ho hob hsupp _
    R (C (2*(d+2))) hb) u).symm

end JanetCartan.RegularSector.FiniteAssembly
