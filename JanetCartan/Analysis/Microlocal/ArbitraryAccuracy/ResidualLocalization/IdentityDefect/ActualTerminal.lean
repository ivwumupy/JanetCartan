module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.MaskedRealization

/-!
# The original finite angular PDO and its literal adjoint

The finite angular symbol, its radial collar, and the two physical masks are
those of `ActualMaskFamily`. The physical PDO is identified with its bounded
Fourier composition. The sector parent must still identify its chart sum
with this operator; no arbitrary sector operator is equated to this definition.
Consumer: the terminal observation in `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral LowBounds RegularSector.FiniteMasks
open CharacteristicTransport.CompleteResidual

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The original finite angular symbol with its fixed low-frequency collar
and original physical masks, realized by the pre-existing canonical PDO.
The definition has no accuracy parameter (`resolved-angular-tail`). -/
def actualAngularPDO (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M) : H →L[ℂ] H :=
  maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun y ↦ (f.inputMask y : ℂ))
    (fun _ ξ ↦ ((∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ : ℝ) : ℂ) •
      (1 : Mat))

private theorem norm_le_one_of_range {a : E → ℝ} (h : ∀ ξ, a ξ ∈ Icc (0 : ℝ) 1)
    (ξ : E) : ‖a ξ‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (h ξ).1]
  exact (h ξ).2

/-- Identify the bounded forward and literal adjoint of the actual finite
angular PDO using the original scalar symbol and masks. All regularity and
range inputs are discharged by the finite-mask construction. The source
cutoff remains inside the Fourier action, including at low frequencies
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem actualAngularPDO_eq_fourier_composition
    (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M) :
    let b := fun ξ ↦ ∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ
    let hb : Continuous b := continuous_finsetSum _ (fun p _ ↦
      (contDiff_dilatedConicMask (f.angularMask_smooth p) f.radialThreshold).continuous)
    let hbound : ∀ ξ, ‖b ξ‖ ≤ 1 := fun ξ ↦
      (Real.norm_of_nonneg (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).1).trans_le
        (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).2
    let B := scalarPhysicalFrequencyOperator (r := r) b hb hbound
    let Mo := sourceCutMultiplier (r := r) f.outputMask f.outputMask_smooth.continuous
      (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)
    let Ms := sourceCutMultiplier (r := r) f.inputMask f.inputMask_smooth.continuous
      (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)
    B.adjoint = B ∧ ‖B‖ ≤ 1 ∧
      actualAngularPDO f = Mo.comp (B.comp Ms) ∧
      (actualAngularPDO f).adjoint = Ms.comp (B.comp Mo) := by
  intro b hb hbound B Mo Ms
  have he : actualAngularPDO (r := r) f = Mo.comp (B.comp Ms) :=
    maskedPhysicalPDO_scalarFrequency_eq b hb hbound
      (actualFamily_angularSymbol_hasTemperateGrowth f)
      f.outputMask f.inputMask f.outputMask_smooth.continuous f.inputMask_smooth
      (norm_le_one_of_range f.outputMask_range) (norm_le_one_of_range f.inputMask_range)
  have hBa : B.adjoint = B := scalarPhysicalFrequencyOperator_adjoint b hb hbound
  refine ⟨hBa, norm_scalarPhysicalFrequencyOperator_le b hb hbound, he, ?_⟩
  rw [he, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hBa]
  dsimp only [Mo, Ms]
  rw [sourceCutMultiplier_adjoint, sourceCutMultiplier_adjoint,
    ContinuousLinearMap.comp_assoc]

/-- The fixed angular operator and its full identity defect have uniform L²
bounds in both literal orientations. These are only low bounds; rapid
Sobolev decay requires the buffered-localizer argument in
`app:ch_regular:eq:chain-tail`. -/
theorem actualAngularPDO_low_bounds
    (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M) :
    ‖actualAngularPDO (r := r) f‖ ≤ 1 ∧
      ‖(actualAngularPDO (r := r) f).adjoint‖ ≤ 1 ∧
      ‖actualAngularPDO (r := r) f - 1‖ ≤ 2 ∧
      ‖(actualAngularPDO (r := r) f).adjoint - 1‖ ≤ 2 := by
  obtain ⟨_, hB, he, _⟩ := actualAngularPDO_eq_fourier_composition (r := r) f
  have hP : ‖actualAngularPDO (r := r) f‖ ≤ 1 := by
    rw [he]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_sourceCutMultiplier_le _ _ _)
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul hB (norm_sourceCutMultiplier_le _ _ _)
            (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hPa : ‖(actualAngularPDO (r := r) f).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hP
  have hid : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact ⟨hP, hPa, (norm_sub_le _ _).trans (by linarith),
    (norm_sub_le _ _).trans (by linarith)⟩

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
