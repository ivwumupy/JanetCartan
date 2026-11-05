module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.InverseBounds

/-!
# The selected family's physical masks for the algebraic terms

Pull back the common original masks through each selected permutation. Their
closed supports stay in the original coefficient ball. The angular collar is
the family's already constructed spatial mask. These facts discharge the mask
inputs of `SupportedBudgets`, for indices zero and three of the complete
residual in `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open Characteristic Characteristic.ResidualCoordinates
open FiniteMasks FiniteMasks.ActualFamily
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Literal pullback of the fixed common input mask (`measured-adjoint`). -/
def chartInputMask (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (y : Euclidean (d+1)) : ℂ := f.inputMask (physicalCoordinates (f.chart p).index y)

/-- Literal pullback of the fixed common output mask (`energy-complete-residual`). -/
def chartOutputMask (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (y : Euclidean (d+1)) : ℂ := f.outputMask (physicalCoordinates (f.chart p).index y)

/-- The actual common masks have the smoothness, compact support and original
coefficient-domain containment required by the algebraic PDO producer.
No extra physical mask or support hypothesis is introduced (`complement-symbol`). -/
theorem chartPhysicalMasks_properties (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) :
    ContDiff ℝ ∞ (chartOutputMask f p) ∧ ContDiff ℝ ∞ (chartInputMask f p) ∧
    HasCompactSupport (chartOutputMask f p) ∧ HasCompactSupport (chartInputMask f p) ∧
    tsupport (chartOutputMask f p) ⊆
      closedBall ((physicalCoordinates (f.chart p).index).symm x) RQ := by
  let e := physicalCoordinates (f.chart p).index
  have ho : HasCompactSupport (fun y ↦ (f.outputMask y : ℂ)) :=
    f.outputMask_compact.comp_left Complex.ofReal_zero
  have hi : HasCompactSupport (fun y ↦ (f.inputMask y : ℂ)) :=
    f.inputMask_compact.comp_left Complex.ofReal_zero
  refine ⟨Complex.ofRealCLM.contDiff.comp (f.outputMask_smooth.comp e.contDiff),
    Complex.ofRealCLM.contDiff.comp (f.inputMask_smooth.comp e.contDiff),
    ho.comp_homeomorph e.toHomeomorph, hi.comp_homeomorph e.toHomeomorph, ?_⟩
  intro y hy
  have hs : e y ∈ tsupport f.outputMask := by
    have ht := tsupport_comp_subset_preimage
      (fun y ↦ (f.outputMask y : ℂ)) e.continuous hy
    exact tsupport_comp_subset Complex.ofReal_zero f.outputMask ht
  have hball := f.physicalBall_coefficientDomain
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by linarith [f.physicalRadius_pos] : 2*f.physicalRadius ≤ 4*f.physicalRadius)))
      (f.outputMask_support hs))
  change dist y (e.symm x) ≤ RQ
  have he : dist (e y) x = dist y (e.symm x) := by
    conv_lhs => arg 2; rw [← e.apply_symm_apply x]
    rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
  simpa only [mem_closedBall, he] using hball

/-- The actual collared spatial mask meets the positive-section and range
inputs of the algebraic source symbol, including its full closed support
(`complement-symbol`). -/
theorem chartConicMask_properties (f : ActualMaskFamily Ω x RQ A₀ K M)
    (p : f.centers) :
    ContDiff ℝ ∞ (conicMask (f.spatialMask p)) ∧
    tsupport (conicMask (f.spatialMask p)) ⊆ {η | 0 < (f.chart p).radialSection η} ∧
    ∀ η, conicMask (f.spatialMask p) η ∈ Icc (0 : ℝ) 1 := by
  refine ⟨contDiff_conicMask (f.spatialMask_properties p).1,
    conicMask_tsupport_subset_cone _ (fun _ hη ↦ f.spatialMask_positive_section p hη) ?_,
    conicMask_mem_Icc (f.spatialMask_properties p).2.1⟩
  intro η hη r hr
  change 0 < (f.chart p).radialSection (r • η)
  simpa only [map_smul, smul_eq_mul] using mul_pos hr hη

end JanetCartan.RegularSector.FiniteAlgebraic
