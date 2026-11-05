module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.SectorIncidenceSelection
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Masks

/-!
# The actual common masks remain inside the selected stationary boxes

The full-source incidence selector controls the original physical masks.
The direct solver's smaller common output lies in the original output's
plateau. These inclusions apply that selected box to the literal capped
solver and residual, with no further selection or shrinking.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.KernelIdentification
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FinitePdo
open CompatibleResponse ResponseTransfer.RetainedFactors
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The common physical output is supported in the original selected output,
by its proved plateau. Consumer: the full-source stationary box for the actual
capped factors (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem commonOutput_support_subset_selected_outputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M) {output : E → ℝ}
    (hout : tsupport output ⊆ ball x f.physicalRadius) :
    tsupport output ⊆ tsupport f.outputMask := by
  intro y hy
  have he := interior_subset (f.outputMask_plateau (ball_subset_closedBall (hout hy)))
  change f.outputMask y = 1 at he
  apply subset_tsupport
  change f.outputMask y ≠ 0
  rw [he]
  exact one_ne_zero

/-- Both literal chart masks for the common finite solver lie in the SAME
stationary physical box as the originally selected family. This uses the
actual support of the smaller output and the unchanged input, including
their complexification and coordinate permutation
(`app:ch_response:eq:fixed-factor-transfer`, `characteristic-kernel`). -/
theorem commonOutput_masks_in_stationary_box
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {output : E → ℝ} (hout : tsupport output ⊆ ball x f.physicalRadius)
    (z : RootState (Euclidean d)) (ε : ℝ)
    (hphysical : MapsTo (primaryCoordinateChange (f.chart p).index)
      (tsupport f.inputMask ∪ tsupport f.outputMask) (elapsedPhysicalBox z ε)) :
    tsupport (endpointOutputMask f p output) ∪ tsupport (chartInputMask f p) ⊆
      elapsedPhysicalBox z ε := by
  intro y hy
  have hmem : physicalCoordinates (f.chart p).index y ∈
      tsupport f.inputMask ∪ tsupport f.outputMask := by
    rcases hy with hy | hy
    · apply Or.inr
      apply commonOutput_support_subset_selected_outputMask f hout
      exact tsupport_comp_subset Complex.ofReal_zero output
        (tsupport_comp_subset_preimage (fun y ↦ (output y : ℂ))
          (physicalCoordinates (f.chart p).index).continuous hy)
    · apply Or.inl
      exact tsupport_comp_subset Complex.ofReal_zero f.inputMask
        (tsupport_comp_subset_preimage (fun y ↦ (f.inputMask y : ℂ))
          (physicalCoordinates (f.chart p).index).continuous hy)
  simpa only [primaryCoordinateChange, physicalCoordinates,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using
    hphysical hmem

/-- The literal endpoint frequency support is captured by the original
physical incidence selector at exactly `2 * L`. Complexification and the
time-first permutation preserve this support implication, including cutoff
shoulders. Consumer: the same-family full-source stationary application for
both direct factors (`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selectedEndpointMultiplier_incidence_support
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ) {ξ : E}
    (hξ : primaryCoordinateChange (f.chart p).index ξ ∈
      tsupport (selectedEndpointMultiplier f p L)) :
    ξ ∈ tsupport (dilatedConicMask (f.angularMask p) (2 * L)) := by
  have hmem := tsupport_comp_subset Complex.ofReal_zero
    (dilatedConicMask (f.angularMask p) (2 * L))
    (tsupport_comp_subset_preimage
      (fun ζ ↦ (dilatedConicMask (f.angularMask p) (2 * L) ζ : ℂ))
      (physicalCoordinates (f.chart p).index).continuous hξ)
  simpa only [primaryCoordinateChange, physicalCoordinates,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hmem

end JanetCartan.RegularSector.FiniteAssembly
