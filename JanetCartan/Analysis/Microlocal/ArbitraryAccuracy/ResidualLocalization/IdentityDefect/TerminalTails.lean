module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencyLocalization

/-!
# The full terminal defect on a protected right localizer

Exact frequency cancellation leaves two physical tails, with the source and
output masks in their original order. Literal adjunction reverses those masks.
This identifies the terms whose quantitative estimates are needed for
`finiteChain_observation_rapidDecayAt.hBnear`; it does not assume or assert
their rapid decay (`app:ch_regular:eq:resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral LowBounds FiniteChain.Graph RegularSector.FiniteMasks

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Cancellation of the FULL actual angular identity defect on the buffered
annular right localizer. The surviving terms are physical cutoff tails,
including the original source cutoff before the Fourier operator. The fixed
low bump is retained in `B`; it has only been cancelled on the localizer's
exact frequency support. Geometry is supplied by `ProtectedMasks` and the
SAME `ActualMaskFamily`. This is an operator identity, not the rapid-decay
estimate (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails
    {Ω : Set E} {center : E} {RQ Mbound : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K Mbound) (backward : Bool)
    {lo ρ : ℝ} (hlo : 0 < lo) (hρ : 2 * f.radialThreshold / lo < ρ)
    (mi : LocalizerSymbol (d + 1)) (M : H →L[ℂ] H)
    (hM : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hann : ∀ p ∈ tsupport mi, lo ≤ ‖p.2‖)
    (hang : ∀ p ∈ tsupport mi,
      NormedSpace.normalize p.2 ∈ interior {η | ∑ i, f.angularMask i η = 1}) :
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
    let Mout := if backward then Ms else Mo
    let Msource := if backward then Mo else Ms
    let P := if backward then (actualAngularPDO (r := r) f).adjoint else actualAngularPDO f
    (P - 1).comp M.adjoint =
      Mout.comp (B.comp ((Msource - 1).comp M.adjoint)) +
        (Mout - 1).comp M.adjoint := by
  intro b hb hbound B Mo Ms Mout Msource P
  have hfreq : B.comp M.adjoint = M.adjoint :=
    actualAngularFrequency_comp_rightLocalizer_eq f hlo hρ mi M hM hann hang
  obtain ⟨_, _, hf, ha⟩ := actualAngularPDO_eq_fourier_composition (r := r) f
  have hP : P = Mout.comp (B.comp Msource) := by
    cases backward
    · exact hf
    · exact ha
  have hfreq_apply (u : H) : B (M.adjoint u) = M.adjoint u :=
    DFunLike.congr_fun hfreq u
  rw [hP]
  ext u : 1
  simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply,
    one_apply_eq_self, map_sub, hfreq_apply]
  abel

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
