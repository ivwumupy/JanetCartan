module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.SourceExtension
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Transfer
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint

/-!
# Localization of the actual bounded full-amplitude operator

For `app:ch_background:eq:bg-commutator`, source locality and output support
pass from literal compact-frequency kernels to their proved strong L² limit.
These results have no assumed kernel-realization or locality premise. They
allow the unit-cell lift to be replaced by the compact smooth source extension.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "L²" => EuclideanL2 d ℂ

section
variable (hd : 0 < d) (r : ℝ)
  (b : (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (A : ℝ)
  (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)

/-- The actual bounded Euclidean operator only uses the physical source box
(`app:ch_background:eq:bg-commutator`). -/
theorem twoPositionL2Operator_congr_on_source (f g : L²)
    (hfg : ∀ᵐ y ∂volume, y ∈ chartBox r → f y = g y) :
    twoPositionL2Operator hd r b hb hs A hA f = twoPositionL2Operator hd r b hb hs A hA g := by
  let B := boxCompactFrequencyAmplitudeOperator b hb.continuous.stronglyMeasurable hd
    (amplitudeBoxScale_pos r) (div_amplitudeBoxScale_lt r) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) A hA.norm_le hA.pure_le
  have hlim (v : L²) : Tendsto (fun ρ ↦ B ρ v) atTop
      (𝓝 (twoPositionL2Operator hd r b hb hs A hA v)) :=
    tendsto_boxCompactFrequencyAmplitudeOperator ..
  have he (ρ : ℝ) : B ρ f = B ρ g := by
    apply Lp.ext
    have hf : B ρ f =ᵐ[volume] boxScalarAmplitudeKernel b ρ f :=
      boxCompactFrequencyAmplitudeOperator_ae_kernel ..
    have hg : B ρ g =ᵐ[volume] boxScalarAmplitudeKernel b ρ g :=
      boxCompactFrequencyAmplitudeOperator_ae_kernel ..
    filter_upwards [hf, hg] with x hx hx'
    rw [hx, hx']
    unfold boxScalarAmplitudeKernel
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    by_cases hz : b ξ (pairedPosition x y) = 0
    · simp [hz]
    · rw [hy (positions_mem_chartBox hs hz).2]
  exact tendsto_nhds_unique (hlim f) ((hlim g).congr (fun ρ ↦ (he ρ).symm))

/-- Output support persists through the actual compact-frequency strong limit
(`app:ch_background:eq:bg-commutator`). -/
theorem twoPositionL2Operator_supported (f : L²) :
    ∀ᵐ x ∂volume, x ∉ chartBox r → twoPositionL2Operator hd r b hb hs A hA f x = 0 := by
  let B := boxCompactFrequencyAmplitudeOperator b hb.continuous.stronglyMeasurable hd
    (amplitudeBoxScale_pos r) (div_amplitudeBoxScale_lt r) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) A hA.norm_le hA.pure_le
  have hlim : Tendsto (fun ρ ↦ B ρ f) atTop
      (𝓝 (twoPositionL2Operator hd r b hb hs A hA f)) :=
    tendsto_boxCompactFrequencyAmplitudeOperator ..
  have hK := (isCompact_chartBox (d := d) r).isClosed.measurableSet
  let P : L² →L[ℂ] L² := chartProjection hK
  have he (ρ : ℝ) : P (B ρ f) = B ρ f := by
    apply chartProjection_eq_self
    have hf : B ρ f =ᵐ[volume] boxScalarAmplitudeKernel b ρ f :=
      boxCompactFrequencyAmplitudeOperator_ae_kernel ..
    filter_upwards [hf] with x hx hnot
    rw [hx]
    have hz (ξ y : (EuclideanSpace ℝ (Fin d))) : b ξ (pairedPosition x y) = 0 := by
      by_contra h
      exact hnot (positions_mem_chartBox hs h).1
    simp [boxScalarAmplitudeKernel, hz]
  have hp : P (twoPositionL2Operator hd r b hb hs A hA f) =
      twoPositionL2Operator hd r b hb hs A hA f :=
    tendsto_nhds_unique ((P.continuous.tendsto _).comp hlim)
      (hlim.congr (fun ρ ↦ (he ρ).symm))
  rw [← hp]
  exact chartProjection_supported hK _

/-- The bounded unit-torus operator, constructed from the actual Euclidean
operator and the measure-preserving chart maps
(`app:ch_background:eq:bg-commutator`). -/
def torusL2Operator : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ :=
  transferOperator (twoPositionL2Operator hd r b hb hs A hA)

/-- The low operator bound uses only the fixed physical box and low budget
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_torusL2Operator_le :
    ‖torusL2Operator hd r b hb hs A hA‖ ≤ fixedBoxAmplitudeConstant d r * A :=
  (norm_transferOperator_le _).trans (norm_twoPositionL2Operator_le hd r b hb hs A hA)

/-- Exact L² output comparison, derived from actual amplitude support and the
normalized chart measure (`app:ch_background:eq:bg-commutator`). -/
theorem norm_torusL2Operator_apply (hr : r < 1 / 2) (f : PeriodicL2 d ℂ) :
    ‖torusL2Operator hd r b hb hs A hA f‖ =
      ‖twoPositionL2Operator hd r b hb hs A hA (toEuclidean (𝕜 := ℂ) f)‖ := by
  apply norm_transferOperator_apply
  intro v
  filter_upwards [twoPositionL2Operator_supported hd r b hb hs A hA v] with x hx hnot
  exact hx (fun h ↦ hnot (chartBox_subset_cell hr h))

/-- Literal adjoints are transported through the same normalized chart; the
full amplitude is reversed and conjugated (`app:ch_background:eq:bg-commutator`). -/
theorem torusL2Operator_adjoint :
    (torusL2Operator hd r b hb hs A hA).adjoint =
      torusL2Operator hd r (adjointAmplitude b) (contDiff_adjointAmplitude hb)
        (supportedInCenteredBox_adjointAmplitude hs) A
        (hasAmplitudeDerivativeBound_adjointAmplitude
          (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hA) := by
  unfold torusL2Operator
  rw [transferOperator_adjoint, twoPositionL2Operator_adjoint]

end
end JanetCartan.Pseudodifferential.DifferentialChart
