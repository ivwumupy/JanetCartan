module

public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint.CompactKernel
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.Algebra
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Differentiating the compact-frequency kernel

The compact parameter integral justifies the output derivative in
`app:ch_regular_base:eq:fio-input`, before any frequency limit is taken.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem contDiff_compactFrequencyIntegrand
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (y : E) :
    ContDiff ℝ ∞ (fun p : E × E ↦
      Complex.exp (↑(2 * Real.pi * ⟪p.1 - y, p.2⟫) * Complex.I) *
        b p.2 (pairedPosition p.1 y)) := by
  apply ContDiff.mul
    (Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul ((contDiff_fst.sub contDiff_const).inner ℝ contDiff_snd))).mul contDiff_const))
  exact hb.comp (contDiff_snd.prodMk
    (contDiff_pairedPosition.comp (contDiff_fst.prodMk contDiff_const)))

/-- `app:ch_regular_base:eq:fio-input`: compact frequency integration preserves
smoothness of each output section of the literal kernel. -/
theorem contDiff_compactFrequencyAmplitudeKernel_left
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (ρ : ℝ) (y : E) :
    ContDiff ℝ ∞ (fun x ↦ compactFrequencyAmplitudeKernel b ρ x y) := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) ρ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : E) ρ).measure_lt_top.ne
  rw [← contDiffOn_univ]
  exact contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ
    (isCompact_closedBall (0 : E) ρ) (Set.subset_univ _)
    (contDiff_compactFrequencyIntegrand hb y).contDiffOn

/-- `app:ch_regular_base:eq:fio-input`: differentiation of the literal truncated
kernel gives the complete output derivative amplitude, including the phase term. -/
theorem fderiv_compactFrequencyAmplitudeKernel_left
    {b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (ρ : ℝ) (i : Fin d) (x y : E) :
    fderiv ℝ (fun z ↦ compactFrequencyAmplitudeKernel b ρ z y) x
        (EuclideanSpace.single i 1) =
      compactFrequencyAmplitudeKernel (outputDerivativeAmplitude b i) ρ x y := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) ρ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : E) ρ).measure_lt_top.ne
  have hf := (contDiff_compactFrequencyIntegrand hb y).contDiffOn
    (s := Set.univ ×ˢ Set.univ)
  unfold compactFrequencyAmplitudeKernel
  rw [fderiv_compactParameterIntegral isOpen_univ isOpen_univ
    (isCompact_closedBall (0 : E) ρ) (Set.subset_univ _) hf (Set.mem_univ x)]
  rw [ContinuousLinearMap.integral_apply
    (integrableOn_parameterFDeriv isOpen_univ isOpen_univ
      (isCompact_closedBall (0 : E) ρ) (Set.subset_univ _) hf (Set.mem_univ x))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simpa only [Real.fourierChar_apply, real_inner_comm ξ] using
    fderiv_phasedPairedAmplitude_apply b
      (fun ξ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i x y ξ

end JanetCartan.Pseudodifferential
