module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.CompactFrequency
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.FrequencyTransfer.FullIntegral
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint

/-!
# Schwartz pairings through the strong frequency limit

For `app:ch_regular_base:eq:graph-derivative-transfer`, strong L² convergence
implies convergence of the literal compact-frequency kernels against every
Schwartz test. The embedding into tempered distributions supplies continuity.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the compact-frequency
realization agrees with its literal kernel on any specified L² representative. -/
theorem twoPositionCompactFrequencyL2Operator_toLp_ae_kernel
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (ρ : ℝ) (u : E → ℂ) (hu : MemLp u 2) :
    twoPositionCompactFrequencyL2Operator hd R b hb hs A hA ρ (hu.toLp u) =ᵐ[volume]
      fun x ↦ ∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y :=
  (twoPositionCompactFrequencyL2Operator_ae_kernel hd R b hb hs A hA ρ (hu.toLp u)).trans
    (Eventually.of_forall (fun x ↦ integral_congr_ae
      (hu.coeFn_toLp.mono (fun y hy ↦ congrArg (fun z ↦
        compactFrequencyAmplitudeKernel b ρ x y * z) hy))))

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: integrability of every
Schwartz pairing follows from the checked L² realization of the compact kernel. -/
theorem integrable_schwartz_mul_compactFrequencyAmplitudeKernel
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (ρ : ℝ) (u : E → ℂ) (hu : MemLp u 2) (φ : 𝓢(E, ℂ)) :
    Integrable (fun x ↦ φ x * (∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y)) :=
  (φ.memLp 2).integrable_mul ((Lp.memLp _).ae_eq
    (twoPositionCompactFrequencyL2Operator_toLp_ae_kernel hd R b hb hs A hA ρ u hu))

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: strong exhaustion of
frequency balls passes to Schwartz pairings by the continuous L² embedding into
tempered distributions. -/
theorem tendsto_pairing_compactFrequencyAmplitudeKernel
    (hd : 0 < d) (R : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (u : E → ℂ) (hu : MemLp u 2) (φ : 𝓢(E, ℂ)) :
    Tendsto (fun ρ : ℝ ↦ ∫ x, φ x *
      (∫ y, compactFrequencyAmplitudeKernel b ρ x y * u y)) atTop
      (𝓝 ((twoPositionL2Operator hd R b hb hs A hA (hu.toLp u) : 𝓢'(E, ℂ)) φ)) :=
  let h := (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).continuous.continuousAt.tendsto.comp
    (tendsto_twoPositionCompactFrequencyL2Operator hd R b hb hs A hA (hu.toLp u))
  let hp := (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp h) φ
  hp.congr (fun ρ ↦ (Lp.toTemperedDistribution_apply _ φ).trans
    (integral_congr_ae ((twoPositionCompactFrequencyL2Operator_toLp_ae_kernel
      hd R b hb hs A hA ρ u hu).mono (fun x hx ↦ congrArg (fun z ↦ φ x * z) hx))))

end JanetCartan.Pseudodifferential
