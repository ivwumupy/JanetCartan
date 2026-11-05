module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.FixedTime
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Schwartz regularity of the temporal Fourier slice

Compact frequency support supplies a common temporal carrier for differentiation
and a compact spatial support. These facts construct the input to spatial
Fourier inversion in `app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral FiniteChain.Retarded.KernelDecay
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- The actual time/space insertion is smooth. Consumer: smoothness of the
temporal slice in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem contDiff_timeSpacePoint :
    ContDiff ℝ ∞ (fun p : ℝ × Euclidean d ↦ timeSpacePoint p.1 p.2) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact contDiff_fst
  · exact (contDiff_piLp_apply (p := 2) (i := j)).comp contDiff_snd

/-- Projection of the compact cutoff support bounds the spatial support
of the temporal integral. Consumer: `cutTemporalSchwartz`, for
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem hasCompactSupport_cutTemporalFourierSlice
    (β θ : E → ℂ) (v : SchwartzMap E V) (hθcs : HasCompactSupport θ) (s : ℝ) :
    HasCompactSupport (cutTemporalFourierSlice β θ v s) := by
  apply HasCompactSupport.intro (hθcs.image continuous_spatialPart)
  intro η hη
  have hz (τ : ℝ) : θ (timeSpacePoint τ η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦
      hη ⟨timeSpacePoint τ η, h, spatialPart_timeSpacePoint τ η⟩)
  simp [cutTemporalFourierSlice, cutTemporalFourierIntegrand, hz]

/-- Differentiating the actual temporal integral is legitimate because
the temporal projection of the cutoff support is a common compact carrier.
Consumer: `cutTemporalSchwartz`, for
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem contDiff_cutTemporalFourierSlice
    (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) :
    ContDiff ℝ ∞ (cutTemporalFourierSlice β θ v s) := by
  have hp : ContDiff ℝ ∞ (fun p : Euclidean d × ℝ ↦ timeSpacePoint p.2 p.1) :=
    contDiff_timeSpacePoint.comp (contDiff_snd.prodMk contDiff_fst)
  have hc : ContDiff ℝ ∞
      (fun p : Euclidean d × ℝ ↦ cutTemporalFourierIntegrand β θ v s p.1 p.2) := by
    unfold cutTemporalFourierIntegrand
    exact (show ContDiff ℝ ∞
      (fun p : Euclidean d × ℝ ↦ Complex.exp (Complex.I * ((s * p.2 : ℝ) : ℂ)))
      by exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul contDiff_snd))).cexp).smul
        (((hθ.comp hp).mul (hβ.comp hp)).smul
          (((sourceInputFourierTransform v).smooth ⊤).comp hp))
  unfold cutTemporalFourierSlice
  apply ContDiff.const_smul
  apply contDiff_integral_commonCarrier hc
    (hθcs.image (show Continuous (fun ξ : E ↦ ξ 0) by fun_prop))
  intro η τ hτ
  have hz : θ (timeSpacePoint τ η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦
      hτ ⟨timeSpacePoint τ η, h, timeSpacePoint_time τ η⟩)
  simp [cutTemporalFourierIntegrand, hz]

/-- The published temporal Fourier slice as an actual Schwartz function,
with regularity proved from the smooth cutoff and symbol. This is the input
to spatial inversion in `app:ch_regular_base:eq:fixed-time-representation`. -/
def cutTemporalSchwartz (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) : SchwartzMap (Euclidean d) V :=
  (hasCompactSupport_cutTemporalFourierSlice β θ v hθcs s).toSchwartzMap
    (contDiff_cutTemporalFourierSlice β θ v hβ hθ hθcs s)

/-- The Schwartz construction retains the literal temporal integral of
`app:ch_regular_base:eq:fixed-time-representation`. -/
@[simp] theorem cutTemporalSchwartz_apply (β θ : E → ℂ) (v : SchwartzMap E V)
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (s : ℝ) (η : Euclidean d) :
    cutTemporalSchwartz β θ v hβ hθ hθcs s η = cutTemporalFourierSlice β θ v s η := rfl

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
