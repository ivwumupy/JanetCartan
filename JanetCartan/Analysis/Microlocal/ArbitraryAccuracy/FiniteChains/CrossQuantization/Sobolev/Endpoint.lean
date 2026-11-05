module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Sobolev.Normalization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Schur
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Extension
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.CommutatorBounds.SourceIndependentBounds.KernelSobolev.Forward.Coordinates

/-!
# All-L² extension of a physical Fourier kernel bound

The weighted kernel estimate in `app:ch_regular:eq:chain-tail` gives a
Schwartz test estimate by the existing Schur theorem. The existing compact
smooth density theorem extends it to the same bounded vector L² operator.
The reusable endpoint takes only a literal Schwartz Fourier action and a
pointwise weighted kernel bound; it proves output Sobolev membership.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform

namespace JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization

open FourierIntegral FiniteChain.Graph.KernelLimits Pseudodifferential
open FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
open ResidualLocalization.IdentityDefect.PhysicalTailSobolev
open FourierIntegral.LowBounds.FrequencyCutoff

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The Schur estimate for Schwartz representatives in Mathlib's Fourier
convention. It supplies the test bound for
`exists_channelFourierKernel_sobolev_constant`, including order zero
(`app:ch_regular:eq:chain-tail`). -/
theorem fourierKernel_schwartz_sobolev_bound (m : ℕ) (k : E → E → ℂ)
    (hk : StronglyMeasurable (Function.uncurry k)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ξ η, (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) * ‖k ξ η‖ ≤ B)
    (f w : SchwartzMap E (Fin r → ℂ))
    (hw : ∀ ξ, (𝓕 w) ξ = ∫ η, k ξ η • (𝓕 f) η) :
    vectorFourierSobolevNorm (m : ℝ) (schwartzVectorToLp w) ≤
      physicalTailSchurConstant n * B * ‖schwartzVectorToLp f‖ := by
  let v := toEuclideanSchwartz (𝓕 f)
  let j : E → E → V := fun ξ η ↦ euclideanSobolevWeight (m : ℝ) ξ • (k ξ η • v η)
  have hj : StronglyMeasurable (Function.uncurry j) :=
    ((continuous_euclideanSobolevWeight _).stronglyMeasurable.comp_measurable measurable_fst).smul
      (hk.smul (v.continuous.stronglyMeasurable.comp_measurable measurable_snd))
  have hjb (ξ η : E) : ‖j ξ η‖ ≤
      B * (frequencyDifferenceMajorant (ξ - η) * ‖v η‖) := by
    have hp : (1 + ‖ξ - η‖) ^ (n + 1) *
        (euclideanSobolevWeight (m : ℝ) ξ * ‖k ξ η‖) ≤ B := by
      calc
        _ ≤ (1 + ‖ξ - η‖) ^ (n + 1) * ((1 + ‖ξ‖) ^ m * ‖k ξ η‖) := by
          gcongr
          exact euclideanSobolevWeight_nat_le_one_add_norm_pow m ξ
        _ = (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) * ‖k ξ η‖ := by ring
        _ ≤ B := hb ξ η
    have hh := le_physicalTailMajorant ξ η hp
    simpa only [j, norm_smul, Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,
      mul_assoc] using mul_le_mul_of_nonneg_right hh (norm_nonneg (v η))
  obtain ⟨_, _, hn⟩ := physicalTail_integral_memLp_bound j hj (fun η ↦ ‖v η‖)
    v.continuous.norm.stronglyMeasurable (fun _ ↦ norm_nonneg _) v.integrable.norm
    (v.memLp 2 volume).norm hB hjb
  have he (ξ : E) : (∫ η, j ξ η) = euclideanSobolevWeight (m : ℝ) ξ •
      (WithLp.toLp 2 ((𝓕 w) ξ) : V) := by
    rw [hw]
    change (∫ η, j ξ η) = euclideanSobolevWeight (m : ℝ) ξ •
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm (∫ η, k ξ η • (𝓕 f) η)
    rw [← (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.integral_comp_comm]
    simp only [j, integral_smul, v]
    rfl
  simp_rw [he] at hn
  rw [frequencyKernel_eLpNorm_schwartz_fourier, eLpNorm_norm _ v.continuous.aestronglyMeasurable] at hn
  have hf : (eLpNorm v 2 volume).toReal = ‖schwartzVectorToLp f‖ := by
    change (eLpNorm (fun ξ ↦ (WithLp.toLp 2 ((𝓕 f) ξ) : V)) 2 volume).toReal = _
    simpa only [euclideanSobolevWeight_zero, one_smul, vectorFourierSobolevNorm_zero]
      using frequencyKernel_eLpNorm_schwartz_fourier 0 f
  rwa [hf] at hn

/-- A weighted scalar physical Fourier kernel gives an all-L² vector
Sobolev bound for the SAME bounded operator realizing its literal Schwartz
action. The constant precedes the kernel, its budget and the operator.

The forward producer is `bounded_crossQuantization_schwartz_fourier_action`
together with `exists_crossQuantizationFourierKernel_weighted_decay`.
The endpoint also applies independently to a proved adjoint Fourier action;
no adjoint identification is assumed here. The physical normalization is
handled by `normalizedCrossFourierKernel`, and output membership follows
from the existing compact-smooth extension (`app:ch_regular:eq:chain-tail`). -/
theorem exists_channelFourierKernel_sobolev_constant (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : E → E → ℂ),
      StronglyMeasurable (Function.uncurry k) → ∀ B : ℝ, 0 ≤ B →
      (∀ ξ η, (1 + ‖ξ‖) ^ m * (1 + ‖ξ - η‖) ^ (n + 1) * ‖k ξ η‖ ≤ B) →
      ∀ T : H →L[ℂ] H,
      (∀ f : SchwartzMap E (Fin r → ℂ), ∃ w : SchwartzMap E (Fin r → ℂ),
        T ((toEuclideanSchwartz f).toLp 2) =ᵐ[volume]
          (fun x ↦ WithLp.toLp 2 (w x)) ∧
        ∀ ξ, channelFourierTransform w ξ =
          ∫ η, k ξ η • channelFourierTransform f η) →
      ∀ u : H, MemVectorFourierSobolev (m : ℝ) (T u) ∧
        vectorFourierSobolevNorm (m : ℝ) (T u) ≤ C * B * ‖u‖ := by
  let S := physicalTailSchurConstant n
  have hS : 0 ≤ S := physicalTailSchurConstant_nonneg
  let A := (2 * Real.pi) ^ n
  have hA : 0 ≤ A := by positivity
  refine ⟨(r : ℝ) * r * (S * A), by positivity, ?_⟩
  intro k hk B hB hb T hT u
  have htest (f : SchwartzMap E (Fin r → ℂ)) :
      MemVectorFourierSobolev (m : ℝ) (T (schwartzVectorToLp f)) ∧
      vectorFourierSobolevNorm (m : ℝ) (T (schwartzVectorToLp f)) ≤
        (S * A * B) * ‖schwartzVectorToLp f‖ := by
    obtain ⟨w, hw, hF⟩ := hT f
    have he : T (schwartzVectorToLp f) = schwartzVectorToLp w := by
      rw [schwartzVectorToLp_eq_toEuclideanSchwartz_toLp]
      exact Lp.ext (hw.trans (schwartzVectorToLp_ae w).symm)
    rw [he]
    refine ⟨frequencyKernel_schwartz_memSobolev _ w, ?_⟩
    have hn := fourierKernel_schwartz_sobolev_bound m (normalizedCrossFourierKernel k)
      (stronglyMeasurable_normalizedCrossFourierKernel k hk) (mul_nonneg hA hB)
      (normalizedCrossFourierKernel_weighted_bound m k hb) f w
      (fourier_action_of_channelFourier_action k f w hF)
    simpa only [S, A, mul_assoc] using hn
  have hu : MemVectorFourierSobolev (0 : ℝ) u := fun _ ↦ memFourierSobolev_zero _
  have h := graph_vector_bound_of_compactSmooth T 0 (m : ℝ) (S * A * B) 0
    (by positivity) le_rfl (fun v ↦ by
      simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, zero_mul, add_zero,
        schwartzVectorToLp_graphTestToSchwartz] using htest (graphTestToSchwartz v)) u
    (by simpa only [Nat.cast_zero] using hu)
  simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, zero_mul, add_zero,
    mul_assoc] using h

end JanetCartan.ArbitraryAccuracy.FiniteChains.CrossQuantization
