module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.HilbertPlancherel.Radial
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.HilbertPlancherel.Coordinates

/-!
# Hilbert-valued parameter Plancherel

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, radial Hilbert-valued Plancherel
and the measure-preserving coordinate comparison give weighted membership
and the parameter-jet bound on the literal carrier product measure. All three
carrier directions and the exact `2π` normalization are retained; no derivative
acts on the transverse Hilbert fiber.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

set_option maxHeartbeats 1600000 in
/-- Compact smooth Hilbert-valued parameter representatives have weighted
Fourier L² membership and a bound by their parameter jets. This supplies the
parameter Plancherel step of `app:ch_background:eq:bg-density-adjoint` for
`app:ch_background:prop:bg-adjoint`, on the literal product measure. -/
theorem exists_iteratedParameterFourier_compact_bound {n : ℕ} (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : IteratedCarrierL2 n)
      (φ : CarrierParameter → TransverseL2 n),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → (g =ᵐ[volume.prod volume] φ) →
      MemLp (fun z : CarrierParameter => initialWeight s (z, (0 : Euclidean (n - 1))) •
        iteratedParameterFourier n g z) 2 (volume.prod volume) ∧
      lpNorm (fun z : CarrierParameter => initialWeight s (z, (0 : Euclidean (n - 1))) •
        iteratedParameterFourier n g z) 2 (volume.prod volume) ≤
        B * (∑ k ∈ Finset.range (s + 1),
          lpNorm (iteratedFDeriv ℝ k φ) 2 (volume.prod volume)) := by
  obtain ⟨B, hB, hbound⟩ := exists_parameterFourierIntegral_compact_bound (n := n) s
  refine ⟨B, hB, ?_⟩
  intro g φ hφ hc hg
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Euclidean 2)
  let ψ : ParameterSpace → TransverseL2 n := φ ∘ e
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.contDiff
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph e.toHomeomorph
  obtain ⟨hm, hb⟩ := hbound ψ hψ hcψ
  obtain ⟨hm', he⟩ := parameterWeight_fourierIntegral_compact s g φ hφ.continuous hc hg hm
  refine ⟨hm', he.le.trans (hb.trans ?_)⟩
  apply mul_le_mul_of_nonneg_left _ hB
  apply Finset.sum_le_sum
  intro k _
  exact lpNorm_parameterSection_iteratedFDeriv_le φ hφ hc k

end JanetCartan.ContinuumAdjoint.DensityMultiplier
