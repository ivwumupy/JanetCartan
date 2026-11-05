module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.CompactOperator
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.CompactKernel

/-!
# Differentiation under the actual compact-frequency integral

The finite-cutoff Fourier normalization in
`app:ch_regular_base:eq:energy-complete-residual` is inherited from
`KernelIdentification.integral_cutFixedTimeFourier`.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB FourierIntegral.GraphDifferentiation
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FiniteChain.Retarded.KernelDecay
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "FV" => Fin q → ℂ

/-- The full physical operator passes through the actual finite-frequency
integral, at fixed source time and spectral covector. Consumer: the columnwise
two-term cancellation in `app:ch_regular_base:eq:energy-complete-residual`.
No differentiated-action premise or extra Fourier normalization is introduced. -/
theorem firstOrderApply_cutFixedTimeFourier (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (β θ : E → ℂ)
    (v : SchwartzMap E FV)
    (hΨ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (hθ : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (C : E → Fin (d + 1) → FV →L[ℂ] FV) (D : E → FV →L[ℂ] FV)
    (s : ℝ) (x : E) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)) x =
      ((2 * Real.pi)^(d + 1) : ℂ)⁻¹ • ∫ ξ,
        firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
          (fun y ↦ cutFixedTimeFourierIntegrand Ψ b β θ v (y 0) s (spatialPart y) ξ) x := by
  let f : E × E → FV := fun p ↦
    cutFixedTimeFourierIntegrand Ψ b β θ v (p.1 0) s (spatialPart p.1) p.2
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_cutFixedTimeFourierIntegrand Ψ b β θ v hΨ hb hβ hθ).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hs : ∀ y ξ, ξ ∉ tsupport θ → f (y,ξ) = 0 := by
    intro y ξ hξ
    simp [f, cutFixedTimeFourierIntegrand, image_eq_zero_of_notMem_tsupport hξ]
  have he (y : E) : cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y) =
      ((2 * Real.pi)^(d + 1) : ℂ)⁻¹ • ∫ ξ, f (y,ξ) := by
    exact (integral_cutFixedTimeFourier Ψ b β θ v (y 0) s (spatialPart y)
      (hΨ.continuous.comp (f := fun η ↦ ((y 0,s),(spatialPart y,η)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
      (hb.continuous.comp (f := fun η ↦ ((y 0,s),(spatialPart y,η)))
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
      hβ.continuous hθ.continuous hθcs).symm
  simp_rw [he]
  rw [firstOrderApply_const_smul _ _
    ((contDiff_integral_commonCarrier hf hθcs hs).differentiable (by simp) x),
    firstOrderApply_compactIntegral hf hθcs hs C D x]
end JanetCartan.CharacteristicTransport.KernelDifferentiation
