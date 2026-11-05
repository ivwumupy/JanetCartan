module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Sobolev

/-!
# Physical test actions of the Cartesian graph kernels

The measure-preserving coordinate hypothesis here is purely geometric: it
specifies the exact Euclidean volume used by the literal graph integral. No
convergence or kernel estimate is part of it. The input swap matches the
existing Cartesian jet completion (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral Retarded.KernelSobolev AmplitudeBound
open JanetCartan.RetardedSobolev.Spaces
variable {n r d : ℕ}
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The input coordinate swap for the graph kernel, from the Cartesian L²
space to the actual Euclidean base (`app:ch_regular:eq:chain-tail`). -/
def graphInputCoordinates (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n) :
    ((Fin d → ℝ) × ℝ) ≃L[ℝ] Euclidean n :=
  (ContinuousLinearEquiv.prodComm ℝ (Fin d → ℝ) ℝ).trans J

/-- Exact physical action of each concrete regularized matrix entry. This
keeps the scalar Fourier normalization inside the actual joint kernel
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem kernelIntegral_supportedJointKernelEntry_physical
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (μ : Measure ((Fin d → ℝ) × ℝ))
    (hJ : MeasurePreserving (graphInputCoordinates J) μ volume)
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo ψ : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo)
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo)
    (hg0 : (0 : Euclidean n) ∉ tsupport χA)
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ) (a b : Fin r)
    (f : (ℝ × (Fin d → ℝ)) → ℂ) (x : ℝ × (Fin d → ℝ)) :
    kernelIntegral (supportedJointKernelEntry J backward S A mi mo χA χo ψ
      c hS hA hi ho hg hc hg0 hψ hsψ a b) μ f x =
      (ψ (J x) : ℂ) * ∫ y, regularizedJointKernel backward S A mi mo χA χo
        (J x) y a b * f (J.symm y) := by
  have he := hJ.integral_comp (graphInputCoordinates J).toHomeomorph.measurableEmbedding
    (fun y => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo χA χo
      (J x) y a b * f (J.symm y))
  simpa only [kernelIntegral, supportedJointKernelEntry, graphInputCoordinates,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodComm_apply,
    ContinuousLinearEquiv.symm_apply_apply, Prod.swap, mul_assoc, integral_const_mul] using he

/-- Summing actual matrix entries commutes with a fixed output cutoff. The
matrix Frobenius majorant is retained as the summability hypothesis supplied
by `jc-graph-factor-kernel-estimates` (`app:ch_regular:eq:chain-tail`). -/
theorem tsum_cutJointKernel_entry (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ)
    (C : ℕ × ℕ → ℝ) (hs : Summable C)
    (hb : ∀ j k x y, ‖regularizedJointKernel backward S A mi mo (χA j) (χo k) x y‖ ≤ C (j,k))
    (ψ : Euclidean n → ℝ) (x y : Euclidean n) (a b : Fin r) :
    (∑' p : ℕ × ℕ, (ψ x : ℂ) * regularizedJointKernel backward S A mi mo
      (χA p.1) (χo p.2) x y a b) =
      (ψ x : ℂ) * (∑' p : ℕ × ℕ, regularizedJointKernel backward S A mi mo
        (χA p.1) (χo p.2) x y) a b := by
  rw [tsum_mul_left]
  congr 1
  exact ((matrixEntryEvaluation a b).map_tsum
    (hs.of_norm_bounded (fun p => hb p.1 p.2 x y))).symm

end JanetCartan.FiniteChain.Graph.KernelLimits
