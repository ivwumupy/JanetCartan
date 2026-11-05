module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Identities
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth phase extensions on the actual integration support

A conic phase need only be smooth on its original open chart domain. The shared
smooth-localization theorem gives an extension agreeing near the compact
carrier, so all primitive phase derivatives and the actual cutoff kernels are
unchanged. This supplies the global smoothness needed by the normalized
estimates in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open FourierIntegral
variable {n r : ℕ}

/-- A phase smooth on its actual conic domain admits a global smooth extension
with every derivative preserved near the compact integration carrier. Its
normalized kernel equals the original one for both orientations and every
output base, input base, and output cutoff. Consumer: application of the global
normalized estimates in `app:ch_regular:eq:chain-tail`. -/
theorem exists_normalizedPhaseExtension
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (χA : Euclidean n → ℝ) (ρ : ℝ)
    {U K : Set (Euclidean n × Euclidean n)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) U)
    (hcarrier : ∀ u z ξ, A u z (ρ • ξ) ≠ 0 → χA (ρ • ξ) ≠ 0 → (u, ξ) ∈ K) :
    ∃ ψ : Euclidean n → Euclidean n → ℝ,
      ContDiff ℝ ∞ (Function.uncurry ψ) ∧
      (∀ p ∈ K, Function.uncurry ψ =ᶠ[𝓝 p] Function.uncurry φ) ∧
      (∀ p ∈ K, ∀ m, iteratedFDeriv ℝ m (Function.uncurry ψ) p =
        iteratedFDeriv ℝ m (Function.uncurry φ) p) ∧
      ∀ (backward : Bool) (mi mo : LocalizerSymbol n) (χo : Euclidean n → ℝ)
        (x y : Euclidean n),
        KernelEstimates.regularizedJointKernel backward ρ φ A mi mo χA χo x y =
          KernelEstimates.regularizedJointKernel backward ρ ψ A mi mo χA χo x y := by
  obtain ⟨f, hf, _, _, _, heq⟩ :=
    JanetCartan.NormalComparison.exists_contDiff_localization hU hK hKU hφ
  refine ⟨fun u ξ => f (u, ξ), hf, heq, ?_, ?_⟩
  · intro p hp m
    exact ((heq p hp).iteratedFDeriv ℝ m).eq_of_nhds
  · intro backward mi mo χo x y
    apply normalizedJointKernel_congr_phase backward ρ φ (fun u ξ => f (u, ξ))
      A mi mo χA χo x y
    intro u z ξ hA hg
    exact ((heq (u, ξ) (hcarrier u z ξ hA hg)).eq_of_nhds).symm

/-- Smoothness of the extension's joint phase is global, as required by
`BufferedDecay.exists_buffered_comparable_kernel_constants` and the shell
derivative formula (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_jointPhase_of_contDiff_phase (backward : Bool)
    (φ : Euclidean n → Euclidean n → ℝ)
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) (x y : Euclidean n) :
    ContDiff ℝ ∞ (jointPhase backward φ x y) := by
  have hs : ContDiff ℝ ∞ (fun p : JointVariables (Euclidean n) => φ p.1.1 p.2.1) :=
    hφ.comp (f := fun p : JointVariables (Euclidean n) => (p.1.1, p.2.1)) (by fun_prop)
  change ContDiff ℝ ∞ (fun p => jointPhase backward φ x y p)
  cases backward
  · simp only [jointPhase, Bool.false_eq_true, ite_false, forwardPhase]
    exact ((hs.sub (contDiff_fst.snd.inner ℝ contDiff_snd.fst)).add
      ((contDiff_fst.snd.sub contDiff_const).inner ℝ contDiff_snd.snd.fst)).add
        ((contDiff_const.sub contDiff_fst.fst).inner ℝ contDiff_snd.snd.snd)
  · simp only [jointPhase, ite_true, reversePhase]
    exact (((contDiff_fst.snd.inner ℝ contDiff_snd.fst).sub hs).add
      ((contDiff_fst.fst.sub contDiff_const).inner ℝ contDiff_snd.snd.fst)).add
        ((contDiff_const.sub contDiff_fst.snd).inner ℝ contDiff_snd.snd.snd)

end JanetCartan.FiniteChain.Graph.PhysicalShells
