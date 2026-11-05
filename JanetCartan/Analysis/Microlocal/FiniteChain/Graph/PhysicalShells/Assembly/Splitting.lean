module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.CutoffGeometry.KernelSplitting
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.ConicExtension
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.CompactKernels

/-!
# Smooth physical kernels and their exact high/low splitting

The smoothness needed to add actual output derivatives in
`app:ch_regular:eq:chain-tail` follows from the original conic phase and
compact primitive support. No smoothness outside that support is assumed.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells
open FourierIntegral Noncomparable
variable {n r : ℕ}
set_option synthInstance.maxSize 256

/-- A physical regularized kernel is smooth in both external bases when
its phase is smooth on an open neighborhood of the compact projected
amplitude support. Extension is justified by equality of the literal
integrals, preserving both amplitude positions and normalization
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem contDiff_regularizedJointKernel_of_conicPhase (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : KernelLimits.RegularizedCarriers A mi χA χo)
    {V K : Set (Euclidean n × Euclidean n)}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) V)
    (hs : ∀ u z ξ, A u z ξ ≠ 0 → χA ξ ≠ 0 → (u, ξ) ∈ K)
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ContDiff ℝ ∞ χA) (hc : ContDiff ℝ ∞ χo)
    (hg0 : (0 : Euclidean n) ∉ tsupport χA) :
    ContDiff ℝ ∞ (Function.uncurry
      (KernelLimits.regularizedJointKernel backward S A mi mo χA χo)) := by
  obtain ⟨f, hf, _, _, _, heq⟩ :=
    JanetCartan.NormalComparison.exists_contDiff_localization hV hK hKV hS
  have he : Function.uncurry (KernelLimits.regularizedJointKernel backward S A mi mo χA χo) =
      Function.uncurry (KernelLimits.regularizedJointKernel backward
        (fun u ξ => f (u, ξ)) A mi mo χA χo) := by
    funext p
    apply physicalJointKernel_congr_phase
    intro u z ξ ha hg'
    exact ((heq _ (hs u z ξ ha hg')).eq_of_nhds).symm
  rw [he]
  exact KernelLimits.contDiff_regularizedJointKernel backward _ A mi mo χA χo c
    (fun _ _ _ => hf.contDiffAt) hA hi ho hg hc hg0

/-- Convert the concrete normalized carrier condition to the physical
support condition used for smoothness. This changes neither the physical
phase nor the two-position amplitude (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem physicalBranch_support_of_normalized {ρ : ℝ} (hρ : ρ ≠ 0)
    (A : FullAmplitude n r) (low : Bool) (j : ℕ)
    {K : Set (Euclidean n × Euclidean n)}
    (hs : ∀ ξ ∈ normalizedGraphCarrier ρ low j,
      ∀ z ∈ tsupport (fun z : Euclidean n × Euclidean n => A z.1 z.2 (ρ • ξ)),
      (z.1, ρ • ξ) ∈ K) :
    ∀ u z ξ, A u z ξ ≠ 0 → graphBranchCutoff low j ξ ≠ 0 → (u, ξ) ∈ K := by
  intro u z ξ ha hg
  have hscale : ρ • (ρ⁻¹ • ξ) = ξ := smul_inv_smul₀ hρ ξ
  have hξ := tsupport_rescaled_graphBranchCutoff_subset (n := n) hρ low j
    (subset_tsupport _ (show graphBranchCutoff low j (ρ • (ρ⁻¹ • ξ)) ≠ 0 by
      simpa only [hscale] using hg))
  have hz : (u, z) ∈ tsupport
      (fun b : Euclidean n × Euclidean n => A b.1 b.2 (ρ • (ρ⁻¹ • ξ))) :=
    subset_tsupport _ (by simpa only [Function.mem_support, hscale] using ha)
  simpa only [hscale] using hs _ hξ _ hz

/-- Actual evaluated output derivatives split into the high and low physical
kernels. The two smoothness premises are supplied by
`contDiff_regularizedJointKernel_of_conicPhase`, while cutoff linearity is
proved from primitive integrability (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_physicalGraphCutoff_split (backward : Bool)
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (j k : ℕ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (c : KernelLimits.RegularizedCarriers A mi (graphCutoff j) (outputCutoff k))
    (y : Euclidean n)
    (hs : ∀ low : Bool, ContDiff ℝ ∞ (fun x =>
      KernelLimits.regularizedJointKernel backward S A mi mo
        (graphBranchCutoff low j) (outputCutoff k) x y))
    (m : ℕ) (x : Euclidean n) (v : Fin m → Euclidean n) :
    iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
      (graphCutoff j) (outputCutoff k) t y) x v =
      iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
        (graphBranchCutoff false j) (outputCutoff k) t y) x v +
      iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
        (graphBranchCutoff true j) (outputCutoff k) t y) x v := by
  have he : (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
      (graphCutoff j) (outputCutoff k) t y) =
      (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
        (graphBranchCutoff false j) (outputCutoff k) t y) +
      (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
        (graphBranchCutoff true j) (outputCutoff k) t y) := by
    funext t
    exact regularizedJointKernel_graphCutoff_split backward S A mi mo j k hS hA hi ho c t y
  rw [he, iteratedFDeriv_add ((hs false).of_le (by simp)) ((hs true).of_le (by simp))]
  rfl

/-- In dimension zero the original graph cutoff and all its actual output
derivatives vanish. Positive-dimensional volume summation is unnecessary
in this case (`app:ch_regular:eq:chain-tail`). -/
theorem iteratedFDeriv_physicalGraphKernel_dim_zero (backward : Bool)
    (S : Euclidean 0 → Euclidean 0 → ℝ) (A : FullAmplitude 0 r)
    (mi mo : LocalizerSymbol 0) (j k m : ℕ) (x y : Euclidean 0)
    (v : Fin m → Euclidean 0) :
    iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
      (graphCutoff j) (outputCutoff k) t y) x v = 0 := by
  have hg (ξ : Euclidean 0) : graphCutoff j ξ = 0 := by
    have hh := graphBranchCutoff_dim_zero false j ξ
    have hl := graphBranchCutoff_dim_zero true j ξ
    change highGraphCutoff j ξ = 0 at hh
    change lowGraphCutoff j ξ = 0 at hl
    simp only [graphCutoff, hh, hl, add_zero]
  have hk : (fun t => KernelLimits.regularizedJointKernel backward S A mi mo
      (graphCutoff j) (outputCutoff k) t y) = fun _ => 0 := by
    funext t
    simp [KernelLimits.regularizedJointKernel, KernelLimits.regularizedJointIntegrand,
      KernelLimits.regularizedJointAmplitude, hg]
  simp only [hk, iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply]

end JanetCartan.FiniteChain.Graph.PhysicalShells
