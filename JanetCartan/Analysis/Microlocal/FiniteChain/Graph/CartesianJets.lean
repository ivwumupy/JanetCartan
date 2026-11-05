module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.CartesianJets.Summation

/-!
# Cartesian output jets of the literal regularized graph kernels

This is the transfer required for `app:ch_regular:eq:chain-tail`. The actual
producer of the physical unit-direction bounds is
`jc-graph-factor-physical-shell-bridge`; the implication here needs no wait on
that producer. Smoothness of `regularizedJointKernel` is derived from its
primitive phase, amplitude, masks and regularizers, in both orientations.

The conclusion supplies precisely the nonnegative summable `C` and `hb` inputs
of `KernelLimits.exists_jointKernel_physical_extension`. Its total sum is an
explicit finite combination of the physical derivative sums. The theorem
`tsum_jetMajorant_le_grades` retains the graded physical powers and the entire
accuracy factor, with constants depending only on the fixed cutoff, coordinate
map and Sobolev order. The parent must still supply the physical bounds, choose
the plateau and physical measures, and assemble the operator estimate.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
open Set
namespace JanetCartan.FiniteChain.Graph.CartesianJets
open FourierIntegral KernelLimits JanetCartan.RetardedSobolev.Spaces
variable {n r d m : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Transfer the physical shell estimates to the literal Cartesian output jets
of the regularized joint kernel. All channels and all jets of order at most
`m` share the displayed explicit majorant; no smoothness of the integral, jet
bound, or operator estimate is assumed. Consumer: the `C`, `hC`, `hs`, `hb`
arguments of `KernelLimits.exists_jointKernel_physical_extension`
(`app:ch_regular:eq:chain-tail`). -/
theorem summable_regularizedJointKernel_jet_majorant
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean n)
    (backward : Bool) (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : ℕ → Euclidean n → ℝ) (ψ : Euclidean n → ℝ)
    (c : ∀ j k, RegularizedCarriers A mi (χA j) (χo k))
    (hS : ∀ u ξ, ξ ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (u, ξ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi) (ho : ContDiff ℝ ∞ mo)
    (hg : ∀ j, ContDiff ℝ ∞ (χA j)) (hc : ∀ k, ContDiff ℝ ∞ (χo k))
    (hg0 : ∀ j, (0 : Euclidean n) ∉ tsupport (χA j))
    (hψ : ContDiff ℝ ∞ ψ) (hsψ : HasCompactSupport ψ)
    (B : ℕ → (ℕ × ℕ) → ℝ)
    (hB : ∀ l ≤ m, ∀ α, 0 ≤ B l α) (hs : ∀ l ≤ m, Summable (B l))
    (hb : ∀ j k x, x ∈ tsupport ψ → ∀ y, ∀ l ≤ m,
      ∀ v : Fin l → Euclidean n, (∀ a, ‖v a‖ ≤ 1) →
        ‖iteratedFDeriv ℝ l (fun z =>
          regularizedJointKernel backward S A mi mo (χA j) (χo k) z y) x v‖ ≤ B l (j, k)) :
    let C := fun α => jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l => B l α) m
    (∀ α, 0 ≤ C α) ∧ Summable C ∧
      (∑' α, C α) = jetMajorant J (cutoffDerivativeProfile hψ hsψ) (fun l => ∑' α, B l α) m ∧
      ∀ j k (a b : Fin r) (i : JetIndex d m) p (y : (Fin d → ℝ) × ℝ),
        ‖jet i (fun x => (ψ (J x) : ℂ) * regularizedJointKernel backward S A mi mo
          (χA j) (χo k) (J x) (J (y.2, y.1)) a b) p‖ ≤ C (j, k) := by
  let K := fun α : ℕ × ℕ => regularizedJointKernel backward S A mi mo (χA α.1) (χo α.2)
  have hK : ∀ α, ContDiff ℝ ∞ (Function.uncurry (K α)) := fun α =>
    contDiff_regularizedJointKernel backward S A mi mo (χA α.1) (χo α.2)
      (c α.1 α.2) hS hA hi ho (hg α.1) (hc α.2) (hg0 α.1)
  obtain ⟨hn, hsum, htotal, hjet⟩ := summable_cutMatrixEntry_jet_majorant J hψ hsψ K hK
    B hB hs (fun α => hb α.1 α.2)
  exact ⟨hn, hsum, htotal, fun j k => hjet (j, k)⟩

end JanetCartan.FiniteChain.Graph.CartesianJets
