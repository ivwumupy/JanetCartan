module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.ShellJets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Assembly.Transport

/-!
# Conic continuation of the constructed buffered two-time phase

This assembles the local primitive published by
`BufferedKernel.exists_buffered_physical_pencil_kernel`, without changing its
root, flow or inverse chart. One smaller buffer fixes the section, angular
margins, global continuous auxiliary, conic mixed and averaged geometry, and
normalized phase jets. All compact inclusions are proved for concrete sets.

`phase_eikonal_on_buffer` retains both time identities under exactly the
positive-scaling property of the SAME root from `exists_pencilRoot_domain`.
The parent must retain that producer's conclusion through its root witness;
this module does not choose a replacement root. The physical and covector
gradients are `gradient_phase_position` and `gradient_phase_covector`.

Consumer: the unbounded elapsed graph chart in
`app:ch_regular_base:lem:retarded-kernel`, built from
`app:ch_regular_base:lem:characteristic-kernel` in `paper-v2.tex`.
Coefficient-family estimates and the sector theorem are separate obligations.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral EvolutionIntegral NormalComparison WholeImageGeometry
variable {d : ℕ}

/-- Assemble the actual conic phase from the buffered local primitive.
The smaller radius stays inside the original diagonal box. The same fixed
section is used by every conclusion; constants precede all elapsed times,
positive radial scales and phase jets. The generic jet constant even precedes
the local function `F`, so specialization to the original smooth phase adds
no analytic premise. For supported graphs use
`elapsedGraph_eq_on_buffered_masks`; for both time identities use
`phase_eikonal_on_buffer` with the SAME root's positive-scaling property.
Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem exists_buffered_conicPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {ε₀ δ : ℝ}
    (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hsmall : 2 * ε₀ < ‖z.2.2‖)
    (hbuffer : closedBall (z.1, z) (2 * ε₀) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hdiag : ∀ w ∈ ball z.1 δ ×ˢ ball z.2 δ,
      twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ)
    (hnear : ∀ q ∈ closedBall (z.1, z) (2 * ε₀), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2) :
    ∃ ε > (0 : ℝ), ε ≤ ε₀ ∧ ε ≤ δ ∧
    ∃ ℓ : Euclidean d →L[ℝ] ℝ, ℓ z.2.2 = 1 ∧
      z.2.2 ∈ angularCone ℓ z.2.2 (ε / 2) ∧
      IsOpen (angularCone ℓ z.2.2 ε) ∧ Convex ℝ (angularCone ℓ z.2.2 ε) ∧
      (0 : Euclidean d) ∉ angularCone ℓ z.2.2 ε ∧
      closure (angularCone ℓ z.2.2 (ε / 2)) \ {0} ⊆ angularCone ℓ z.2.2 ε ∧
      ContDiffOn ℝ ∞ (phase ℓ C) (domain ℓ C.target) ∧
      (∀ (q : TwoTimePoint (Euclidean d)) (a : ℝ), 0 < a →
        phase ℓ C (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = a * phase ℓ C q) ∧
      (∀ q ∈ localPatch (bufferedBase z ε) (ball z.2.2 (2 * ε)) ∩
          domain ℓ (localPatch (bufferedBase z ε) (ball z.2.2 (2 * ε))),
        phase ℓ C =ᶠ[𝓝 q] twoTimePhase C) ∧
      (∀ x ∈ elapsedPhysicalBox z ε, ∀ η ∈ angularCone ℓ z.2.2 ε,
        phase ℓ C (x 0, (x 0, (spatialPart x, η))) = ⟪spatialPart x, η⟫_ℝ) ∧
      (∀ a > (0 : ℝ), ∀ b : ℝ, ∀ n : ℕ, ∃ A > (0 : ℝ),
        ∀ F : TwoTimePoint (Euclidean d) → ℝ, ContDiffOn ℝ ∞ F C.target →
        ∀ R > (0 : ℝ),
          cNorm (bufferedJetSet ℓ z ε a b) n
            (SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase R
              (curriedExtend ℓ F))) ≤ A * cNorm (closedBall (z.1, z) (2 * ε)) n F ∧
          ∀ k ≤ n, ∀ p ∈ bufferedJetSet ℓ z ε a b,
            ‖iteratedFDeriv ℝ k (SymbolBudgets.jointPhase
              (SymbolBudgets.normalizedTwoTimePhase R (curriedExtend ℓ F))) p‖ ≤
                A * cNorm (closedBall (z.1, z) (2 * ε)) n F) ∧
      (∀ T ≥ (0 : ℝ), ∀ a > (0 : ℝ), ∀ b : ℝ, ∀ n : ℕ,
        ∃ A > (0 : ℝ), ∃ B ≥ (0 : ℝ),
          ∀ F : TwoTimePoint (Euclidean d) → ℝ, ContDiffOn ℝ ∞ F C.target →
          ∀ R > (0 : ℝ), ∀ r ∈ Icc 0 ε,
          ∀ p ∈ elapsedPhysicalBox z ε ×ˢ
              normalizedSourceBand (fullAngularCone ℓ z.2.2 ε T) R a b,
          ∀ k ≤ n,
            ‖iteratedFDeriv ℝ k (Function.uncurry (normalizedPhase R
              (elapsedPhase (curriedExtend ℓ F) r))) p‖ ≤
                B + A * cNorm (closedBall (z.1, z) (2 * ε)) n F) ∧
      (∃ G : TwoTimePoint (Euclidean d) → ℝ,
        Continuous G ∧ ContDiffOn ℝ ∞ G {q | q.2.2.2 ≠ 0} ∧
        (∀ (q : TwoTimePoint (Euclidean d)) (a : ℝ), 0 < a →
          G (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = a * G q) ∧
        ∀ q ∈ domain ℓ (closedBall (z.1, z) (2 * ε)), G =ᶠ[𝓝 q] phase ℓ C) ∧
      ∃ κ > 0, ∃ M > 0, ∃ L > 0,
        (∀ r ∈ Icc 0 ε, ∀ Y : Set (Euclidean (d + 1)),
          SupportedPhaseRegularity (elapsedPhase (curriedPhase ℓ C) r)
            ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) ∧
          SupportedPhaseHomogeneity (elapsedPhase (curriedPhase ℓ C) r)
            ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε)) ∧
          SupportedMixedInvertibility (elapsedPhase (curriedPhase ℓ C) r)
            ((elapsedPhysicalBox z ε ×ˢ Y) ×ˢ (spatialPart ⁻¹' angularCone ℓ z.2.2 ε))) ∧
        ∀ r ∈ Icc 0 ε, ∀ x ∈ elapsedPhysicalBox z ε,
          (∀ η ∈ angularCone ℓ z.2.2 ε,
            ‖mixedPhaseMatrix (curriedPhase ℓ C (x 0) (x 0 - r)) (spatialPart x) η - 1‖ ≤ 1 / 2 ∧
            ‖fun j : Fin d ↦ partialDeriv
              (elapsedTimeDerivative (curriedPhase ℓ C) r (x 0, spatialPart x)) η j‖ ≤ L) ∧
          (∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
            IsUnit (mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det ∧
            κ ≤ |(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ).det| ∧
            ‖(mixedPhaseMatrix (elapsedPhase (curriedPhase ℓ C) r) x ξ)⁻¹‖ ≤ M) ∧
          ∀ y ∈ elapsedPhysicalBox z ε,
            InjOn (averagedGradient (elapsedPhase (curriedPhase ℓ C) r) x y)
              (spatialPart ⁻¹' angularCone ℓ z.2.2 ε) ∧
            ∀ ξ : Euclidean (d + 1), spatialPart ξ ∈ angularCone ℓ z.2.2 ε →
              κ ≤ |(averagedJacobian (elapsedPhase (curriedPhase ℓ C) r) x y ξ).det| := by
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hsub : closedBall (z.1, z) (2 * ε) ⊆ closedBall (z.1, z) (2 * ε₀) :=
    closedBall_subset_closedBall (by linarith)
  have hbuffer' := hsub.trans hbuffer
  have hnear' := fun q hq ↦ hnear q (hsub hq)
  obtain ⟨ℓ, hℓ, hz, hD, hcD, h0, hmargin, κ, hκ, M, hM, L, hL, hreg, hgeom⟩ :=
    exists_angular_elapsed_geometry C hε (by linarith) hbuffer' hs hdiff hnear'
  refine ⟨ε, hε, hεε₀, hεδ, ℓ, hℓ, hz, hD, hcD, h0, hmargin,
    contDiffOn_phase ℓ hs, fun q _ ha ↦ extend_smul ℓ (twoTimePhase C) q ha,
    ?_, ?_, ?_, ?_, ?_, κ, hκ, M, hM, L, hL, hreg, ?_⟩
  · intro q hq
    exact phase_eventuallyEq_on_overlap ℓ hdiff isOpen_ball isOpen_ball (convex_ball _ _)
      ((localPatch_bufferedBase_subset z ε).trans hbuffer') hq
  · intro x hx η hη
    exact phase_diagonal_on_buffer ℓ C hεδ hdiag hx hη
  · intro a ha b n
    exact exists_buffered_normalized_jet_bound ℓ hε.le ha C.open_target hbuffer' n
  · intro T hT a ha b n
    exact exists_normalizedShell_jet_bound ℓ hε.le hT ha C.open_target hbuffer' n
  · exact exists_continuous_conicPhase_extension ℓ C (isCompact_closedBall _ _) hbuffer' hs
  · intro r hr x hx
    obtain ⟨ht, hm, hg⟩ := hgeom r hr x hx
    exact ⟨fun η hη ↦
      ⟨norm_mixedPhaseMatrix_phase_sub_one_le ℓ hε hbuffer' hs hdiff hnear' hr hx hη,
        ht η hη⟩, hm, hg⟩

end JanetCartan.RegularSector.Characteristic.ConicPhase
