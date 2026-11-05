module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.SelectedIncidenceGap
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Phase.Bounds
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalIncidenceTemplate

/-!
# The original signed parameter cutoffs before source selection

The exact signed stationary family supplies the conic capture field. Apply the
checked cutoff-and-gap producer once to each original sector, SOURCE sign and
patch. These cutoffs precede the final contraction of the one source reference;
no regular family, physical source window, mask, phase or inverse is changed.
The common finite minimum is the actual input to the original graph-and-frame
source interval and hence to the whole-source retarded application.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalIncidence
open PhysicalSeed PhysicalInitialization

/-- The original physical source ball is nonempty before any inverse choice. -/
theorem original_source_nonempty {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    (OriginalProtected.Xsrc hn a).Nonempty :=
  ⟨0,mem_closedBall_self (OriginalProtected.sourceRadius_pos hn).le⟩

/-- A single band for the SAME full source phase on the original physical
source ball and all independent label/covector cells, in every original sector
coordinate system. Its coefficient tolerance is chosen before the regular
inverse or the final source contraction. -/
theorem exists_original_whole_source_gradient_band {d : ℕ}
    (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn) :
    let T := OriginalBoundary.T hn a
    ∃ wholeLo wholeHi δWhole : ℝ, 0 < wholeLo ∧ wholeLo < wholeHi ∧
      0 < δWhole ∧ δWhole ≤ T.family.threshold ∧
      ∀ Q : {Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) //
        ContDiffOn ℝ ∞ Q (ball 0 (OriginalBoundary.R hn)) ∧
        cNorm (closedBall (0 : Euclidean (d+1)) T.data.localReference.stateRadius) 6
          (Q-fun _ ↦ cubeStress (d+1)) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean (d+1)) T.data.localReference.stateRadius) 6
        (Q.1-fun _ ↦ cubeStress (d+1)) < δWhole →
      ∀ index : Fin (d+1), ∀ y : Euclidean (d+1),
        (CompatibleResponse.primaryCoordinateChange index).symm y ∈ OriginalProtected.Xsrc hn a →
      ∀ b ∈ OriginalProtected.Csrc hn a,
        wholeLo ≤ ‖fderiv ℝ (fun z ↦ T.fullSourcePhaseInCoordinates index Q z b) y‖ ∧
        ‖fderiv ℝ (fun z ↦ T.fullSourcePhaseInCoordinates index Q z b) y‖ ≤ wholeHi := by
  intro T
  have hd := OriginalProtected.source_domains hn a
  obtain ⟨lo,hi,δ,hlo,hhi,hδ,hδT,hband⟩ :=
    ResponsePrimarySources.exists_fullPhase_differential_bounds T (hd.1.prod hd.2.1) hd.2.2.2.1
  refine ⟨lo,hi,δ,hlo,hhi,hδ,hδT,?_⟩
  intro Q hQ index y hy b hb
  have hpoint : ((CompatibleResponse.primaryCoordinateChange index).symm y,b) ∈
      OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a := ⟨hy,hb⟩
  have hsource : OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a ⊆
      LeadingWave.FullModulation.domain T := hd.2.2.2.1
  have hdomainFull : ((CompatibleResponse.primaryCoordinateChange index).symm y,b) ∈
      LeadingWave.FullModulation.domain T :=
    hsource (a := ((CompatibleResponse.primaryCoordinateChange index).symm y,b)) hpoint
  have hdomain : ((CompatibleResponse.primaryCoordinateChange index).symm y,b.2) ∈
      LeadingWave.FullModulation.phaseDomain T := hdomainFull
  have he : ‖fderiv ℝ (fun z ↦ T.fullSourcePhaseInCoordinates index Q z b) y‖ =
      ‖fderiv ℝ (fun z ↦ LeadingWave.FullModulation.phase T Q z b.2)
        ((CompatibleResponse.primaryCoordinateChange index).symm y)‖ := by
    rw [← (InnerProductSpace.toDual ℝ (Euclidean (d+1))).symm.norm_map]
    change ‖gradient (fun z ↦ T.fullSourcePhaseInCoordinates index Q z b) y‖ = _
    rw [T.fullSourcePhaseInCoordinates_gradient index Q (x := y) (c := b) hdomain,
      ResponseTransfer.RetainedFactors.norm_primaryCoordinateChange]
    exact (InnerProductSpace.toDual ℝ (Euclidean (d+1))).symm.norm_map _
  rw [he]
  exact hband Q hQ ((CompatibleResponse.primaryCoordinateChange index).symm y,b) hpoint

/-- A single positive margin controls every original sector, independent source
sign and source patch. The retained factor two leaves the exact inactive
angular gap after graph transport; no mask radius is altered.
Consumer: `OriginalRegular.Graph.source_interval`, then the literal-adjoint
whole-source retarded envelope (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_original_signed_incidence_margin
    {Sect Patch : Type*} [Finite Sect] [Finite Patch]
    (δ gap : Sect → Bool → Patch → ℝ) (δWhole : Patch → ℝ)
    (hδ : ∀ p negative a, 0 < δ p negative a)
    (hgap : ∀ p negative a, 0 < gap p negative a)
    (hWhole : ∀ a, 0 < δWhole a) :
    ∃ γ > (0 : ℝ), (∀ p negative a,
      γ ≤ δ p negative a ∧ 2*γ ≤ gap p negative a) ∧ (∀ a, γ ≤ δWhole a) := by
  let tol : (Sect × (Bool × Patch)) ⊕ Patch → ℝ :=
    Sum.elim (fun q ↦ min (δ q.1 q.2.1 q.2.2) (gap q.1 q.2.1 q.2.2/2)) δWhole
  have ht : ∀ q, (0 : ℝ) < tol q := by
    intro q
    cases q with
    | inl q => exact lt_min (hδ q.1 q.2.1 q.2.2) (half_pos (hgap q.1 q.2.1 q.2.2))
    | inr a => exact hWhole a
  obtain ⟨γ,hγ,hsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : (Sect × (Bool × Patch)) ⊕ Patch ↦ (0 : ℝ)) (y := tol) ht
  refine ⟨γ,hγ,?_,?_⟩
  · intro p negative a
    have hb : γ < min (δ p negative a) (gap p negative a/2) := by
      simpa only [zero_add,tol,Sum.elim_inl] using hsmall (Sum.inl (p,(negative,a)))
    exact ⟨(hb.trans_le (min_le_left _ _)).le, by linarith [(hb.trans_le (min_le_right _ _)).le]⟩
  · intro a
    have hb : γ < δWhole a := by
      simpa only [zero_add,tol,Sum.elim_inr] using hsmall (Sum.inr a)
    exact hb.le

/-- The same pre-source margin preserves the original signed inactive gap
against the ACTUAL transported adjoint momentum. This is the final triangle
inequality after the original root-flow estimate, not a bare-frequency
substitution (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem original_signed_gap_of_graph_transport {n : ℕ} {gap γ : ℝ}
    (u ξ momentum : Euclidean n) (hmargin : 2*γ ≤ gap)
    (hgap : gap ≤ dist (NormedSpace.normalize u) (NormedSpace.normalize ξ))
    (htransport : dist (NormedSpace.normalize momentum) (NormedSpace.normalize ξ) ≤ γ) :
    γ ≤ dist (NormedSpace.normalize u) (NormedSpace.normalize momentum) := by
  have htriangle := dist_triangle (NormedSpace.normalize u)
    (NormedSpace.normalize momentum) (NormedSpace.normalize ξ)
  linarith

retain_original_whole_source_band
retain_original_signed_incidence_cutoffs
retain_original_common_incidence_margin

end JanetCartan.PhysicalPrimary.OriginalIncidence
