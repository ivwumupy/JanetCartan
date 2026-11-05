module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ConicInvariance
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ExtendedPhaseCover

/-!
# Propagation of the actual comparison graphs

The conic invariance step of `app:ch_regular:thm:no-return`. The compact
covector set needed for uniqueness is constructed from the complete segment
and the actual comparison gradient. The globally smooth derivative used in
that estimate is a representative agreeing with the actual Hessian on the
physical ball. Thus neither a covector-buffer hypothesis nor preservation is
imposed on the segment beyond its staying in the punctured symbol domain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.ProtectedFlow
open HamiltonPhase PhaseCover ActualCarriers

/-- Every complete segment of the literal punctured-domain Hamiltonian stays
on the same positive conic comparison graph. The interval may be traversed in
either orientation, since the initial time is arbitrary. Compact auxiliary
sets and the defect estimate are constructed, not assumed
(`app:ch_regular:thm:no-return`). -/
theorem comparisonChart_preserves_complete_segment {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)}
    (hdomain : H.domain = normalizedSymbolDomain (univ : Set (Euclidean n)))
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    {g : ComparisonGeometry (Euclidean n)} (C : ComparisonChart H g)
    {η : ℝ × g.tangentSpace} (hη : η ∈ g.parameters)
    {x p : ℝ → Euclidean n} {a b t₀ scale : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hscale : 0 < scale)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (H.hp (x t, p t)) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (-H.hx (x t, p t)) t)
    (hxW : ∀ t ∈ Icc a b, x t ∈ ball 0 g.radius)
    (hdom : ∀ t ∈ Icc a b, (x t, p t) ∈ H.domain)
    (hinit : p t₀ = scale • C.gradientMap η (x t₀)) :
    ∀ t ∈ Icc a b, p t = scale • C.gradientMap η (x t) := by
  let Y := closedBall (0 : Euclidean n) g.radius
  let W := ball (0 : Euclidean n) g.radius
  have hXY : W ⊆ Y := ball_subset_closedBall
  have hlarge (y : Euclidean n) (hy : y ∈ ball 0 (2 * g.radius)) :
      (y, η) ∈ g.domain :=
    g.outer_product_subset_domain ⟨ball_subset_closedBall hy, hη⟩
  have hgrad : ContDiffOn ℝ ∞ (C.gradientMap η) (ball 0 (2 * g.radius)) := by
    intro y hy
    exact ((C.gradient_smooth.contDiffAt (g.isOpen_domain.mem_nhds (hlarge y hy))).comp y
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hderiv : ContDiffOn ℝ ∞ (fderiv ℝ (C.gradientMap η)) (ball 0 (2 * g.radius)) := by
    intro y hy
    exact ((hgrad.contDiffAt (isOpen_ball.mem_nhds hy)).fderiv_right (by simp)).contDiffWithinAt
  obtain ⟨dg, hdg, _, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall 0 g.radius_pos
      isOpen_ball (closedBall_subset_ball (by linarith [g.radius_pos])) hderiv
  have hYlarge : Y ⊆ ball 0 (2 * g.radius) :=
    closedBall_subset_ball (by linarith [g.radius_pos])
  have hgraph : ∀ y ∈ W, HasFDerivAt (C.gradientMap η) (dg y) y := by
    intro y hy
    rw [(heq y (hXY hy)).eq_of_nhds]
    exact ((hgrad.contDiffAt (isOpen_ball.mem_nhds (hYlarge (hXY hy)))).differentiableAt
      (by simp)).hasFDerivAt
  have hpc : ContinuousOn p (Icc a b) := fun t ht ↦ (hp t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (C.gradientMap η) Y := hgrad.continuousOn.mono hYlarge
  let D := (p '' Icc a b) ∪ ((fun t ↦ scale⁻¹ • p t) '' Icc a b) ∪ (C.gradientMap η '' Y)
  have hDc₁ : IsCompact (p '' Icc a b) := isCompact_Icc.image_of_continuousOn hpc
  have hqc : ContinuousOn (fun t ↦ scale⁻¹ • p t) (Icc a b) := hpc.const_smul scale⁻¹
  have hDc₂ : IsCompact ((fun t ↦ scale⁻¹ • p t) '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hqc
  have hY : IsCompact Y := isCompact_closedBall (0 : Euclidean n) g.radius
  have hDc₃ : IsCompact (C.gradientMap η '' Y) := hY.image_of_continuousOn hgc
  have hD : IsCompact D := (hDc₁.union hDc₂).union hDc₃
  have hDz : ∀ q ∈ D, q ≠ 0 := by
    intro q hq
    rcases hq with (hq | hq) | hq
    · obtain ⟨t, ht, rfl⟩ := hq
      have hh := hdom t ht
      rw [hdomain] at hh
      exact hh.2
    · obtain ⟨t, ht, rfl⟩ := hq
      have hh := hdom t ht
      rw [hdomain] at hh
      exact smul_ne_zero (inv_ne_zero hscale.ne') hh.2
    · obtain ⟨y, hy, rfl⟩ := hq
      have hh := (C.zero_energy (closedBall_subset_closedBall
        (by linarith [g.radius_pos]) hy) hη).1
      rw [hdomain] at hh
      exact hh.2
  apply characteristic_stays_on_positive_conic_graph H C.homogeneous
    (W := W) (Y := Y) (D := D) (ψ := fun y ↦ C.phaseFunction (y, η))
    (dg := dg) isOpen_ball ht₀ hscale
  · intro y hy
    exact (((C.phase_smooth.contDiffAt
      (g.isOpen_domain.mem_nhds (hlarge y (hYlarge (hXY hy))))).comp y
        (contDiffAt_id.prodMk contDiffAt_const))).of_le (by simp)
  · exact hgraph
  · intro y hy
    exact (C.zero_energy (closedBall_subset_closedBall
      (by linarith [g.radius_pos]) (hXY hy)) hη).1
  · intro y hy
    exact (C.zero_energy (closedBall_subset_closedBall
      (by linarith [g.radius_pos]) (hXY hy)) hη).2
  · exact isCompact_closedBall _ _
  · exact hD
  · exact hXY
  · intro z hz
    rw [hdomain]
    exact ⟨mem_univ _, hDz z.2 hz.2⟩
  · exact hH.of_le (by simp)
  · exact hdg.of_le (by simp)
  · intro y hy
    exact Or.inr ⟨y, hXY hy, rfl⟩
  · exact hx
  · exact hp
  · exact hxW
  · intro t ht
    exact Or.inl (Or.inl ⟨t, ht, rfl⟩)
  · intro t ht
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  · exact hinit

/-- An actual characteristic segment wholly in the physical region. Both
endpoint times are arbitrary points of the same full interval, which includes
both orientations and retains all intermediate points
(`app:ch_regular:defn:protected-saturation`). -/
def CompleteCharacteristicSegment {n : ℕ} (H : HomogeneousSymbol (Euclidean n))
    (W : Set (Euclidean n)) (z w : Euclidean n × Euclidean n) : Prop :=
  H.h z = 0 ∧ ∃ (x p : ℝ → Euclidean n) (a b t₀ t₁ : ℝ),
    t₀ ∈ Icc a b ∧ t₁ ∈ Icc a b ∧
    (∀ t ∈ Icc a b, HasDerivAt x (H.hp (x t, p t)) t) ∧
    (∀ t ∈ Icc a b, HasDerivAt p (-H.hx (x t, p t)) t) ∧
    (∀ t ∈ Icc a b, x t ∈ W) ∧
    (∀ t ∈ Icc a b, (x t, p t) ∈ H.domain) ∧
    z = (x t₀, p t₀) ∧ w = (x t₁, p t₁)

/-- The positive conic lift of the actual finite comparison family is preserved
by every whole characteristic segment in the common physical ball. No one-step
preservation assumption is used (`app:ch_regular:thm:no-return`). -/
theorem comparisonFamily_preserves_characteristicSegment {n : ℕ} {I : Type*}
    {H : HomogeneousSymbol (Euclidean n)}
    (hdomain : H.domain = normalizedSymbolDomain (univ : Set (Euclidean n)))
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    {g : I → ComparisonGeometry (Euclidean n)} (C : (i : I) → ComparisonChart H (g i))
    {r : ℝ} (hradius : ∀ i, 2 * r < (g i).radius)
    {z w : Euclidean n × Euclidean n}
    (hz : z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hseg : CompleteCharacteristicSegment H (ball 0 (2 * r)) z w) :
    w ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ := by
  obtain ⟨_, η, _, scale, hscale, hz⟩ := hz
  obtain ⟨_, x, p, a, b, t₀, t₁, ht₀, ht₁, hx, hp, hxW, hdom, rfl, rfl⟩ := hseg
  have he := comparisonChart_preserves_complete_segment hdomain hH (C η.1) η.2.2 ht₀ hscale
    hx hp (fun t ht ↦ ball_subset_ball (hradius η.1).le (hxW t ht)) hdom hz t₁ ht₁
  exact ⟨hxW t₁ ht₁, η, mem_univ _, scale, hscale, he⟩

/-- Entire finite chains of diagonal and actual characteristic relations
preserve the constructed conic family, without a bound on chain length
(`app:ch_regular:thm:no-return`). -/
theorem comparisonFamily_preserves_chain {n : ℕ} {I : Type*}
    {H : HomogeneousSymbol (Euclidean n)}
    (hdomain : H.domain = normalizedSymbolDomain (univ : Set (Euclidean n)))
    (hH : ContDiffOn ℝ ∞ H.h H.domain)
    {g : I → ComparisonGeometry (Euclidean n)} (C : (i : I) → ComparisonChart H (g i))
    {r : ℝ} (hradius : ∀ i, 2 * r < (g i).radius)
    {z w : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain (CompleteCharacteristicSegment H (ball 0 (2 * r))) z w k)
    (hz : z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ) :
    w ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ :=
  positiveConicChain_preserves
    (fun _ _ hmem hseg ↦ comparisonFamily_preserves_characteristicSegment
      hdomain hH C hradius hmem hseg) hchain hz

/-- An elliptic source undergoes only identity steps in a finite chain of
diagonal and zero-energy characteristic relations. Thus its entire chain has
the same covector and the same source buffer
(`app:ch_regular:thm:no-return`, elliptic identity images). -/
theorem elliptic_completeCharacteristic_chain_eq {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)} {W : Set (Euclidean n)}
    {z w : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain (CompleteCharacteristicSegment H W) z w k)
    (helliptic : H.h z ≠ 0) : z = w := by
  induction hchain with
  | refl z => rfl
  | @tail z y w k hstep _ ih =>
    rcases hstep with hdiag | hchar
    · exact hdiag.trans (ih (by simpa only [← hdiag] using helliptic))
    · exact (helliptic hchar.1).elim

end JanetCartan.ProtectedFlow
