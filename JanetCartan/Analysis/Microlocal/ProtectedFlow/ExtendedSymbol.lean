module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.FrameExtension
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CubeSymbol
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbolBounds

/-!
# Symbol comparison for the fixed extended frame

For `app:ch_regular:thm:no-return`, the compact estimate set returned by the
comparison-phase construction is covered by finitely many buffered covector
balls. The literal determinant estimates and the fixed affine extension then
give the required scalar-symbol neighborhood from primitive frame closeness.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open ActualCarriers ActualCarriers.FrozenPhaseReference

/-- Frame closeness gives normalized-symbol closeness on an arbitrary compact
punctured phase-space set. The finite annular cover is constructed internally,
including the empty-set case (`app:ch_regular:thm:no-return`). -/
theorem exists_symbol_comparison_radius_compact {n : ℕ}
    {K : Set (Euclidean n × Euclidean n)} (hK : IsCompact K)
    (hzero : ∀ z ∈ K, z.2 ≠ 0) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q : Euclidean n → Fin n → MetricTensor n,
      ContDiff ℝ ∞ Q → HasCompactSupport (Q - fun _ ↦ cubeStress n) →
      cNorm univ m (Q - fun _ ↦ cubeStress n) < δ →
      cNorm K m (normalizedSymbol Q - normalizedSymbol (fun _ ↦ cubeStress n)) < ε := by
  classical
  by_cases hKe : K = ∅
  · subst K
    exact ⟨1, zero_lt_one, fun _ _ _ _ ↦ by simpa [cNorm] using hε⟩
  have hballs (z : K) : ∃ ρ > (0 : ℝ),
      closedBall z.1 ρ ⊆ (frozenSymbol n).domain :=
    nhds_basis_closedBall.mem_iff.mp ((frozenSymbol n).isOpen_domain.mem_nhds
      ((mem_frozenSymbol_domain z.1).mpr (hzero z.1 z.2)))
  choose ρ hρ hdomain using hballs
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun z : K ↦ ball z.1 (ρ z))
    (fun _ ↦ isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hρ ⟨z, hz⟩)⟩)
  have hcover : ∀ z ∈ K, ∃ i : s, z ∈ closedBall i.1.1 (ρ i.1) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp (hs hz)
    exact ⟨⟨i, hi⟩, ball_subset_closedBall hz⟩
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hKe
  obtain ⟨i, _⟩ := hcover z hz
  let : Nonempty s := ⟨i⟩
  let B : Set (Euclidean n) := ⋃ i : s, closedBall i.1.1.1 (ρ i.1)
  have hB : IsCompact B := isCompact_iUnion (fun i : s ↦ isCompact_closedBall _ _)
  have hphysical (i : s) : closedBall i.1.1.1 (ρ i.1) ⊆ B :=
    subset_iUnion (fun i : s ↦ closedBall i.1.1.1 (ρ i.1)) i
  have hξ (i : s) (ξ : Euclidean n) (hξ : ξ ∈ closedBall i.1.1.2 (ρ i.1)) : ξ ≠ 0 := by
    apply (mem_frozenSymbol_domain (i.1.1.1, ξ)).mp
    apply hdomain i.1
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hξ
  obtain ⟨δ, hδ, hb⟩ := NormalizedSymbolBounds.exists_symbol_comparison_radius_finiteCover
    (fun i : s ↦ i.1.1) (fun i : s ↦ ρ i.1) (fun i ↦ hρ i.1) hξ
    hB hcover hphysical (cubeStress n) m hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ hsupp hsmall
  apply hb univ isOpen_univ (subset_univ _) Q hQ.contDiffOn
  apply (cNorm_mono_set_of_bddAbove (subset_univ B) ?_).trans_lt hsmall
  obtain ⟨C, _, hC⟩ := hsupp.exists_bound_iteratedFDeriv (hQ.sub contDiff_const) m
  intro j hj
  exact ⟨C, by rintro _ ⟨x, _, rfl⟩; exact hC j hj x⟩

/-- The fixed affine extension produces the prescribed scalar-symbol tolerance
on the comparison construction's entire compact estimate set. Only the same
order of primitive frame closeness is used; no symbol comparison is assumed
(`app:ch_regular:thm:no-return`). -/
theorem exists_extended_symbol_comparison_radius {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n))
    {K : Set (Euclidean n × Euclidean n)} (hK : IsCompact K)
    (hzero : ∀ z ∈ K, z.2 ≠ 0) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q : Euclidean n → Fin n → MetricTensor n,
      (∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x) →
      cNorm (closedBall p.center p.radius) m (Q - fun _ ↦ cubeStress n) < δ →
      cNorm K m (normalizedSymbol (affineFrameExtension p Q) -
        normalizedSymbol (fun _ ↦ cubeStress n)) < ε := by
  obtain ⟨d, hd, hb⟩ := exists_symbol_comparison_radius_compact hK hzero m hε
  obtain ⟨C, hC, he⟩ := exists_affineFrameExtension_bound p m
  refine ⟨d / C, div_pos hd hC, ?_⟩
  intro Q hQ hsmall
  apply hb (affineFrameExtension p Q)
    (contDiff_affineFrameExtension p (fun x hx ↦ (hQ x hx).contDiffWithinAt))
    ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_affineFrameExtension_sub p Q))
  exact (he Q hQ).trans_lt ((mul_lt_mul_of_pos_left hsmall hC).trans_eq
    (mul_div_cancel₀ d hC.ne'))

end JanetCartan.ProtectedFlow
