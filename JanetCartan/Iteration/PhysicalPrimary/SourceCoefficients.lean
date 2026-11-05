module

public import JanetCartan.Iteration.PhysicalGeometry.Retained

/-!
# Reserved jets of the actual unextended source stress

Project the full geometric reduced array on the SAME physical history. The
identification with its projected stress is local on the original geometric
ball, not a replacement by a periodic history or a new stress frame.
Consumer: the literal half-stress source in
`app:ch_response:eq:response-graded-source`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary
open GeometricProfile ProtectedFlow ProjectedStressFrame
open ResponseTransfer.RetainedFactors ContinuumRow.ImageGeometry

/-- The original physical projected stress has every reserved source jet,
with constants preceding the history (`app:ch_response:eq:response-graded-source`). -/
theorem exists_history_rawStress_reserved_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ)/2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ AQ : ℕ → ℝ, (∀ j, 0 ≤ AQ j) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) ∧
        ∀ x ∈ closedBall (0 : Euclidean n) r, ∀ k,
          ‖iteratedFDeriv ℝ k (projectedStress F) x‖ ≤
            AQ k * currentCoefficientScale R₀ j ^ (k-reserve) := by
  obtain ⟨SG,hSG,_M,_hM,_κ,_hκ,hgeom⟩ := PhysicalGeometry.exists_geometric_neighborhood
    G hr hrR hR hBband hStar horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨SQ,hSQ,A,hA,hcoeff⟩ := PhysicalGeometry.exists_reduced_coefficient_profiles
    G hr hrR hR hBband hStar hreserve horder
  refine ⟨max SG SQ,hSG.trans (le_max_left _ _),fun k ↦ ‖reducedFrameProjection n‖ * A k,
    fun k ↦ mul_nonneg (norm_nonneg _) (hA k),?_⟩
  intro R₀ hR₀ j u ell hu F
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨_,hrank,_⟩ := hgeom R₀ ((le_max_left _ _).trans hR₀) j u ell hu
  obtain ⟨hsm,hprof⟩ := hcoeff R₀ ((le_max_right _ _).trans hR₀) j u ell hu
  have he : EqOn (reducedFrameProjection n ∘ geometricReducedCoefficients F)
      (projectedStress F) (ball 0 R) := by
    intro x hx
    funext i a b
    change (StressFrame.geometricCubeStress F x i).val a b = projectedStress F x i a b
    rw [geometricCubeStress_val_eq_projectedStress (hF.contDiffAt.of_le (by simp)) (hrank x hx)]
  have hraw : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) :=
    ((reducedFrameProjection n).contDiff.comp_contDiffOn hsm).congr (fun x hx ↦ (he hx).symm)
  refine ⟨hraw,?_⟩
  intro x hx k
  have hxR : x ∈ ball (0 : Euclidean n) R := closedBall_subset_ball hrR hx
  have hevent : projectedStress F =ᶠ[𝓝 x] reducedFrameProjection n ∘ geometricReducedCoefficients F := by
    filter_upwards [isOpen_ball.mem_nhds hxR] with y hy
    exact (he hy).symm
  rw [(hevent.iteratedFDeriv ℝ k).eq_of_nhds]
  apply ((reducedFrameProjection n).norm_iteratedFDeriv_comp_left
    (hsm.contDiffAt (isOpen_ball.mem_nhds hxR)) (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  have hb := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall (0 : Euclidean n) r)
    (fun y hy ↦ (hsm.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hy))).of_le (by simp))
    hx le_rfl).trans (hprof k)
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring)

end JanetCartan.PhysicalPrimary
