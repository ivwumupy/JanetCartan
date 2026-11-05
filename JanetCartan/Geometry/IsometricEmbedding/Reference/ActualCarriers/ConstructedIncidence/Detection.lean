module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.RootDetection

/-!
# Full detector stability on the constructed refinement

The frozen common-kernel premise is discharged from `CoverData.IsValid`'s
actual image-channel inequality. Compact covector buffers lie inside the
original frozen charts (`app:ch_seed:eq:seed-actual-detection`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open FrozenMenu

/-- The actual frozen detector on a compact subchart supplies a uniform
positive perturbation radius. This discharges all frozen inputs of
`exists_uniform_detection_at_supplied_roots` from the original menu, and is
used at the constructed roots in `exists_constructed_incidence_detection`
(`app:ch_seed:eq:seed-actual-detection`). -/
theorem exists_refined_frozen_detection_threshold {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀) {R : IncidenceRefinement D} (hR : R.IsValid) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ j : Fin R.chartCount,
      ∀ {X : Type*} (Q : X → Fin n → MetricTensor n)
        (ξ : X → Fin (D.patchCount (R.sourceChart j)) → Euclidean 3 → Euclidean n)
        (z : X → Fin (D.patchCount (R.sourceChart j)) → Euclidean n → Euclidean 3),
        (∀ x a, ∀ k ∈ closedBall (R.center j) (R.radius j),
          z x a k ∈ parameterCube (D.patches (R.sourceChart j) a).radius) →
        (∀ x, ‖Q x - cubeStress n‖ < δ) →
        (∀ x a, ∀ w ∈ parameterCube (D.patches (R.sourceChart j) a).radius,
          ‖ξ x a w - (D.patches (R.sourceChart j) a).toFun w‖ < δ) →
        (∀ x a, ∀ k ∈ closedBall (R.center j) (R.radius j),
          ‖z x a k - D.roots (R.sourceChart j) a k‖ < δ) →
        ∀ x, ∀ k ∈ closedBall (R.center j) (R.radius j), ∀ s : Euclidean n,
          c * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (Q x) k) s‖ ^ 2 +
            ∑ a, ⟪quadratic (Q x) (ξ x a (z x a k)), s⟫_ℝ ^ 2 := by
  have hKD (j) : closedBall (R.center j) (R.radius j) ⊆ D.domain (R.sourceChart j) :=
    (closedBall_subset_closedBall (by linarith [hR.1 j] : R.radius j ≤ 2 * R.radius j)).trans
      (hR.2.1 j)
  have hfrozen (j) := exists_uniform_detection_at_supplied_roots (cubeStress n)
    (isCompact_closedBall (R.center j) (R.radius j))
    (fun a ↦ parameterCube (D.patches (R.sourceChart j) a).radius)
    (fun a ↦ isCompact_parameterCube _) (fun a ↦ (D.patches (R.sourceChart j) a).toFun)
    (fun a ↦ ((hD.2.2.2.2.1 (R.sourceChart j) a).1.2.2.2.1).continuousOn.mono
      (parameterCube_subset_doubledInterior (hD.2.2.2.2.1 (R.sourceChart j) a).1.1))
    (fun a ↦ D.roots (R.sourceChart j) a)
    (fun a ↦ ((hD.2.2.2.2.1 (R.sourceChart j) a).2.1).continuousOn.mono (hKD j))
    (fun a k hk i ↦ ((hD.2.2.2.2.1 (R.sourceChart j) a).2.2.1 k (hKD j hk)).1 i |>.le)
    (by
      intro k hk s hM hs
      have hb := hD.2.2.2.2.2 (R.sourceChart j) k (hKD j hk) s
      have hM' : imageChannel (cubePencil k) s = 0 := by simpa only [pencil_cubeStress] using hM
      have hs' (a) : ⟪CubeCarrier.quadratic
          ((D.patches (R.sourceChart j) a).toFun (D.roots (R.sourceChart j) a k)), s⟫_ℝ = 0 := by
        simpa only [CubeCarrier.quadratic_eq_cubeQuadraticContraction, quadratic_cubeStress]
          using hs a
      have hn : c₀ * ‖s‖ ^ 2 ≤ 0 := by simpa [hM', hs'] using hb
      have hsquare : ‖s‖ ^ 2 ≤ 0 := by
        by_contra! h
        exact (not_lt_of_ge hn) (mul_pos hD.1 h)
      have hn₀ : ‖s‖ = 0 := by nlinarith [sq_nonneg ‖s‖, norm_nonneg s]
      exact norm_eq_zero.mp hn₀)
  choose cj dj hcj hdj hdet using hfrozen
  obtain ⟨c, hc, hci⟩ := Pi.exists_forall_pos_add_lt hcj
  obtain ⟨d, hd, hdi⟩ := Pi.exists_forall_pos_add_lt hdj
  refine ⟨c, d, hc, hd, fun j X Q ξ z hz hQ hξ hroot x k hk s ↦ ?_⟩
  have hcle : c ≤ cj j := by simpa using (hci j).le
  have hdle : d ≤ dj j := by simpa using (hdi j).le
  exact (mul_le_mul_of_nonneg_right hcle (sq_nonneg ‖s‖)).trans
    (hdet j Q ξ z hz (fun x ↦ (hQ x).trans_le hdle)
      (fun x a w hw ↦ (hξ x a w hw).trans_le hdle)
      (fun x a k hk ↦ (hroot x a k hk).trans_le hdle) x k hk s)

end JanetCartan.ActualCarriers
