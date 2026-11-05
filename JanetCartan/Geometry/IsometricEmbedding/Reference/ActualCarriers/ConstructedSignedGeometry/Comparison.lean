module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties

/-!
# One primitive frame threshold for the retained carrier family

This is the actual comparison input to the signed-family assembly in
`app:ch_seed:prop:seed-actual-menu`, Step 2. Every chart is the given
`PatchQuantitativeFamily.currentChart`; no second phase construction is made.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.ConstructedSignedGeometry
open FrozenMenu CurrentFullPhase

/-- The primitive componentwise `C⁶` frame neighborhood used for the uniform
signed directions (`app:ch_seed:setup:seed-current`). -/
abbrev FrameNeighborhood {n : ℕ} (U K : Set (Euclidean n)) (δ : ℝ) :=
  {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    ∀ j, cNorm K 6 (fun x ↦ Q x j - cubeStress n j) < δ}

/-- A finite common threshold gives the value and full parameter-derivative
comparison of every selected literal carrier. The only smallness input is
componentwise frame `C⁶` closeness on the compact construction set containing
all retained frame balls. It includes empty menus and preserves the same
chart objects (`app:ch_seed:prop:seed-actual-menu`, Steps 1–2). -/
theorem exists_common_carrier_comparison_threshold {n : ℕ}
    {D : CoverData n} {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (b : Fin D.chartCount) × Fin (D.patchCount b)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ),
      ∃ hlow : ∀ (Q : FrameNeighborhood U K δ) i,
        cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < (T i).family.threshold,
      ∀ (Q : FrameNeighborhood U K δ) i,
      ∀ x ∈ ball (0 : Euclidean n) (T i).physicalRadius,
      ∀ z ∈ parameterCube (D.patches i.1 i.2).radius,
        ‖(T i).carrierGradient ⟨Q.1, Q.2.1, hlow Q i⟩ x z -
          (D.patches i.1 i.2).toFun z‖ ≤ ε ∧
        ‖fderiv ℝ ((T i).carrierGradient ⟨Q.1, Q.2.1, hlow Q i⟩ x) z -
          fderiv ℝ (D.patches i.1 i.2).toFun z‖ ≤ ε := by
  classical
  choose d hd hcomp using fun i ↦
    (T i).exists_carrier_comparison_threshold (hD.2.2.2.2.1 i.1 i.2).1 hε
  obtain ⟨_, e, _, _, _, he, _, hmin⟩ := exists_common_phase_buffers
    (fun i ↦ (T i).physicalRadius)
    (fun i ↦ min (T i).family.threshold (d i)) (fun _ ↦ (1 : ℝ))
    (fun i ↦ (T i).physicalRadius_pos)
    (fun i ↦ lt_min (T i).family.threshold_pos (hd i))
  have hlocal (Q : FrameNeighborhood U K (e / (2 * (6 + 1)))) (i : _) :
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < e := by
    have hs : ∀ x ∈ K, ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) x := by
      intro x hx
      exact ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
    exact (cNorm_mono_set_of_contDiffAt (hball i) hK hs).trans_lt
      (frame_cNorm_lt_of_componentwise hK hs he Q.2.2)
  let hlow (Q : FrameNeighborhood U K (e / (2 * (6 + 1)))) (i : _) :=
    (hlocal Q i).trans_le ((hmin i).2.1.trans (min_le_left _ _))
  refine ⟨e / (2 * (6 + 1)), by positivity, hlow, ?_⟩
  intro Q i
  exact hcomp i ⟨Q.1, Q.2.1, hlow Q i⟩
    ((hlocal Q i).trans_le ((hmin i).2.1.trans (min_le_right _ _)))

end JanetCartan.ActualCarriers.ConstructedSignedGeometry
