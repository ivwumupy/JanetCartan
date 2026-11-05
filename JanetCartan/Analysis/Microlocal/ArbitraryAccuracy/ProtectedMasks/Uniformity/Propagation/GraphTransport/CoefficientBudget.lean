module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.UniformProjected

/-!
# The primitive C³ budget of the retained extended projected frame

The fixed extension and componentwise C⁶ neighborhood in
`app:ch_regular:thm:no-return` produce a common coefficient budget before the
current immersion. `Construction` uses it to instantiate the annular Hamilton
field estimate without an additional coefficient-budget hypothesis.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow

open ActualCarriers.CurrentFullPhase

/-- The actual projected-frame neighborhood has one C³ budget on the prescribed
physical ball, chosen before the immersion (`app:ch_regular:thm:no-return`,
`app:ch_regular:eq:coefficient-extension`). -/
theorem exists_uniform_extendedProjectedStress_cNorm_three_bound
    {n N : ℕ} {U : Set (Euclidean n)} (hU : IsOpen U)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (p : BallExtension.Parameters (Euclidean n))
    (hpK : closedBall p.center p.radius ⊆ K) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ∃ M ≥ (0 : ℝ), ∀ F : ProjectedImmersionNeighborhood N U K δ,
      cNorm (closedBall 0 r) 3 (extendedProjectedStress p F.1) ≤ M := by
  obtain ⟨A, hA, hbound⟩ := exists_affineFrameExtension_bound (n := n) p 3
  let B := cNorm (closedBall (0 : Euclidean n) r) 3
    (fun _ : Euclidean n ↦ cubeStress n)
  have hB : 0 ≤ B := cNorm_nonneg _ _ _
  refine ⟨A * (14 * δ) + B, by positivity, ?_⟩
  intro F
  let Q := (frameOfImmersion hU F).1
  have hQ := (frameOfImmersion hU F).2.1
  have hs : ∀ x ∈ K, ContDiffAt ℝ 6 (Q - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le
      (by simp)
  have hsmall : cNorm K 6 (Q - fun _ ↦ cubeStress n) < 14 * δ := by
    apply frame_cNorm_lt_of_componentwise hK hs (by positivity)
    intro i
    convert (frameOfImmersion hU F).2.2 i using 1; ring
  have hlocal : cNorm (closedBall p.center p.radius) 3
      (Q - fun _ ↦ cubeStress n) ≤ 14 * δ :=
    ((cNorm_mono_order (by decide : 3 ≤ 6)).trans
      (cNorm_mono_set_of_contDiffAt hpK hK hs)).trans hsmall.le
  have hQE : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ Q x :=
    fun x hx ↦ hQ.contDiffAt (hU.mem_nhds (hKU (hpK hx)))
  have hE := contDiff_affineFrameExtension p (hQ.mono (hpK.trans hKU))
  have hsupport : HasCompactSupport (affineFrameExtension p Q - fun _ ↦ cubeStress n) :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_affineFrameExtension_sub p Q)
  have hrestrict : cNorm (closedBall (0 : Euclidean n) r) 3
      (affineFrameExtension p Q - fun _ ↦ cubeStress n) ≤
      cNorm univ 3 (affineFrameExtension p Q - fun _ ↦ cubeStress n) := by
    obtain ⟨B, _, hB⟩ := hsupport.exists_bound_iteratedFDeriv (hE.sub contDiff_const) 3
    apply cNorm_mono_set_of_bddAbove (subset_univ _)
    intro j hj
    exact ⟨B, by rintro _ ⟨x, _, rfl⟩; exact hB j hj x⟩
  have hbudget := (hrestrict.trans (hbound Q hQE)).trans
    (mul_le_mul_of_nonneg_left hlocal hA.le)
  have hadd := cNorm_add_le (f := affineFrameExtension p Q - fun _ ↦ cubeStress n) (r := 3) (isCompact_closedBall (0 : Euclidean n) r)
    ((hE.sub contDiff_const).of_le (by simp))
    (show ContDiff ℝ 3 (fun _ : Euclidean n ↦ cubeStress n) from contDiff_const)
  rw [sub_add_cancel] at hadd
  exact hadd.trans (add_le_add hbudget le_rfl)

end JanetCartan.ProtectedFlow
