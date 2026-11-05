module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.Restriction

/-!
# Uniform low carrier budgets from the constructed family

The same family's qualitative phase continuity supplies a fixed `C¹` carrier
budget from primitive frame `C⁶` closeness. No linear continuity modulus and no
high immersion bound is used (`app:ch_seed:prop:seed-actual-menu`, Steps 2–3).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Primitive frame closeness and the actual phase continuity give a uniform
joint `C¹` carrier budget, with its threshold before every varying frame
(`app:ch_seed:prop:seed-actual-menu`, Steps 2–3). -/
theorem exists_carrierGradient_low_bound {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      cNorm K 1 (fun q ↦ T.carrierGradient Q q.1 q.2) ≤ L := by
  obtain ⟨D, hD, hb⟩ := T.exists_carrierGradient_le_phase hP hK hKU
  obtain ⟨δ, hδ, hc⟩ := T.current_phase_continuity 2 zero_lt_one
  let A := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  let S₀ := phase T.reference.chart.coordinates
  have hKW : A ⊆ ball (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) (2 * T.family.radius) :=
    closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hcoords₀ : ContDiffOn ℝ ∞ T.data.localReference.family.chart.coordinates
      T.data.localReference.family.chart.target := by
    rw [T.data.localReference.family.reference_control.target_eq]
    exact T.data.localReference.family.reference_control.coordinates_smooth
  have hS₀ : ∀ x ∈ A, ContDiffAt ℝ 2 S₀ x := fun x hx ↦
    ((T.data.localReference.family.chart.contDiffOn_phase hcoords₀).contDiffAt
      (T.data.localReference.family.chart.isOpen_target.mem_nhds
        (T.family.reference_target (hKW hx)))).of_le (by simp)
  refine ⟨δ, D 1 * (1 + cNorm A 2 S₀), hδ,
    mul_pos (hD 1) (by linarith [cNorm_nonneg A 2 S₀]), fun Q hQ ↦ ?_⟩
  have hsmall := hc Q ((cNorm_mono_order (by omega : 2 + 1 ≤ 6)).trans_lt hQ)
  have hS : ∀ x ∈ A, ContDiffAt ℝ 2 (phase (T.currentChart Q).coordinates) x :=
    fun x hx ↦ ((T.family.phase_smooth Q).contDiffAt
      (isOpen_ball.mem_nhds (hKW hx))).of_le (by simp)
  have hsum := cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
    (fun x hx ↦ (hS x hx).sub (hS₀ x hx)) hS₀
  change cNorm A 2 ((phase (T.currentChart Q).coordinates - S₀) + S₀) ≤ _ at hsum
  rw [sub_add_cancel] at hsum
  change cNorm A 2 (phase (T.currentChart Q).coordinates - S₀) < 1 at hsmall
  change cNorm A 2 (phase (T.currentChart Q).coordinates) ≤
    cNorm A 2 (phase (T.currentChart Q).coordinates - S₀) + cNorm A 2 S₀ at hsum
  exact (hb Q 1).trans (mul_le_mul_of_nonneg_left
    (hsum.trans (add_le_add hsmall.le (le_refl _))) (hD 1).le)

/-- The primitive frame `C⁶` neighborhood itself supplies the needed fixed
frame `C¹` budget; no projected-frame high estimate is used here
(`app:ch_seed:setup:seed-current`). -/
theorem frame_low_bound
    (hballU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (hQ : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) < 1) :
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1 Q.1 ≤
      1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1
        (fun _ : Euclidean n ↦ cubeStress n) := by
  have hs : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ContDiffAt ℝ 1 Q.1 x := fun x hx ↦
    (Q.2.1.contDiffAt (hU.mem_nhds (hballU hx))).of_le (by simp)
  have hb := cNorm_add_le_of_contDiffAt
    (f := Q.1 - fun _ ↦ cubeStress n) (g := fun _ ↦ cubeStress n)
    (isCompact_closedBall _ _)
    (fun x hx ↦ (hs x hx).sub contDiffAt_const)
    (fun _ _ ↦ (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Euclidean n ↦ cubeStress n) _))
  change cNorm _ 1 ((Q.1 - fun _ ↦ cubeStress n) + fun _ ↦ cubeStress n) ≤ _ at hb
  rw [sub_add_cancel] at hb
  have hsmall : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1
      (Q.1 - fun _ ↦ cubeStress n) ≤ 1 :=
    (cNorm_mono_order (by omega : 1 ≤ 6)).trans hQ.le
  exact hb.trans (add_le_add hsmall (le_refl _))

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
