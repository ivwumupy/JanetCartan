module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.Restriction

/-! # Sharp bounds for the literal zero-energy phase -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ProjectedStressFrame ConstructedCarrierJets
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The same full phase restricted to energy zero, before substitution of
its frozen spatial patch (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
def zeroEnergyPhase (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (p : Euclidean n × Euclidean (n - 1)) : ℝ :=
  phase (T.currentChart Q).coordinates (p.1, (0, p.2))

/-- Fixed closed buffer for the zero-energy phase, inside its doubled smooth
target (`app:ch_seed:eq:seed-phase-tame`). -/
def zeroEnergyBuffer : Set (Euclidean n × Euclidean (n - 1)) :=
  closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2.2) T.family.radius

/-- The canonical carrier uses exactly this zero-energy phase, with the
original spatial patch and sign (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem carrier_eq_zeroEnergyPhase (Q : _) (x : Euclidean n) (z : Euclidean 3) :
    T.carrier Q x z = T.zeroEnergyPhase Q (x, T.reference.spatialPatch z) := rfl

/-- Restriction to energy zero preserves the sharp immersion reserve three
on the SAME chosen chart (`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_projected_zeroEnergyPhase_sharp_bound {N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm T.zeroEnergyBuffer m (T.zeroEnergyPhase Q) ≤
          A m * (1 + cNorm K (m + 3) F) := by
  let L := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  let ψ : Euclidean n × Euclidean (n - 1) → Euclidean n × (ℝ × Euclidean (n - 1)) :=
    fun p ↦ (p.1, (0, p.2))
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hmap : MapsTo ψ T.zeroEnergyBuffer L := by
    intro p hp
    have he : T.data.adapted.baseData.2.1 = 0 := rfl
    simpa only [L, zeroEnergyBuffer, ψ, mem_closedBall, Prod.dist_eq, he,
      dist_self, max_eq_right (dist_nonneg)] using hp
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le (G := ℝ)
    (isCompact_closedBall _ _) (isCompact_closedBall _ _) (fun _ _ ↦ hψ.contDiffAt) hmap
  obtain ⟨A, hA, ha⟩ := T.exists_projected_phase_sharp_bound (N := N)
    hK hKU hball C₀ hκmet hκ
  refine ⟨fun m ↦ D m * A m, fun m ↦ mul_pos (hD m) (hA m), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} := ⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  have hs : ∀ q ∈ L, ContDiffAt ℝ ∞ (phase (T.currentChart Q).coordinates) q :=
    fun q hq ↦ (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos]) hq))
  have hh := hd (phase (T.currentChart Q).coordinates) hs m
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (ha F hF hi hrank hlowF hmet hnormal hlow m) (hD m).le).trans_eq (by ring))

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
