module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedPhases
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame

/-!
# Sharp immersion bounds for the constructed full phase

The projected-stress loss two is instantiated in the actual Hamilton family's
frame-order `m+1` bound. Thus the same chart used for the carriers has immersion
order `m+3`, before the reserve-six bundling in `app:ch_seed:eq:seed-phase-tame`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ProjectedStressFrame

/-- The sharp full-phase estimate on the identical chart used in
`exists_constructed_carrier_phases`. All constants precede the immersion and
all high norms. The inputs are the original metric/normal gaps, low immersion
bound and primitive frame neighborhood; no frame or phase high estimate is
assumed (`app:ch_seed:eq:seed-frame-tame`, `app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_projected_phase_sharp_bound {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
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
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) T.family.radius) m
          (phase (T.currentChart Q).coordinates) ≤ A m * (1 + cNorm K (m + 3) F) := by
  choose B hB hbound using fun m : ℕ ↦ exists_cNorm_projectedStress_le_tame
    (N := N) (0 : Euclidean n) T.data.localReference.stateRadius_pos C₀ hκmet hκ (m + 1)
  let A (m : ℕ) := T.family.coefficient m * (1 + ((m + 1 : ℕ) + 1) * B m)
  refine ⟨A, fun m ↦ mul_pos (T.family.coefficient_pos m) (by have := hB m; positivity), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  have hs : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hcomponent := hbound m F U K hU hK hball hKU hF hi hlowF hmet hnormal
  have hframe := frame_cNorm_le_of_componentwise
    (isCompact_closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (fun x hx ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))).of_le
      (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞))
    (mul_nonneg (hB m).le (by linarith [cNorm_nonneg K ((m + 1) + 2) F])) hcomponent
  have hp := T.current_phase_bound ⟨projectedStress F, hs, hlow⟩ m
  apply hp.trans
  dsimp only [A]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (T.family.coefficient_pos m).le
  have hFnonneg := cNorm_nonneg K (m + 3) F
  norm_num only [Nat.add_assoc, Nat.reduceAdd] at hframe
  nlinarith

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
