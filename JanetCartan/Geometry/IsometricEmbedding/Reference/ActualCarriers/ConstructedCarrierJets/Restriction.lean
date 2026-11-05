module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SharpPhaseBounds

/-!
# Sharp jets of the selected carrier restriction

The restriction is literally `(x,z) ↦ (x,(0,spatialPatch z))`. Differentiating
its full phase once and applying the fixed physical Riesz contraction proves
frame loss two and immersion loss four for the same canonical carrier gradient
in `app:ch_seed:eq:seed-phase-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ConstructedCarrierJets ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Literal fixed restriction used in Steps 2–3 of
`app:ch_seed:prop:seed-actual-menu`. -/
def carrierRestriction (q : Euclidean n × Euclidean 3) :
    Euclidean n × (ℝ × Euclidean (n - 1)) :=
  (q.1, (0, T.reference.spatialPatch q.2))

/-- All derivative budgets of the restriction are fixed smooth-map budgets
on compact subsets of this open domain (`app:ch_seed:eq:seed-phase-tame`). -/
theorem carrierRestriction_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ T.carrierRestriction
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :=
  contDiffOn_fst.prodMk (contDiffOn_const.prodMk
    ((T.reference.spatialPatch_smooth hP).comp contDiffOn_snd (fun _ h ↦ h.2)))

/-- The restriction's range is in the retained target for every selected
current chart (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem carrierRestriction_mem_target (Q : _) {q : Euclidean n × Euclidean 3}
    (hq : q ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    T.carrierRestriction q ∈ (T.currentChart Q).target :=
  T.reference.target_contains _ hq.1 _ hq.2

/-- The actual carrier gradient is the fixed physical contraction of the
full phase differential, evaluated at the literal restriction
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem carrierGradient_eq_extracted (Q : _) {q : Euclidean n × Euclidean 3}
    (hq : q ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    T.carrierGradient Q q.1 q.2 = momentumDifferentialExtraction
      (fderiv ℝ (phase (T.currentChart Q).coordinates) (T.carrierRestriction q)) := by
  exact (hasGradientAt_carrierPhase (T.currentChart Q) T.reference.spatialPatch
    (T.carrierRestriction_mem_target Q hq)).gradient.trans
      (chartMomentum_eq_extracted_phaseDifferential _ (T.carrierRestriction_mem_target Q hq))

/-- One full phase derivative controls every joint carrier jet, with constants
from the fixed restriction alone. The full target is the same as that in
`current_phase_bound` (`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_carrierGradient_le_phase {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧ ∀ Q m,
      cNorm K m (fun q ↦ T.carrierGradient Q q.1 q.2) ≤
        D m * cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) T.family.radius) (m + 1)
          (phase (T.currentChart Q).coordinates) := by
  let O := ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)
  have hO : IsOpen O := isOpen_ball.prod (isOpen_parameterInterior _)
  have hψ : ∀ x ∈ K, ContDiffAt ℝ ∞ T.carrierRestriction x :=
    fun x hx ↦ (T.carrierRestriction_smooth hP).contDiffAt (hO.mem_nhds (hKU hx))
  choose D hD hb using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound
    (G := Euclidean n) hK hψ m
  refine ⟨D, hD, fun Q m ↦ ?_⟩
  let S := phase (T.currentChart Q).coordinates
  let L := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hS : ∀ x ∈ L, ContDiffAt ℝ ∞ S x := fun x hx ↦
    (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) hx))
  have hψL : MapsTo T.carrierRestriction K L := fun q hq ↦
    ball_subset_closedBall (T.carrierRestriction_mem_target Q (hKU hq))
  let g := momentumDifferentialExtraction (n := n) ∘ fderiv ℝ S
  have hg : ∀ x ∈ L, ContDiffAt ℝ ∞ g x := fun x hx ↦
    momentumDifferentialExtraction.contDiff.contDiffAt.comp x
      ((hS x hx).fderiv_right (m := ∞) (by simp))
  have he : cNorm K m (fun q ↦ T.carrierGradient Q q.1 q.2) =
      cNorm K m (g ∘ T.carrierRestriction) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro q hq
    exact eventuallyEq_of_mem (hO.mem_nhds (hKU hq))
      (fun y hy ↦ T.carrierGradient_eq_extracted Q hy)
  rw [he]
  apply hb m g (cNorm L (m + 1) S) (cNorm_nonneg ..)
    (fun x hx ↦ (hg _ (hψL hx)).of_le (by simp))
  intro j hj x hx
  calc
    _ ≤ ‖momentumDifferentialExtraction (n := n)‖ *
        ‖iteratedFDeriv ℝ j (fderiv ℝ S) (T.carrierRestriction x)‖ :=
      momentumDifferentialExtraction.norm_iteratedFDeriv_comp_left
        ((hS _ (hψL hx)).fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ S) (T.carrierRestriction x)‖ :=
      mul_le_mul_of_nonneg_right norm_momentumDifferentialExtraction_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 1) S (T.carrierRestriction x)‖ := by
      rw [one_mul, norm_iteratedFDeriv_fderiv]
    _ ≤ _ := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hS y hy).of_le (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞))
      (hψL hx) (by omega)

/-- Joint carrier order `m` uses frame order `m+2` on the identical chart,
with all constants fixed before the frame (`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_carrierGradient_frame_bound {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ Q m,
      cNorm K m (fun q ↦ T.carrierGradient Q q.1 q.2) ≤ A m *
        (1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
          (m + 2) Q.1) := by
  obtain ⟨D, hD, hb⟩ := T.exists_carrierGradient_le_phase hP hK hKU
  refine ⟨fun m ↦ D m * T.family.coefficient (m + 1),
    fun m ↦ mul_pos (hD m) (T.family.coefficient_pos _), fun Q m ↦ ?_⟩
  exact (hb Q m).trans (by
    simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc] using
      mul_le_mul_of_nonneg_left (T.current_phase_bound Q (m + 1)) (hD m).le)

/-- The projected-stress estimate discharges the frame input and gives
immersion order `m+4` for the canonical gradient, preserving the separate
metric/normal gaps (`app:ch_seed:eq:seed-frame-tame`, `seed-phase-tame`). -/
theorem exists_projected_carrierGradient_sharp_bound {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    {Kc : Set (Euclidean n × Euclidean 3)} (hKc : IsCompact Kc)
    (hKcU : Kc ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
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
        ∀ m, cNorm Kc m (fun q ↦ T.carrierGradient Q q.1 q.2) ≤
          A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨D, hD, hd⟩ := T.exists_carrierGradient_le_phase hP hKc hKcU
  obtain ⟨B, hB, hb⟩ := T.exists_projected_phase_sharp_bound
    (N := N) hK hKU hball C₀ hκmet hκ
  refine ⟨fun m ↦ D m * B (m + 1), fun m ↦ mul_pos (hD m) (hB _), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  apply (hd _ m).trans
  simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc] using
    mul_le_mul_of_nonneg_left (hb F hF hi hrank hlowF hmet hnormal hlow (m + 1)) (hD m).le

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
