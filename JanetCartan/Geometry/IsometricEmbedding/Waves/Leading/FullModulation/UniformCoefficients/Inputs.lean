module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.PhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds

/-!
# Primitive inputs for full-modulation null coefficients

The consumer is the uniform full-covector extension of the existing minor in
`app:ch_waves:thm:leading`. Low bounds come from the retained Hamilton family's
phase continuity, and high bounds use its reserve-four gradient estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open ActualCarriers.ConstructedCarrierJets NullTransport.CoefficientBounds

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The original stress frame and full gradient, with independent carrier label
and covector (`app:ch_waves:thm:leading`). -/
def fullInput (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) : Input n :=
  (Q.1 w.1, phaseGradient T Q w.1 w.2.2)

/-- Open joint domain of the frame and full gradient
(`app:ch_waves:eq:joint-tame`). -/
def inputDomain : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :=
  domain T ∩ Prod.fst ⁻¹' U

/-- Ordinary joint derivatives are available on the input domain
(`app:ch_waves:eq:joint-tame`). -/
theorem isOpen_inputDomain : IsOpen (inputDomain T) :=
  (isOpen_domain T).inter (hU.preimage continuous_fst)

/-- Smoothness of the actual full input, before imposing a denominator gap
(`app:ch_waves:thm:leading`). -/
theorem smooth_fullInput (Q : _) : ContDiffOn ℝ ∞ (fullInput T Q) (inputDomain T) :=
  (Q.2.1.comp contDiffOn_fst (fun _ hw ↦ hw.2)).prodMk
    ((phaseGradient_joint_smooth T Q).mono inter_subset_left)

/-- Primitive frame closeness and the actual phase continuity give a uniform
joint full-covector `C¹` gradient budget, with its threshold before every varying frame
(`app:ch_waves:eq:joint-tame`). -/
theorem exists_fullGradient_low_bound
    {K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hK : IsCompact K)
    (hKU : K ⊆ domain T) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      cNorm K 1 (fun q ↦ phaseGradient T Q q.1 q.2.2) ≤ L := by
  obtain ⟨D, hD, hb⟩ := exists_phaseGradient_le_phase T hK hKU
  obtain ⟨δ, hδ, hc⟩ := T.current_phase_continuity 2 zero_lt_one
  let A := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  let S₀ := HamiltonPhase.phase T.reference.chart.coordinates
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
  have hS : ∀ x ∈ A, ContDiffAt ℝ 2 (HamiltonPhase.phase (T.currentChart Q).coordinates) x :=
    fun x hx ↦ ((T.family.phase_smooth Q).contDiffAt
      (isOpen_ball.mem_nhds (hKW hx))).of_le (by simp)
  have hsum := cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
    (fun x hx ↦ (hS x hx).sub (hS₀ x hx)) hS₀
  change cNorm A 2 ((HamiltonPhase.phase (T.currentChart Q).coordinates - S₀) + S₀) ≤ _ at hsum
  rw [sub_add_cancel] at hsum
  change cNorm A 2 (HamiltonPhase.phase (T.currentChart Q).coordinates - S₀) < 1 at hsmall
  change cNorm A 2 (HamiltonPhase.phase (T.currentChart Q).coordinates) ≤
    cNorm A 2 (HamiltonPhase.phase (T.currentChart Q).coordinates - S₀) + cNorm A 2 S₀ at hsum
  exact (hb Q 1).trans (mul_le_mul_of_nonneg_left
    (hsum.trans (add_le_add hsmall.le (le_refl _))) (hD 1).le)

/-- Primitive `C⁶` frame closeness supplies a fixed joint `C¹` budget for
the actual input. This supplies the value range and the low direction bound
in `app:ch_waves:thm:leading`, independently of high immersion norms. -/
theorem exists_fullInput_low_bound
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (ρ : ℝ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hballU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hc : closedBall a ρ ⊆ domain T) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      cNorm (closedBall a ρ) 1 (fullInput T Q) ≤ L := by
  obtain ⟨δ, Lξ, hδ, hLξ, hξ⟩ :=
    exists_fullGradient_low_bound T (isCompact_closedBall a ρ) hc
  obtain ⟨A, hA, ha⟩ := exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) (isCompact_closedBall a ρ) (isCompact_closedBall _ _)
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  let LQ := 1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1
    (fun _ : Euclidean n ↦ cubeStress n)
  have hLQ : 0 < LQ := by
    have := cNorm_nonneg (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
      1 (fun _ : Euclidean n ↦ cubeStress n)
    dsimp [LQ]
    linarith
  refine ⟨min δ 1, 2 * (A 1 * LQ + Lξ), lt_min hδ zero_lt_one,
    by have := hA 1; positivity, ?_⟩
  intro Q hclose
  have hQ := T.frame_low_bound hballU Q (hclose.trans_le (min_le_right _ _))
  have hQ' := ha Q.1 (fun x hx ↦ Q.2.1.contDiffAt (hU.mem_nhds (hballU hx))) 1
  have hξ' := hξ Q (hclose.trans_le (min_le_left _ _))
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨hc hw, hballU (hx hw)⟩
  have hb := cNorm_pair_le a 1 (isOpen_inputDomain T) hdom
    (Q.2.1.comp contDiffOn_fst (fun _ hw ↦ hw.2))
    ((phaseGradient_joint_smooth T Q).mono inter_subset_left)
  change cNorm (closedBall a ρ) 1 (fullInput T Q) ≤ _ at hb
  dsimp only [Function.comp_def] at hQ'
  change cNorm _ 1 Q.1 ≤ LQ at hQ
  have hQ'' := hQ'.trans (mul_le_mul_of_nonneg_left hQ (hA 1).le)
  norm_num only [Nat.cast_one, Function.comp_def] at hb
  linarith

/-- The projected stress loss two and the identical full-gradient loss
four yield a joint input estimate with fixed reserve four. No input high
estimate is assumed (`app:ch_waves:eq:joint-tame`). -/
theorem exists_projected_fullInput_bound
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (ρ : ℝ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall a ρ ⊆ domain T)
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
        ∀ m, cNorm (closedBall a ρ) m (fullInput T Q) ≤
          A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) (isCompact_closedBall a ρ) (isCompact_closedBall _ _)
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  obtain ⟨B, hB, hb⟩ := exists_phaseGradient_projected_sharp_bound T
    (N := N) (isCompact_closedBall a ρ) hc hK hKU hball C₀ hκmet hκ
  choose A hA ha using fun m ↦ exists_cNorm_projectedStress_le_tame
    (N := N) (0 : Euclidean n) T.data.localReference.stateRadius_pos C₀ hκmet hκ m
  refine ⟨fun m ↦ (m + 1) * (D m * ((m + 1) * A m) + B m),
    fun m ↦ by have := hD m; have := hA m; have := hB m; positivity, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hs := Q.2.1
  have hframe := frame_cNorm_le_of_componentwise
    (isCompact_closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (fun x hx ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))).of_le
      (by simp : (m : ℕ∞ω) ≤ ∞))
    (mul_nonneg (hA m).le (by linarith [cNorm_nonneg K (m + 2) F]))
    (ha m F U K hU hK hball hKU hF hi hlowF hmet hnormal)
  have hframe' := hd Q.1
    (fun x hx ↦ hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))) m
  have hgrad := hb F hF hi hrank hlowF hmet hnormal hlow m
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨hc hw, hKU (hball (hx hw))⟩
  have hpair := cNorm_pair_le a m (isOpen_inputDomain T) hdom
    (hs.comp contDiffOn_fst (fun _ hw ↦ hw.2))
    ((phaseGradient_joint_smooth T Q).mono inter_subset_left)
  apply hpair.trans
  have horder : cNorm K (m + 2) F ≤ cNorm K (m + 4) F := cNorm_mono_order (by omega)
  have hframe'' : cNorm (closedBall a ρ) m (fun w ↦ Q.1 w.1) ≤
      (D m * ((m + 1) * A m)) * (1 + cNorm K (m + 4) F) := by
    apply hframe'.trans
    apply (mul_le_mul_of_nonneg_left hframe (hD m).le).trans
    calc
      _ = (D m * ((m + 1) * A m)) * (1 + cNorm K (m + 2) F) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) horder)
        (mul_nonneg (hD m).le (mul_nonneg (by positivity) (hA m).le))
  have hsum := add_le_add hframe'' hgrad
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ m + 1)
  exact hh.trans_eq (by ring)

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
