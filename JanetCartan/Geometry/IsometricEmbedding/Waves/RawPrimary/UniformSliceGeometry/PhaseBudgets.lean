module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.PhaseBudgets

/-!
# Uniform joint budgets for the canonical integral quotient

The constants precede every carrier label and the immersion. The primitive
full phase estimate has immersion cost `m+3`, and the integral quotient uses phase order `k+1`.
Thus joint orders through `20*((n-1)+1)+1` fit precisely the fixed immersion
budget at `20*((n-1)+1)+5`. The final restriction to `input_jets` uses this
extra joint order for the actual epsilon derivative.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.UniformSliceGeometry
open SliceGeometry ActualCarriers FrozenMenu CurrentFullPhase SliceBounds
open FullPhaseCharts.ActualPhase FourierIntegral.NormalOneHigh ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

private theorem exists_uniform_rawSliceShift_jetBounds {c C : ℝ} (hP : P.IsValid c C) (a e : ℝ) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ z ∈ parameterCube P.radius, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ q ∈ sliceClosedCore n a e, ∀ j,
        ‖iteratedFDeriv ℝ j (rawSliceShift (T.reference.spatialPatch z) s) q‖ ≤ b j := by
  have hsub : parameterCube P.radius ⊆ parameterInterior (2 * P.radius) := by
    intro z hz i
    exact (hz i).trans_lt (by linarith [hP.1])
  obtain ⟨D, hD⟩ := (isCompact_parameterCube P.radius).exists_bound_of_continuousOn
    ((T.reference.spatialPatch_smooth hP).continuousOn.mono hsub)
  obtain ⟨b, hb, hmap⟩ := exists_rawSliceShift_jetBounds (0 : E)
    (isCompact_sliceClosedCore (n := n) a e)
  refine ⟨fun j ↦ b j + max D 0, fun j ↦ add_nonneg (hb j) (le_max_right _ _), ?_⟩
  intro z hz s hs q hq j
  have heq : rawSliceShift (T.reference.spatialPatch z) s =
      rawSliceShift (0 : E) s +
        fun _ : ℝ × (ℝ × E) × E ↦ ((0 : ℝ × E), T.reference.spatialPatch z) := by
    funext q
    simp [rawSliceShift, add_comm]
  rw [heq, iteratedFDeriv_add_apply (by unfold rawSliceShift; fun_prop) contDiffAt_const]
  apply (norm_add_le _ _).trans
  apply add_le_add (hmap s hs q hq j)
  cases j with
  | zero => simpa using (hD z hz).trans (le_max_left D 0)
  | succ j =>
    simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using (le_max_right D (0 : ℝ))

/-- Finite joint budgets of the SAME raw integral quotient, chosen from the
fixed domains and primitive immersion budget before every carrier label and
immersion.
No phase, chart-inverse or normal-data bound is an input. The consumer is
`exists_uniform_canonicalSlicePhase_input_budgets`, including its epsilon derivative
(`app:ch_seed:eq:seed-phase-tame`, `app:ch_seed:eq:seed-quotient-integral`). -/
theorem exists_uniform_canonicalSlicePhase_joint_budgets {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {a e b : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ∀ z ∈ parameterCube P.radius, ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K (20 * ((n - 1) + 1) + 5) F ≤ M →
        (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ z ∈ parameterCube P.radius, ∀ q ∈ sliceClosedCore n a e, ∀ k ≤ 20 * ((n - 1) + 1) + 1,
          ‖iteratedFDeriv ℝ k
            (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)) q‖ ≤
              B k := by
  obtain ⟨A, hA, hphase⟩ := LeadingWave.FullModulation.exists_phase_projected_sharp_bound
    (N := embeddingDimension n) T hK hKU hball M hγ hκ
  obtain ⟨c, hc, hmap⟩ := exists_uniform_rawSliceShift_jetBounds T hP a e
  let p : ℕ → ℝ := fun j ↦ 2 ^ (j + 1) * A (j + 1) * (1 + max M 0)
  let d : ℕ → ℝ := fun j ↦ cNorm (sliceClosedCore n a e) j
    (fun q : ℝ × (ℝ × E) × E ↦ q.2.2)
  have hp (j : ℕ) : 0 ≤ p j := by
    dsimp only [p]
    exact mul_nonneg (mul_nonneg (by positivity) (hA _).le)
      (by linarith [le_max_right M 0])
  have hd (j : ℕ) : 0 ≤ d j := cNorm_nonneg _ _ _
  let B := sliceMaskJetConstant (compositionBudget p c) d
  have hB (j : ℕ) : 0 ≤ B j :=
    sliceMaskJetConstant_nonneg (compositionBudget_nonneg hp hc) hd j
  refine ⟨fun j ↦ 1 + B j, fun j ↦ by linarith [hB j], ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow Q z hz q hq k hk
  have hb := hb z hz
  have hlowF : cNorm K 4 F ≤ M :=
    (cNorm_mono_order (by omega : 4 ≤ 20 * ((n - 1) + 1) + 5)).trans hFM
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (canonicalBasePhase T Q))
      (sliceAdaptedDomain T a ×ˢ ball (T.reference.spatialPatch z) b) := by
    apply (canonicalBasePhase_smooth T Q).mono
    intro w hw
    refine ⟨ball_subset_ball (by linarith [T.family.radius_pos]) hw.1, ?_⟩
    exact ball_subset_ball ((min_le_left _ _).trans (by linarith [T.family.radius_pos])) (hb hw.2)
  have hIW : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hprimitive (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (fun w : (ℝ × E) × E ↦
        fderiv ℝ (canonicalBasePhase T Q w.1) w.2)
        (rawSliceShift (T.reference.spatialPatch z) s q)‖ ≤ p j := by
    have hmem := rawSliceShift_mapsTo_sliceShiftDomain T z he heb s (hIW hs)
      (sliceClosedCore_subset_shiftDomain T ha he hq)
    apply (norm_iteratedFDeriv_canonicalBasePhase_covector_le T Q z ha' hb hmem j).trans
    have hh := hphase F hF hi hrank hlowF hmet hnormal hlow (j + 1)
      (closedBall (0, covectorCenter T) T.family.radius) Subset.rfl
    have hFM' : cNorm K (j + 1 + 3) F ≤ max M 0 :=
      ((cNorm_mono_order (by omega : j + 1 + 3 ≤ 20 * ((n - 1) + 1) + 5)).trans hFM).trans
        (le_max_left _ _)
    calc
      _ ≤ 2 ^ (j + 1) * (A (j + 1) * (1 + cNorm K (j + 1 + 3) F)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ p j := by
        dsimp only [p]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add_right hFM' 1) (hA _).le) (by positivity)
  have hbound := norm_iteratedFDeriv_rawSlicePhaseExtension_le
    (k := k) (R := 0) (L := 1)
    (isOpen_sliceAdaptedDomain T a) isOpen_ball (isOpen_sliceShiftDomain T a e)
    isOpen_Ioo hIW hS (rawSliceShift_mapsTo_sliceShiftDomain T z he heb)
    (sliceClosedCore_subset_shiftDomain T ha he hq) le_rfl hp hc hd
    (fun s hs j hj ↦ by simpa using hprimitive s hs j hj)
    (fun s hs j _ _ ↦ hmap z hz s hs q hq j)
    (fun j _ ↦ norm_iteratedFDeriv_le_cNorm (isCompact_sliceClosedCore a e)
      (by fun_prop) hq le_rfl)
  have hh : ‖iteratedFDeriv ℝ k
      (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)) q‖ ≤ B k := by
    simpa only [one_pow, mul_one, B] using hbound
  linarith

/-- Uniform finite phase budgets for the actual canonical raw slices, before
the carrier label varies, including the ordinary epsilon derivative at zero
and the upper endpoint. The SAME
projected stress and Hamilton phase are retained. Only the fixed immersion
budget at `20*((n-1)+1)+5` and the primitive projected-frame hypotheses are
used. This supplies the phase fields of `UniformNormalData.input_jets`
(`app:ch_seed:eq:seed-phase-tame`, `app:ch_seed:eq:seed-quotient-integral`,
`app:ch_waves:setup:oscillatory`). -/
theorem exists_uniform_canonicalSlicePhase_input_budgets {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {a e b : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ∀ z ∈ parameterCube P.radius, ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
        (hrank : HasFullNormalRankOn F U),
        cNorm K (20 * ((n - 1) + 1) + 5) F ≤ M →
        (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ z ∈ parameterCube P.radius, ∀ t ∈ Ioo (-a) a, ∀ ε ∈ Icc 0 e,
          ∀ w ∈ sliceSpatialDomain n a ×ˢ sliceInputDomain n,
          ∀ k ≤ 20 * ((n - 1) + 1),
            ‖iteratedFDeriv ℝ k (Function.uncurry (canonicalSlicePhase T Q z t ε)) w‖ +
              ‖deriv (fun ε' ↦ iteratedFDeriv ℝ k
                (Function.uncurry (canonicalSlicePhase T Q z t ε')) w) ε‖ ≤ C k := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_canonicalSlicePhase_joint_budgets
    T hP ha ha' he heb hb hK hKU hball M hγ hκ
  refine ⟨fun k ↦ B k + B (k + 1), fun k ↦ add_pos (hB k) (hB (k + 1)), ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow Q z hz t ht ε hε w hw k hk
  have hq := sliceClosedCore_contains ht hε ⟨subset_closure hw.1, subset_closure hw.2⟩
  have hj := hbound F hF hi hrank hFM hmet hnormal hlow z hz (ε, (t, w.1), w.2) hq
  exact (canonicalSlicePhase_inputJets_le_joint T Q z ha ha' he heb (hb z hz) ht hε hw k).trans
    (add_le_add (hj k (by omega)) (hj (k + 1) (by omega)))

end JanetCartan.RawPrimary.UniformSliceGeometry
