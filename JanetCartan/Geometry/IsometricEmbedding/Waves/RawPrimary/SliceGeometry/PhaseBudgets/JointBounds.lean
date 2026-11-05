module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.PhaseBudgets.PrimitiveJets

/-!
# Uniform joint budgets for the canonical integral quotient

The constants precede the immersion. The primitive full phase estimate has
immersion cost `m+3`, and the integral quotient uses phase order `k+1`.
Thus joint orders through `20*((n-1)+1)+1` fit precisely the fixed immersion
budget at `20*((n-1)+1)+5`. The final restriction to `input_jets` uses this
extra joint order for the actual epsilon derivative.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers FrozenMenu CurrentFullPhase SliceBounds
open FullPhaseCharts.ActualPhase FourierIntegral.NormalOneHigh ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

/-- Finite joint budgets of the SAME raw integral quotient, chosen from the
fixed domains and primitive immersion budget before the varying immersion.
No phase, chart-inverse or normal-data bound is an input. The consumer is
`exists_canonicalSlicePhase_input_budgets`, including its epsilon derivative
(`app:ch_seed:eq:seed-phase-tame`, `app:ch_seed:eq:seed-quotient-integral`). -/
theorem exists_canonicalSlicePhase_joint_budgets (z : Euclidean 3)
    {a e b : ℝ} (ha : 0 < a) (ha' : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hb : ball (T.reference.spatialPatch z) b ⊆
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
        ∀ q ∈ sliceClosedCore n a e, ∀ k ≤ 20 * ((n - 1) + 1) + 1,
          ‖iteratedFDeriv ℝ k
            (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)) q‖ ≤
              B k := by
  obtain ⟨A, hA, hphase⟩ := LeadingWave.FullModulation.exists_phase_projected_sharp_bound
    (N := embeddingDimension n) T hK hKU hball M hγ hκ
  obtain ⟨c, hc, hmap⟩ := exists_rawSliceShift_jetBounds (T.reference.spatialPatch z)
    (isCompact_sliceClosedCore (n := n) a e)
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
  intro F hF hi hrank hFM hmet hnormal hlow Q q hq k hk
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
    (fun s hs j _ _ ↦ hmap s hs q hq j)
    (fun j _ ↦ norm_iteratedFDeriv_le_cNorm (isCompact_sliceClosedCore a e)
      (by fun_prop) hq le_rfl)
  have hh : ‖iteratedFDeriv ℝ k
      (rawSlicePhaseExtension (canonicalBasePhase T Q) (T.reference.spatialPatch z)) q‖ ≤ B k := by
    simpa only [one_pow, mul_one, B] using hbound
  linarith

end JanetCartan.RawPrimary.SliceGeometry
