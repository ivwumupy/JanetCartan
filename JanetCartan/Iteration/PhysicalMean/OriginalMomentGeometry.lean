module

public import JanetCartan.Iteration.PhysicalAdjointGeometry
public import JanetCartan.Iteration.PhysicalMean.MomentMatrix

/-!
# Original-current physical geometry for the sampled moment estimate

This is the direct original-data application of the task-28 inverse geometry
to `sampledRadialMoment_L2_bound`. The coefficient profile is DERIVED from the
primitive current immersion profile, with the amplitude-test reserve already
spent. The single global joint localization retains the literal full phase
on the complete original carrier compact. No phase or inverse-direction
profile, successful inverse family, or alternate sample is assumed.

The full corrected amplitude and original scalar tester are separate actual
producers; this geometry application is not a complete mean correction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open PhysicalAdjointGeometry ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawPrimary.SliceBounds LeadingWave.FullModulation ProjectedStressFrame ResponseTransfer.GradedPrimitives

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual SAME-current joint physical trade has the moment-test reserve
from primitive immersion bounds. Constants are chosen before the current map,
original sample, fine input cutoff, requested reserve and scale. The compact
is exactly `originalTradeCompact`, not a newly selected physical support
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_original_moment_geometry_profiles
    {c C ρ : ℝ} (hP : P.IsValid c C) (hρ : ρ < T.family.radius)
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (M₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ D : ℕ → ℝ, (∀ j, 0 < D j) ∧
      (originalTradeCompact T ρ ε ⊆ shiftDomain (covectorCenter T) T.family.radius) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ M₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 3
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ rStar r₀ : ℕ, r₀ + (n / 2 + 1) + 5 ≤ rStar →
        ∀ Λ : ℝ, 1 ≤ Λ → (∀ j, cNorm KF j F ≤ B j * Λ ^ (j - rStar)) →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedSpacetimeEquiv T.data.adapted
        ∃ Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1),
        ∃ L : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1) →L[ℝ] Spacetime (n - 1),
          ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ L ∧
          (∀ q ∈ originalTradeCompact T ρ ε, Y =ᶠ[𝓝 q] averagedCovector (current T Q)) ∧
          (∀ q : Point (Euclidean n) (n - 1),
            jointCoordinateEquiv e.symm q ∈ originalTradeCompact T ρ ε →
            ∀ h η : Euclidean (n - 1),
              fderiv ℝ (fun x ↦ inner ℝ (physicalCovector e Y (x, q.2)) η) q.1
                (physicalTrade e L q h) = inner ℝ h η) ∧
          (∀ q : Point (Euclidean n) (n - 1),
            jointCoordinateEquiv e.symm q ∈ originalTradeCompact T ρ ε →
            ∀ h : Euclidean (n - 1), ‖h‖ ≤ 1 → ∀ k : ℕ,
              ‖iteratedFDeriv ℝ k (fun x ↦ physicalTrade e L (x, q.2) h) q.1‖ ≤
                D k * Λ ^ (k - (r₀ + (n / 2 + 1)))) := by
  obtain ⟨ε, hε, δ₁, hδ₁, hcompact, hfamily⟩ := exists_original_joint_trade_family T hP hρ
  obtain ⟨δ₂, hδ₂, A, hA, hprofile⟩ :=
    exists_primitive_trade_profiles (N := N) T hKF hKU hball M₀ hκmet hκ B hB
  let D := fun k ↦ 1 + |inverseConstant 2 (mixedJetConstant A) k|
  have hD (k) : 0 < D k := by dsimp only [D]; positivity
  refine ⟨ε, hε, min δ₁ δ₂, lt_min hδ₁ hδ₂, D, hD, hcompact, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose rStar r₀ horder Λ hΛ hBΛ Q e
  obtain ⟨Y, L, hY, hL, heY, heL, hid⟩ := hfamily Q (hclose.trans_le (min_le_left _ _))
  have hactual := hprofile F hF hi hrank hFM hmet hnormal hlow
    (hclose.trans_le (min_le_right _ _)) rStar (by omega) Λ hΛ hBΛ
  refine ⟨Y, L, hY, hL, heY, hid, ?_⟩
  intro q hq h hh k
  have hb := norm_jet_localized_physicalDirection_le e hL q (heL _ hq) h k
  have hc := (hactual _ (hcompact hq) k).2
  have hCD : inverseConstant 2 (mixedJetConstant A) k ≤ D k :=
    (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)
  have hcD : ‖iteratedFDeriv ℝ k
      (tradeDirection transverseInsertion (averagedCovector (current T Q)))
        (jointCoordinateEquiv e.symm q)‖ ≤ D k * Λ ^ (k - (r₀ + (n / 2 + 1))) :=
    hc.trans (mul_le_mul hCD (pow_le_pow_right₀ hΛ (by omega)) (by positivity) (hD k).le)
  exact hb.trans ((mul_le_mul_of_nonneg_left hcD (norm_nonneg h)).trans
    (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hh (mul_nonneg (hD k).le (by positivity)))))

end JanetCartan.PhysicalMean
