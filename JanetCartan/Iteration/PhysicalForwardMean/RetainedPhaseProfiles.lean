module

public import JanetCartan.Iteration.PhysicalForwardMean.RetainedPhaseGerm

/-!
# Primitive physical profiles for the ORIGINAL retained native full phase

The pre-current constants of the actual28 phase producer transfer through the
proved PHYSICAL GERM identity to the literal retained phase already used by
original scalar26/36. Thus a parent can choose Φ to be the ORIGINAL globally
smooth native phase itself; it need not change the tester phase on χstar.
Only original primitive current-immersion data and the SAME28 Y germ occur.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open PhysicalAdjointGeometry ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawPrimary.SliceBounds LeadingWave.FullModulation ProjectedStressFrame Sampling.MeasuredAmplitude

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (m + 1)
local notation "Eta" => Euclidean (m + 1 - 1)

/-- Actual primitive SAME-current data produce the normalized positive physical
jets of the ORIGINAL native retained full phase. Constants are chosen before
F, reserve, scale, carriers, shifts and samples. There is no assumed native
phase profile and no new Y selection (`app:ch_mean_pairs:eq:block-fields`). -/
theorem exists_original_retainedPhase_profiles
    {KF : Set E} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : E) T.data.localReference.stateRadius ⊆ KF)
    (M₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ δ > (0 : ℝ), ∃ D : ℕ → ℝ, (∀ j, 0 < D j) ∧
      ∀ (F : E → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ M₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 3
          (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
        ∀ rStar s0 : ℕ, s0 + ((m + 1) / 2 + 1) + 5 ≤ rStar →
        ∀ Λ : ℝ, 1 ≤ Λ → (∀ j, cNorm KF j F ≤ B j * Λ ^ (j - rStar)) →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedSpacetimeEquiv T.data.adapted
        ∀ Y : Point (Spacetime (m + 1 - 1)) (m + 1 - 1) → Eta, ContDiff ℝ ∞ Y →
        ∀ (x : E) (ζ η : Eta) (τ : ℝ), τ ≠ 0 →
          (e.symm x, ζ, τ • η) ∈ shiftDomain (covectorCenter T) T.family.radius →
          Y =ᶠ[𝓝 (e.symm x, ζ, τ • η)] averagedCovector (current T Q) →
          η ≠ 0 → ∀ k : ℕ, 1 ≤ k →
            ‖iteratedFDeriv ℝ k
              (fun y ↦ rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ y η / ‖η‖) x‖ ≤
                D k * Λ ^ (k - 1 - (s0 + ((m + 1) / 2 + 1))) := by
  obtain ⟨δ, hδ, D, hD, hprofile⟩ :=
    exists_original_normalizedPhase_profiles (N := N) T hKF hKU hball M₀ hκmet hκ B hB
  refine ⟨δ, hδ, D, hD, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose rStar s0 horder Λ hΛ hBΛ Q e Y hY x ζ η τ hτ hq heY hη k hk
  rw [iteratedFDeriv_normalizedRetainedRawPhase_eq T Q hτ hq heY k]
  exact hprofile F hF hi hrank hFM hmet hnormal hlow hclose rStar s0 horder Λ hΛ hBΛ
    Y hY (x,ζ,τ • η) hq heY η hη k hk

end JanetCartan.PhysicalForwardMean
