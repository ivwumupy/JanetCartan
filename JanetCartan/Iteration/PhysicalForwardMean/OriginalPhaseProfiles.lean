module

public import JanetCartan.Iteration.PhysicalAdjointGeometry

/-!
# Actual original-current normalized phase profiles for the forward mean field

The phase input of `sampledForward_physical_coordinate_bounds` is produced here
from primitive immersion profiles, original metric/normal gaps and original
projected-frame closeness. The SAME globally localized averaged covector chosen
by the adjoint geometry is accepted through its literal germ, not reselected.
No phase-profile or derivative-trade success bound is assumed. Every physical
derivative, including adapted time, is included and no initial-frequency loss
occurs. The scalar amplitude-test reserve is paid exactly once.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open PhysicalAdjointGeometry ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawPrimary.SliceBounds LeadingWave.FullModulation ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The SAME full physical sampled phase, using the original joint localized Y,
carrier ζ and literal displacement τ eta. No leading-phase substitution occurs. -/
def originalSampledPhysicalPhase
    (Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1))
    (ζ : Euclidean (n - 1)) (τ : ℝ) (η : Euclidean (n - 1)) (x : Euclidean n) : ℝ :=
  inner ℝ (physicalCovector (adaptedSpacetimeEquiv T.data.adapted) Y (x,ζ,τ • η)) η

/-- The actual fixed-sample full phase is jointly smooth in frequency and
physical space, without quantitative frequency derivative assumptions. -/
theorem contDiff_originalSampledPhysicalPhase
    {Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1)} (hY : ContDiff ℝ ∞ Y)
    (ζ : Euclidean (n - 1)) (τ : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (originalSampledPhysicalPhase T Y ζ τ)) := by
  apply ((contDiff_physicalCovector (adaptedSpacetimeEquiv T.data.adapted) hY).comp
    (show ContDiff ℝ ∞ (fun q : Euclidean (n - 1) × Euclidean n ↦
      (q.2,ζ,τ • q.1)) from by fun_prop)).inner ℝ contDiff_fst

/-- Exact original raw phase equality on the original source germ. This is the
source-local `hagree` of the sampled forward theorem, not an output estimate. -/
theorem literal_rawPhase_eq_originalSampledPhysicalPhase (Q : _)
    {Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1)}
    {x : Euclidean n} {ζ η : Euclidean (n - 1)} {τ : ℝ} (hτ : τ ≠ 0)
    (hq : ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ, τ • η) ∈
      shiftDomain (covectorCenter T) T.family.radius)
    (heY : Y =ᶠ[𝓝 ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ, τ • η)]
      averagedCovector (current T Q)) :
    (phase T Q x (ζ + τ • η) - phase T Q x ζ) / τ =
      originalSampledPhysicalPhase T Y ζ τ η x :=
  literal_rawPhase_eq_inner_physicalCovector T Q hτ hq heY

/-- Primitive SAME-current data produce the full normalized positive physical
phase jets required by the forward binary branches. Constants precede the
current map, reserve, scale, sample and cutoff. Any SAME original localized Y
may be used; no new phase family is selected
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-fields`). -/
theorem exists_original_normalizedPhase_profiles
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (M₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ δ > (0 : ℝ), ∃ D : ℕ → ℝ, (∀ j, 0 < D j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ M₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 3
          (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ rStar s0 : ℕ, s0 + (n / 2 + 1) + 5 ≤ rStar →
        ∀ Λ : ℝ, 1 ≤ Λ → (∀ j, cNorm KF j F ≤ B j * Λ ^ (j - rStar)) →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedSpacetimeEquiv T.data.adapted
        ∀ Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1), ContDiff ℝ ∞ Y →
        ∀ q : Point (Euclidean n) (n - 1),
          jointCoordinateEquiv e.symm q ∈ shiftDomain (covectorCenter T) T.family.radius →
          Y =ᶠ[𝓝 (jointCoordinateEquiv e.symm q)] averagedCovector (current T Q) →
          ∀ η : Euclidean (n - 1), η ≠ 0 → ∀ k : ℕ, 1 ≤ k →
            ‖iteratedFDeriv ℝ k
              (fun x ↦ inner ℝ (physicalCovector e Y (x, q.2)) η / ‖η‖) q.1‖ ≤
                D k * Λ ^ (k - 1 - (s0 + (n / 2 + 1))) := by
  obtain ⟨δ, hδ, A, hA, hprofile⟩ :=
    exists_primitive_trade_profiles (N := N) T hKF hKU hball M₀ hκmet hκ B hB
  let D := fun k ↦ 2 ^ k * A (k+1)
  have hD (k) : 0 < D k := mul_pos (pow_pos (by norm_num) _) (hA (k+1))
  refine ⟨δ, hδ, D, hD, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose rStar s0 horder Λ hΛ hBΛ Q e Y hY q hq heY η hη k _hk
  have hactual := hprofile F hF hi hrank hFM hmet hnormal hlow hclose rStar
    (by omega) Λ hΛ hBΛ (jointCoordinateEquiv e.symm q) hq k
  exact (norm_jet_localized_normalized_phase_le e hY q heY hη k).trans
    (hactual.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ (by omega)) (hD k).le))

end JanetCartan.PhysicalForwardMean
