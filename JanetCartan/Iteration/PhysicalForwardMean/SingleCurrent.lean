module

public import JanetCartan.Iteration.PhysicalForwardMean.SingleOriginal
public import JanetCartan.Iteration.PhysicalForwardMean.RetainedPhaseProfiles

/-!
# Actual-current individual forward estimate with the original native phase

All phase profiles below are PRODUCED from primitive SAME-current immersion
bounds and the SAME28 localized-Y germ. The analysis phase is literally the
original globally smooth retained phase, so there is no alternative Φ, no
pointwise phase-agreement premise and no assumed phase-jet success bound.
The original scalar36 bare tester acts on the original shell measure, and the
output is the SAME complete halfweighted raw integral with k+1/2 moments.

Consumer: mean14's individual block-field bound, `app:ch_mean_pairs:eq:block-fields`.
The complete A13 amplitude and actual36 tester identities remain explicit
independent producer inputs. This does not claim their original-data parent.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalForwardMean
open PhysicalMean PhysicalSamplingShells PhysicalScalarChannel RawInputPartition
open Sampling Sampling.MeasuredAmplitude SamplingKernelBounds
open PhysicalAdjointGeometry ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open ContinuumRow Pseudodifferential AmplitudeBound RawPrimary.SliceBounds ProjectedStressFrame

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
local notation "E" => Euclidean (m + 1)
local notation "Eta" => Euclidean (m + 1 - 1)

/-- Pre-current constants for the ORIGINAL full individual raw field, with all
physical native phase profiles discharged by primitive current geometry and
SAME28 germ data. There are no quantitative frequency-derivative inputs and no
shell-ceiling loss (`app:ch_mean_pairs:eq:block-fields`). -/
theorem exists_originalCurrent_singleForward_constants
    (T : PatchQuantitativeFamily P U hU)
    (χ : ContDiffBump (0 : E)) (center : E × (Euclidean 3 × Eta))
    {ρ : ℝ} (hρ : 0 < ρ) {ηb : Eta} {r : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r)
    {K : Set E} (hK : IsCompact K) (hχK : ∀ x ∈ K, χ x = 1)
    (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {KF : Set E} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : E) T.data.localReference.stateRadius ⊆ KF)
    (M₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    (B a : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (ha : ∀ j, 0 ≤ a j) :
    ∃ ε > (0 : ℝ), ∃ p : ℕ → ℝ, (∀ j, 0 < p j) ∧
      ∀ (F : E → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ M₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress (m+1)) < T.family.threshold,
        cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 3
          (projectedStress F - fun _ ↦ cubeStress (m+1)) < ε →
        ∀ rStar s0 : ℕ, s0 + ((m+1)/2+1) + 5 ≤ rStar →
        ∀ Λ : ℝ, 1 ≤ Λ → (∀ j, cNorm KF j F ≤ B j * Λ^(j-rStar)) →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let e := adaptedSpacetimeEquiv T.data.adapted
        ∀ Y : Point (Spacetime (m+1-1)) (m+1-1) → Eta, ContDiff ℝ ∞ Y →
        ∀ (τ : ℝ) (z : Euclidean 3), τ ≠ 0 →
        let ζ := extendedRetainedCarrier T center.2.1 hρ z
        ∀ J : ℕ,
        let μ := annularShellMeasure (n := m+1) (refinedRadius (J := J))
        ∀ A : RefinedIndex J → Eta → E → ℂ,
        (∀ i, ContDiff ℝ ∞ (Function.uncurry (A i))) →
        (∀ i η, tsupport (A i η) ⊆ K) →
        (∀ (i : RefinedIndex J) (η : Eta), singleBareScalarMask (originalForwardDetector hηb hr) (i,η) ≠ 0 →
          ∀ x ∈ K, (e.symm x, ζ, τ • η) ∈ shiftDomain (covectorCenter T) T.family.radius) →
        (∀ (i : RefinedIndex J) (η : Eta), singleBareScalarMask (originalForwardDetector hηb hr) (i,η) ≠ 0 →
          ∀ x ∈ K, Y =ᶠ[𝓝 (e.symm x, ζ, τ • η)] averagedCovector (current T Q)) →
        (∀ (i : RefinedIndex J) (η : Eta), singleBareScalarMask (originalForwardDetector hηb hr) (i,η) ≠ 0 →
          ∀ x ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (A i η) x‖ ≤
            a j * Λ^(j-(s0+((m+1)/2+1)))) →
        ∀ Tbare : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure E),
        (∀ v : Lp ℂ 2 μ, Tbare v =ᵐ[volume] fun x ↦
          ∫ u, originalBareNativeKernel T Q χ center hρ hηb hr τ z x u * v u ∂μ) →
        ∀ v : Lp ℂ 2 μ,
        let w := fun x ↦ ∫ u, physicalForwardKernel (singleRetainedForwardPhase T Q center hρ τ z)
          (fun u : RefinedIndex J × Eta ↦
            forwardScalarBandMask (m+1) (originalForwardDetector hηb hr) u.1.1.val u.2)
          (fun u ↦ A u.1 u.2) x u * v u ∂μ
        ContDiff ℝ ∞ w ∧ tsupport w ⊆ K ∧
          (∀ ds : List (Fin (m+1)), MemLp (euclideanCoordinateDerivList ds w) 2 volume) ∧
          ∀ ds : List (Fin (m+1)),
            (eLpNorm (euclideanCoordinateDerivList ds w) 2 volume).toReal ≤
              forwardDerivativeConstant (m+1) Rbox a p ds.length * ‖Tbare‖ *
                ∑ k ∈ Finset.range (ds.length+1), Λ^(ds.length-k-s0) *
                  (eLpNorm (fun u : RefinedIndex J × Eta ↦
                    ((‖u.2‖^((k : ℝ)+1/2) : ℝ) : ℂ) * v u) 2 μ).toReal := by
  obtain ⟨ε, hε, p, hp, hphase⟩ :=
    exists_original_retainedPhase_profiles (N := N) T hKF hKU hball M₀ hκmet hκ B hB
  refine ⟨ε, hε, p, hp, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose rStar s0 horder Λ hΛ hBF Q e
    Y hY τ z hτ ζ J μ A hA hAK hdomain hgerm hAj Tbare hTbare v
  let Φ : RefinedIndex J → Eta → E → ℝ := fun _ η x ↦
    rawPrimaryPhaseDifference (extendedRetainedPhase T Q) ζ τ x η
  have hΦ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i)) := by
    intro i
    exact contDiff_retainedRawPhase T Q ζ τ
  have hΦj : ∀ (i : RefinedIndex J) (η : Eta),
      singleBareScalarMask (originalForwardDetector hηb hr) (i,η) ≠ 0 →
      ∀ x ∈ K, ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y / ‖η‖) x‖ ≤
        p j * Λ^(j-1-(s0+((m+1)/2+1))) := by
    intro i η hm x hx j hj
    have hh : (1 : ℝ) < ‖η‖ := one_lt_norm_of_singleBareScalarMask_ne_zero
      (n := m+1) (J := J) (u := (i,η)) hηb hr hm
    have hη : η ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hh)
    exact hphase F hF hi hrank hFM hmet hnormal hlow hclose rStar s0 horder Λ hΛ hBF
      Y hY x ζ η τ hτ (hdomain i η hm x hx) (hgerm i η hm x hx) hη j hj
  exact originalSingleForward_physical_halfMoment_bounds T Q χ center hρ τ z hηb hr Φ A
    hΦ hA hK hAK (fun _ _ _ _ ↦ rfl) hχK Rbox hbox hΛ a p ha (fun j ↦ (hp j).le)
    hAj hΦj Tbare hTbare v

end JanetCartan.PhysicalForwardMean
