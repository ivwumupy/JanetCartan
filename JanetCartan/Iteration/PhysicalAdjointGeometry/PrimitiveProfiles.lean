module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.ActualGeometry
public import JanetCartan.Iteration.PhysicalAdjointGeometry.Reserve

/-!
# Actual current-phase trade profiles from primitive immersion data

The constants and frame tolerance are chosen before the varying immersion,
scale, reserve, sample carrier and frequency. The only high-order input is the
original immersion profile. The retained Hamilton-phase theorem produces all
phase derivatives; averaging, mixed differentiation and inversion then produce
the actual coefficient profiles with fixed costs four and five.

This is the original-data analytic producer for
`PhysicalMean.sampledAdjointMomentTemplate_physical_jet_le`. Physical-history
admission supplies the primitive immersion profile and low geometric gaps from
its already constructed same current map; no coefficient-success predicate is
an input to this theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalAdjointGeometry
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open FullPhaseCharts ActualPhase ResponseTransfer.GradedPrimitives

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual uniform all-order profiles for the literal averaged phase and its
inverse-transpose directions. The immersion reserve loses exactly four orders
for `Y` and five for `L`, including adapted time. Every phase/inverse estimate
is a conclusion from primitive immersion data on the same retained chart
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_primitive_trade_profiles
    {KF : Set (Euclidean n)} (hKF : IsCompact KF) (hKU : KF ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ KF)
    (M₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ δ > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm KF 4 F ≤ M₀ →
        (∀ x ∈ KF, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ KF, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 3
            (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∀ (rStar : ℕ), 5 ≤ rStar → ∀ Λ : ℝ, 1 ≤ Λ →
        (∀ j, cNorm KF j F ≤ B j * Λ ^ (j - rStar)) →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ q ∈ shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius,
          ∀ k : ℕ,
            ‖iteratedFDeriv ℝ k (averagedCovector (current T Q)) q‖ ≤
                (2 ^ k * A (k + 1)) * Λ ^ (k - (rStar - 4)) ∧
            ‖iteratedFDeriv ℝ k
              (tradeDirection transverseInsertion (averagedCovector (current T Q))) q‖ ≤
                inverseConstant 2 (mixedJetConstant A) k * Λ ^ (k - (rStar - 5)) := by
  obtain ⟨δ, hδ, hinverse⟩ := exists_current_mixed_inverse T
  obtain ⟨Pjet, hPjet, hphase⟩ := exists_current_projected_sharp_bound (N := N) T
    hKF hKU hball M₀ hκmet hκ
  let A : ℕ → ℝ := fun j ↦ Pjet j * (1 + B (j + 3))
  have hA (j : ℕ) : 0 < A j := mul_pos (hPjet j) (by linarith [hB (j + 3)])
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose rStar hrStar Λ hΛ hprofile Q q hq k
  let Ω := ball ((0 : Spacetime (n - 1)), covectorCenter T) T.family.radius
  let Ωbig := ball ((0 : Spacetime (n - 1)), covectorCenter T) (2 * T.family.radius)
  let V := shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius
  have hSbig : ContDiffOn ℝ ∞ (current T Q) Ωbig := current_smooth T Q
  have hS : ContDiffOn ℝ ∞ (current T Q) Ω :=
    hSbig.mono (ball_subset_ball (by linarith [T.family.radius_pos]))
  have hV := isOpen_shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius
  have hseg : ∀ p ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t p ∈ Ω :=
    fun _ hp _ ht ↦ segment_mem_phaseBall hp ht
  have hphasejet : ∀ j, ∀ p ∈ Ω,
      ‖iteratedFDeriv ℝ j (current T Q) p‖ ≤ A j * Λ ^ (j - (rStar - 3)) := by
    intro j p hp
    have hn := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall ((0 : Spacetime (n - 1)), covectorCenter T) T.family.radius)
      (fun w hw ↦ (hSbig.contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith [T.family.radius_pos]) hw))).of_le
          (by simp : (j : ℕ∞ω) ≤ ∞)) (ball_subset_closedBall hp) le_rfl
    have hs := hphase F hF hi hrank hFM hmet hnormal hlow j
      (closedBall ((0 : Spacetime (n - 1)), covectorCenter T) T.family.radius) Subset.rfl
    apply (hn.trans hs).trans
    have he : j + 3 - rStar = j - (rStar - 3) := by omega
    have hf := hprofile (j + 3)
    rw [he] at hf
    have h1 := one_le_pow₀ hΛ (n := j - (rStar - 3))
    calc
      _ ≤ Pjet j * (Λ ^ (j - (rStar - 3)) + B (j + 3) * Λ ^ (j - (rStar - 3))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hf) (hPjet j).le
      _ = A j * Λ ^ (j - (rStar - 3)) := by dsimp [A]; ring
  have hY := norm_jet_averagedCovector_reserve_le isOpen_ball hV hS hseg
    (by omega : 1 ≤ rStar - 3) (fun j _ p hp ↦ hphasejet j p hp) hq (k := k)
  have hgap := hinverse Q hclose q hq
  have hL := norm_jet_tradeDirection_reserve_le norm_transverseInsertion_le isOpen_ball hV hS hseg
    (fun j ↦ (hA j).le) hΛ (by omega : 2 ≤ rStar - 3)
    (fun j _ p hp ↦ hphasejet j p hp) hq hgap.1 hgap.2 (k := k)
  have he₁ : rStar - 3 - 1 = rStar - 4 := by omega
  have he₂ : rStar - 3 - 2 = rStar - 5 := by omega
  exact ⟨by simpa only [he₁] using hY, by simpa only [he₂] using hL⟩

end JanetCartan.PhysicalAdjointGeometry
