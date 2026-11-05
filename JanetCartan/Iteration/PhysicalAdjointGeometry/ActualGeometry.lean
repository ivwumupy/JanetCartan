module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Reference
public import JanetCartan.Iteration.PhysicalAdjointGeometry.Localization

/-!
# Actual inverse geometry of the retained raw Hamilton phase

The uniform inverse gap is a conclusion of the original current/frozen phase
comparison. The single new positive tolerance is a primitive frame C3 tolerance
on the same original state ball. It is selected before current immersions and
all frequencies. No mixed inverse or successful coefficient profile is assumed.

The fixed support inclusion below is geometric: it keeps the original carrier
and its literal displacement in the original phase ball. It never reselects or
shrinks the already supplied measurement/source cutoffs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalAdjointGeometry
open ActualCarriers FrozenMenu CurrentFullPhase
open FullPhaseCharts ActualPhase Comparison

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- The original phase-ball buffer for a carrier and its actual displacement.
Every physical coordinate remains in the first component. -/
def shiftDomain (ξ : Euclidean m) (r : ℝ) : Set (Point X m) :=
  {q | ‖q.1‖ < r ∧ dist q.2.1 ξ + ‖q.2.2‖ < r}

omit [NormedSpace ℝ X] in
/-- The buffer is one open joint domain, not separately selected for each
frequency (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem isOpen_shiftDomain (ξ : Euclidean m) (r : ℝ) :
    IsOpen (shiftDomain (X := X) ξ r) := by
  have hx : Continuous (fun q : Point X m ↦ ‖q.1‖) := by fun_prop
  have hξ : Continuous (fun q : Point X m ↦ dist q.2.1 ξ + ‖q.2.2‖) := by fun_prop
  exact (isOpen_lt hx continuous_const).inter (isOpen_lt hξ continuous_const)

/-- Every point of the literal closed segment stays in the same phase ball
(`app:ch_seed:eq:seed-quotient-integral`). -/
theorem segment_mem_phaseBall {ξ : Euclidean m} {r : ℝ} {q : Point X m}
    (hq : q ∈ shiftDomain ξ r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segment t q ∈ ball ((0 : X), ξ) r := by
  rw [mem_ball, segment_apply, Prod.dist_eq, dist_zero_right, max_lt_iff]
  refine ⟨hq.1, ?_⟩
  calc
    dist (q.2.1 + t • q.2.2) ξ ≤ dist q.2.1 ξ + ‖t • q.2.2‖ := by
      simpa only [dist_eq_norm, add_sub_right_comm] using
        norm_add_le (q.2.1 - ξ) (t • q.2.2)
    _ = dist q.2.1 ξ + t * ‖q.2.2‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ dist q.2.1 ξ + ‖q.2.2‖ :=
      add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) ht.2)
    _ < r := hq.2

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- Actual inverse of the averaged transverse mixed derivative on the full
original phase buffer. Its tolerance comes from primitive state-ball frame
closeness. The phase is literally `current T Q`, and the bounds precede all
current maps, sample carriers, band limits, and inverse frequencies
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_current_mixed_inverse :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 3
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ q ∈ shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius,
        IsUnit (mixedTranspose transverseInsertion (averagedCovector (current T Q)) q) ∧
          ‖Ring.inverse (mixedTranspose transverseInsertion (averagedCovector (current T Q)) q)‖ ≤ 2 := by
  obtain ⟨δ, hδ, hcompare⟩ := exists_current_comparison_threshold T 2
    (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ q hq
  let Ω := ball ((0 : Spacetime (n - 1)), covectorCenter T) T.family.radius
  let Ωbig := ball ((0 : Spacetime (n - 1)), covectorCenter T) (2 * T.family.radius)
  let V := shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius
  let S₀ := referencePhase (dispersion T)
  have hR : T.family.radius ≤ 2 * T.family.radius := by linarith [T.family.radius_pos]
  have hSbig : ContDiffOn ℝ ∞ (current T Q) Ωbig := current_smooth T Q
  have hS₀big : ContDiffOn ℝ ∞ S₀ Ωbig :=
    contDiffOn_referencePhase (dispersion_smooth T)
      (fun p hp ↦ (mem_ball.mp hp).trans_le' (le_max_right _ _))
  have hS := hSbig.mono (ball_subset_ball hR)
  have hS₀ := hS₀big.mono (ball_subset_ball hR)
  have hV := isOpen_shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius
  have hseg : ∀ p ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t p ∈ Ω :=
    fun _ hp _ ht ↦ segment_mem_phaseBall hp ht
  have hjet : ∀ j ≤ 2, ∀ p ∈ Ω,
      ‖iteratedFDeriv ℝ j (current T Q - S₀) p‖ ≤ (1 / 8 : ℝ) := by
    intro j hj p hp
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall ((0 : Spacetime (n - 1)), covectorCenter T) T.family.radius)
      (fun w hw ↦ ((hSbig.sub hS₀big).contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith [T.family.radius_pos]) hw))).of_le (by simp))
      (ball_subset_closedBall hp) hj).trans
    exact (hcompare Q hQ _ Subset.rfl).le
  have hC₀ : mixedTranspose transverseInsertion (averagedCovector S₀) q = 1 := by
    apply mixedTranspose_reference isOpen_ball
      ((dispersion_smooth T).mono (ball_subset_ball hR)) q
    · intro t ht
      exact (mem_ball.mp (hseg q hq t ht)).trans_le' (le_max_right _ _)
    · exact ((contDiffOn_averagedCovector isOpen_ball hV hS₀ hseg).contDiffAt
        (hV.mem_nhds hq)).differentiableAt (by simp)
  have hb := norm_mixedTranspose_sub_le norm_transverseInsertion_le isOpen_ball hV
    hS hS₀ hseg hjet hq
  rw [hC₀] at hb
  exact inverse_of_mixed_near_one _ (hb.trans (by norm_num))

/-- The actual original Hamilton phase supplies one jointly smooth global
trade family on any prescribed compact subset of its original buffer. Only
primitive frame closeness and fixed geometric support inclusion are inputs;
invertibility and the exact physical derivative identity are conclusions
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_current_joint_trade_extension :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 3
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ K : Set (Point (Spacetime (n - 1)) (n - 1)), IsCompact K →
        K ⊆ shiftDomain (covectorCenter T) T.family.radius →
      ∃ Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1),
      ∃ L : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1) →L[ℝ] Spacetime (n - 1),
        ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ L ∧
        (∀ q ∈ K, Y =ᶠ[𝓝 q] averagedCovector (current T Q)) ∧
        (∀ q ∈ K, L =ᶠ[𝓝 q] tradeDirection transverseInsertion (averagedCovector (current T Q))) ∧
        ∀ q ∈ K, ∀ h η : Euclidean (n - 1),
          fderiv ℝ (fun x ↦ inner ℝ (Y (x, q.2)) η) q.1 (L q h) = inner ℝ h η := by
  obtain ⟨δ, hδ, hunit⟩ := exists_current_mixed_inverse T
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ K hK hKV
  have hV := isOpen_shiftDomain (X := Spacetime (n - 1)) (covectorCenter T) T.family.radius
  apply exists_joint_trade_extension transverseInsertion hV hK hKV
  · apply contDiffOn_averagedCovector isOpen_ball hV (current_smooth T Q)
    intro q hq t ht
    exact ball_subset_ball (by linarith [T.family.radius_pos]) (segment_mem_phaseBall hq ht)
  · exact fun q hq ↦ (hunit Q hQ q hq).1

end JanetCartan.PhysicalAdjointGeometry
