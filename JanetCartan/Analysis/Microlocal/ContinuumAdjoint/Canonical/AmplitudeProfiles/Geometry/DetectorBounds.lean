module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.Smoothness

/-!
# Detector bounds from the same primitive immersion budget

The existing `CanonicalBudgets.Detector` supplies the literal quadratic formula
and smoothness. Here its compact input range is obtained from the order-zero
case of the primitive projected-input bound. Thus no further stress-smallness
hypothesis is needed beyond membership of the actual `Q` in the carrier family.
Consumer: `Geometry.ComponentBounds` (`bg-T`, `joint-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport.CoefficientBounds ActualCarriers.ConstructedCarrierJets

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Loss-four estimates for the actual quadratic detector, using the primitive
low immersion budget to bound its input range. In contrast to a separate
small-neighborhood low estimate, this imposes no new stress threshold
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_geometricDetector_bounds {c C : ℝ} (hP : P.IsValid c C)
    (z : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall ((0 : Euclidean n), z) ρ ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLa : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) L (closedBall ((0 : Euclidean n), z) ρ))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (M : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K 4 F ≤ M →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ m, cNorm L m (fun p : Euclidean n × CarrierParameter ↦
        quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (CanonicalCarrier.parameter p.2))) ≤
        B m * (1 + cNorm K (m + 4) F) := by
  let a₀ := ((0 : Euclidean n), z)
  let J := closedBall a₀ ρ
  obtain ⟨A, hA, hb⟩ := exists_projected_actualInput_bound T (N := N) hP
    a₀ ρ hx hc hK hKU hball M hκmet hκ
  let R := A 0 * (1 + M)
  choose C hC hcomp using fun m : ℕ ↦
    exists_cNorm_comp_le_tame_closedBall_contDiffOn a₀ hρ
      (isCompact_closedBall (0 : Input n) R) (r := m) (k := m) le_rfl
      (g := fun p : Input n ↦ quadratic p.1 p.2)
      (fun _ _ ↦ contDiff_quadratic.contDiffAt.of_le (by simp))
  let ψ := fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_fst.prodMk (CanonicalCarrier.parameter.contDiff.comp contDiff_snd)
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean n)
    hL (isCompact_closedBall a₀ ρ) (fun _ _ ↦ hψ.contDiffAt) hLa
  let B := fun m ↦ D m * (C m * (1 + A m))
  have hB m : 0 < B m := mul_pos (hD m) (mul_pos (hC m) (by linarith [hA m]))
  refine ⟨B, hB, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    rw [← hQ]
    exact Q.2.2
  have hQeq : (⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
        {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}) = Q := Subtype.ext hQ.symm
  have hinput := hb F hF hi hrank hFM hmet hnormal hlow
  dsimp only at hinput
  rw [hQeq] at hinput
  have hdom : J ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hKU (hball (hx hw)), (hc hw).1⟩, (hc hw).2⟩
  have hs := smooth_actualInput T hP Q
  have hmap : MapsTo (actualInput T Q) J (closedBall (0 : Input n) R) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a₀ ρ)
      (fun y hy ↦ (hs.contDiffAt ((isOpen_inputDomain T).mem_nhds (hdom hy))).of_le
        (by simp : (0 : ℕ∞ω) ≤ ∞)) hw (le_refl 0)
    rw [norm_iteratedFDeriv_zero] at hh
    exact (hh.trans (hinput 0)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hFM) (hA 0).le)
  let q := fun w : Euclidean n × Euclidean 3 ↦
    quadratic (Q.1 w.1) (T.carrierGradient Q w.1 w.2)
  have hq : ContDiffOn ℝ ∞ q (inputDomain T) := by
    have hh := contDiff_quadratic.comp_contDiffOn hs
    simpa only [Function.comp_def, actualInput] using hh
  intro m
  have hlocal : cNorm J m q ≤ C m * (1 + A m) * (1 + cNorm K (m + 4) F) := by
    have hh := hcomp m (inputDomain T) (isOpen_inputDomain T) hdom (actualInput T Q) hs hmap
    apply hh.trans
    have hh' : 1 + cNorm J m (actualInput T Q) ≤ (1 + A m) * (1 + cNorm K (m + 4) F) := by
      have := hinput m
      nlinarith [cNorm_nonneg K (m + 4) F]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh' (hC m).le
  exact (hd q (fun w hw ↦ hq.contDiffAt ((isOpen_inputDomain T).mem_nhds (hdom hw))) m).trans
    ((mul_le_mul_of_nonneg_left hlocal (hD m).le).trans_eq (by dsimp [B]; ring))

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
