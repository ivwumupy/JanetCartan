module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.ActualEstimates.PrimitiveJets

/-!
# Closed low and sharp high budgets for both actual chart primitives

These are the exact primitive norms in `InverseEstimates.PhaseBounds`.
The construction sets have geometric containment hypotheses only. The phase
budgets are deduced from the actual Hamilton producer, and the frozen carrier
norms are absorbed in constants fixed before the immersion. In particular,
putting `m = r+3` gives the immersion order `r+6` in
`app:ch_seed:prop:seed-phase-charts`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FullPhaseCharts.ActualEstimates
open ActualCarriers ActualCarriers.CurrentFullPhase FrozenMenu ActualPhase ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)
local notation "X" => WithLp 2 (ℝ × E)

/-- The full and transverse primitive `C³` budgets are fixed before the
current frame. The carrier/direction bounds require no current-frame input
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_primitive_low_bounds
    (KF : Set (((Euclidean 2 × (ℝ × E)) × X) × E))
    (KT : Set ((((Euclidean 2 × ℝ × ℝ) × E) × E) × E))
    (JF : Set (Euclidean 2 × (ℝ × E))) (JT : Set ((Euclidean 2 × ℝ × ℝ) × E))
    (hKF : MapsTo fullPhaseProjection KF (closedBall (0, covectorCenter T) T.family.radius))
    (hKT : MapsTo transversePhaseProjection KT (closedBall (0, covectorCenter T) T.family.radius)) :
    ∃ δ > (0 : ℝ), ∃ N > (0 : ℝ), ∃ M > (0 : ℝ),
      cNorm JF 3 (fun p ↦ spatialCarrier T (p.1, p.2.1)) ≤ M ∧
      cNorm JF 3 (fun p ↦ p.2.2) ≤ M ∧
      cNorm JT 3 (fun p ↦ spatialCarrier T (p.1.1, p.1.2.2)) ≤ M ∧
      cNorm JT 3 (fun p ↦ p.2) ≤ M ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        cNorm KF 3 (fun q ↦ current T Q (q.1.2, q.2)) ≤ N ∧
        cNorm KT 3 (fun q ↦ current T Q (WithLp.toLp 2 (q.1.1.1.2.1, q.1.2), q.2)) ≤ N := by
  obtain ⟨δ, hδ, N, hN, hb⟩ := exists_current_low_bound T
  let a := cNorm JF 3 (fun p ↦ spatialCarrier T (p.1, p.2.1))
  let b := cNorm JF 3 (fun p ↦ p.2.2)
  let c := cNorm JT 3 (fun p ↦ spatialCarrier T (p.1.1, p.1.2.2))
  let d := cNorm JT 3 (fun p ↦ p.2)
  have ha : 0 ≤ a := cNorm_nonneg _ _ _
  have hb' : 0 ≤ b := cNorm_nonneg _ _ _
  have hc : 0 ≤ c := cNorm_nonneg _ _ _
  have hd : 0 ≤ d := cNorm_nonneg _ _ _
  refine ⟨δ, hδ, 32 * N, by positivity, 1 + a + b + c + d, by positivity,
    by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro Q hQ
  have hf := cNorm_fullPhase_le T Q hKF 3
  have ht := cNorm_transversePhase_le T Q hKT 3
  have hn := hb Q hQ
  norm_num at hf ht
  constructor <;> nlinarith

/-- Primitive full and transverse phase/carrier bounds with sharp immersion
order `m+3`, hence `r+6` for the inverse/epsilon estimate. All high constants
precede the immersion. The only immersion hypotheses are the actual projected
stress construction's primitive smoothness, gaps, low norm and neighborhood
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_primitive_projected_budget {N : ℕ}
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ)
    (KF : Set (((Euclidean 2 × (ℝ × E)) × X) × E))
    (KT : Set ((((Euclidean 2 × ℝ × ℝ) × E) × E) × E))
    (JF : Set (Euclidean 2 × (ℝ × E))) (JT : Set ((Euclidean 2 × ℝ × ℝ) × E))
    (hKF : MapsTo fullPhaseProjection KF (closedBall (0, covectorCenter T) T.family.radius))
    (hKT : MapsTo transversePhaseProjection KT (closedBall (0, covectorCenter T) T.family.radius)) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
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
        ∀ m,
          cNorm KF m (fun q ↦ current T Q (q.1.2, q.2)) +
          cNorm JF m (fun p ↦ spatialCarrier T (p.1, p.2.1)) +
          cNorm JF m (fun p ↦ p.2.2) +
          cNorm KT m (fun q ↦ current T Q (WithLp.toLp 2 (q.1.1.1.2.1, q.1.2), q.2)) +
          cNorm JT m (fun p ↦ spatialCarrier T (p.1.1, p.1.2.2)) +
          cNorm JT m (fun p ↦ p.2) ≤ B m * (1 + cNorm K (m + 3) F) := by
  obtain ⟨A, hA, hphase⟩ := exists_current_projected_sharp_bound T hK hKU hball C₀ hκmet hκ
  let Z := fun m ↦ cNorm JF m (fun p ↦ spatialCarrier T (p.1, p.2.1)) +
    cNorm JF m (fun p ↦ p.2.2) +
    cNorm JT m (fun p ↦ spatialCarrier T (p.1.1, p.1.2.2)) + cNorm JT m (fun p ↦ p.2)
  have hZ (m) : 0 ≤ Z m := by
    dsimp only [Z]
    exact add_nonneg (add_nonneg (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _))
      (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  let B := fun m : ℕ ↦ 1 + ((m + 1 : ℝ) + (m + 1 : ℝ) * 2 ^ m) * A m + Z m
  refine ⟨B, fun m ↦ by dsimp [B]; have := hA m; have := hZ m; positivity, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow Q m
  have hp := hphase F hF hi hrank hlowF hmet hnormal hlow m
    (closedBall (0, covectorCenter T) T.family.radius) Subset.rfl
  have hf := (cNorm_fullPhase_le T Q hKF m).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))
  have ht := (cNorm_transversePhase_le T Q hKT m).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))
  have hF0 := cNorm_nonneg K (m + 3) F
  have hfixed := mul_nonneg (hZ m) hF0
  dsimp only [B, Z] at *
  nlinarith

end JanetCartan.FullPhaseCharts.ActualEstimates
