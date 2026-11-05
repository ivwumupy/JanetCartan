module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Transport.LowBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.JetBounds

/-!
# One-high transfer from the named physical null direction

The high field norm in `app:ch_waves:eq:joint-tame` is transferred through the
fixed adapted coordinates. Constants are chosen before the projected stress
and the nullvector indices. The consumer is `ActualFlow`'s joint flow bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts.InverseEstimates

private theorem cNorm_compLinear_le_on
    {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : A →L[ℝ] B) {S : Set A} {K Ω : Set B}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : B → F} (hf : ContDiffOn ℝ ∞ f Ω) (hm : MapsTo L S K) (k : ℕ) :
    cNorm S k (f ∘ L) ≤ ((k + 1 : ℝ) * (max 1 ‖L‖) ^ k) * cNorm K k f := by
  have hb : ∀ j ≤ k, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ (max 1 ‖L‖) ^ k * cNorm K k f := by
    intro j hj x hx
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L hΩ hf
      (hKΩ (hm hx)) j).trans
    have hpow : ‖L‖ ^ j ≤ (max 1 ‖L‖) ^ k :=
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hj)
    exact (mul_le_mul (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hKΩ hy))).of_le (by simp))
      (hm hx) hj) hpow (by positivity) (cNorm_nonneg _ _ _)).trans_eq (mul_comm _ _)
  have h := cNorm_le_sum_of_bounds (fun _ _ ↦ mul_nonneg (by positivity) (cNorm_nonneg K k f)) hb
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, ← mul_assoc] using h

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)

/-- The literal lifted field has an additive one-high bound in the literal
physical direction on the coefficient compact set (`app:ch_waves:eq:joint-tame`).
Only fixed coordinate maps and the order enter the constant. -/
theorem exists_liftedDirection_cNorm_bound
    (p₀ : Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) (R : ℝ) (k : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (row col : Fin n) (Ω K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → ContDiffOn ℝ ∞ (transportDirection T Q row col) Ω →
      IsCompact K → K ⊆ Ω →
      MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall (0, p₀) R) K →
      cNorm (closedBall (0, p₀) R) k (liftedDirection T Q row col) ≤
        C * (1 + cNorm K k (transportDirection T Q row col)) := by
  let A : Euclidean n →L[ℝ] ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) :=
    (0 : Euclidean n →L[ℝ] ℝ).prod ((directionProjection T).prod 0)
  let L := (FlowAmplitude.coordinates (Z := (Euclidean 3 × Euclidean (n - 1)))
    (adaptedCoordinates T.data.adapted)).symm.toContinuousLinearMap
  let S := closedBall ((0 : ℝ), p₀) R
  let b : (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))) →
      ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) := fun _ ↦ (1, 0, 0)
  let B := cNorm S k b
  let H := (k + 1 : ℝ) * (max 1 ‖L‖) ^ k
  have hB : 0 ≤ B := cNorm_nonneg _ _ _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨1 + B + ‖A‖ * H, by positivity, ?_⟩
  intro Q row col Ω K hΩ hd hK hKΩ hm
  let d := transportDirection T Q row col
  have hreg : ∀ q ∈ S, ContDiffAt ℝ k (d ∘ L) q := fun q hq ↦
    (hd.contDiffAt (hΩ.mem_nhds (hKΩ (hm hq)))).of_le (by simp) |>.comp q L.contDiff.contDiffAt
  have heq : liftedDirection T Q row col = b + A ∘ (d ∘ L) := by
    funext q
    simp [liftedDirection, b, A, d, L, directionProjection]
  rw [heq]
  have hadd := cNorm_add_le_of_contDiffAt (isCompact_closedBall _ _)
    (fun _ _ ↦ (contDiff_const : ContDiff ℝ k b).contDiffAt)
    (fun q hq ↦ A.contDiff.contDiffAt.comp q (hreg q hq))
  have hpost := cNorm_postLinear_le_on (isCompact_closedBall _ _) k A hreg
  have hpre := cNorm_compLinear_le_on L hK hΩ hKΩ hd hm k
  have hv := cNorm_nonneg K k d
  calc
    _ ≤ B + ‖A‖ * cNorm S k (d ∘ L) := hadd.trans (add_le_add le_rfl hpost)
    _ ≤ B + ‖A‖ * (H * cNorm K k d) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hpre (norm_nonneg _)) _
    _ ≤ (1 + B + ‖A‖ * H) * (1 + cNorm K k d) := by
      nlinarith [mul_nonneg (norm_nonneg A) hH]
end JanetCartan.LeadingWave.FullModulation
