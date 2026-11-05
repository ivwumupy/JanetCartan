module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.JetBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.JetGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.JetCompact
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# Uniform tame bounds for the actual projected stresses

The estimate `app:ch_seed:eq:seed-frame-tame` follows from the stipulated low
bound and the separate metric and normal gaps. The compact admissible jet
range is derived from these hypotheses. All constants are chosen before the
immersion and its high norms; smoothness is needed only on the open chart.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ProjectedStressFrame

/-- The local version of the compact-range second-jet estimate used in
`app:ch_seed:eq:seed-frame-tame`. The immersion is smooth on an open
neighborhood of the working ball, with no global extension hypothesis. -/
theorem exists_cNorm_jetStress_le_tame_contDiffOn_of_compact_range {n N : ℕ}
    (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (StressJet n N)} (ht : IsCompact t)
    (hg : ∀ J ∈ t, IsUnit (jetMetric J))
    (hA : ∀ J ∈ t, IsUnit (jetAmbient J))
    (Q : MetricTensor n) (r : ℕ) :
    ∃ C > 0, ∀ (s : Set (Euclidean n)), IsOpen s → Metric.closedBall a ρ ⊆ s →
      ∀ F : Euclidean n → Euclidean N, ContDiffOn ℝ ∞ F s →
      Set.MapsTo (stressJet F) (Metric.closedBall a ρ) t →
      cNorm (Metric.closedBall a ρ) r (fun x ↦ jetStress Q (stressJet F x)) ≤
        C * (1 + cNorm (Metric.closedBall a ρ) (r + 2) F) := by
  obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_contDiffOn
    a hρ ht (le_refl r)
    (fun J hJ ↦ (contDiffAt_jetStress (hg J hJ) (hA J hJ) Q).of_le (by simp))
  refine ⟨2 * C, by positivity, ?_⟩
  intro s hs hKs F hF hFt
  have h := hbound s hs hKs (stressJet F) (contDiffOn_stressJet hs hF) hFt
  have hjet := cNorm_stressJet_le (isCompact_closedBall a ρ)
    (fun x hx ↦ (hF x (hKs hx)).contDiffAt (hs.mem_nhds (hKs hx))) r
  exact h.trans (by nlinarith)

/-- The low `C⁴` bound and the normal singular-value gap put the actual
second jet in the fixed admissible range of
`app:ch_seed:setup:seed-current`. The metric gap remains a separate input. -/
theorem stressJet_mem_admissibleStressJets {n N : ℕ}
    {F : Euclidean n → Euclidean N} {K : Set (Euclidean n)}
    (hK : IsCompact K) (hF : ∀ x ∈ K, ContDiffAt ℝ ∞ F x)
    {C₀ κmet κ : ℝ} (hκ : 0 < κ) (hlow : cNorm K 4 F ≤ C₀)
    {x : Euclidean n} (hx : x ∈ K) (hi : Function.Injective (fderiv ℝ F x))
    (hmet : ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2)
    (hnormal : ∀ w ∈ normalSpace F x,
      κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) :
    stressJet F x ∈ admissibleStressJets n N (2 * C₀) κmet (max 1 (κ ^ 2)⁻¹) := by
  refine ⟨(norm_stressJet_le_cNorm_four hK hF hx).trans ?_, hmet, ?_⟩
  · linarith
  · exact jetAmbient_lower_bound_of_normal_gap ((hF x hx).of_le (by simp)) hi hκ hnormal

/-- The actual geometric stress and its rational second-jet formula have the
same seminorm on a compact working set, including its boundary
(`app:ch_seed:eq:seed-frame-tame`). -/
theorem cNorm_projectedStress_eq_jetStress {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s K : Set (Euclidean n)}
    (hs : IsOpen s) (hKs : K ⊆ s) (hF : ContDiffOn ℝ ∞ F s)
    (hi : IsImmersionOn F s) (i : Fin n) (r : ℕ) :
    cNorm K r (fun x ↦ projectedStress F x i) =
      cNorm K r (fun x ↦ jetStress (cubeStress n i) (stressJet F x)) := by
  apply GeometricProfile.cNorm_eq_of_eventuallyEq _ r
  intro x hx
  filter_upwards [hs.mem_nhds (hKs hx)] with y hy
  exact (jetStress_stressJet
    (((hF y hy).contDiffAt (hs.mem_nhds hy)).of_le (by simp)) (hi y hy) i).symm

/-- `app:ch_seed:eq:seed-frame-tame`: a single constant bounds every actual
projected cube stress, with exactly two derivatives of loss. The constant
depends only on the fixed ball, dimensions, order, low `C⁴` bound and the two
separate gaps. The construction compact set can be any larger set inside the
open smooth domain; no compact-range, inverse, or tame conclusion is assumed.
Full normal rank and low frame closeness are not needed for this estimate. -/
theorem exists_cNorm_projectedStress_le_tame {n N : ℕ}
    (a : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (r : ℕ) :
    ∃ C > 0, ∀ (F : Euclidean n → Euclidean N) (s Kconstruction : Set (Euclidean n)),
      IsOpen s → IsCompact Kconstruction → Metric.closedBall a ρ ⊆ Kconstruction →
      Kconstruction ⊆ s → ContDiffOn ℝ ∞ F s → IsImmersionOn F s →
      cNorm Kconstruction 4 F ≤ C₀ →
      (∀ x ∈ Kconstruction, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kconstruction, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ i : Fin n, cNorm (Metric.closedBall a ρ) r (fun x ↦ projectedStress F x i) ≤
        C * (1 + cNorm Kconstruction (r + 2) F) := by
  let t := admissibleStressJets n N (2 * C₀) κmet (max 1 (κ ^ 2)⁻¹)
  have ht : IsCompact t := isCompact_admissibleStressJets _ hκmet _
  have hg : ∀ J ∈ t, IsUnit (jetMetric J) := fun _ hJ ↦
    isUnit_jetMetric_of_lower_bound hκmet hJ.2.1
  have hA : ∀ J ∈ t, IsUnit (jetAmbient J) := fun _ hJ ↦
    isUnit_jetAmbient_of_lower_bound hJ.2.2
  have hb := fun i : Fin n ↦ exists_cNorm_jetStress_le_tame_contDiffOn_of_compact_range
    a hρ ht hg hA (cubeStress n i) r
  choose D hD hbound using hb
  have hsum : 0 ≤ ∑ i, D i := Finset.sum_nonneg (fun i _ ↦ (hD i).le)
  refine ⟨1 + ∑ i, D i, by linarith, ?_⟩
  intro F s K hs hK hball hKs hF hi hlow hmet hnormal i
  have hFat : ∀ x ∈ K, ContDiffAt ℝ ∞ F x := fun x hx ↦
    (hF x (hKs hx)).contDiffAt (hs.mem_nhds (hKs hx))
  have hFt : Set.MapsTo (stressJet F) (Metric.closedBall a ρ) t := by
    intro x hx
    exact stressJet_mem_admissibleStressJets hK hFat hκ hlow (hball hx)
      (hi x (hKs (hball hx))) (hmet x (hball hx)) (hnormal x (hball hx))
  rw [cNorm_projectedStress_eq_jetStress hs (hball.trans hKs) hF hi]
  have h := hbound i s hs (hball.trans hKs) F hF hFt
  have hmono : cNorm (Metric.closedBall a ρ) (r + 2) F ≤ cNorm K (r + 2) F :=
    cNorm_mono_set_of_contDiffAt hball hK
      (fun x hx ↦ (hFat x hx).of_le (by simp))
  have hDi : D i ≤ 1 + ∑ j, D j := by
    have := Finset.single_le_sum (s := Finset.univ) (f := D)
      (fun j _ ↦ (hD j).le) (Finset.mem_univ i)
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_left
    (show 1 + cNorm (Metric.closedBall a ρ) (r + 2) F ≤
      1 + cNorm K (r + 2) F by linarith) (hD i).le).trans
    (mul_le_mul_of_nonneg_right hDi (add_nonneg zero_le_one (cNorm_nonneg ..))))

end JanetCartan.ProjectedStressFrame
