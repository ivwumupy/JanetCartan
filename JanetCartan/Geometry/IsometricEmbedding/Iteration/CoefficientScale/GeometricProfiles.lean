module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ActualHistory
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile

/-!
# Actual geometric coefficient profiles along finite histories

The geometric part of `main:prop:current-scale` and
`app:eq:uniform-high-coeff`: the metric, inverse metric, second form, literal
projected stresses and canonical normal inverse share the paper scale and a
fixed reserve of two. Compact jet containment and all geometric hypotheses are
derived for the actual prefix. Phase, transport, extension and prepared positive
scalar profiles remain separate parts of the source proposition.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.NormalRankStability

namespace JanetCartan.CurrentCoefficientProfiles

open ProjectedStressFrame GeometricProfile AmbientResponse

/-- The actual geometric coefficient norms consumed by
`app:eq:uniform-high-coeff`. This sum includes the canonical ambient normal
completion and the literal projected stresses of the current immersion. -/
def currentGeometricCoefficientNorm {n N : ℕ} (K : Set (Euclidean n)) (m : ℕ)
    (F : Euclidean n → Euclidean N) : ℝ :=
  (cNorm K m (inducedMetric F) + cNorm K m (fun x ↦ (inducedMetric F x)⁻¹)) +
    (∑ i, ∑ j, cNorm K m (fun x ↦ secondFundamentalForm F x i j)) +
    (∑ i, cNorm K m (fun x ↦ projectedStress F x i)) +
    cNorm K m (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap)

private theorem exists_geometric_coefficient_bound {n N : ℕ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {L : Set (StressJet n N)} (hL : IsCompact L)
    (hunit : ∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) (m : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      IsImmersionOn F (Metric.ball 0 R) → HasFullNormalRankOn F (Metric.ball 0 R) →
      Set.MapsTo (stressJet F) (Metric.closedBall 0 r) L →
      currentGeometricCoefficientNorm (Metric.closedBall 0 r) m F ≤
        C * (1 + cNorm (Metric.closedBall 0 r) (m + 2) F) := by
  have hinj (J) (hJ : J ∈ L) : Function.Injective J.1 :=
    J.1.adjoint_comp_self_injective_iff.mp
      (ContinuousLinearMap.isUnit_iff_bijective.mp (hunit J hJ).1).1
  obtain ⟨M, hM, hmetric⟩ := exists_cNorm_metric_and_inverse_le_closedBall
    (0 : Euclidean n) hr (hL.image continuous_fst) (by
      rintro _ ⟨J, hJ, rfl⟩
      exact firstJetMetric_isUnit_of_injective (hinj J hJ)) m
  choose B hB hform using fun i j : Fin n ↦
    exists_cNorm_secondFundamentalForm_le_closedBall (0 : Euclidean n) hr hL hinj m i j
  choose S hS hstress using fun i : Fin n ↦
    exists_cNorm_jetStress_le_tame_contDiffOn_of_compact_range (0 : Euclidean n) hr hL
      (fun J hJ ↦ (hunit J hJ).1) (fun J hJ ↦ (hunit J hJ).2) (cubeStress n i) m
  let I : StressJet n N → MetricTensor n →L[ℝ] Euclidean N :=
    fun J ↦ (Ring.inverse (jetAmbient J)).comp (jetNormalMap J)
  have hI (J) (hJ : J ∈ L) : ContDiffAt ℝ ∞ I J := by
    have hi : ContDiffAt ℝ ∞ Ring.inverse (jetAmbient J) := by
      simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ (hunit J hJ).2.unit
    exact (hi.comp J (contDiffAt_jetAmbient (hunit J hJ).1)).clm_comp
      (contDiffAt_jetNormalMap (hunit J hJ).1)
  obtain ⟨D, hD, hnormal⟩ := exists_cNorm_secondJet_comp_le_closedBall
    (0 : Euclidean n) hr hL (fun J hJ ↦ (hI J hJ).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  refine ⟨M + (∑ i, ∑ j, B i j) + (∑ i, S i) + D, ?_, ?_⟩
  · exact add_pos (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hM
        (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (hB i j).le))
      (Finset.sum_nonneg fun i _ ↦ (hS i).le)) hD
  · intro F hF hi hrank hFL
    have hK : Metric.closedBall (0 : Euclidean n) r ⊆ Metric.ball 0 R :=
      Metric.closedBall_subset_ball hrR
    have hm := (hmetric F hF (fun x hx ↦ ⟨stressJet F x, hFL hx, rfl⟩)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add_right (cNorm_mono_order (show m + 1 ≤ m + 2 by omega)) 1) hM.le)
    have hb := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hform i j F hF hFL
    have hs : ∀ i, cNorm (Metric.closedBall 0 r) m (fun x ↦ projectedStress F x i) ≤
        S i * (1 + cNorm (Metric.closedBall 0 r) (m + 2) F) := by
      intro i
      rw [cNorm_projectedStress_eq_jetStress Metric.isOpen_ball hK hF.contDiffOn hi]
      exact hstress i (Metric.ball 0 R) Metric.isOpen_ball hK F hF.contDiffOn hFL
    have he : cNorm (Metric.closedBall 0 r) m
        (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap) =
        cNorm (Metric.closedBall 0 r) m (I ∘ secondJet F) := by
      apply cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [Metric.isOpen_ball.mem_nhds (hK hx)] with y hy
      change (canonicalNormalCompletion F y).toContinuousLinearMap = I (stressJet F y)
      dsimp only [I]
      rw [jetAmbient_stressJet (hF.contDiffAt.of_le (by simp)) (hi y hy),
        jetNormalMap_stressJet (hF.contDiffAt.of_le (by simp)) (hi y hy)]
      ext H : 1
      exact canonicalNormalCompletion_eq_ambient_inverse (hrank y hy) H
    have hd := hnormal F hF hFL
    rw [← he] at hd
    have hh := add_le_add (add_le_add (add_le_add hm hb)
      (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hs i)) hd
    simpa only [currentGeometricCoefficientNorm, ← Finset.sum_mul, ← add_mul] using hh

/-- The geometric part of `main:prop:current-scale` and
`app:eq:uniform-high-coeff`, for every actual admissible prefix of the SAME
flat reference. One threshold supplies the geometric neighborhood and all
orders of the metric, inverse metric, second form, projected stress and normal
inverse profile. The reserve is two, independent of high order or accuracy.
There is no assumed Bernstein, compact-range or analytic coefficient bound. -/
theorem exists_admissible_history_geometric_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
      ∃ A C : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ C m) ∧
      ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
          (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
        let F := finiteHistoryMap G.map u
        IsImmersionOn F (Metric.ball 0 R) ∧ HasFullNormalRankOn F (Metric.ball 0 R) ∧
        cNorm (Metric.closedBall 0 r) 4 F ≤ C₀ ∧
        (∀ x ∈ Metric.ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ Metric.ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (Metric.closedBall 0 r) F rStar
          (currentCoefficientScale R₀ j) A ∧
        ∀ m, currentGeometricCoefficientNorm (Metric.closedBall 0 r) m F ≤
          C m * currentCoefficientScale R₀ j ^ (m - r₀) := by
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (8 : ℝ) ≤ rStar := by exact_mod_cast hStar
    exact lt_of_le_of_lt (by
      have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
      nlinarith) horder
  obtain ⟨T, hT, C₀, hC₀, κ, hκ, hgeom⟩ :=
    HistoryGeometry.exists_geometric_neighborhood G hr hrR hR h8 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L, hL, hunit, S, hS, hjet⟩ := exists_admissible_history_jet_range G hR h8
  obtain ⟨A, hA, hprofile⟩ := exists_admissible_history_profile G.map G.contDiff
    (isCompact_closedBall (0 : Euclidean n) r) rStar kMin horder
  choose D hD hbound using exists_geometric_coefficient_bound hr hrR hL hunit
  refine ⟨max T S, hT.trans (le_max_left _ _), C₀, hC₀, κ, hκ,
    A, (fun m ↦ D m * (1 + A (m + 2))), hA,
    (fun m ↦ mul_nonneg (hD m).le (by linarith [hA (m + 2)])), ?_⟩
  intro R₀ hR₀ j u ell hu
  have hRT := (le_max_left T S).trans hR₀
  have hRS := (le_max_right T S).trans hR₀
  obtain ⟨hi, hrank, hlow, hmet, hnormal, _, _⟩ := hgeom R₀ hRT j u ell hu
  have hp := hprofile R₀ (hT.trans hRT) j u ell hu _ (Set.Subset.refl _)
  refine ⟨hi, hrank, hlow, hmet, hnormal, hp, ?_⟩
  intro m
  apply JointBudget.fixed_profile_transfer_bound
    (one_le_currentCoefficientScale (by linarith [hT.trans hRT]) j)
    (hA (m + 2)) (hD m).le hreserve (hp (m + 2))
  exact hbound m _ (hu.contDiff_finiteHistoryMap G.contDiff) hi hrank
    (fun _ hx ↦ hjet R₀ hRS j u ell hu (Metric.closedBall_subset_closedBall hrR.le hx))

end JanetCartan.CurrentCoefficientProfiles
