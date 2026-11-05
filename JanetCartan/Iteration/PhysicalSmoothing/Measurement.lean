module

public import JanetCartan.Iteration.PhysicalSmoothing.Periodization
public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.CanonicalMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Representatives

/-!
# The original measurement on the actual physical history source

For `new:eq:mean-source`, retain the literal corrected canonical carrier and
its fixed measurement cutoff.  Its measurement profiles are produced from
physical history admissibility and the prescribed reference's compact jet
neighborhood.  No coefficient profile, periodized history, or successful
source iteration is a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.NormalRankStability

namespace JanetCartan.PhysicalSmoothing

open CurrentMean ContinuumRow CanonicalCarrier CorrectedPositiveInverse
  ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame GeometricProfile
  AmplitudeBound DefectSmoothing

/-- The measured normalized source of `new:eq:mean-source`, with the SAME
carrier measurement and only the compact physical tensor realized on the torus. -/
def measuredNormalizedSource {n N j : ℕ} (d : CarrierData n N)
    (D : LocalDomain) (R : ℝ) (m : ℕ) (δ : ℝ) (g : MetricField n)
    (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) : Torus n → Euclidean n :=
  fun x ↦ preparationMeasurement d x (tensorPeriodization (normalizedSource D R m δ g G u) x)

/-- Literal physical reconstruction of the source, with its original fixed
cutoff, tensor contraction and corrected carrier (`new:eq:mean-source`).
There is no assertion that a physical history increment is periodic. -/
theorem measuredNormalizedSource_canonical_eq {n N j : ℕ}
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (w : CarrierVariable n → ℝ)
    (D : LocalDomain) (R : ℝ) (m : ℕ) (δ : ℝ) (g : MetricField n)
    (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) :
    measuredNormalizedSource
      (correctedCarrierData (data T Q F row col Φ Y initial hr hcell angular high) w)
      D R m δ g G u =
    UniformStep.Periodization.vectorPeriodization (fun x ↦ FixedCutoffs.physical hr 1 x •
      WithLp.toLp 2 (fun i ↦ tensorPairing (Q.1 x i) (normalizedSource D R m δ g G u x))) := by
  ext x i
  change preparationMeasurement (correctedCarrierData
    (data T Q F row col Φ Y initial hr hcell angular high) w) x
      (tensorPeriodization (normalizedSource D R m δ g G u) x) i = _
  rw [preparationMeasurement_correctedCarrierData, preparationMeasurement_canonical_apply]
  rfl

private theorem exists_stress_sum_bound {n N : ℕ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {L : Set (StressJet n N)} (hL : IsCompact L)
    (hunit : ∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) (m : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      IsImmersionOn F (ball 0 R) → MapsTo (stressJet F) (closedBall 0 r) L →
      (∑ i, cNorm (closedBall 0 r) m (fun x ↦ projectedStress F x i)) ≤
        C * (1 + cNorm (closedBall 0 r) (m + 2) F) := by
  classical
  choose S hS hstress using fun i : Fin n ↦
    exists_cNorm_jetStress_le_tame_contDiffOn_of_compact_range (0 : Euclidean n) hr hL
      (fun J hJ ↦ (hunit J hJ).1) (fun J hJ ↦ (hunit J hJ).2) (cubeStress n i) m
  have hsum : 0 ≤ ∑ i, S i := Finset.sum_nonneg (fun i _ ↦ (hS i).le)
  refine ⟨1 + ∑ i, S i, by linarith, ?_⟩
  intro F hF hi hFL
  have hb (i : Fin n) : cNorm (closedBall 0 r) m (fun x ↦ projectedStress F x i) ≤
      S i * (1 + cNorm (closedBall 0 r) (m + 2) F) := by
    rw [cNorm_projectedStress_eq_jetStress isOpen_ball (closedBall_subset_ball hrR) hF.contDiffOn hi]
    exact hstress i (ball 0 R) isOpen_ball (closedBall_subset_ball hrR) F hF.contDiffOn hFL
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hb i)
  rw [← Finset.sum_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith)
    (by linarith [cNorm_nonneg (closedBall (0 : Euclidean n) r) (m + 2) F]))

/-- Actual all-order measurement profiles for `new:eq:mean-source` and the
same-source canonical recurrence.  The SAME corrected carrier, projected
stress and reference map are retained.  All flow and density parameters are
arbitrary: the proved measurement formula eliminates their influence.

The original common initializer supplies `4*r<R<G.domain.chartRadius` (using
its prescribed dilated reference when needed); no measurement is reselected. -/
theorem exists_history_preparation_measurement_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (h4rR : 4 * r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 R) isOpen_ball)
        (Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q (ball 0 R) ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      Q.1 = projectedStress F → ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
        (w : CarrierVariable n → ℝ),
      let d := correctedCarrierData (data T Q F row col Φ Y initial hr hcell angular high) w
      IsSmoothPeriodic (preparationMeasurement d) ∧
      ∀ s, cNorm (fundamentalCell n) s (periodicLift (preparationMeasurement d)) ≤
        C s * currentCoefficientScale R₀ j ^ (s - reserve) := by
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ := PhysicalGeometry.exists_geometric_neighborhood
    G (by positivity : 0 < 4 * r) h4rR hR hB hStar horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L, hL, hunit, Sj, hSj, hjet⟩ :=
    PhysicalGeometry.exists_history_jet_range G hR hB hStar horder
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) (4 * r)) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  choose D hD hbound using exists_stress_sum_bound (by positivity : 0 < 4 * r) h4rR hL hunit
  choose Cmeas hCmeas hmeasurement using fun s ↦
    PreparedHistory.exists_canonical_preparation_measurement_cNorm_bound (n := n) hr hcell s
  refine ⟨max Sg Sj, hSg.trans (le_max_left _ _),
    (fun s ↦ Cmeas s * (D s * (1 + A (s + 2)))),
    (fun s ↦ mul_pos (hCmeas s) (mul_pos (hD s) (by linarith [hA (s + 2)]))), ?_⟩
  intro R₀ hR₀ j u ell hu F P T Q hQ row col Φ Y initial angular high w d
  have hRg := (le_max_left Sg Sj).trans hR₀
  have hRj := (le_max_right Sg Sj).trans hR₀
  have htwo := hSg.trans hRg
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, _, _⟩ := hgeom R₀ hRg j u ell hu
  have hLmap : MapsTo (stressJet F) (closedBall 0 (4 * r)) L :=
    (hjet R₀ hRj j u ell hu).mono_left (closedBall_subset_closedBall h4rR.le)
  have hp := hprofile R₀ htwo j u ell hu _ Subset.rfl
  refine ⟨(hmeasurement 0 T Q (closedBall_subset_ball h4rR)
    F row col Φ Y initial angular high w).1, ?_⟩
  intro s
  have hcoeff : (∑ i, cNorm (closedBall 0 (4 * r)) s (fun x ↦ Q.1 x i)) ≤
      (D s * (1 + A (s + 2))) * currentCoefficientScale R₀ j ^ (s - reserve) := by
    rw [hQ]
    exact JointBudget.fixed_profile_transfer_bound
      (one_le_currentCoefficientScale (by linarith) j) (hA (s + 2)) (hD s).le
      hreserve (hp (s + 2)) (hbound s F hF hi hLmap)
  exact ((hmeasurement s T Q (closedBall_subset_ball h4rR)
    F row col Φ Y initial angular high w).2).trans
      ((mul_le_mul_of_nonneg_left hcoeff (hCmeas s).le).trans_eq (by ring))

end JanetCartan.PhysicalSmoothing
