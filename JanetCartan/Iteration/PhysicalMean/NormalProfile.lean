module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PhysicalCompletion

/-!
# Actual normal multiplier profiles on the physical current map

The canonical normal completion in `main:eq:mean-normal-field` is evaluated on
the literal revised Schwartz prefix.  Its compact jet range and derivative
profile are produced from physical admissibility.  No bound for a normal
inverse or for a successfully completed field is assumed.

The consumer is the physical `H^r` mean profile in `main:prop:mean`, after the
fixed-source canonical field and complete Hermitian tensor have been estimated.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open scoped JanetCartan.NormalRankStability

namespace JanetCartan.PhysicalMean

open GeometricProfile AmbientResponse ProjectedStressFrame

private theorem exists_normal_multiplier_bound {n N : ℕ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {L : Set (StressJet n N)} (hL : IsCompact L)
    (hunit : ∀ J ∈ L, IsUnit (jetMetric J) ∧ IsUnit (jetAmbient J)) (m : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      IsImmersionOn F (ball 0 R) → HasFullNormalRankOn F (ball 0 R) →
      MapsTo (stressJet F) (closedBall 0 r) L →
      cNorm (closedBall 0 r) m
        (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap) ≤
          C * (1 + cNorm (closedBall 0 r) (m + 2) F) := by
  let I : StressJet n N → MetricTensor n →L[ℝ] Euclidean N :=
    fun J ↦ (Ring.inverse (jetAmbient J)).comp (jetNormalMap J)
  have hI (J) (hJ : J ∈ L) : ContDiffAt ℝ ∞ I J := by
    have hi : ContDiffAt ℝ ∞ Ring.inverse (jetAmbient J) := by
      simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ (hunit J hJ).2.unit
    exact (hi.comp J (contDiffAt_jetAmbient (hunit J hJ).1)).clm_comp
      (contDiffAt_jetNormalMap (hunit J hJ).1)
  obtain ⟨C, hC, hnormal⟩ := exists_cNorm_secondJet_comp_le_closedBall
    (0 : Euclidean n) hr hL (fun J hJ ↦ (hI J hJ).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  refine ⟨C, hC, ?_⟩
  intro F hF hi hrank hFL
  have he : cNorm (closedBall 0 r) m
      (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap) =
      cNorm (closedBall 0 r) m (I ∘ secondJet F) := by
    apply cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds (closedBall_subset_ball hrR hx)] with y hy
    change (canonicalNormalCompletion F y).toContinuousLinearMap = I (stressJet F y)
    dsimp only [I]
    rw [jetAmbient_stressJet (hF.contDiffAt.of_le (by simp)) (hi y hy),
      jetNormalMap_stressJet (hF.contDiffAt.of_le (by simp)) (hi y hy)]
    ext H : 1
    exact canonicalNormalCompletion_eq_ambient_inverse (hrank y hy) H
  rw [he]
  exact hnormal F hF hFL

/-- `main:prop:current-scale` applied to the canonical NORMAL multiplier:
all-order constants and a single threshold precede every physical history and
measurement tensor.  The reserve-two loss is transferred from the actual map
profile; no periodic-history or assumed inverse-profile producer is used. -/
theorem exists_history_normal_multiplier_profile {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      ContDiffOn ℝ ∞ (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap)
        (ball 0 R) ∧
      HasDerivativeProfile (closedBall 0 r)
        (fun x ↦ (canonicalNormalCompletion F x).toContinuousLinearMap)
        reserve (currentCoefficientScale R₀ j) C := by
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ := PhysicalGeometry.exists_geometric_neighborhood
    G hr hrR hR hB hStar horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L, hL, hunit, Sj, hSj, hjet⟩ :=
    PhysicalGeometry.exists_history_jet_range G hR hB hStar horder
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) r) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  choose D hD hbound using exists_normal_multiplier_bound hr hrR hL hunit
  refine ⟨max Sg Sj, hSg.trans (le_max_left _ _), (fun m ↦ D m * (1 + A (m + 2))),
    (fun m ↦ mul_nonneg (hD m).le (by linarith [hA (m + 2)])), ?_⟩
  intro R₀ hR₀ j u ell hu F
  have hRg := (le_max_left Sg Sj).trans hR₀
  have hRj := (le_max_right Sg Sj).trans hR₀
  have htwo := hSg.trans hRg
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, hrank, _⟩ := hgeom R₀ hRg j u ell hu
  have hLmap : MapsTo (stressJet F) (closedBall 0 r) L :=
    (hjet R₀ hRj j u ell hu).mono_left (closedBall_subset_closedBall hrR.le)
  have hp := hprofile R₀ htwo j u ell hu _ Subset.rfl
  refine ⟨hi, hrank, ?_, ?_⟩
  · apply contDiffOn_clm_apply.mpr
    intro H
    exact contDiffOn_canonicalNormalCompletion isOpen_ball hF.contDiffOn
      contDiffOn_const hi hrank
  · intro m
    exact JointBudget.fixed_profile_transfer_bound
      (one_le_currentCoefficientScale (by linarith) j) (hA (m + 2)) (hD m).le
      hreserve (hp (m + 2)) (hbound m F hF hi hrank hLmap)

end JanetCartan.PhysicalMean
