module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FixedReferenceProfiles.SourceInterval
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.QuotientProfiles

/-!
# History profiles at the initializer's single reference scale

For `main:prop:current-scale`, `main:prop:seed` and v2
`new:sec:order-of-choices`, the quotient boxes and an upper source-scale cap
are fixed before the derivative orders, baseline decay, target or history.
Every positive source scale below that cap works. Thus
`exists_fixed_reference_initialization_with_full_margins` can impose its
additional finite margins by taking this cap, and the resulting reference
has all the actual history profiles on the SAME Hamilton charts.

The initialized reference's working chart is separate from the analytic
source's outer carrier domain. Map equality transfers the construction;
no outer-radius condition is imposed on the initialized record.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.NormalRankStability

namespace JanetCartan.FixedReferenceProfiles

open ActualCarriers CurrentFullPhase FrozenMenu ProjectedStressFrame HamiltonPhase
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates ProtectedFlow GeometricProfile CurrentCoefficientProfiles

/-- `main:prop:current-scale` on the very reference selected by
`exists_fixed_reference_initialization_with_full_margins`. Supply the returned
positive cap to that initializer, retain its `G.map = sourceDilation G₀.map σ`,
and apply this conclusion using `σ < cap`. No new reference scale is selected.

The fixed finite Hamilton families and frozen incidences determine the quotient
boxes and cap before `rStar`, `r₀`, `kMin` and every accuracy. For EACH positive
scale below the cap, all metric/normal gaps, actual full Hamilton phases,
full/transverse forward and inverse charts (including their first epsilon
derivatives), and the prescribed extended reduced array are constructed along
EVERY admissible history. Reserves are two for geometry/extension, three for
phase, and six for quotient. The initial-frequency threshold and constants
precede the initial frequency, stage and history. The outer radius is compared
only to the original analytic source's chart, never to `G.domain.chartRadius`.
This is the same-reference input for the uniform-history step and final
iteration; it does not assert those later correction constructions. -/
theorem exists_source_scale_cap_for_fixed_reference_history_profiles {n : ℕ} {I : Type*} [Fintype I]
    (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    (P : I → Patch n) {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    (family : (i : I) → PatchQuantitativeFamily (P i) (ball 0 R) isOpen_ball)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius ⊆ closedBall 0 r)
    (z : I → Euclidean 3) (k : I → Euclidean n)
    (hz : ∀ i, z i ∈ parameterInterior (P i).radius) (hk : ∀ i, k i ≠ 0)
    (hinc : ∀ i, incidence (k i) ((P i).toFun (z i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun w ↦ incidence (k i) ((P i).toFun w)) (z i)
      (EuclideanSpace.single 0 1) ≠ 0)
    :
    ∃ ρF ρT qrad s e cF bF cT bT : I → ℝ,
    ∃ VF LF : I → Set (ℝ × Euclidean (n - 1)),
    ∃ VT LT : I → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρF i ∧ 0 < ρT i ∧ 0 < qrad i ∧ 0 < s i ∧ s i ≤ qrad i ∧
        3 * qrad i < (family i).family.radius / 8 ∧ 0 < e i ∧
        2 * qrad i ≤ ρF i ∧ 2 * qrad i ≤ ρT i ∧ e i ≤ ρF i ∧ e i ≤ ρT i ∧
        0 < cF i ∧ 0 < bF i ∧ 0 < cT i ∧ 0 < bT i ∧
        IsOpen (VF i) ∧ IsCompact (closure (VF i)) ∧ IsCompact (LF i) ∧ LF i ⊆ VF i ∧
        IsOpen (VT i) ∧ IsCompact (closure (VT i)) ∧ IsCompact (LT i) ∧ LT i ⊆ VT i) ∧
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ cap →
    ∀ G : FlatReference n, G.map = sourceDilation G₀.map σ →
    ∀ rStar r₀ kMin : ℕ, 8 ≤ rStar → 6 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
    ∃ A E Bphase Bquotient Eext : ℕ → ℝ,
      (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ m, 0 ≤ Bphase m) ∧ (∀ m, 0 ≤ Bquotient m) ∧ (∀ m, 0 ≤ Eext m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm (closedBall 0 r) 4 F ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) A ∧
        (∀ m, currentGeometricCoefficientNorm (closedBall 0 r) m F ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) ∧
        EqOn (extendedReducedCoefficients p (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
          (closedBall 0 r) ∧
        tsupport (extendedReducedCoefficients p (fun _ _ ↦ 0) F -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (r + p.width / 2) ∧
        HasDerivativeProfile univ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) r₀
          (currentCoefficientScale R₀ j) Eext ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (family i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold,
        ∀ i,
          let T := family i
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
          let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
          BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (fullParameterSet (z i) (s i) (2 * e i))
            (dataBox (z i) ηb (qrad i)) (dataSet (z i) ηb (2 * qrad i))
            (dataBox (z i) ηb (2 * qrad i)) (VF i) (LF i) (bF i) (cF i)
            (FrozenIncidence.referenceEquiv T (hP i) (hz i) (hinc i) (hd i)) ∧
          BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (transverseParameterSet (z i) (s i) (2 * e i))
            (closedBall ηb (qrad i)) (ball ηb (2 * qrad i)) (closedBall ηb (2 * qrad i))
            (VT i) (LT i) (bT i) (cT i) (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
          HasDerivativeProfile
            (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
              T.data.adapted.baseData.2) T.family.radius)
            (phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase ∧
          ∀ m, currentQuotientCoefficientNorm T Q (z i) ηb
              (ρF i) (ρT i) (qrad i) (s i) (e i) (VF i) (VT i) m ≤
            Bquotient m * currentCoefficientScale R₀ j ^ (m - r₀) := by
  classical
  have hK : IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  choose ρF hρF ρT hρT qrad hqrad s hs hsq hphysical hcarrier e he hrF hrT heF heT
    δ hδ cF hcF bF hbF VF LF cT hcT bT hbT VT LT annLow hannLow annHigh hannHigh
    H hH hVF hVFc hLFc hLFV hVT hVTc hLTc hLTV hcharts using
    fun i ↦ exists_actual_buffered_inverse_phase_bounds (family i) (hP i) (hz i)
      (hk i) (hinc i) (hd i)
  obtain ⟨_, ε, _, _, _, hε, _, hcommon⟩ := exists_common_phase_buffers
    (fun _ : I ↦ (1 : ℝ)) (fun i ↦ min (δ i) (family i).family.threshold)
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_lt_one)
    (fun i ↦ lt_min (hδ i) (family i).family.threshold_pos)
  have heps : 0 < ε / (2 * (6 + 1 : ℝ)) := by positivity
  obtain ⟨cap, hcap, hcap₁, hsmall⟩ :=
    exists_source_scale_interval_projectedStress_lt G₀ hK (half_pos heps)
  refine ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, ?_,
    cap, hcap, hcap₁, ?_⟩
  · intro i
    exact ⟨hρF i, hρT i, hqrad i, hs i, hsq i, hphysical i, he i,
      hrF i, hrT i, heF i, heT i, hcF i, hbF i, hcT i, hbT i,
      hVF i, hVFc i, hLFc i, hLFV i, hVT i, hVTc i, hLTc i, hLTV i⟩
  intro σ hσ hσcap Gfixed hmap rStar r₀ kMin hStar hreserve horder
  -- Transfer every literal map, coefficient and chart by equality. The analytic
  -- source retains the outer domain; Gfixed's working chart is not enlarged.
  rw [hmap]
  have hσ₁ : σ ≤ 1 := hσcap.trans hcap₁
  let G := sourceDilationReference G₀ hσ hσ₁
  have hreference := hsmall σ hσ hσcap
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (8 : ℝ) ≤ rStar := by exact_mod_cast hStar
    exact lt_of_le_of_lt (by
      have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
      nlinarith) horder
  obtain ⟨S, hS, C₀, hC₀, κ, hκ, hgeom⟩ :=
    HistoryGeometry.exists_cube_frame_neighborhood G hr hrR hR h8 heps hreference
  obtain ⟨Sg, hSg, _, _, _, _, A, E, hA, hE, hgeometric⟩ :=
    exists_admissible_history_geometric_profiles G hr hrR hR
      (r₀ := r₀) hStar (by omega) horder
  obtain ⟨Se, hSe, _, Ee, _, hEe, hextended⟩ :=
    exists_admissible_history_extended_reduced_profiles G hr hrR hR p hpcenter hpradius
      hStar (by omega : 2 + r₀ ≤ rStar) horder
  choose L hL hphase using fun i ↦ (family i).exists_projected_phase_sharp_bound
    (N := embeddingDimension n) hK hKU (hball i) C₀
      (by norm_num : (0 : ℝ) < 1 / 4) hκ
  let Bphase : ℕ → ℝ := fun m ↦ (1 + ∑ i, L i m) * (1 + A (m + 3))
  let D : I → ℕ → ℝ := fun i m ↦ H i m * (1 + (m + 4 : ℝ) * L i (m + 3))
  let Bquotient : ℕ → ℝ := fun m ↦ (1 + ∑ i, D i m) * (1 + A (m + 6))
  have hD (i) (m) : 0 ≤ D i m := by
    have := hH i m
    have := hL i (m + 3)
    dsimp [D]
    positivity
  have hBp (m) : 0 ≤ Bphase m :=
    mul_nonneg (by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ (hL i m).le); linarith)
      (by linarith [hA (m + 3)])
  have hBq (m) : 0 ≤ Bquotient m :=
    mul_nonneg (by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hD i m); linarith)
      (by linarith [hA (m + 6)])
  refine ⟨max (max S Sg) Se,
    (hS.trans (le_max_left _ _)).trans (le_max_left _ _), C₀, hC₀, κ, hκ,
    A, E, Bphase, Bquotient, Ee, hA, hE, hBp, hBq, hEe, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hRpair := (le_max_left (max S Sg) Se).trans hR₀
  have hRS := (le_max_left S Sg).trans hRpair
  have hRSg := (le_max_right S Sg).trans hRpair
  have hRSe := (le_max_right (max S Sg) Se).trans hR₀
  have hscale := one_le_currentCoefficientScale (show 1 ≤ R₀ by linarith [hS.trans hRS]) j
  let F := finiteHistoryMap G.map u
  have hF : ContDiffOn ℝ ∞ F (ball 0 R) :=
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
  obtain ⟨hi, hrank, hlowF, hmet, hnormal, hQ, hclose⟩ := hgeom R₀ hRS j u ell hu
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) :=
    contDiffOn_pi.mpr hQ
  have hframeK : cNorm (closedBall 0 r) 6
      (projectedStress F - fun _ ↦ cubeStress n) < ε :=
    frame_cNorm_lt_of_componentwise hK
      (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
        contDiffAt_const).of_le (by simp)) hε hclose
  have hlocal (i) : cNorm (closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < ε :=
    (cNorm_mono_set_of_contDiffAt (hball i) hK
      (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
        contDiffAt_const).of_le (by simp))).trans_lt hframeK
  have hlow (i) : cNorm (closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold :=
    (hlocal i).trans_le ((hcommon i).2.1.trans (min_le_right _ _))
  obtain ⟨_, _, _, _, _, hp, hcoefficients⟩ := hgeometric R₀ hRSg j u ell hu
  obtain ⟨heSmooth, heEq, heSupport, _, heProfile⟩ := hextended R₀ hRSe j u ell hu
  refine ⟨hF, hi, hrank, hlowF, hmet, hnormal, hp, hcoefficients,
    heSmooth, heEq, heSupport, heProfile, hlow, ?_⟩
  intro i
  dsimp only
  let T := family i
  let Q := (⟨projectedStress F, hframe, hlow i⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball 0 R) ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  obtain ⟨_, _, _, _, hfInv, htInv, _, _, _, _, _, hbound⟩ :=
    hcharts i Q ((hlocal i).trans_le ((hcommon i).2.1.trans (min_le_left _ _)))
  have hb (m) := hphase i F hF hi hrank hlowF
    (fun x hx ↦ hmet x (hKU hx)) (fun x hx ↦ hnormal x (hKU hx)) (hlow i) m
  refine ⟨hfInv, htInv, ?_, ?_⟩
  · intro m
    have hh := JointBudget.fixed_profile_transfer_bound hscale (hA (m + 3))
      (hL i m).le (show 3 + r₀ ≤ rStar by omega) (hp (m + 3)) (hb m)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hscale) _)
    apply mul_le_mul_of_nonneg_right _ (by linarith [hA (m + 3)])
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ L i m)
      (fun i _ ↦ (hL i m).le) (Finset.mem_univ i)
    linarith
  · intro m
    have hpcurrent := (cNorm_current_le T Q (m + 3) Subset.rfl).trans
      (mul_le_mul_of_nonneg_left (hb (m + 3)) (by positivity))
    have hraw : currentQuotientCoefficientNorm T Q (z i)
        (T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i))
        (ρF i) (ρT i) (qrad i) (s i) (e i) (VF i) (VT i) m ≤
        D i m * (1 + cNorm (closedBall 0 r) (m + 6) F) := by
      apply (hbound m).trans
      dsimp only [D]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hH i m).le
      simp only [show m + 3 + 3 = m + 6 by omega,
        Nat.cast_add, Nat.cast_ofNat] at hpcurrent
      nlinarith [cNorm_nonneg (closedBall 0 r) (m + 6) F]
    have hh := JointBudget.fixed_profile_transfer_bound hscale (hA (m + 6))
      (hD i m) hreserve (hp (m + 6)) hraw
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hscale) _)
    apply mul_le_mul_of_nonneg_right _ (by linarith [hA (m + 6)])
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ D i m)
      (fun i _ ↦ hD i m) (Finset.mem_univ i)
    linarith

/-- The literal source-map form of `main:prop:current-scale`, with quotient
boxes and a positive source cap chosen before all history orders. Every positive
source scale below the cap satisfies the profiles, so a subsequent intersection
with the initializer's finite full-array margins preserves these very maps and
charts (`main:prop:seed`, v2 `new:sec:order-of-choices`). -/
theorem exists_source_scale_cap_for_history_quotient_profiles {n : ℕ} {I : Type*} [Fintype I]
    (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    (P : I → Patch n) {c C : ℝ} (hP : ∀ i, (P i).IsValid c C)
    (family : (i : I) → PatchQuantitativeFamily (P i) (ball 0 R) isOpen_ball)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius ⊆ closedBall 0 r)
    (z : I → Euclidean 3) (k : I → Euclidean n)
    (hz : ∀ i, z i ∈ parameterInterior (P i).radius) (hk : ∀ i, k i ≠ 0)
    (hinc : ∀ i, incidence (k i) ((P i).toFun (z i)) = 0)
    (hd : ∀ i, fderiv ℝ (fun w ↦ incidence (k i) ((P i).toFun w)) (z i)
      (EuclideanSpace.single 0 1) ≠ 0)
    :
    ∃ ρF ρT qrad s e cF bF cT bT : I → ℝ,
    ∃ VF LF : I → Set (ℝ × Euclidean (n - 1)),
    ∃ VT LT : I → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρF i ∧ 0 < ρT i ∧ 0 < qrad i ∧ 0 < s i ∧ s i ≤ qrad i ∧
        3 * qrad i < (family i).family.radius / 8 ∧ 0 < e i ∧
        2 * qrad i ≤ ρF i ∧ 2 * qrad i ≤ ρT i ∧ e i ≤ ρF i ∧ e i ≤ ρT i ∧
        0 < cF i ∧ 0 < bF i ∧ 0 < cT i ∧ 0 < bT i ∧
        IsOpen (VF i) ∧ IsCompact (closure (VF i)) ∧ IsCompact (LF i) ∧ LF i ⊆ VF i ∧
        IsOpen (VT i) ∧ IsCompact (closure (VT i)) ∧ IsCompact (LT i) ∧ LT i ⊆ VT i) ∧
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ cap →
    ∀ rStar r₀ kMin : ℕ, 8 ≤ rStar → 6 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
    ∃ A E Bphase Bquotient Eext : ℕ → ℝ,
      (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ m, 0 ≤ Bphase m) ∧ (∀ m, 0 ≤ Bquotient m) ∧ (∀ m, 0 ≤ Eext m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap (sourceDilation G₀.map σ) u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm (closedBall 0 r) 4 F ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) A ∧
        (∀ m, currentGeometricCoefficientNorm (closedBall 0 r) m F ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) ∧
        EqOn (extendedReducedCoefficients p (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
          (closedBall 0 r) ∧
        tsupport (extendedReducedCoefficients p (fun _ _ ↦ 0) F -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (r + p.width / 2) ∧
        HasDerivativeProfile univ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) r₀
          (currentCoefficientScale R₀ j) Eext ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (family i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold,
        ∀ i,
          let T := family i
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
          let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (k i)
          BufferedPhaseInverse (fullChartFamily (current T Q) (spatialCarrier T))
            (fullParameterSet (z i) (s i) (2 * e i))
            (dataBox (z i) ηb (qrad i)) (dataSet (z i) ηb (2 * qrad i))
            (dataBox (z i) ηb (2 * qrad i)) (VF i) (LF i) (bF i) (cF i)
            (FrozenIncidence.referenceEquiv T (hP i) (hz i) (hinc i) (hd i)) ∧
          BufferedPhaseInverse (transverseChartFamily (current T Q) (spatialCarrier T))
            (transverseParameterSet (z i) (s i) (2 * e i))
            (closedBall ηb (qrad i)) (ball ηb (2 * qrad i)) (closedBall ηb (2 * qrad i))
            (VT i) (LT i) (bT i) (cT i) (ContinuousLinearEquiv.refl ℝ (Euclidean (n - 1))) ∧
          HasDerivativeProfile
            (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
              T.data.adapted.baseData.2) T.family.radius)
            (phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase ∧
          ∀ m, currentQuotientCoefficientNorm T Q (z i) ηb
              (ρF i) (ρT i) (qrad i) (s i) (e i) (VF i) (VT i) m ≤
            Bquotient m * currentCoefficientScale R₀ j ^ (m - r₀) := by
  obtain ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, hboxes,
    cap, hcap, hcap₁, hprofiles⟩ :=
    exists_source_scale_cap_for_fixed_reference_history_profiles G₀ hr hrR hR
      p hpcenter hpradius P hP family hball z k hz hk hinc hd
  refine ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, hboxes,
    cap, hcap, hcap₁, ?_⟩
  intro σ hσ hσcap
  exact hprofiles σ hσ hσcap (sourceDilationReference G₀ hσ (hσcap.trans hcap₁)) rfl

end JanetCartan.FixedReferenceProfiles
