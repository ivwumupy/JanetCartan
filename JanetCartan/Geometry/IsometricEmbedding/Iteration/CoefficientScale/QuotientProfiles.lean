module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.PhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ExtendedReducedProfiles
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts

/-!
# Actual full and transverse quotient profiles along a common history

For `main:prop:current-scale` and `app:eq:uniform-high-coeff`, take a finite
collection of the already constructed Hamilton families and frozen incidences.
The actual quotient producer fixes all buffers before a single source dilation.
Every admissible history of that same reference then has the joint forward,
inverse and first-epsilon derivative profiles, with reserve six. The geometric,
Hamilton and global affine reduced-array profiles are retained for the same
maps and families, using one prescribed Seeley operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.NormalRankStability

namespace JanetCartan.CurrentCoefficientProfiles

open ActualCarriers CurrentFullPhase FrozenMenu ProjectedStressFrame HamiltonPhase
open FullPhaseCharts FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open FullPhaseCharts.ActualEstimates ProtectedFlow GeometricProfile

/-- The eight literal joint coefficient seminorms of
`app:ch_seed:prop:seed-phase-charts`: full and transverse forward/inverse maps,
each with its first epsilon derivative, on the producer's fixed domains. -/
def currentQuotientCoefficientNorm {n : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (ρF ρT r s e : ℝ) (VF : Set (ℝ × Euclidean (n - 1)))
    (VT : Set (Euclidean (n - 1))) (m : ℕ) : ℝ :=
  let fF := Function.uncurry (fullChartFamily (current T Q) (spatialCarrier T))
  let fT := fun q ↦ transverseChartFamily (current T Q) (spatialCarrier T)
          (transverseParameterReindex q.1) q.2
  let BF := closedBall (((0 : ℝ), spectatorCenter z₀,
          (0 : WithLp 2 (ℝ × Euclidean (n - 1))), (0 : WithLp 2 (ℝ × Euclidean (n - 1)))),
          (z₀ 0,ηb)) ρF
  let BT := closedBall (((0 : ℝ), (spectatorCenter z₀, (0 : ℝ), z₀ 0),
          (0 : Euclidean (n - 1)), (0 : Euclidean (n - 1))), ηb) ρT
  let gF := Function.uncurry (phaseChartInverse
          (fullChartFamily (current T Q) (spatialCarrier T)) (dataSet z₀ ηb (2 * r)))
  let gT := fun q ↦ phaseChartInverse
          (transverseChartFamily (current T Q) (spatialCarrier T)) (ball ηb (2 * r))
          (transverseParameterReindex q.1) q.2
  ((cNorm BF m fF + cNorm BF m
            (fun q ↦ deriv (fun ε ↦ fF ((ε,q.1.2),q.2)) q.1.1)) +
          (cNorm (fullParameterBox z₀ (s / 2) e ×ˢ closure VF) m gF +
          cNorm (fullParameterBox z₀ (s / 2) e ×ˢ closure VF) m
            (fun q ↦ deriv (fun ε ↦ gF ((ε,q.1.2),q.2)) q.1.1))) +
  ((cNorm BT m fT + cNorm BT m
            (fun q ↦ deriv (fun ε ↦ fT ((ε,q.1.2),q.2)) q.1.1)) +
          (cNorm (transversePrimitiveBox z₀ (s / 2) e ×ˢ closure VT) m gT +
          cNorm (transversePrimitiveBox z₀ (s / 2) e ×ˢ closure VT) m
            (fun q ↦ deriv (fun ε ↦ gT ((ε,q.1.2),q.2)) q.1.1)))

/-- The quotient part of `main:prop:current-scale`, simultaneously for a finite
collection of the actual Hamilton families. The frozen incidences are primitive
finite-menu data; no current-map, phase, inverse or coefficient bound is assumed.
One source dilation, one initial-scale threshold and all domains precede every
admissible history, high derivative and accuracy. The derivative reserves are
two for geometry, three for the Hamilton phase and six for all eight quotient
coefficients. The prescribed affine extension of the full reduced array has
the same profile and reference. Later transport and prepared-scalar constructions must retain this
same reference and these families. -/
theorem exists_scaled_history_quotient_profiles {n : ℕ} {I : Type*} [Fintype I]
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
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 6 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ ρF ρT qrad s e cF bF cT bT : I → ℝ,
    ∃ VF LF : I → Set (ℝ × Euclidean (n - 1)),
    ∃ VT LT : I → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρF i ∧ 0 < ρT i ∧ 0 < qrad i ∧ 0 < s i ∧ s i ≤ qrad i ∧
        3 * qrad i < (family i).family.radius / 8 ∧ 0 < e i ∧
        2 * qrad i ≤ ρF i ∧ 2 * qrad i ≤ ρT i ∧ e i ≤ ρF i ∧ e i ≤ ρT i ∧
        0 < cF i ∧ 0 < bF i ∧ 0 < cT i ∧ 0 < bT i ∧
        IsOpen (VF i) ∧ IsCompact (closure (VF i)) ∧ IsCompact (LF i) ∧ LF i ⊆ VF i ∧
        IsOpen (VT i) ∧ IsCompact (closure (VT i)) ∧ IsCompact (LT i) ∧ LT i ⊆ VT i) ∧
    ∃ (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1),
    let G := sourceDilationReference G₀ hσ hσ₁
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
  obtain ⟨σ, hσ, hσ₁, V, hV, hKV, _, _, _, _, hreference, _⟩ :=
    exists_source_scale_projectedStress_lt G₀ hK (half_pos heps)
  let G := sourceDilationReference G₀ hσ hσ₁
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
  refine ⟨ρF, ρT, qrad, s, e, cF, bF, cT, bT, VF, LF, VT, LT, ?_,
    σ, hσ, hσ₁, max (max S Sg) Se,
    (hS.trans (le_max_left _ _)).trans (le_max_left _ _), C₀, hC₀, κ, hκ,
    A, E, Bphase, Bquotient, Ee, hA, hE, hBp, hBq, hEe, ?_⟩
  · intro i
    exact ⟨hρF i, hρT i, hqrad i, hs i, hsq i, hphysical i, he i,
      hrF i, hrT i, heF i, heT i, hcF i, hbF i, hcT i, hbT i,
      hVF i, hVFc i, hLFc i, hLFV i, hVT i, hVTc i, hLTc i, hLTV i⟩
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

/-- Instantiate the finite quotient profile construction with the actual frozen
menu and Hamilton producer (`main:prop:current-scale`). A finite choice of
incidence directions fixes the charts before the common source scale. The
roots, incidence identity and transverse derivative are supplied by that SAME
menu. All current geometry and coefficient profiles are conclusions. -/
theorem exists_constructed_history_quotient_profiles {n : ℕ} (hn : 5 ≤ n)
    {I : Type*} [Fintype I] (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 6 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ (D : CoverData n) (c C : ℝ) (hD : D.IsValid c C),
    ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
      (∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
        closedBall 0 r) ∧
      ∀ (chart : I → Fin D.chartCount) (patch : (i : I) → Fin (D.patchCount (chart i)))
        (k : I → Euclidean n), (∀ i, k i ≠ 0) → (∀ i, k i ∈ D.domain (chart i)) →
      let family := fun i ↦ T ⟨chart i, patch i⟩
      let z := fun i ↦ D.roots (chart i) (patch i) (k i)
      ∃ (hz : ∀ i, z i ∈ parameterInterior (D.patches (chart i) (patch i)).radius)
        (hinc : ∀ i, incidence (k i) ((D.patches (chart i) (patch i)).toFun (z i)) = 0)
        (hd : ∀ i, fderiv ℝ (fun w ↦ incidence (k i)
          ((D.patches (chart i) (patch i)).toFun w)) (z i) (EuclideanSpace.single 0 1) ≠ 0),
    ∃ ρF ρT qrad s e cF bF cT bT : I → ℝ,
    ∃ VF LF : I → Set (ℝ × Euclidean (n - 1)),
    ∃ VT LT : I → Set (Euclidean (n - 1)),
      (∀ i, 0 < ρF i ∧ 0 < ρT i ∧ 0 < qrad i ∧ 0 < s i ∧ s i ≤ qrad i ∧
        3 * qrad i < (family i).family.radius / 8 ∧ 0 < e i ∧
        2 * qrad i ≤ ρF i ∧ 2 * qrad i ≤ ρT i ∧ e i ≤ ρF i ∧ e i ≤ ρT i ∧
        0 < cF i ∧ 0 < bF i ∧ 0 < cT i ∧ 0 < bT i ∧
        IsOpen (VF i) ∧ IsCompact (closure (VF i)) ∧ IsCompact (LF i) ∧ LF i ⊆ VF i ∧
        IsOpen (VT i) ∧ IsCompact (closure (VT i)) ∧ IsCompact (LT i) ∧ LT i ⊆ VT i) ∧
    ∃ (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1),
    let G := sourceDilationReference G₀ hσ hσ₁
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
            (FrozenIncidence.referenceEquiv T ((hD.2.2.2.2.1 (chart i) (patch i)).1) (hz i) (hinc i) (hd i)) ∧
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
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  obtain ⟨D, c, C, hD, T, hphysical, _⟩ :=
    exists_constructed_carrier_phases hn isOpen_ball hr hKU
  have hball (i) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall 0 r :=
    (frameBall_subset_of_stateDomain (T i).data.localReference (hphysical i)).trans
      ball_subset_closedBall
  refine ⟨D, c, C, hD, T, hball, ?_⟩
  intro chart patch k hk hkD
  dsimp only
  have hz (i) := ((hD.2.2.2.2.1 (chart i) (patch i)).2.2.1 (k i) (hkD i)).1
  have hinc (i) := ((hD.2.2.2.2.1 (chart i) (patch i)).2.2.1 (k i) (hkD i)).2.2.2
  have hd (i) : fderiv ℝ (fun w ↦ incidence (k i)
      ((D.patches (chart i) (patch i)).toFun w)) (D.roots (chart i) (patch i) (k i))
      (EuclideanSpace.single 0 1) ≠ 0 :=
    abs_pos.mp (hD.1.trans_le
      ((hD.2.2.2.2.1 (chart i) (patch i)).2.2.2 (k i) (hkD i) _ (fun j ↦ (hz i j).le)))
  refine ⟨hz, hinc, hd, ?_⟩
  exact exists_scaled_history_quotient_profiles G₀ hr hrR hR p hpcenter hpradius
    (fun i ↦ D.patches (chart i) (patch i))
    (fun i ↦ (hD.2.2.2.2.1 (chart i) (patch i)).1)
    (fun i ↦ T ⟨chart i, patch i⟩) (fun i ↦ hball ⟨chart i, patch i⟩)
    (fun i ↦ D.roots (chart i) (patch i) (k i)) k hz hk hinc hd hStar hreserve horder

end JanetCartan.CurrentCoefficientProfiles
