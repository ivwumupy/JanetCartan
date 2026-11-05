module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FixedReferenceProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ExtendedGeometricProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry.TransportBudget
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Hamilton

/-!
# Hamilton extensions at every sufficiently small source scale

For `main:prop:current-scale` and `app:eq:uniform-high-coeff`, the source cap
precedes the history orders and the initializer's choice of reference. The
geometric, reduced-array and Hamilton profiles below are the analytic inputs
of `exists_source_scale_cap_for_fixed_reference_joint_extensions`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.NormalRankStability
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers CurrentFullPhase FrozenMenu ProjectedStressFrame HamiltonPhase
open ProtectedFlow GeometricProfile JointExtensions

/-- The geometric and Hamilton part of `main:prop:current-scale` and
`app:eq:uniform-high-coeff` for every sufficiently small source dilation.
The consumer `exists_source_scale_cap_for_fixed_reference_joint_extensions`
supplies the extra frame margin needed by its fixed quotient and transport
extensions. All low budgets and gaps are proved for the literal history;
geometry and reduced-array extension use reserve two and Hamilton uses three.
Map equality retains the original outer analytic domain even when the
initialized reference has a smaller working chart. -/
theorem exists_source_scale_cap_for_fixed_reference_hamilton_profiles
    {n : ℕ} {I : Type*} [Fintype I]
    (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    (P : I → Patch n)
    (family : (i : I) → PatchQuantitativeFamily (P i) (ball 0 R) isOpen_ball)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius ⊆ closedBall 0 r)
    {εextra : ℝ} (hεextra : 0 < εextra) :
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ cap →
    ∀ G : FlatReference n, G.map = sourceDilation G₀.map σ →
    ∀ rStar r₀ kMin : ℕ, 12 ≤ rStar → 3 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
    ∃ A E Bphase Egeom Eext Bextended : ℕ → ℝ,
      (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ m, 0 ≤ Bphase m) ∧
      (∀ m, 0 ≤ Egeom m) ∧ (∀ m, 0 ≤ Eext m) ∧ (∀ m, 0 ≤ Bextended m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm (closedBall 0 r) 4 F ≤ C₀ ∧
        cNorm (closedBall 0 r) 12 F ≤ cNorm (closedBall 0 r) 12 G.map + 1 ∧
        cNorm (closedBall 0 r) 6 (projectedStress F - fun _ ↦ cubeStress n) < εextra ∧
        (∀ x ∈ ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) A ∧
        (∀ m, currentGeometricCoefficientNorm (closedBall 0 r) m F ≤
          E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
        (∀ m, extendedGeometricCoefficientNorm p m F ≤
          Egeom m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
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
          HasDerivativeProfile
            (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
              T.data.adapted.baseData.2) T.family.radius)
            (phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase ∧
          ContDiff ℝ ∞ (extendedHamiltonPhase T Q) ∧
          EqOn (extendedHamiltonPhase T Q) (phase (T.currentChart Q).coordinates)
            (closedBall (hamiltonExtensionCenter T) (hamiltonExtensionRadius T)) ∧
          tsupport (extendedHamiltonPhase T Q) ⊆ hamiltonExtensionSupport T ∧
          HasDerivativeProfile univ (extendedHamiltonPhase T Q) r₀
            (currentCoefficientScale R₀ j) Bextended := by
  classical
  have hK : IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  obtain ⟨_, d, _, _, _, hd, _, hcommon⟩ := exists_common_phase_buffers
    (fun _ : I ↦ (1 : ℝ)) (fun i ↦ (family i).family.threshold)
    (fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_lt_one) (fun i ↦ (family i).family.threshold_pos)
  let tol := min d εextra
  have htol : 0 < tol := lt_min hd hεextra
  have heps : 0 < tol / (2 * (6 + 1 : ℝ)) := by positivity
  obtain ⟨cap, hcap, hcap₁, hsmall⟩ :=
    FixedReferenceProfiles.exists_source_scale_interval_projectedStress_lt G₀ hK (half_pos heps)
  refine ⟨cap, hcap, hcap₁, ?_⟩
  intro σ hσ hσcap Gfixed hmap rStar r₀ kMin hStar hreserve horder
  -- The analytic source keeps its outer chart; only the literal map is transferred.
  rw [hmap]
  have hσ₁ : σ ≤ 1 := hσcap.trans hcap₁
  let G := sourceDilationReference G₀ hσ hσ₁
  have hreference := hsmall σ hσ hσcap
  have h12 : displacementLoss n + bandExponent * (12 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (12 : ℝ) ≤ rStar := by exact_mod_cast hStar
    have hb : 0 < bandExponent := by norm_num [bandExponent]
    nlinarith
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hb : 0 < bandExponent := by norm_num [bandExponent]
    linarith
  obtain ⟨S, hS, C₀, hC₀, κ, hκ, hgeom⟩ :=
    HistoryGeometry.exists_cube_frame_neighborhood G hr hrR hR h8 heps hreference
  obtain ⟨Sg, _, _, _, _, _, A, E, hA, hE, hgeometric⟩ :=
    exists_admissible_history_geometric_profiles G hr hrR hR
      (r₀ := r₀) (by omega) (by omega) horder
  obtain ⟨St, _, hbudget⟩ := HistoryGeometry.exists_initialScale_for_transport_low_bound
    G.map G.contDiff (closedBall 0 r) hK h12
  obtain ⟨Se, _, _, Ee, _, hEe, hextended⟩ :=
    exists_admissible_history_extended_reduced_profiles G hr hrR hR p hpcenter hpradius
      (by omega : 8 ≤ rStar) (by omega : 2 + r₀ ≤ rStar) horder
  obtain ⟨Seg, _, Eg, hEg, hextgeom⟩ :=
    exists_admissible_history_extended_geometric_profiles G hr hrR hR p hpcenter hpradius
      (by omega : 8 ≤ rStar) (by omega : 2 + r₀ ≤ rStar) horder
  choose Hp hHp hphase using fun i ↦ (family i).exists_projected_phase_sharp_bound
    (N := embeddingDimension n) hK hKU (hball i) C₀
      (by norm_num : (0 : ℝ) < 1 / 4) hκ
  choose Cext hCext hext using fun i ↦ exists_extendedHamiltonPhase_cNorm_bound (family i)
  let Bphase := fun m ↦ (1 + ∑ i, Hp i m) * (1 + A (m + 3))
  let Bextended := fun m ↦ (1 + ∑ i, Cext i m) * Bphase m
  have hBp (m) : 0 ≤ Bphase m := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ (hHp i m).le)
    exact mul_nonneg (by linarith) (by linarith [hA (m + 3)])
  have hBe (m) : 0 ≤ Bextended m := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ (hCext i m).le)
    exact mul_nonneg (by linarith) (hBp m)
  refine ⟨max (max (max S Sg) St) (max Se Seg),
    ((hS.trans (le_max_left _ _)).trans (le_max_left _ _)).trans (le_max_left _ _),
    C₀, hC₀, κ, hκ, A, E, Bphase, Eg, Ee, Bextended, hA, hE, hBp, hEg, hEe, hBe, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hRtriple := (le_max_left (max (max S Sg) St) (max Se Seg)).trans hR₀
  have hRpair := (le_max_left (max S Sg) St).trans hRtriple
  have hRS := (le_max_left S Sg).trans hRpair
  have hRSg := (le_max_right S Sg).trans hRpair
  have hRSt := (le_max_right (max S Sg) St).trans hRtriple
  have hRext := (le_max_right (max (max S Sg) St) (max Se Seg)).trans hR₀
  have hRSe := (le_max_left Se Seg).trans hRext
  have hRSeg := (le_max_right Se Seg).trans hRext
  have hscale := one_le_currentCoefficientScale (show 1 ≤ R₀ by linarith [hS.trans hRS]) j
  let F := finiteHistoryMap G.map u
  have hF : ContDiffOn ℝ ∞ F (ball 0 R) :=
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
  obtain ⟨hi, hrank, hlowF, hmet, hnormal, hQ, hclose⟩ := hgeom R₀ hRS j u ell hu
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) := contDiffOn_pi.mpr hQ
  have hframeK : cNorm (closedBall 0 r) 6
      (projectedStress F - fun _ ↦ cubeStress n) < tol :=
    frame_cNorm_lt_of_componentwise hK
      (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
        contDiffAt_const).of_le (by simp)) htol hclose
  have hlow (i) : cNorm (closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt (hball i) hK _).trans_lt
      (hframeK.trans_le ((min_le_left _ _).trans (hcommon i).2.1))
    intro x hx
    exact ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
      contDiffAt_const).of_le (by simp)
  obtain ⟨_, _, _, _, _, hp, hcoefficients⟩ := hgeometric R₀ hRSg j u ell hu
  obtain ⟨heSmooth, heEq, heSupport, _, heProfile⟩ := hextended R₀ hRSe j u ell hu
  refine ⟨hF, hi, hrank, hlowF, hbudget R₀ hRSt j u ell hu,
    hframeK.trans_le (min_le_right _ _), hmet, hnormal, hp, hcoefficients,
    hextgeom R₀ hRSeg j u ell hu, heSmooth, heEq, heSupport, heProfile, hlow, ?_⟩
  intro i
  dsimp only
  let T := family i
  let Q := (⟨projectedStress F, hframe, hlow i⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q (ball 0 R) ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hphaseProfile : HasDerivativeProfile
      (closedBall (hamiltonExtensionCenter T) T.family.radius)
      (phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) Bphase := by
    intro m
    have hb := hphase i F hF hi hrank hlowF
      (fun x hx ↦ hmet x (hKU hx)) (fun x hx ↦ hnormal x (hKU hx)) (hlow i) m
    have hh := JointBudget.fixed_profile_transfer_bound hscale (hA (m + 3)) (hHp i m).le
      hreserve (hp (m + 3)) hb
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hscale) _)
    apply mul_le_mul_of_nonneg_right _ (by linarith [hA (m + 3)])
    have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ Hp i m)
      (fun i _ ↦ (hHp i m).le) (Finset.mem_univ i)
    linarith
  obtain ⟨hs, heq, hsupport⟩ := extendedHamiltonPhase_properties T Q
  refine ⟨hphaseProfile, hs, heq, hsupport, ?_⟩
  intro m
  have hraw := (hext i m Q).trans
    (mul_le_mul_of_nonneg_left (hphaseProfile m) (hCext i m).le)
  apply hraw.trans
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hscale) _)
  apply mul_le_mul_of_nonneg_right _ (hBp m)
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun i ↦ Cext i m)
    (fun i _ ↦ (hCext i m).le) (Finset.mem_univ i)
  linarith

end JanetCartan.CurrentCoefficientProfiles
