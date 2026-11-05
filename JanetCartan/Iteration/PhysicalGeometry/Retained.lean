module

public import JanetCartan.Iteration.PhysicalGeometry.Profiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles

/-!
# The actual retained Q and full B profiles on physical histories

The same-consumer handoff for `main:prop:current-scale` and
`app:ch_response:eq:direct-envelope-profile` in `paper-v2.tex`.  The principal
field is literally `extendedProjectedStress p F`, and the lower-order field
is the full zeroth projection of the same prescribed extended reduced array.
No Christoffel/connection entry is canceled or discarded.

All constants precede the physical prefix and every compact measurement set.
The reference, source scale and affine Seeley operator are preserved.  These
actual geometric/coefficient producers are inputs to the regular-sector and
retained-response estimates, not producers of the correction or inverse.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalGeometry

open GeometricProfile ProtectedFlow ProjectedStressFrame
open ResponseTransfer.RetainedFactors FullPhaseCharts.InverseEstimates

private theorem bddAbove_extended_jets {n : ℕ}
    {a : Euclidean n → ReducedCoefficientIndex n → ℝ}
    (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport (a - reducedCoefficientBackground (fun _ _ ↦ 0)))
    (m : ℕ) : BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ m a x‖) '' univ) := by
  let a₀ : Euclidean n → ReducedCoefficientIndex n → ℝ :=
    reducedCoefficientBackground (fun _ _ ↦ 0)
  have ha₀ : a₀ = fun _ ↦ a₀ 0 := rfl
  have hs₀ : ContDiff ℝ ∞ a₀ := contDiff_reducedCoefficientBackground contDiff_const
  obtain ⟨M, _, hM⟩ := hc.exists_bound_iteratedFDeriv (ha.sub hs₀) m
  refine ⟨M + ‖a₀ 0‖, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  have he : a = (a - a₀) + a₀ := by abel
  conv_lhs => rw [he]
  dsimp only
  rw [iteratedFDeriv_add_apply (f := a - a₀) (g := a₀) ((ha.sub hs₀).contDiffAt.of_le (by simp))
    (hs₀.contDiffAt.of_le (by simp))]
  apply (norm_add_le _ _).trans (add_le_add (hM m le_rfl x) ?_)
  rw [ha₀]
  cases m with
  | zero => simp
  | succ m => simp [iteratedFDeriv_succ_const]

/-- `app:ch_response:eq:direct-envelope-profile`: produce the original Q and
FULL B profiles for every actual physical prefix, using the same reference and
prescribed affine extension.  Frobenius coefficient norms are obtained by the
existing continuous projections, not identified with the array sup norm.  The
constants are uniform in all compact measurement sets and all histories. -/
theorem exists_retained_coefficient_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0)
    (hpradius : p.radius = r) {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ AQ AB : ℕ → ℝ,
      (∀ m, 0 ≤ AQ m) ∧ (∀ m, 0 ≤ AB m) ∧
      ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap G.map u
        let Q := extendedProjectedStress p F
        let Bfull := reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F
        ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ Bfull ∧
        ∀ K : Set (Euclidean n), IsCompact K →
          HasDerivativeProfile K Q reserve (currentCoefficientScale R₀ j) AQ ∧
          HasDerivativeProfile K Bfull reserve (currentCoefficientScale R₀ j) AB := by
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ :=
    exists_geometric_neighborhood G hr hrR hR hB hStar horder (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Se, hSe, _, E, _, hE, hext⟩ :=
    exists_extended_reduced_profiles G hr hrR hR p hpcenter hpradius hB hStar hreserve horder
  refine ⟨max Sg Se, hSg.trans (le_max_left _ _),
    (fun m ↦ ‖reducedFrameProjection n‖ * E m),
    (fun m ↦ ‖reducedZerothProjection n‖ * E m),
    (fun m ↦ mul_nonneg (norm_nonneg _) (hE m)),
    (fun m ↦ mul_nonneg (norm_nonneg _) (hE m)), ?_⟩
  intro R₀ hR₀ j u ell hu F Q Bfull
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨_, hrank, _⟩ := hgeom R₀ ((le_max_left _ _).trans hR₀) j u ell hu
  obtain ⟨ha, _, hsupp, _, hprofile⟩ :=
    hext R₀ ((le_max_right _ _).trans hR₀) j u ell hu
  let a := extendedReducedCoefficients p (fun _ _ ↦ 0) F
  have hcompact : HasCompactSupport (a - reducedCoefficientBackground (fun _ _ ↦ 0)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (r + p.width / 2))
      ((subset_tsupport _).trans hsupp)
  have hQ : reducedFrameProjection n ∘ a = Q :=
    reducedFrameProjection_extended_eq p F (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
      (fun x hx ↦ hrank x (closedBall_subset_ball hrR (by simpa [hpcenter, hpradius] using hx)))
  refine ⟨hQ ▸ (reducedFrameProjection n).contDiff.comp ha,
    (reducedZerothProjection n).contDiff.comp ha, ?_⟩
  intro K hK
  have hlocal (m : ℕ) : cNorm K m a ≤ E m * currentCoefficientScale R₀ j ^ (m - reserve) :=
    (cNorm_mono_set_of_bddAbove (subset_univ K)
      (fun k _ ↦ bddAbove_extended_jets ha hcompact k)).trans (hprofile m)
  constructor <;> intro m
  · rw [← hQ]
    exact (cNorm_postLinear_le_on hK m (reducedFrameProjection n)
      (fun _ _ ↦ ha.contDiffAt.of_le (by simp))).trans
        ((mul_le_mul_of_nonneg_left (hlocal m) (norm_nonneg _)).trans_eq (by ring))
  · exact (cNorm_postLinear_le_on hK m (reducedZerothProjection n)
      (fun _ _ ↦ ha.contDiffAt.of_le (by simp))).trans
        ((mul_le_mul_of_nonneg_left (hlocal m) (norm_nonneg _)).trans_eq (by ring))

/-- `main:prop:current-scale`: one same-reference handoff contains actual
geometric gaps and frame closeness together with the ORIGINAL extended Q and
FULL zeroth B profiles.  The minimum order and source dilation are supplied
unchanged; neither is reselected to fit a later history or derivative order. -/
theorem exists_retained_geometric_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0)
    (hpradius : p.radius = r) {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > (0 : ℝ), ∃ κ > (0 : ℝ), ∃ AQ AB : ℕ → ℝ,
      (∀ m, 0 ≤ AQ m) ∧ (∀ m, 0 ≤ AB m) ∧
      ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap G.map u
        let Q := extendedProjectedStress p F
        let Bfull := reducedZerothProjection n ∘ extendedReducedCoefficients p (fun _ _ ↦ 0) F
        IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
        cNorm (closedBall 0 r) 4 F ≤ C₀ ∧
        (∀ x ∈ ball 0 R, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (ball 0 R)) ∧
        (∀ i, cNorm (closedBall 0 r) 6
          (fun x ↦ projectedStress F x i - projectedStress G.map x i) < η) ∧
        ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ Bfull ∧
        ∀ K : Set (Euclidean n), IsCompact K →
          HasDerivativeProfile K Q reserve (currentCoefficientScale R₀ j) AQ ∧
          HasDerivativeProfile K Bfull reserve (currentCoefficientScale R₀ j) AB := by
  obtain ⟨Sg, hSg, C₀, hC₀, κ, hκ, hgeom⟩ :=
    exists_geometric_neighborhood G hr hrR hR hB hStar horder hη
  obtain ⟨Sp, hSp, AQ, AB, hAQ, hAB, hprofiles⟩ :=
    exists_retained_coefficient_profiles G hr hrR hR p hpcenter hpradius hB hStar hreserve horder
  refine ⟨max Sg Sp, hSg.trans (le_max_left _ _), C₀, hC₀, κ, hκ, AQ, AB, hAQ, hAB, ?_⟩
  intro R₀ hR₀ j u ell hu F Q Bfull
  obtain ⟨hi, hrank, hlow, hmetric, hnormal, hframe, hnear⟩ :=
    hgeom R₀ ((le_max_left _ _).trans hR₀) j u ell hu
  exact ⟨hi, hrank, hlow, hmetric, hnormal, hframe, hnear,
    hprofiles R₀ ((le_max_right _ _).trans hR₀) j u ell hu⟩

end JanetCartan.PhysicalGeometry
