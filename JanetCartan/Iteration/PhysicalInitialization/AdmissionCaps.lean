module

public import JanetCartan.Iteration.PhysicalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.SectorHistoryAdmission.CoefficientCap

/-!
# The physical-history coefficient cap before the reference and mask family

This is the original-data admission needed by the same retained regular inverse
in `app:ch_regular:thm:exact-correction`. A cap chosen after the reference or
larger than the already chosen mask family's cap would not suffice. The full
reduced-array reference margin is supplied by the original initializer's
arbitrary finite-margin continuation; actual physical displacement proves the
current-map neighborhood. Both Q and the FULL B retain their literal fields.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization
open GeometricProfile ProtectedFlow ResponseTransfer.RetainedFactors
open FullPhaseCharts.InverseEstimates

private theorem cNorm_zero_background_le {n : ℕ} (K : Set (Euclidean n)) (m : ℕ) :
    cNorm K m (reducedCoefficientBackground (fun _ _ ↦ 0)) ≤
      (m + 1 : ℝ) * ‖reducedCoefficientBackground (fun _ _ ↦ 0) (0 : Euclidean n)‖ := by
  let a₀ := reducedCoefficientBackground (n := n) (fun _ _ ↦ 0)
  have heq : a₀ = fun _ ↦ a₀ 0 := rfl
  have hb := cNorm_le_sum_of_bounds (s := K) (r := m) (f := a₀)
    (C := fun _ ↦ ‖a₀ 0‖) (fun _ _ ↦ norm_nonneg _) (by
      intro j _ x _
      rw [heq]
      cases j with
      | zero => simp
      | succ j => simp [iteratedFDeriv_succ_const])
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] using hb

/-- `main:prop:current-scale` and `app:ch_regular:eq:coefficient-extension`:
one actual full coefficient cap BEFORE the reference, masks and physical
histories. The reference margin, unlike a current coefficient bound, is an
original output of the prescribed initialization callback. No periodic history
is introduced, and the reserve is exactly `max 8 (m + 2)`. -/
theorem exists_reference_tolerance_for_physical_coefficient_cap {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n)) (hextcenter : ext.center = 0)
    {R : ℝ} (hextR : ext.radius < R) (m : ℕ) :
    ∃ M > (0 : ℝ), ∃ η > (0 : ℝ),
      ∀ G : FlatReference n, R < G.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean n) ext.radius) m
        (geometricReducedCoefficients G.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      ∀ {Cband : ℝ}, 1 ≤ Cband →
      ∀ rStar kMin : ℕ, 8 ≤ rStar → m + 2 ≤ rStar →
      RevisedScales.displacementLoss n +
        bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection n ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      ∀ K : Set (Euclidean n), IsCompact K →
        cNorm K m Q ≤ M ∧ cNorm K m B ≤ M := by
  let a₀ := reducedCoefficientBackground (n := n) (fun _ _ ↦ 0)
  let C : ℝ := 1 + (m + 1 : ℝ) * ‖a₀ 0‖
  have hC : 0 < C := by dsimp [C]; positivity
  let M : ℝ := 1 + (‖reducedFrameProjection n‖ + ‖reducedZerothProjection n‖) * C
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨η, hη, hreference⟩ := exists_extendedReducedCoefficients_low_neighborhood
    ext hextcenter hextR m (by norm_num : (0 : ℝ) < 1)
  refine ⟨M, hM, η, hη, ?_⟩
  intro G hR href Cband hband rStar kMin hStar hreserve horder
  obtain ⟨δ, hδ, hnear⟩ := hreference G hR
  obtain ⟨S, hS, hhistory⟩ :=
    PhysicalHistory.exists_initialScale_for_prefix_neighborhood
      (N := embeddingDimension n) hband horder hδ
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu F Q B
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  have hdisplacement := hhistory R₀ hR₀ (closedBall 0 R) G.map
    (isCompact_closedBall _ _) s u ell hu
  have hclose : cNorm (closedBall (0 : Euclidean n) R) (max 8 (m + 2))
      (F - G.map) < δ :=
    (cNorm_mono_order (max_le hStar hreserve)).trans_lt
      (hdisplacement.trans (half_lt_self hδ))
  obtain ⟨_, hrank, ha, hsmall⟩ :=
    hnear (fun _ _ ↦ 0) contDiff_const href F hF hclose
  let a := extendedReducedCoefficients ext (fun _ _ ↦ 0) F
  have h₀ : ContDiff ℝ ∞ a₀ := contDiff_reducedCoefficientBackground contDiff_const
  have hcompact : HasCompactSupport (a - a₀) :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall ext.center (ext.radius + ext.width / 2))
      ((subset_tsupport _).trans (tsupport_extendedReducedCoefficients_sub ext (fun _ _ ↦ 0) F))
  obtain ⟨Cjet, _, hjet⟩ := hcompact.exists_bound_iteratedFDeriv (ha.sub h₀) m
  have hQ : reducedFrameProjection n ∘ a = Q :=
    reducedFrameProjection_extended_eq ext F
      (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
      (fun x hx ↦ hrank x (closedBall_subset_ball hextR (hextcenter ▸ hx)))
  refine ⟨hQ ▸ (reducedFrameProjection n).contDiff.comp ha,
    (reducedZerothProjection n).contDiff.comp ha, ?_⟩
  intro K hK
  have hpert : cNorm K m (a - a₀) < 1 :=
    (cNorm_mono_set_of_bddAbove (subset_univ K) (fun j hj ↦
      ⟨Cjet, by rintro _ ⟨x, _, rfl⟩; exact hjet j hj x⟩)).trans_lt hsmall
  have htotal : cNorm K m a ≤ C := by
    have htri := cNorm_add_le (f := a - a₀) (g := a₀) hK
      ((ha.sub h₀).of_le (by simp) : ContDiff ℝ m (a - a₀))
      (h₀.of_le (by simp))
    rw [sub_add_cancel] at htri
    have hbg := cNorm_zero_background_le K m
    dsimp only [C, a₀]
    linarith
  have hbound (L : ℝ) (hL : 0 ≤ L)
      (hLsum : L ≤ ‖reducedFrameProjection n‖ + ‖reducedZerothProjection n‖) :
      L * cNorm K m a ≤ M := by
    calc
      _ ≤ L * C := mul_le_mul_of_nonneg_left htotal hL
      _ ≤ (‖reducedFrameProjection n‖ + ‖reducedZerothProjection n‖) * C :=
        mul_le_mul_of_nonneg_right hLsum hC.le
      _ ≤ M := by dsimp [M]; linarith
  constructor
  · rw [← hQ]
    exact (cNorm_postLinear_le_on hK m (reducedFrameProjection n)
      (fun _ _ ↦ ha.contDiffAt.of_le (by simp))).trans
      (hbound _ (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _)))
  · exact (cNorm_postLinear_le_on hK m (reducedZerothProjection n)
      (fun _ _ ↦ ha.contDiffAt.of_le (by simp))).trans
      (hbound _ (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)))

end JanetCartan.PhysicalInitialization
