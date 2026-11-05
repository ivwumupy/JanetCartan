module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryAdmission
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedContinuity

/-!
# Full coefficient caps chosen before the common reference

The full-array margin in the original normalized initializer supplies one bound
for both the principal frame and the complete zeroth coefficient. The bound and
reference tolerance precede the reference; only the displacement threshold may
depend on that same reference. The consumers are the sector and elliptic gain
constructors in `NormalizedRegularSolver` and `FixedDomainInverse.FullSource`.
Sources: `app:ch_regular:eq:coefficient-extension`, `main:prop:current-scale`,
and `main:eq:displacement-budget`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.SectorHistoryAdmission
open GeometricProfile ProtectedFlow ResponseTransfer.RetainedFactors
open FullPhaseCharts.InverseEstimates

/-- The fixed zero-completion background has a bound independent of the
measurement compact set (`app:ch_regular:eq:coefficient-extension`). This is
used only to turn the unit perturbation budget into the full coefficient cap. -/
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

/-- A fixed positive cap and a full-array reference tolerance are chosen
BEFORE the reference and every finite history. The actual admissible-prefix
displacement supplies the primitive map neighborhood, with reserve exactly
`max 8 (m + 2)`. Both projections retain their Frobenius norms and the full
zeroth coefficient; no coefficient estimate is a hypothesis on the history
(`main:prop:current-scale`, `app:ch_regular:eq:coefficient-extension`).

The original initializer's finite `orders, margin` continuation supplies the
displayed reference margin on the SAME `G`. Consumers specialize `m` to
`RegularSector.FiniteEvolution.sectorLowOrder d` before selecting their masks. -/
theorem exists_reference_tolerance_for_history_coefficient_cap {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n)) (hextcenter : ext.center = 0)
    {R : ℝ} (hextR : ext.radius < R) (m : ℕ) :
    ∃ M > (0 : ℝ), ∃ η > (0 : ℝ),
      ∀ G : FlatReference n, R < G.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean n) ext.radius) m
        (geometricReducedCoefficients G.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      ∀ rStar kMin : ℕ, 8 ≤ rStar → m + 2 ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
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
  intro G hR href rStar kMin hStar hreserve horder
  obtain ⟨δ, hδ, hnear⟩ := hreference G hR
  obtain ⟨S, hS, hhistory⟩ :=
    FiniteHistoryBounds.exists_initialScale_for_prefix_neighborhood
      (F := Euclidean (embeddingDimension n)) rStar horder hδ
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu F Q B
  have hF : ContDiff ℝ ∞ F := hu.contDiff_finiteHistoryMap G.contDiff
  have hdisplacement := hhistory R₀ hR₀ (closedBall 0 R) G.map s u
    (fun i ↦ (ell i : ℝ)) (isCompact_closedBall _ _)
    (fun i ↦ (hu i).2.1) (fun i ↦ (hu i).2.2.1)
    (fun i ↦ (hu i).2.2.2) (fun i ↦ Nat.cast_le.mpr (hu i).1)
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

end JanetCartan.SectorHistoryAdmission
