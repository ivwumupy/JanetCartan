module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalLeading

/-!
# Leading data on the same supplied original source callback

The current inverse keeps the full original callback prefix. This application
uses that EXACT prefix and its source dilation, rather than identifying it with
the convenient concrete prefix in `OriginalReference`. The sole extra numerical
restriction is the original leading frame tolerance, supplied by
`originalFrameTolerance_le_leading`. No current leading/profile premise remains.
Consumer: the actual leading/current-inverse join, `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.PhysicalInitialization
open PhysicalSeed PhysicalPrimary ProjectedStressFrame

variable {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean n))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : OriginalPatchIndex hn → Euclidean n) (hk : ∀ i, k i ≠ 0)
  (hkD : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.1)
  (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ j ∈ orders, 0 < margin j) (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
  (cap : ℝ) (hcap : 0 < cap)

local notation "Hsource" => ReferenceBoundary.H hn εframe hεframe qext hqcenter hqradius
  k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap

/-- The original geometric continuation proves the literal source dilation's
frame estimate; no alternate contracted reference is selected. -/
theorem supplied_original_source_frame {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) (i : Fin n) :
    cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
      (fun x ↦ projectedStress (sourceDilation (Hsource).map σ) x i - cubeStress n i) < εframe := by
  let G := ContractionBoundary.G hn εframe hεframe qext hqcenter hqradius
    k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap σ hσ hσone
  have hmap : G.map = sourceDilation (Hsource).map σ :=
    ContractionBoundary.fact5 hn εframe hεframe qext hqcenter hqradius
      k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap σ hσ hσone
  obtain ⟨δ, C₀, κ, hδ, _hC₀, _hκ, hnear, _hself⟩ :=
    ContractionBoundary.fact11 hn εframe hεframe qext hqcenter hqradius
      k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap σ hσ hσone
  have hzero : cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.R hn)) 8
      (G.map - G.map) < δ := by simpa only [sub_self, cNorm_zero] using hδ
  obtain ⟨_hi, _hrank, _hC4, _hmet, _hnormal, _hQ, hframe⟩ :=
    hnear univ G.map isOpen_univ (subset_univ _) G.contDiff.contDiffOn hzero
  simpa only [hmap] using hframe i

/-- All original leading cells on the SAME arbitrary original source prefix,
with every budget and threshold before the physical history. The reference is
literally `sourceDilation (Hsource).map σ`, as required by `StrongCurrent` and
`StrongSource`; no convenient-reference witness is substituted. -/
theorem exists_supplied_original_retained_physical_leading
    (hleading : ∀ a : OriginalPatchIndex hn,
      εframe ≤ (OriginalBoundary.η hn a / (2 * (6 + 1 : ℝ))) / 2)
    {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    {Cband : ℝ} (hband : 1 ≤ Cband) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {Mscalar mscalar : ℝ} (hMscalar : 0 ≤ Mscalar) (hmscalar : 0 < mscalar) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧
      ∃ Amap : OriginalPatchIndex hn → ℕ → ℝ,
      ∃ c : OriginalPatchIndex hn → ℝ,
      ∃ E : OriginalPatchIndex hn → ℕ → ℝ,
      ∃ A H B : (a : OriginalPatchIndex hn) → OriginalBoundary.centers hn a → ℕ → ℝ,
      (∀ a q, 0 ≤ Amap a q) ∧ (∀ a, 0 < c a) ∧ (∀ a q, 0 < E a q) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap (sourceDilation (Hsource).map σ) u
      ∀ a : OriginalPatchIndex hn,
        ∃ hF : ContDiff ℝ ∞ F,
        ∃ hi : IsImmersionOn F (ball 0 (OriginalBoundary.R hn)),
        ∃ hrank : HasFullNormalRankOn F (ball 0 (OriginalBoundary.R hn)),
        RetainedLeadingData (OriginalBoundary.T hn a)
          (K := closedBall (0 : Euclidean n) (OriginalBoundary.b hn))
          (OriginalBoundary.centers hn a) (OriginalBoundary.row hn a) (OriginalBoundary.col hn a)
          (OriginalBoundary.ρlead hn a) (OriginalBoundary.L hn a) (OriginalBoundary.τ hn a)
          (OriginalBoundary.Rc hn a) (OriginalBoundary.τc hn a) (OriginalBoundary.Mc hn a)
          (OriginalBoundary.rcomp hn a) (OriginalBoundary.δcomp hn a) (OriginalBoundary.σcover hn a)
          (OriginalBoundary.Ωc hn a) (OriginalBoundary.ρc hn a) (OriginalBoundary.Bc hn a)
          (OriginalBoundary.gc hn a) (OriginalBoundary.Bfull hn a)
          Mscalar mscalar (c a) (E a) (A a) (H a) (B a) F hF.contDiffOn hi hrank ∧
        HasDerivativeProfile (closedBall 0 (OriginalBoundary.b hn)) F rStar
          (currentCoefficientScale R₀ j) (Amap a) := by
  classical
  let G := sourceDilationReference Hsource hσ hσone
  have hmap : G.map = sourceDilation (Hsource).map σ := rfl
  have hdomain := ReferenceBoundary.fact5 hn εframe hεframe qext hqcenter hqradius
    k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
  have hR : OriginalBoundary.R hn < G.domain.chartRadius := by
    change OriginalBoundary.R hn < (Hsource).domain.chartRadius
    rw [hdomain]
    exact OriginalBoundary.R_lt_chartRadius hn
  have hreference (a : OriginalPatchIndex hn) (i : Fin n) :
      cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) <
          (OriginalBoundary.η hn a / (2 * (6 + 1 : ℝ))) / 2 := by
    rw [hmap]
    exact (supplied_original_source_frame hn εframe hεframe qext hqcenter hqradius
      k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap hσ hσone i).trans_le (hleading a)
  have hconstruct (a : OriginalPatchIndex hn) :=
    exists_history_retained_leading_data G (OriginalBoundary.b_pos hn)
      (OriginalBoundary.b_lt_R hn) hR
      (T := OriginalBoundary.T hn a) (OriginalBoundary.η_pos hn a)
      (OriginalBoundary.centers hn a) (OriginalBoundary.row hn a) (OriginalBoundary.col hn a)
      (OriginalBoundary.ρlead hn a) (OriginalBoundary.L hn a) (OriginalBoundary.τ hn a)
      (OriginalBoundary.Rc hn a) (OriginalBoundary.τc hn a) (OriginalBoundary.Mc hn a)
      (OriginalBoundary.rcomp hn a) (OriginalBoundary.δcomp hn a) (OriginalBoundary.σcover hn a)
      (OriginalBoundary.Ωc hn a) (OriginalBoundary.ρc hn a) (OriginalBoundary.Bc hn a)
      (OriginalBoundary.gc hn a) (OriginalBoundary.Bfull hn a)
      (OriginalBoundary.generic_leading hn a) hband hStar horder (hreference a) hMscalar hmscalar
  choose Sa hSa Amap hAmap c E A H B hc hE hdata using hconstruct
  let threshold := 2 + ∑ a, Sa a
  have hnonneg a : 0 ≤ Sa a := (by norm_num : (0 : ℝ) ≤ 2).trans (hSa a)
  have hthreshold : 2 ≤ threshold := le_add_of_nonneg_right (Finset.sum_nonneg fun a _ ↦ hnonneg a)
  have hle a : Sa a ≤ threshold :=
    (Finset.single_le_sum (fun b _ ↦ hnonneg b) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨threshold, hthreshold, Amap, c, E, A, H, B, hAmap, hc, hE, ?_⟩
  intro R₀ hR₀ j u ell hu F a
  simpa only [hmap] using hdata a R₀ ((hle a).trans hR₀) j u ell hu

end JanetCartan.PhysicalInitialization
