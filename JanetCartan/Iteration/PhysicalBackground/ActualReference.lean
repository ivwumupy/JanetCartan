module

public import JanetCartan.Iteration.PhysicalBackground.ReferenceBudget
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongReference

/-!
# Actual reference raw seed at half the finite-low tolerance

This is the concrete join needed before current-history continuity.  The source
is the literal v2 measured source at cutoff one and factor two, built from the
same normalized carrier tuple `(μ,K,V,w,ν,ξ)`.  The raw operator is the SAME
`rightInverse` of the supplied augmented row.  The strong reference estimate
is consumed in its native inverse-plus-raw form (the form returned by
`StrongSourceGap.reference_uncorrected_raw`), so no row-operator norm
continuity and no sigma-dependent Cfull is used to choose the initial scale.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev PositiveBackground CoerciveInverse
open ProjectedStressFrame NormalizedBackground NormalizedBackground.SourceGeometry

variable {n N : ℕ}

/-- The index of the already-selected center/cell family used by the original
source inverse.  This is only a type abbreviation for the retained selection;
no new center, cell, or row is chosen here. -/
noncomputable def originalReferenceIndex
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = PhysicalSeed.OriginalBoundary.b hn)
    (k : (j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount) ×
        Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (PhysicalSeed.OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter
          (PhysicalSeed.OriginalBoundary.D hn)) →
      (l : Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ PhysicalSeed.OriginalBoundary.centers hn
        ⟨(p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) → { ε : ℝ // 0 < ε }) : Type :=
  (j : {j // j ∈ PhysicalSeed.SelectedBoundary.centers hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra}) ×
    Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
      ((↑↑j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))

noncomputable instance originalReferenceIndex_fintype
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = PhysicalSeed.OriginalBoundary.b hn)
    (k : (j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount) ×
        Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (PhysicalSeed.OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter
          (PhysicalSeed.OriginalBoundary.D hn)) →
      (l : Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ PhysicalSeed.OriginalBoundary.centers hn
        ⟨(p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) →
      { ε : ℝ // 0 < ε }) : Fintype (originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) := by
  dsimp [originalReferenceIndex]
  infer_instance

theorem original_sourceCap_pos
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = PhysicalSeed.OriginalBoundary.b hn)
    (k : (j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount) ×
      Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (PhysicalSeed.OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter
          (PhysicalSeed.OriginalBoundary.D hn)) →
      (l : Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ PhysicalSeed.OriginalBoundary.centers hn
        ⟨(p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) →
      { ε : ℝ // 0 < ε }) :
    0 < PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra := by
  let g := PhysicalSeed.SourceInverseBoundary.g hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let rInner := PhysicalSeed.SourceInverseBoundary.rInner hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hrInner := PhysicalSeed.SourceInverseBoundary.hrInner hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hInnerCell := PhysicalSeed.SourceInverseBoundary.hInnerCell hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let Mlimit := PhysicalSeed.SourceInverseBoundary.Mlimit hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  have hspec := Classical.choose_spec
    (p := fun sourceCap : ℝ =>
      PhysicalSeed.SourceInverseBoundary.Prefix10 hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
        g rInner hrInner hInnerCell Mlimit sourceCap)
    (PhysicalSeed.SourceInverseBoundary.selectedPrefix9 hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra)
  exact hspec.1

theorem original_selected_a'_le_a
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = PhysicalSeed.OriginalBoundary.b hn)
    (k : (j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount) ×
      Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (PhysicalSeed.OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter
          (PhysicalSeed.OriginalBoundary.D hn)) →
      (l : Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ PhysicalSeed.OriginalBoundary.centers hn
        ⟨(p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) →
      { ε : ℝ // 0 < ε })
    (i : (j : PhysicalSeed.SelectedBoundary.centers hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) ×
      Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((↑↑j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) :
    PhysicalSeed.SelectedBoundary.a' hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i ≤
    PhysicalSeed.SelectedBoundary.a hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i := by
  have hsCap := original_sourceCap_pos hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  obtain ⟨kMin, hkMin⟩ := exists_nat_gt
    (RevisedScales.displacementLoss n + bandExponent *
      ((ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2)
  exact PhysicalNormalInverse.StrongSource.Arguments.haa
    hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
      incidenceCap hinc aExtra
      (PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra / 2)
      ⟨by linarith, by linarith⟩ (Bband := 1)
      (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
      (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i

/-- Exact v2 measured-source equality on the fixed
physical support.  This is the bridge from the retained physical mean identity
to the normalized reference source; it preserves cutoff index one and factor
two. -/
theorem measuredSourceToL2_eq_of_residual_eqOn
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n)
    {R S : MetricField n}
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r)))
    (hS : ContDiffOn ℝ ∞ S (ball 0 (4 * r)))
    (heq : EqOn R S (ball 0 (4 * r))) :
    measuredSourceToL2 hr hcell Q R hQ hR =
      measuredSourceToL2 hr hcell Q S hQ hS := by
  unfold measuredSourceToL2
  exact congrArg Neg.neg
    (fixedResidualToL2_eq_of_residual_eqOn hr hcell Q hQ hR hS heq)


/-- The actual SAME-row reference source and raw correction admit a source
scale chosen before current-history perturbation.  The normalized source
producer is invoked on the literal index-one measured source; the raw estimate
is the exact inverse-plus-raw clause supplied by
`StrongSourceGap.reference_uncorrected_raw`. -/
theorem exists_actual_reference_rawSeed_half_budget
    {ι T : Type} [Fintype ι]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    {δ σcap : ℝ} (hδ : 0 < δ) (hσcap : 0 < σcap)
    {m : ℕ}
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω) (h0 : (0 : Euclidean n) ∈ Ω)
    (hflat : ∀ x ∈ Ω, inducedMetric F x = 1)
    (hrank : HasFullNormalRankOn F Ω)
    (μ : ι → Measure CarrierParameter)
    (K V : ι → Set CarrierParameter)
    [∀ a, IsFiniteMeasure ((μ a).restrict (K a))]
    (hV : ∀ a, IsOpen (V a)) (hK : ∀ a, IsCompact (K a))
    (hKV : ∀ a, K a ⊆ V a)
    (w : ι → CarrierParameter → ℝ)
    (ν : ι → Euclidean n × CarrierParameter → T)
    (ξ : ι → Euclidean n × CarrierParameter → Euclidean n)
    (hw : ∀ a, ContDiffOn ℝ ∞ (w a) (V a))
    (hwpos : ∀ a z, 0 ≤ w a z)
    (hν : ∀ a, ContDiffOn ℝ ∞ (ν a) (Ω ×ˢ V a))
    (hξ : ∀ a, ContDiffOn ℝ ∞ (ξ a) (Ω ×ˢ V a))
    (hwSupport : ∀ a z, z ∉ K a → w a z = 0)
    (hQ : ∀ ρ, ρ ∈ Ioc (0 : ℝ) 1 →
      ContDiffOn ℝ ∞ (projectedStress (sourceDilation F ρ)) (ball 0 (4 * r)))
    (hR : ∀ ρ, ρ ∈ Ioc (0 : ℝ) 1 →
      ContDiffOn ℝ ∞
        (referenceMeanResidual (sourceDilation F ρ)
          (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ ρ))
        (ball 0 (4 * r)))
    (Arow : ∀ (σ : ℝ), σ ∈ Ioc (0 : ℝ) σcap →
      (AugmentedInput n ι →L[ℝ] OutputL2 n))
    (Cfull : ℕ → ℝ)
    (hstrong : ∀ (σ : ℝ), (hσ : σ ∈ Ioc (0 : ℝ) σcap) → ∀ (s : ℕ)
      (f : PeriodicL2 n (Euclidean n)),
      f ∈ periodicSobolevLevel n (Euclidean n) s →
      rightInverse (Arow σ hσ) f ∈ augmentedInputLevel n ι s ∧
        (periodicSobolevScale n (Euclidean n)).gradeNorm s
            ((normalOperator (Arow σ hσ)).inverse f) +
          (augmentedInputSobolevScale n ι).gradeNorm s (rightInverse (Arow σ hσ) f) ≤
          Cfull s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s f + ‖f‖)) :
    ∃ σhalf > (0 : ℝ), σhalf ≤ σcap ∧
      ∀ (σ : ℝ) (_hσ : σ ∈ Ioc (0 : ℝ) σhalf)
        (hσcap : σ ∈ Ioc (0 : ℝ) σcap)
        (hσ1 : σ ∈ Ioc (0 : ℝ) 1),
        (augmentedInputSobolevScale n ι).gradeNorm m
          (rightInverse (Arow σ hσcap)
            (measuredSourceToL2 hr hcell
              (projectedStress (sourceDilation F σ))
              (referenceMeanResidual (sourceDilation F σ)
                (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ σ))
              (hQ σ hσ1) (hR σ hσ1))) ≤ δ / 2 := by
  obtain ⟨ρ₀, hρ₀, hρ₀1, hbaseline⟩ :=
    exists_normalized_reference_measuredSource_bounds hF hΩ h0 hflat hrank
      μ K V hV hK hKV w ν ξ hw hwpos hν hξ hwSupport hr hcell hQ hR
  obtain ⟨Cm, hCm, hCmBound⟩ := hbaseline m
  obtain ⟨C0, hC0, hC0Bound⟩ := hbaseline 0
  let cap₀ := min σcap ρ₀
  have hcap₀ : 0 < cap₀ := lt_min hσcap hρ₀
  have hcap₀σ : cap₀ ≤ σcap := min_le_left _ _
  let A := |Cfull m| * (Cm + C0)
  let D := A + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (abs_nonneg _) (add_nonneg hCm.le hC0.le)
  have hD : 0 < D := by
    dsimp [D]
    linarith
  let σhalf := min cap₀ (δ / (2 * D))
  have hδD : 0 < δ / (2 * D) := by positivity
  have hhalf : 0 < σhalf := lt_min hcap₀ hδD
  refine ⟨σhalf, hhalf, (min_le_left _ _).trans hcap₀σ, ?_⟩
  intro σ hσ hσcap hσ1
  have hσρ : σ ∈ Ioc (0 : ℝ) ρ₀ :=
    ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  let eσ := measuredSourceToL2 hr hcell
    (projectedStress (sourceDilation F σ))
    (referenceMeanResidual (sourceDilation F σ)
      (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ σ))
    (hQ σ hσ1) (hR σ hσ1)
  have heMem : eσ ∈ periodicSobolevLevel n (Euclidean n) m := by
    exact measuredSourceToL2_mem hr hcell
      (projectedStress (sourceDilation F σ))
      (referenceMeanResidual (sourceDilation F σ)
        (carrierMean μ w ν ξ 0) (normalizedCarrierMean μ w ν ξ σ))
      (hQ σ hσ1) (hR σ hσ1) m
  have hpair := hstrong σ hσcap m eσ heMem
  have hsrcm := hCmBound σ hσρ hσ1
  have hsrc0 := hC0Bound σ hσρ hσ1
  have hnorm : ‖eσ‖ ≤ C0 * σ := by
    simpa only [GradedScale.gradeNorm_zero] using hsrc0
  have hraw :
      (augmentedInputSobolevScale n ι).gradeNorm m (rightInverse (Arow σ hσcap) eσ) ≤
        Cfull m * ((periodicSobolevScale n (Euclidean n)).gradeNorm m eσ + ‖eσ‖) := by
    exact (le_add_of_nonneg_left
      ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg m
        ((normalOperator (Arow σ hσcap)).inverse eσ))).trans hpair.2
  have hrawA :
      (augmentedInputSobolevScale n ι).gradeNorm m (rightInverse (Arow σ hσcap) eσ) ≤ A * σ := by
    calc
      _ ≤ Cfull m * ((periodicSobolevScale n (Euclidean n)).gradeNorm m eσ + ‖eσ‖) := hraw
      _ ≤ |Cfull m| * ((periodicSobolevScale n (Euclidean n)).gradeNorm m eσ + ‖eσ‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg
          ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg _ _) (norm_nonneg _))
      _ ≤ |Cfull m| * (Cm * σ + C0 * σ) :=
        mul_le_mul_of_nonneg_left (add_le_add hsrcm hnorm) (abs_nonneg _)
      _ = A * σ := by
        dsimp [A]
        ring
  have hσD : σ ≤ δ / (2 * D) := hσ.2.trans (min_le_right _ _)
  have hDσ : D * σ ≤ D * (δ / (2 * D)) :=
    mul_le_mul_of_nonneg_left hσD (le_of_lt hD)
  have hAσ : A * σ ≤ D * σ := by
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hσ.1.le
  have hfinal :
      (augmentedInputSobolevScale n ι).gradeNorm m (rightInverse (Arow σ hσcap) eσ) ≤ δ / 2 := by
    calc
      _ ≤ A * σ := hrawA
      _ ≤ D * σ := hAσ
      _ ≤ D * (δ / (2 * D)) := hDσ
      _ = δ / 2 := by field_simp [ne_of_gt hD]
  simpa only [eσ] using hfinal


/-- The literal augmented row used by the generated StrongReference theorem at
zero density.  Its Vop is the supplied `StrongSourceGap.Vop`, with no new row,
flow, cell, cutoff, or exterior. -/
abbrev originalReferenceRow
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = PhysicalSeed.OriginalBoundary.b hn)
    (k : (j : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount) ×
        Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (PhysicalSeed.OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter
          (PhysicalSeed.OriginalBoundary.D hn)) →
      (l : Fin ((PhysicalSeed.OriginalBoundary.D hn).patchCount
        ((p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ PhysicalSeed.OriginalBoundary.centers hn
        ⟨(p : Fin (PhysicalSeed.OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) → { ε : ℝ // 0 < ε })
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ)
      (PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra)) :
    AugmentedInput n (originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders
      margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) →L[ℝ] OutputL2 n :=
  augmentedRow
    (imageChannel
      (PhysicalSeed.SelectedBoundary.coeff hn εframe hε qext hq0 hqr k hk0 hkdom p orders
        margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra σ)
      (FixedCutoffs.periodic hr hcell 1) (FixedCutoffs.periodic hr hcell 2))
    (fun i ↦ CommonMeasurement.restrictCarrier (FixedCutoffs.periodic hr hcell 1)
      (JanetCartan.PhysicalNormalInverse.StrongSourceGap.Vop hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
        hmarg hext cap hcap incidenceCap hinc aExtra σ hσ (fun _ _ ↦ 0)
        (fun _ ↦ contDiffOn_const)
        (by intro _ _ _; norm_num)
        (by intro _ _ _; constructor <;> norm_num)
        (by intro _; change cNorm _ _ (0 : (Euclidean (n - 1) × Euclidean 3) → ℝ) ≤ 1
            rw [cNorm_zero]
            norm_num)
        i))
     (ContinuumNormal.innerCutoff hr (by nlinarith [hcell]))

end JanetCartan.PhysicalBackground

