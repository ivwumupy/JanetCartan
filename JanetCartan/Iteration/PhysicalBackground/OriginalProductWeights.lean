module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SelectedProductWeights
public import JanetCartan.Iteration.PhysicalNormalInverse.StrongSource
public import JanetCartan.Iteration.PhysicalBackground.ActualReference

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev PositiveBackground
open PhysicalSeed

/-- The exact original carrier collar attached to a selected product cell. -/
noncomputable def originalProductV
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = OriginalBoundary.b hn)
    (k : (j : Fin (OriginalBoundary.D hn).chartCount) ×
      Fin ((OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)) →
      (l : Fin ((OriginalBoundary.D hn).patchCount
        ((p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ OriginalBoundary.centers hn
        ⟨(p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) →
      { ε : ℝ // 0 < ε })
    (i : originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) : Set CarrierParameter :=
  let i' := i
  ball ((↑↑(SelectedBoundary.cell hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i'.fst i'.snd) : Euclidean 3).ofLp 0,
    FullPhaseCharts.ActualComparison.spectatorCenter
      (↑↑(SelectedBoundary.cell hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
        extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i'.fst i'.snd) : Euclidean 3))
    (OriginalBoundary.εcarrier hn
      ⟨(↑↑i'.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, i'.snd⟩
      (SelectedBoundary.cell hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
        extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i'.fst i'.snd))

noncomputable def originalProductRoot
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = OriginalBoundary.b hn)
    (k : (j : Fin (OriginalBoundary.D hn).chartCount) × Fin ((OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0) (hkdom : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ) (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j) (cap : ℝ) (hcap : 0 < cap)
    (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)) →
      (l : Fin ((OriginalBoundary.D hn).patchCount ((p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ OriginalBoundary.centers hn ⟨(p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) → { ε : ℝ // 0 < ε })
    (i : originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) : Euclidean 3 :=
  let i' := i
  (OriginalBoundary.D hn).roots
    ((↑↑i'.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1)
    i'.snd ((↑↑i'.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).2)

noncomputable def originalProductRadius
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = OriginalBoundary.b hn)
    (k : (j : Fin (OriginalBoundary.D hn).chartCount) × Fin ((OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0) (hkdom : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ) (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j) (cap : ℝ) (hcap : 0 < cap)
    (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)) →
      (l : Fin ((OriginalBoundary.D hn).patchCount ((p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ OriginalBoundary.centers hn ⟨(p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) → { ε : ℝ // 0 < ε })
    (i : originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) : ℝ :=
  let i' := i
  OriginalBoundary.Rproduct hn
    ⟨(↑↑i'.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, i'.snd⟩
    (SelectedBoundary.cell hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i'.fst i'.snd)

theorem exists_original_product_weights
    {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hε : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean n)) (hq0 : qext.center = 0)
    (hqr : qext.radius = OriginalBoundary.b hn)
    (k : (j : Fin (OriginalBoundary.D hn).chartCount) ×
      Fin ((OriginalBoundary.D hn).patchCount j) → Euclidean n)
    (hk0 : ∀ i, k i ≠ 0)
    (hkdom : ∀ i, k i ∈ (OriginalBoundary.D hn).domain i.fst)
    (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ)
    (hmarg : ∀ j ∈ orders, 0 < margin j)
    (hext : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hinc : 0 < incidenceCap)
    (aExtra :
      (p : ContinuumRow.CanonicalConic.IncidenceCenter (OriginalBoundary.D hn)) →
      (l : Fin ((OriginalBoundary.D hn).patchCount
        ((p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1))) →
      (j : {j // j ∈ OriginalBoundary.centers hn
        ⟨(p : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, l⟩}) → { ε : ℝ // 0 < ε }) :
    let ι := originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
    ∃ χ : ι → CarrierParameter → ℝ,
    ∃ V : ι → Set CarrierParameter,
      (∀ a, ContDiff ℝ ∞ (χ a)) ∧
      (∀ a z, χ a z ∈ Icc (0 : ℝ) 1) ∧
      (∀ a, HasCompactSupport (χ a)) ∧
      (∀ a, IsOpen (V a)) ∧
      (∀ a, tsupport (χ a) ⊆ V a) := by
  let ι := originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let zRoot : ι → Euclidean 3 := fun i ↦
    originalProductRoot hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  let am : ι → ℝ := fun i ↦
    SelectedBoundary.a' hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  let R : ι → ℝ := fun i ↦
    originalProductRadius hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  let V : ι → Set CarrierParameter := fun i ↦
    originalProductV hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  have hV : ∀ i, IsOpen (V i) := by intro i; exact isOpen_ball
  have hr : 0 < SelectedBoundary.rMeasure hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra :=
    SelectedBoundary.hrMeasure _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hcell : 4 * SelectedBoundary.rMeasure hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra < 1 / 2 :=
    SelectedBoundary.hMeasureCell _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hram : ∀ i, 6 * SelectedBoundary.rMeasure hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra < am i := by
    intro i
    exact SelectedBoundary.fact60 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
  have hsCap : 0 < PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra :=
    original_sourceCap_pos hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra
  obtain ⟨kMin, hkMin⟩ := exists_nat_gt
    (RevisedScales.displacementLoss n + bandExponent *
      ((ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2)
  have haa : ∀ i, SelectedBoundary.a' hn εframe hε qext hq0 hqr k hk0 hkdom p orders
      margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i ≤
      SelectedBoundary.a hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
        hmarg hext cap hcap incidenceCap hinc aExtra i := by
    intro i
    exact original_selected_a'_le_a hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let σ₀ := PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra / 2
  have hσ₀ : σ₀ ∈ Set.Ioc (0 : ℝ)
      (PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) := by
    exact ⟨by dsimp [σ₀]; linarith, by dsimp [σ₀]; linarith⟩
  have houter (i : ι) : type_of% (PhysicalNormalInverse.StrongSource.Arguments.houter
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i) :=
    PhysicalNormalInverse.StrongSource.Arguments.houter
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i
  have har (i : ι) : type_of% (PhysicalNormalInverse.StrongSource.Arguments.har
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i) :=
    PhysicalNormalInverse.StrongSource.Arguments.har
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i
  have hrr (i : ι) : type_of% (PhysicalNormalInverse.StrongSource.Arguments.hrr
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i) :=
    PhysicalNormalInverse.StrongSource.Arguments.hrr
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i
  have hselected : ∀ i, ContinuumAdjoint.Canonical.PhaseExtension.supportedChart
      (n := n) (zRoot i) (am i) ⊆ ball 0 (R i) ×ˢ V i := by
    intro i q hq
    have hq' : q ∈ ContinuumRow.CanonicalConic.coefficientDomain
        (zRoot i)
        (SelectedBoundary.r hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
          hmarg hext cap hcap incidenceCap hinc aExtra i)
        (6 * SelectedBoundary.a hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
          hmarg hext cap hcap incidenceCap hinc aExtra i) := by
      rcases hq with ⟨hq0', hq1', hq2'⟩
      refine ⟨closedBall_subset_ball (by nlinarith [haa i, hr, hram i]) hq0', ?_, ?_⟩
      · exact closedBall_subset_ball (by nlinarith [hr, hram i, har i, hrr i]) hq1'
      · exact closedBall_subset_ball (by nlinarith [haa i, hr, hram i]) hq2'
    simpa [zRoot, R, V, originalProductRadius, originalProductV,
      ContinuumAdjoint.Canonical.PhaseExtension.supportedChart,
      ContinuumRow.CanonicalConic.carrierSupport] using houter i hq'
  obtain ⟨χ, hχ, hχrange, hχcompact, hχV, hplateau, -⟩ :=
    exists_selected_product_external_weights zRoot (am := am) (R := R)
      (fun i ↦ by linarith [hr, hram i]) V hV hselected hr hram
  exact ⟨χ, V, hχ, hχrange, hχcompact, hV, hχV⟩

end JanetCartan.PhysicalBackground
