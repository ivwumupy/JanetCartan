module

public import JanetCartan.Iteration.PhysicalBackground.OriginalProductWeights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SelectedProductSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.IncidenceSourceDomain
import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.InitializedProofCache

/-!
# Actual source charts on the original selected product cells

This leaf instantiates the positive-background producer on the literal retained
original data.  In particular, the measurement radius is exactly
`SelectedBoundary.rMeasure`; no smaller radius or reselected carrier is used.
The returned existential is the one concrete source/current construction later
consumed by the same-row reference and physical-history applications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev PositiveBackground PhysicalSeed ActualCarriers CurrentFullPhase FrozenMenu
open ContinuumRow.CanonicalConic
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction

set_option warningAsError true
set_option maxHeartbeats 2000000

/- Full native source/current payload, cached before any projection. -/
proof_from originalProductSourceFull
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
      { ε : ℝ // 0 < ε }) :=
  let ι := originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let parent : ι → (j : Fin (OriginalBoundary.D hn).chartCount) ×
      Fin ((OriginalBoundary.D hn).patchCount j) := fun i ↦
    ⟨(↑↑i.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).1, i.snd⟩
  let G := ReferenceBoundary.H hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap
  let U : Set (Euclidean n) := ball 0 (OriginalBoundary.R hn)
  let P : ι → Patch n := fun i ↦ (OriginalBoundary.D hn).patches (parent i).1 (parent i).2
  let T : (i : ι) → ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily (P i) U isOpen_ball := fun i ↦
    OriginalBoundary.T hn (parent i)
  let center : (i : ι) → {j // j ∈ OriginalBoundary.centers hn (parent i)} := fun i ↦
    SelectedBoundary.cell hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext
      cap hcap incidenceCap hinc aExtra i.fst i.snd
  let Ω : ι → Set (Euclidean n × Euclidean 3) := fun i ↦
    OriginalBoundary.Ωc hn (parent i) (center i)
  let z₀ : ι → Euclidean 3 := fun i ↦ (↑↑(center i) : Euclidean 3)
  let ρ : ι → ℝ := fun i ↦ OriginalBoundary.ρc hn (parent i) (center i)
  let Rc : ι → ℝ := fun i ↦ OriginalBoundary.Rc hn (parent i) (center i)
  let M : ι → ℝ := fun i ↦ OriginalBoundary.Bc hn (parent i) (center i)
  let τ : ι → ℝ := fun i ↦ OriginalBoundary.τc hn (parent i) (center i)
  let δgeometry : ι → ℝ := fun i ↦ OriginalBoundary.δcomp hn (parent i) (center i)
  let row : ι → Fin n := fun i ↦ OriginalBoundary.row hn (parent i) (center i)
  let col : ι → Fin n := fun i ↦ OriginalBoundary.col hn (parent i) (center i)
  let seed : (i : ι) → Chart (T i) (Ω i) (closedBall ((0 : Euclidean n), z₀ i) (ρ i))
      ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (M i) (τ i) (row i) (col i) G.map := fun i ↦
    SeedBoundary.seed hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap (parent i) (center i)
  let zRoot : ι → Euclidean 3 := fun i ↦ originalProductRoot hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let Rcell : ι → ℝ := fun i ↦ originalProductRadius hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let V : ι → Set CarrierParameter := fun i ↦ originalProductV hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let θ : ι → Euclidean (n - 1) := fun i ↦ NormedSpace.normalize
    ((ContinuousLinearMap.adjoint
      ((T i).data.adapted.embedding.toContinuousLinearMap))
      ((SelectedBoundary.t hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i) •
        (fun i ↦ (↑↑i.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).2) i))
  let am : ι → ℝ := fun i ↦ SelectedBoundary.a' hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let width : ι → ℝ := fun i ↦ angularWidth
    ((ContinuousLinearMap.adjoint ((T i).data.adapted.embedding.toContinuousLinearMap))
      ((SelectedBoundary.t hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i) •
        (fun i ↦ (↑↑i.fst : Fin (OriginalBoundary.D hn).chartCount × Euclidean n).2) i))
    (SelectedBoundary.r' hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i)
  let r : ℝ := SelectedBoundary.rMeasure hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
    hmarg hext cap hcap incidenceCap hinc aExtra
  let hgeom (a : ι) := OriginalBoundary.transport_cells hn (parent a) (center a)
  let hsource (a : ι) := OriginalBoundary.cofactor_cells hn (parent a) (center a)
  let hpos (a : ι) := OriginalBoundary.comparison_pos hn (parent a) (center a)
  let hproduct (a : ι) := OriginalBoundary.density_product_geometry hn (parent a) (center a)
  let hapos (a : ι) : 0 < am a := by
    exact SelectedBoundary.ha' hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra a
  let hrpos : 0 < r := by
    dsimp [r]
    exact SelectedBoundary.hrMeasure hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra
  let hrampos (a : ι) : 6 * r < am a := by
    exact SelectedBoundary.fact60 hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra a
  let hcellpos : 4 * r < 1 / 2 := by
    dsimp [r]
    exact SelectedBoundary.hMeasureCell hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra
  let hwidthpos (a : ι) : 0 < width a := by
    exact (angularWidth_spec
      (SelectedBoundary.hηb hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext
        cap hcap incidenceCap hinc aExtra a)
      (SelectedBoundary.hr' hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext
        cap hcap incidenceCap hinc aExtra a)).1
  let rLead : ι → ℝ := fun i ↦ SelectedBoundary.r hn εframe hε qext hq0 hqr k hk0 hkdom p orders
    margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let aLead : ι → ℝ := fun i ↦ SelectedBoundary.a hn εframe hε qext hq0 hqr k hk0 hkdom p orders
    margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let hrLead (i : ι) : 0 < rLead i := by
    exact SelectedBoundary._hr hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  let haLead (i : ι) : 0 < aLead i := by
    exact SelectedBoundary._ha hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  let ham (i : ι) : am i ≤ aLead i := by
    exact original_selected_a'_le_a hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra i
  let kMin : ℕ := Classical.choose (exists_nat_gt
    (RevisedScales.displacementLoss n + bandExponent *
      ((ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2))
  let hkMin : RevisedScales.displacementLoss n + bandExponent *
      ((ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) :=
    Classical.choose_spec (exists_nat_gt
      (RevisedScales.displacementLoss n + bandExponent *
        ((ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2))
  let σ₀ := PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
    p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra / 2
  let hsCap : 0 < PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
      p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra :=
    original_sourceCap_pos hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra
  let hσ₀ : σ₀ ∈ Set.Ioc (0 : ℝ)
      (PhysicalSeed.SourceInverseBoundary.sourceCap hn εframe hε qext hq0 hqr k hk0 hkdom
        p orders margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) := by
    exact ⟨by dsimp [σ₀]; linarith [hsCap], by dsimp [σ₀]; linarith [hsCap]⟩
  let houter (i : ι) :=
    PhysicalNormalInverse.StrongSource.Arguments.houter
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i
  let har (i : ι) :=
    PhysicalNormalInverse.StrongSource.Arguments.har
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i
  let hrr (i : ι) :=
    PhysicalNormalInverse.StrongSource.Arguments.hrr
      hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin hmarg hext cap hcap
        incidenceCap hinc aExtra σ₀ hσ₀ (Bband := 1)
        (rStar := ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n)
        (kMin := kMin) (by norm_num) (by norm_num) (by exact hkMin) i
  let hcoeff (i : ι) : coefficientDomain (zRoot i) (rLead i) (6 * aLead i) ⊆
      ball (0 : Euclidean n) (Rcell i) ×ˢ V i := by
    simpa [zRoot, Rcell, V, originalProductRoot, originalProductRadius, originalProductV, rLead, aLead] using houter i
  let hselected : ∀ i, ContinuumAdjoint.Canonical.PhaseExtension.supportedChart
      (n := n) (zRoot i) (am i) ⊆ ball (0 : Euclidean n) (Rcell i) ×ˢ V i := by
    intro i q hq
    let hq' : q ∈ coefficientDomain (n := n) (zRoot i) (rLead i) (6 * aLead i) := by
      rcases hq with ⟨hq0', hq1', hq2'⟩
      refine ⟨closedBall_subset_ball (by nlinarith [ham i, hrpos, hrampos i]) hq0', ?_, ?_⟩
      · exact closedBall_subset_ball (by nlinarith [hrLead i, hrampos i, har i, hrr i]) hq1'
      · exact closedBall_subset_ball (by nlinarith [ham i, hrpos, hrampos i]) hq2'
    exact hcoeff i hq'
  let hRU (i : ι) : ball (0 : Euclidean n) (Rcell i) ⊆ U := by
    simpa [U, Rcell, originalProductRadius] using (hproduct i).2.2.2.2.1
  let : Nonempty ι := by
    dsimp [ι, originalReferenceIndex]
    exact JanetCartan.ContinuumInverse.retained_incidence_channel_nonempty hn (OriginalBoundary.hD hn).1
      (SelectedBoundary.centers hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
        hmarg hext cap hcap incidenceCap hinc aExtra)
      (SelectedBoundary.εcover hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
        hmarg hext cap hcap incidenceCap hinc aExtra)
      (SelectedBoundary.fact5 hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
        hmarg hext cap hcap incidenceCap hinc aExtra)
      (SelectedBoundary.fact7 hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
        hmarg hext cap hcap incidenceCap hinc aExtra)
  let h6U : closedBall (0 : Euclidean n) (6 * r) ⊆ U :=
    JanetCartan.ContinuumInverse.retained_measured_source_ball_subset zRoot hrLead haLead V hcoeff hRU ham hrpos hrampos
  let hV : ∀ i, IsOpen (V i) := by
    intro i
    simp [V, originalProductV]
  let hRphysical : ∀ i, Rcell i ≤ (T i).physicalRadius := by
    intro i
    simpa [Rcell, originalProductRadius, T] using (hproduct i).2.2.2.1
  let hflow : ∀ i, MapsTo (PositiveReference.densityCoordinates (T i))
      (ball (0 : Euclidean n) (Rcell i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (τ i)) := by
    intro i
    simpa [Rcell, V, originalProductRadius, originalProductV, T, z₀, Rc, τ] using
      (hproduct i).2.2.2.2.2.2.2.2.2.1
  let hcall := exists_constructed_source_on_selected_product_cells
    (A := ι) (Ω := Ω) (z₀ := z₀) (ρ := ρ) (Rc := Rc) (M := M) (τ := τ)
    (δgeometry := δgeometry) (row := row) (col := col) (P := P)
    (cP := OriginalBoundary.c hn) (CP := OriginalBoundary.C hn) (r := r) hn G
    (by
      let hdomain : G.domain = (OriginalBoundary.G₀ hn).domain :=
        ReferenceBoundary.fact5 hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
          extendedMargin hmarg hext cap hcap
      let hrchart : OriginalBoundary.R hn < G.domain.chartRadius := by
        rw [hdomain]
        exact OriginalBoundary.R_lt_chartRadius hn
      simpa only [U, LocalDomain.chart] using
        (Metric.ball_subset_ball (le_of_lt hrchart)))
    (by dsimp [U]; exact Metric.isBounded_ball)
    (by intro i; simpa [P] using
      ((OriginalBoundary.hD hn).2.2.2.2.1 (parent i).1 (parent i).2).1) T
    (by intro a; exact (hgeom a).2.2.2.1)
    (by intro a; exact (hgeom a).2.2.2.2.1)
    (by
      intro a w hw
      let hh := (hgeom a).2.2.2.2.2.1 hw
      refine ⟨hh.1.1, ?_⟩
      intro j
      let hj := hh.2 j
      change |w.2 j| < 2 * (P a).radius
      change |w.2 j| < 3 * (P a).radius / 2 at hj
      let hp : 0 < (P a).radius := by
        simpa [P] using ((OriginalBoundary.hD hn).2.2.2.2.1 (parent a).1 (parent a).2).1.1
      exact hj.trans_le (by linarith))
    (by
      intro a w hw
      let hh := (hgeom a).2.2.2.2.2.1 hw
      exact (closedBall_subset_ball (OriginalBoundary.b_lt_R hn))
        (interior_subset hh.1.2))
    (by intro a σ hσ; exact (hsource a).2.1 σ hσ)
    (by intro a; exact (hpos a).2.2.2.1)
    (by intro a; exact (hgeom a).2.1.le)
    (by intro a; exact (hgeom a).2.2.2.2.2.2.2.2.1)
    (by intro a; exact (hpos a).2.2.2.2.2.2.2.1)
    (by intro a; exact (hgeom a).2.2.2.2.2.2.2.1)
    (by
      intro a
      apply frameBall_subset_of_stateDomain (T a).data.localReference
      intro q hq
      exact (Metric.ball_subset_ball (OriginalBoundary.b_lt_R hn).le)
        (OriginalBoundary.stateDomain_subset_ball hn (parent a) q hq))
  let hcall' := hcall seed
    (by
      intro a q hq
      let hseedtrans := SeedBoundary.fact2 hn εframe hε qext hq0 hqr k hk0 hkdom p orders
        margin extendedMargin hmarg hext cap hcap
      exact (hseedtrans (parent a) (center a)).2 q hq)
    Rcell V hV hRphysical hflow zRoot θ am width
    (by intro a; exact hapos a)
    (by intro a; exact hwidthpos a)
    hselected
    hrpos
    hcellpos
    (by intro a; exact hrampos a)
    h6U

  hcall'
noncomputable def originalProductSourceCap
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
      { ε : ℝ // 0 < ε }) : ℝ :=
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hbody := Classical.choose_spec h
  let hcapExists := hbody.2.2.2.2.2.2.2
  Classical.choose hcapExists

proof_from originalProductSourceCap_pos
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
      { ε : ℝ // 0 < ε }) :=
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hbody := Classical.choose_spec h
  let hcapExists := hbody.2.2.2.2.2.2.2
  (Classical.choose_spec hcapExists).1

proof_from originalProductSourceCap_le_one
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
      { ε : ℝ // 0 < ε }) :=
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hbody := Classical.choose_spec h
  let hcapExists := hbody.2.2.2.2.2.2.2
  (Classical.choose_spec hcapExists).2.1

noncomputable def originalProductSourceCurrent
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
      { ε : ℝ // 0 < ε }) :=
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hbody := Classical.choose_spec h
  let hcapExists := hbody.2.2.2.2.2.2.2
  let hsource := Classical.choose_spec hcapExists
  Classical.choose hsource.2.2

proof_from originalProductSourceContinuation
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
      { ε : ℝ // 0 < ε }) :=
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let hbody := Classical.choose_spec h
  let hcapExists := hbody.2.2.2.2.2.2.2
  let hsource := Classical.choose_spec hcapExists
  Classical.choose_spec hsource.2.2

theorem exists_original_product_source_prefix
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
      { ε : ℝ // 0 < ε }) :
    let ι := originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
    ∃ χ : ι → CarrierParameter → ℝ,
      ∃ V : ι → Set CarrierParameter,
        (∀ a, ContDiff ℝ ∞ (χ a)) ∧
        (∀ a z, χ a z ∈ Icc (0 : ℝ) 1) ∧
        (∀ a, HasCompactSupport (χ a)) ∧
        (∀ a, IsOpen (V a)) ∧
        (∀ a, tsupport (χ a) ⊆ V a) ∧
        ∃ sourceCap > (0 : ℝ), sourceCap ≤ 1 := by
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
    extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  obtain ⟨χ, hχ, hχrange, hχcompact, hχV, hplateau, hfinite, hangular,
      sourceCap, hsourceCap, hsourceCapOne, -⟩ := h
  let V : (originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) → Set CarrierParameter :=
    fun i ↦ originalProductV hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  exact ⟨χ, V, hχ, hχrange, hχcompact, (by intro a; exact isOpen_ball), hχV,
    sourceCap, hsourceCap, hsourceCapOne⟩

/-- Stable same-witness cache for the actual source-prefix construction. -/
structure OriginalProductSourcePrefixData (ι : Type) where
  χ : ι → CarrierParameter → ℝ
  hχ : ∀ a, ContDiff ℝ ∞ (χ a)
  hχrange : ∀ a z, χ a z ∈ Icc (0 : ℝ) 1
  hχcompact : ∀ a, HasCompactSupport (χ a)
  V : ι → Set CarrierParameter
  hV : ∀ a, IsOpen (V a)
  hχV : ∀ a, tsupport (χ a) ⊆ V a
  sourceCap : ℝ
  hsourceCap : 0 < sourceCap
  hsourceCapOne : sourceCap ≤ 1

/-- Choose the source prefix once; all downstream getters use these identical
witnesses rather than re-running the existential producer. -/
noncomputable def originalProductSourcePrefixData
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
      { ε : ℝ // 0 < ε }) :
    OriginalProductSourcePrefixData
      (originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
        extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) := by
  let h := originalProductSourceFull hn εframe hε qext hq0 hqr k hk0 hkdom p orders
    margin extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra
  let χ := Classical.choose h
  let hbody := Classical.choose_spec h
  let V : (originalReferenceIndex hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin
      extendedMargin hmarg hext cap hcap incidenceCap hinc aExtra) → Set CarrierParameter :=
    fun i ↦ originalProductV hn εframe hε qext hq0 hqr k hk0 hkdom p orders margin extendedMargin
      hmarg hext cap hcap incidenceCap hinc aExtra i
  let hcapExists := hbody.2.2.2.2.2.2.2
  let sourceCap := Classical.choose hcapExists
  let hsource := Classical.choose_spec hcapExists
  exact {
    χ := χ
    hχ := hbody.1
    hχrange := hbody.2.1
    hχcompact := hbody.2.2.1
    V := V
    hV := by intro a; exact isOpen_ball
    hχV := hbody.2.2.2.1
    sourceCap := sourceCap
    hsourceCap := hsource.1
    hsourceCapOne := hsource.2.1
  }

end JanetCartan.PhysicalBackground
