module

public import JanetCartan.Iteration.PhysicalInitialization.AdmissionCaps
public import JanetCartan.Iteration.PhysicalInitialization.AdmissionRange
public import JanetCartan.Geometry.IsometricEmbedding.Response.SectorHistoryAdmission.ReferenceMargin
public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalReferenceMargins
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoefficientOrder

/-!
# Physical admission on one pre-reference regular-sector cap

The cap precedes the mask family and its coefficient radius. Every later finite
phase tolerance is joined to the original initializer's full-array margin.
Physical band/L2 admissibility then supplies the SAME current Q/full-B to the
actual smooth inverse constructor. The second theorem retains the original wide
chart of the final source dilation without selecting a new reference.

Consumers: `exists_normalized_complete_smooth_fixed_inverse_of_selected_collar`,
`app:ch_regular:thm:exact-correction`, and `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization
open GeometricProfile ProtectedFlow ResponseTransfer.RetainedFactors
open RegularSector.FiniteEvolution RegularSector.FiniteMasks.ActualFamily
open ProjectedStressFrame

/-- The actual Q/full-B cap is fixed before the masks and all phase tolerances.
Every physical history is then admitted using the prescribed reference's
original finite full-array margin, with the literal revised displacement loss. -/
theorem exists_fixed_sector_physical_admission {d : ℕ}
    (ext : BallExtension.Parameters (Euclidean (d + 1)))
    (hextcenter : ext.center = 0) {R : ℝ} (hextR : ext.radius < R) :
    ∃ M > (0 : ℝ), ∀ ε : ℝ, 0 < ε →
      ∀ (ι : Type*) (_ : Finite ι) (phaseMargin : ι → ℝ),
      (∀ i, 0 < phaseMargin i) →
      ∃ η > (0 : ℝ),
      ∀ G : FlatReference (d + 1), R < G.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean (d + 1)) ext.radius)
        (max 6 (sectorLowOrder d))
        (geometricReducedCoefficients G.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      ∀ {Cband : ℝ}, 1 ≤ Cband →
      ∀ rStar kMin : ℕ, 8 ≤ rStar → sectorLowOrder d + 2 ≤ rStar →
      RevisedScales.displacementLoss (d + 1) +
        bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ)
        (u : Fin s → SchwartzMap (Euclidean (d + 1)) (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d + 1) ∘
        extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      MapsTo Q univ (closedBall (cubeStress (d + 1)) ε) ∧
      (∀ i, ∀ K : Set (Euclidean (d + 1)),
        cNorm K 6 (Q - fun _ ↦ cubeStress (d + 1)) < phaseMargin i) ∧
      ∀ K : Set (Euclidean (d + 1)), IsCompact K →
        cNorm K (sectorLowOrder d) Q ≤ M ∧
        cNorm K (sectorLowOrder d) B ≤ M ∧ cNorm K 4 Q ≤ M := by
  classical
  obtain ⟨M, hM, ηlow, hηlow, hlow⟩ :=
    exists_reference_tolerance_for_physical_coefficient_cap ext hextcenter hextR
      (sectorLowOrder d)
  refine ⟨M, hM, ?_⟩
  intro ε hε ι hι phaseMargin hphase
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let margins : Finset ℝ := insert 1 (Finset.univ.image phaseMargin)
  have hne : margins.Nonempty := ⟨1, by simp [margins]⟩
  let δ := margins.min' hne
  have hδ : 0 < δ := by
    apply (Finset.lt_min'_iff margins hne).mpr
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · simp [ht]
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact hphase i
  have hδphase (i : ι) : δ ≤ phaseMargin i :=
    Finset.min'_le margins (phaseMargin i) (by simp [margins])
  obtain ⟨ηframe, hηframe, hadmit⟩ :=
    exists_reference_tolerance_for_physical_frame_admission ext hextcenter rfl hε hδ
  obtain ⟨ηarray, hηarray, hframe⟩ :=
    SectorHistoryAdmission.exists_full_array_tolerance_for_reference_frame_components
      (n := d + 1) 6 hηframe
  refine ⟨min ηlow ηarray, lt_min hηlow hηarray, ?_⟩
  intro G hR href Cband hband rStar kMin hStar hreserve horder
  have hrefLow : cNorm (closedBall (0 : Euclidean (d + 1)) ext.radius)
      (sectorLowOrder d) (geometricReducedCoefficients G.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < ηlow :=
    (cNorm_mono_order (le_max_right _ _)).trans_lt
      (href.trans_le (min_le_left _ _))
  have hrefSix : cNorm (closedBall (0 : Euclidean (d + 1)) ext.radius) 6
      (geometricReducedCoefficients G.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < ηarray :=
    (cNorm_mono_order (le_max_left _ _)).trans_lt
      (href.trans_le (min_le_right _ _))
  obtain ⟨Slow, hSlow, hcoeff⟩ :=
    hlow G hR hrefLow hband rStar kMin hStar hreserve horder
  obtain ⟨Sphase, hSphase, hrange⟩ := hadmit G R ext.radius_pos hextR hR
    (hframe G ext.radius R hextR hR hrefSix) hband rStar kMin hStar horder
  refine ⟨max Slow Sphase, hSlow.trans (le_max_left _ _), ?_⟩
  intro R₀ hR₀ s u ell hu F Q B
  obtain ⟨hQ, hB, hcap⟩ := hcoeff R₀ ((le_max_left _ _).trans hR₀) s u ell hu
  obtain ⟨_, hmap, hsmall⟩ := hrange R₀ ((le_max_right _ _).trans hR₀) s u ell hu
  refine ⟨hQ, hB, hmap, fun i K ↦ (hsmall K).trans_le (hδphase i), ?_⟩
  intro K hK
  obtain ⟨hQcap, hBcap⟩ := hcap K hK
  have hfour : 4 ≤ sectorLowOrder d := by
    have := (sectorLowOrder_bounds d).2.2
    omega
  exact ⟨hQcap, hBcap, (cNorm_mono_order hfour).trans hQcap⟩

/-- `new:sec:order-of-choices`: the fixed cap and supplied mask family admit
physical histories on the SAME final source-dilated reference, measured on its
original wide coefficient ball. The arbitrary finite-margin initializer supplies
`href`; current Q/B success and range are conclusions, not premises. -/
theorem exists_terminal_physical_admission_on_source_dilation {d : ℕ}
    (ext : BallExtension.Parameters (Euclidean (d + 1))) (hext : ext.center = 0)
    {b R : ℝ} (heb : ext.radius ≤ b) (hbR : b < R)
    (m : ℕ) (hm : 6 ≤ m) :
    ∃ M > (0 : ℝ),
      ∀ {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ : ℝ}
        {K : Set (Euclidean (d + 1))}
        (f : ActualMaskFamily Ω x RQ (cubeStress (d + 1)) K M),
      ∀ (ι : Type*) (_ : Finite ι) (phaseMargin : ι → ℝ),
      (∀ i, 0 < phaseMargin i) → ∀ ηprotect > (0 : ℝ),
      ∃ η > (0 : ℝ),
      ∀ G₀ Gref : FlatReference (d + 1), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Gref.map = sourceDilation G₀.map ρ → R < G₀.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean (d + 1)) b) (max m (sectorLowOrder d))
        (geometricReducedCoefficients Gref.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      (∀ i, cNorm (closedBall (0 : Euclidean (d + 1)) b) m
        (fun y ↦ projectedStress Gref.map y i - cubeStress (d + 1) i) < ηprotect) ∧
      ∀ {Cband : ℝ}, 1 ≤ Cband →
      ∀ rStar kMin : ℕ, 8 ≤ rStar → sectorLowOrder d + 2 ≤ rStar →
      RevisedScales.displacementLoss (d + 1) +
        bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ)
        (u : Fin s → SchwartzMap (Euclidean (d + 1)) (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap Gref.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d + 1) ∘
        extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      MapsTo Q univ (closedBall (cubeStress (d + 1)) f.coefficientRadius) ∧
      (∀ i, ∀ K : Set (Euclidean (d + 1)),
        cNorm K 6 (Q - fun _ ↦ cubeStress (d + 1)) < phaseMargin i) ∧
      ∀ K : Set (Euclidean (d + 1)), IsCompact K →
        cNorm K (sectorLowOrder d) Q ≤ M ∧
        cNorm K (sectorLowOrder d) B ≤ M ∧ cNorm K 4 Q ≤ M := by
  obtain ⟨M, hM, hcap⟩ := exists_fixed_sector_physical_admission
    ext hext (heb.trans_lt hbR)
  refine ⟨M, hM, ?_⟩
  intro Ω x RQ K f ι hι phaseMargin hphase ηprotect hprotect
  obtain ⟨ηcap, hηcap, hadmit⟩ :=
    hcap f.coefficientRadius f.coefficientRadius_pos ι hι phaseMargin hphase
  obtain ⟨ηrow, hηrow, hrows⟩ :=
    exists_full_coefficient_margin_for_terminal_reference_admission
      (n := d + 1) m hm hprotect zero_lt_one
  refine ⟨min ηcap ηrow, lt_min hηcap hηrow, ?_⟩
  intro G₀ Gref ρ hρ hρone hmap hR href
  let Gwide := sourceDilationReference G₀ hρ hρone
  have hsame : Gref.map = Gwide.map := hmap
  have himm : IsImmersionOn Gwide.map (Gwide.domain.chart (d + 1)) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun y _ ↦ Gwide.inducedMetric_eq_one y)
  have hball : closedBall (0 : Euclidean (d + 1)) b ⊆ Gwide.domain.chart (d + 1) :=
    closedBall_subset_ball (hbR.trans hR)
  have hrefwide : cNorm (closedBall (0 : Euclidean (d + 1)) b)
      (max m (sectorLowOrder d)) (geometricReducedCoefficients Gwide.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < min ηcap ηrow := by
    simpa only [← hsame] using href
  have hrow := (hrows Gwide.map Gwide.contDiff
    (show IsOpen (Gwide.domain.chart (d + 1)) from isOpen_ball) himm Gwide.fullNormalRank
    heb hball ((cNorm_mono_order (le_max_left _ _)).trans_lt
      (hrefwide.trans_le (min_le_right _ _)))).1
  have hsmooth : ∀ y ∈ closedBall (0 : Euclidean (d + 1)) b,
      ContDiffAt ℝ (max 6 (sectorLowOrder d))
        (geometricReducedCoefficients Gwide.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) y := by
    intro y hy
    exact (((ContinuumRow.ImageGeometry.contDiffOn_geometricReducedCoefficients
      Gwide.contDiff isOpen_ball himm Gwide.fullNormalRank).contDiffAt
        (isOpen_ball.mem_nhds (hball hy))).sub
          (contDiff_reducedCoefficientBackground contDiff_const).contDiffAt).of_le (by simp)
  have hrefcap : cNorm (closedBall (0 : Euclidean (d + 1)) ext.radius)
      (max 6 (sectorLowOrder d)) (geometricReducedCoefficients Gwide.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < ηcap :=
    ((cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall heb)
      (isCompact_closedBall _ _) hsmooth).trans
        (cNorm_mono_order (max_le_max hm le_rfl))).trans_lt
      (hrefwide.trans_le (min_le_left _ _))
  refine ⟨by simpa only [← hsame] using hrow, ?_⟩
  intro Cband hband rStar kMin hStar hreserve horder
  have hh := hadmit Gwide hR hrefcap hband rStar kMin hStar hreserve horder
  simpa only [← hsame] using hh

end JanetCartan.PhysicalInitialization
