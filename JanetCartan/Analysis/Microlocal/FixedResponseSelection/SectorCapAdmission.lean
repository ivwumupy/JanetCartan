module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalReferenceMargins
public import JanetCartan.Geometry.IsometricEmbedding.Response.SectorHistoryAdmission

/-!
# One pre-reference cap and admission for the selected terminal family

Apply the actual sector-history cap before selecting the family. Its later
reference margin is intersected with the original terminal-protection margin.
The same initialized source-dilation map supplies the full Q/B cap, every source
phase margin, and the selected coefficient range. The outer analytic domain is
retained by the deterministic wide source dilation; no reference is reselected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteEvolution
open GeometricProfile ProtectedFlow ProjectedStressFrame

/-- Choose the actual Q/B cap BEFORE the selected family, its coefficient
radius, every original phase margin, and the reference. A single full-array
margin at `max m (sectorLowOrder d)` then admits the SAME later initialized
source-dilation map to terminal protection and all selected history bounds.
The original CarrierData initializer uses its arbitrary finite full/extended
margin continuation with this order and tolerance on the same `D,T` and scale.
No estimate for a separately selected reference is transferred
(`main:prop:current-scale`, `app:ch_regular:thm:no-return`,
`app:ch_response:eq:direct-envelope-profile`, `new:sec:order-of-choices`). -/
theorem exists_terminal_sector_history_admission_on_source_dilation {d : ℕ}
    (ext : BallExtension.Parameters (Euclidean (d+1))) (hext : ext.center = 0)
    {b R : ℝ} (heb : ext.radius ≤ b) (hbR : b < R)
    (m : ℕ) (hm : 6 ≤ m) :
    ∃ M > (0 : ℝ),
      ∀ {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ : ℝ}
        {K : Set (Euclidean (d+1))}
        (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K M),
      ∀ (ι : Type*) (_ : Finite ι) (phaseMargin : ι → ℝ),
      (∀ i, 0 < phaseMargin i) → ∀ ηprotect > (0 : ℝ),
      ∃ η > (0 : ℝ),
      ∀ G₀ Gref : FlatReference (d+1), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Gref.map = sourceDilation G₀.map ρ → R < G₀.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean (d+1)) b) (max m (sectorLowOrder d))
        (geometricReducedCoefficients Gref.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < η →
      (∀ i, cNorm (closedBall (0 : Euclidean (d+1)) b) m
        (fun y ↦ projectedStress Gref.map y i - cubeStress (d+1) i) < ηprotect) ∧
      ∀ rStar kMin : ℕ, 8 ≤ rStar → sectorLowOrder d + 2 ≤ rStar →
      displacementLoss (d+1) +
        bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap Gref.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d+1) ∘
        extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      MapsTo Q univ (closedBall (cubeStress (d+1)) f.coefficientRadius) ∧
      (∀ i, ∀ A : Set (Euclidean (d+1)),
        cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < phaseMargin i) ∧
      ∀ A : Set (Euclidean (d+1)), IsCompact A →
        cNorm A (sectorLowOrder d) Q ≤ M ∧
        cNorm A (sectorLowOrder d) B ≤ M ∧ cNorm A 4 Q ≤ M := by
  obtain ⟨M, hM, hcap⟩ := SectorHistoryAdmission.exists_fixed_sector_history_admission
    ext hext (heb.trans_lt hbR)
  refine ⟨M, hM, ?_⟩
  intro Ω x RQ K f ι hι phaseMargin hphase ηprotect hprotect
  obtain ⟨ηcap, hηcap, hadmit⟩ :=
    hcap f.coefficientRadius f.coefficientRadius_pos ι hι phaseMargin hphase
  obtain ⟨ηrow, hηrow, hrows⟩ :=
    exists_full_coefficient_margin_for_terminal_reference_admission
      (n := d+1) m hm hprotect zero_lt_one
  refine ⟨min ηcap ηrow, lt_min hηcap hηrow, ?_⟩
  intro G₀ Gref ρ hρ hρone hmap hR href
  let Gwide := sourceDilationReference G₀ hρ hρone
  have hsame : Gref.map = Gwide.map := hmap
  have himm : IsImmersionOn Gwide.map (Gwide.domain.chart (d+1)) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun y _ ↦ Gwide.inducedMetric_eq_one y)
  have hball : closedBall (0 : Euclidean (d+1)) b ⊆ Gwide.domain.chart (d+1) :=
    closedBall_subset_ball (hbR.trans hR)
  have hrefwide : cNorm (closedBall (0 : Euclidean (d+1)) b)
      (max m (sectorLowOrder d)) (geometricReducedCoefficients Gwide.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < min ηcap ηrow := by
    simpa only [← hsame] using href
  have hrow := (hrows Gwide.map Gwide.contDiff
    (show IsOpen (Gwide.domain.chart (d+1)) from isOpen_ball) himm Gwide.fullNormalRank
    heb hball ((cNorm_mono_order (le_max_left _ _)).trans_lt
      (hrefwide.trans_le (min_le_right _ _)))).1
  have hsmooth : ∀ y ∈ closedBall (0 : Euclidean (d+1)) b,
      ContDiffAt ℝ (max 6 (sectorLowOrder d))
        (geometricReducedCoefficients Gwide.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) y := by
    intro y hy
    exact (((ContinuumRow.ImageGeometry.contDiffOn_geometricReducedCoefficients
      Gwide.contDiff isOpen_ball himm Gwide.fullNormalRank).contDiffAt
        (isOpen_ball.mem_nhds (hball hy))).sub
          (contDiff_reducedCoefficientBackground contDiff_const).contDiffAt).of_le (by simp)
  have hrefcap : cNorm (closedBall (0 : Euclidean (d+1)) ext.radius)
      (max 6 (sectorLowOrder d)) (geometricReducedCoefficients Gwide.map -
        reducedCoefficientBackground (fun _ _ ↦ 0)) < ηcap :=
    ((cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall heb)
      (isCompact_closedBall _ _) hsmooth).trans
        (cNorm_mono_order (max_le_max hm le_rfl))).trans_lt
      (hrefwide.trans_le (min_le_left _ _))
  refine ⟨by simpa only [← hsame] using hrow, ?_⟩
  intro rStar kMin hStar hreserve horder
  have hh := hadmit Gwide hR hrefcap rStar kMin hStar hreserve horder
  simpa only [← hsame] using hh

end JanetCartan.ResponseTransfer.RetainedFactors
