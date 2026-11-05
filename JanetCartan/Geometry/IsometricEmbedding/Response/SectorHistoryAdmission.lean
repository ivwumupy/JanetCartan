module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SectorHistoryAdmission.ReferenceMargin
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoefficientOrder

/-!
# Common-history sector admission before reference and mask choices

The full Q/B cap is chosen first. After the masks and finite primary tolerances
are fixed, one full-array reference tolerance suffices for the same histories'
coefficient range, all primary C6 margins, and both full low coefficient bounds.
The original initializer's continuation supplies this margin before choosing
its reference scale; this module never chooses a second reference or a scale.

Consumers: the actual paired constructor in `NormalizedRegularSolver` and the
gains and remainders in `FixedDomainInverse.FullSource.HistoryRemainders`.
Sources: `main:prop:current-scale`, `app:ch_seed:setup:seed-current`,
`app:ch_regular:eq:coefficient-extension`, and v2 `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.SectorHistoryAdmission
open GeometricProfile ProtectedFlow ResponseTransfer.RetainedFactors
open RegularSector.FiniteEvolution

/-- Choose the SAME full Q/B cap before the masks' coefficient radius and
all finite primary-phase margins, and before the reference. A single full-array
reference margin then admits every actual history to all these requirements.
The closed measurement balls can be chosen after the history, and the original
displacement reserve and `Scales` are unchanged
(`main:prop:current-scale`, `app:ch_regular:eq:coefficient-extension`).

Apply the ORIGINAL
`ReferenceInitialization.NormalizedHistory.exists_common_normalized_history_reference_with_chart_centers_and_carrier_data_and_comparison_radius_and_position_smoothness`
continuation with `orders = {max 6 (sectorLowOrder d)}`, `margin = fun _ ↦ η`
and any positive extended margin, retaining its already selected `D,T` and its
later SAME `G`. Other finite margins can be joined by a union of orders and
smaller positive margins. The initializer/selector owners retain this final
application. This theorem assumes only that continuation's original full-array
margin, never a current extended-coefficient bound or successful solver.

Set `ε = f.coefficientRadius` for the family selected with this `M`. The C4
cap is retained explicitly for the independently constructed stationary data;
its phase/Hessian radii remain with `FullSourceStationary`. -/
theorem exists_fixed_sector_history_admission {d : ℕ}
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
      ∀ rStar kMin : ℕ, 8 ≤ rStar → sectorLowOrder d + 2 ≤ rStar →
      displacementLoss (d + 1) +
        bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
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
    exists_reference_tolerance_for_history_coefficient_cap ext hextcenter hextR
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
    exists_reference_tolerance_for_retained_history_admission ext hextcenter rfl hε hδ
  obtain ⟨ηarray, hηarray, hframe⟩ :=
    exists_full_array_tolerance_for_reference_frame_components (n := d + 1) 6 hηframe
  refine ⟨min ηlow ηarray, lt_min hηlow hηarray, ?_⟩
  intro G hR href rStar kMin hStar hreserve horder
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
  have h8 : displacementLoss (d + 1) +
      bandExponent * (8 + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin := by
    have hs : (8 : ℝ) ≤ rStar := by exact_mod_cast hStar
    have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by nlinarith) horder
  obtain ⟨Slow, hSlow, hcoeff⟩ := hlow G hR hrefLow rStar kMin hStar hreserve horder
  obtain ⟨Sphase, hSphase, hrange⟩ := hadmit G R ext.radius_pos hextR hR
    (hframe G ext.radius R hextR hR hrefSix) kMin h8
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

end JanetCartan.SectorHistoryAdmission
