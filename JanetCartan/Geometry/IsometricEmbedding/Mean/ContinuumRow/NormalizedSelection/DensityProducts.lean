module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.OriginalDensityGeometry

/-!
# Original density products before incidence selection

The exact retained existence time and full-modulation working cylinder give a
smaller physical radius with the entire original parameter set unchanged.
Every chart on the original coefficient domain has the same uniform forward
bound and original scalar-label range, before any reference or history.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open CanonicalCarrier LeadingPrimitive NormalizedBackground.SourceGeometry
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction

/-- Construct the product geometry needed by the finite measured incidence
selector and the original density carriers. Only the physical radius shrinks;
every zero-position parameter point survives. The characteristic estimate
constructs the forward constant before the map, minor and chart, and the
original full-modulation buffer proves the `L/64` coordinate range. These give
the actual inverse and divided-source inverse ranges in the original `L/16`
ball for every retained chart. No density estimate or inverse bound is assumed.
Consumers: `exists_finite_measured_incidence_row`,
`exists_finite_seed_source_density_carriers_with_normalized_actions`, and
`ActualConstruction.exists_initialScale_for_realized_retained_history_coercivity`
(`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-normalized`,
`app:ch_waves:eq:joint-tame`, `new:sec:order-of-choices`). -/
theorem exists_retained_density_product_geometry
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (zCell : Euclidean 3)
    {L Rc B τ σ τfull rcomp δcomp ε : ℝ}
    (hL : 0 < L) (hRc : 0 < Rc) (hB : 0 ≤ B) (hε : 0 < ε)
    (hτeq : τ = existenceTime Rc (liftedLowBound T B) / 4)
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    (hΩ : IsOpen Ω) (hKc : IsCompact Kc) (hKΩ : Kc ⊆ Ω)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc) Kc)
    (hσ : 0 < σ)
    (hworking : closedBall ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τfull / 2) (τfull / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zCell, T.reference.spatialPatch zCell)) (L / 64)))
    (V : Set CarrierParameter)
    (hgraph : MapsTo (carrierGraph T) (ball (0 : Euclidean n) ε ×ˢ V)
      (ball ((0 : Euclidean n), (zCell, T.reference.spatialPatch zCell)) σ))
    (hcomp : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) ε ×ˢ V)
      (Ioo (-δcomp) δcomp ×ˢ ball ((0 : Euclidean (n - 1)), zCell) rcomp))
    (hrc : 8 * rcomp ≤ Rc / 32) :
    ∃ Mc R : ℝ, 0 < Mc ∧ 0 < R ∧ R ≤ ε ∧ R ≤ L / (64 * Mc) ∧
      (∀ z : CarrierParameter, ((0 : Euclidean n), z) ∈ ball 0 R ×ˢ V ↔
        ((0 : Euclidean n), z) ∈ ball 0 ε ×ˢ V) ∧
      MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
        (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) ∧
      (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V, (densityCoordinates T p).2 ∈
        closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64)) ∧
      (∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
        |(densityCoordinates T p).1| < L / (64 * Mc)) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω Kc ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F),
        cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8))
          1 c.forward ≤ Mc ∧
        MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V) c.D ∧
        MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
          (ball (0 : Euclidean n) R ×ˢ V) Kc ∧
        ContDiffOn ℝ ∞ (densityFootpoint T c.inverse) (ball (0 : Euclidean n) R ×ˢ V) ∧
        MapsTo (densityFootpoint T c.inverse) (ball (0 : Euclidean n) R ×ˢ V)
          (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) ∧
        ∀ s ∈ Ioc (0 : ℝ) 1,
          MapsTo (densityFootpoint T (sourceTransportFlow c.inverse s))
            (ball (0 : Euclidean n) R ×ˢ V)
            (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
  obtain ⟨Mc, hMc, hforward⟩ := exists_retained_chart_forward_bound (N := N)
    hΩ hKc hKΩ hRc hB hτeq hbuffer
  have hτ : 0 < τ := by
    rw [hτeq]
    exact div_pos (existenceTime_pos hRc (liftedLowBound_nonneg T hB)) (by norm_num)
  let R := min ε (min (τ / 2) (L / (64 * Mc)))
  have hR : 0 < R := lt_min hε (lt_min (half_pos hτ) (div_pos hL (by positivity)))
  have hRε : R ≤ ε := min_le_left _ _
  have hRt : R ≤ τ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRL : R ≤ L / (64 * Mc) := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ball (0 : Euclidean n) R ×ˢ V ⊆ ball (0 : Euclidean n) ε ×ˢ V :=
    Set.prod_mono (ball_subset_ball hRε) Subset.rfl
  have htime (p) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :
      |(densityCoordinates T p).1| < R := by
    change |(adaptedCoordinates T.data.adapted p.1).1| < R
    rw [adaptedCoordinates_apply]
    have hh := abs_real_inner_le_norm T.data.adapted.normal p.1
    rw [T.data.adapted.normal_unit, one_mul] at hh
    exact hh.trans_lt (mem_ball_zero_iff.mp hp.1)
  have hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ) := by
    intro p hp
    refine ⟨abs_le.mp ((htime p hp).trans_le hRt).le, ?_⟩
    exact ball_subset_closedBall (ball_subset_ball
      (by linarith : rcomp ≤ Rc / 64) (hcomp (hsub hp)).2)
  have hlabel (p) (hp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :=
    (RetainedRowGeometry.densityCoordinates_mem_original_cylinder T zCell hσ
      hgraph hworking (hsub hp)).2
  refine ⟨Mc, R, hMc, hR, hRε, hRL, ?_, hflow, hlabel,
    (fun p hp ↦ (htime p hp).trans_le hRL), ?_⟩
  · intro z
    simp only [mem_prod, mem_ball_self hR, mem_ball_self hε, true_and]
  · intro F row col c
    have hD := hflow.mono_right ((outputCylinder_spec hRc hτ).2.trans c.small_subset)
    have hsource (s) (hs : s ∈ Ioc (0 : ℝ) 1) :
        MapsTo (densityFootpoint T (sourceTransportFlow c.inverse s))
          (ball (0 : Euclidean n) R ×ˢ V)
          (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)) := by
      intro p hp
      exact RetainedRowGeometry.sourceDensityFootpoint_mem_original_ball_of_forward_cNorm
        T hL hRc hτ hMc c (hforward F row col c) (hflow hp) (hlabel p hp)
        ((htime p hp).trans_le hRL) hs.1 hs.2
    refine ⟨hforward F row col c, hD, ?_,
      c.inverse_smooth.comp (densityCoordinates T).contDiff.contDiffOn hD, ?_, hsource⟩
    · intro p hp
      have hcoords : densityCoordinates T p ∈
          closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc := by
        rw [← closedBall_prod_same]
        refine ⟨?_, closedBall_subset_closedBall (by linarith : Rc / 64 ≤ Rc) (hflow hp).2⟩
        have ht := (existenceTime_le hRc (liftedLowBound_nonneg T hB)).1
        have hτR : τ ≤ Rc / 16 := by rw [hτeq]; linarith
        rw [mem_closedBall, Real.dist_eq, sub_zero]
        exact ((htime p hp).trans_le hRt).le.trans (by linarith)
      have hm := hbuffer hcoords
      change (coordinates (adaptedCoordinates T.data.adapted)).symm
        (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ Kc at hm
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm
    · have hone : sourceTransportFlow c.inverse 1 = c.inverse := by
        funext q
        simp [sourceTransportFlow, transportCoordinateDilation, transportLabelDilation]
      simpa only [hone] using hsource 1
        (show (1 : ℝ) ∈ Ioc 0 1 from ⟨zero_lt_one, le_rfl⟩)

end JanetCartan.ContinuumRow.NormalizedSelection
