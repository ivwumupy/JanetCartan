module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialDifferential
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialRefinement
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialSegments
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.FiniteRefinement
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.InverseControls
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.InteriorGap
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.SupportedGaps

/-!
# Radial realization of the conic interior phase

The finite radial menu, chart conjugacy, full differential and segment
transport are proved in the imported leaves. The quantitative correction
below uses those very same charts and the original conic phase.

The full-carrier gap is deduced from the quantitative mask margin for the
actual finite refinement. `MaskAssembly` instantiates that margin from the
original root and flow controls. The original local target is never
identified with the conic radial band.

Consumer: `exists_uniform_nested_localization_data` and the interior part of
`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization

variable {d : ℕ}

/-- The full normalized elapsed conic phase has the germ of the transported
chart phase. Both times are varied, so the elapsed derivative is retained.
The local germ is supplied by `radialChart_elapsedPoint_target_and_germ`
via the coefficient-independent radial menu
(`app:ch_regular:eq:joint-stationary`). -/
theorem jointElapsedPhase_normalized_conic_eventuallyEq_radialChart
    (ℓ : Euclidean d →L[ℝ] ℝ) {a Rf : ℝ} (ha : 0 < a) (hRf : 0 < Rf)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hlocal : ConicPhase.phase ℓ C =ᶠ[𝓝 ((twoTimeRadialEquiv a ha.ne').symm
      (elapsedChartPoint p.1 p.2.1.1 p.2.2.1))] twoTimePhase C) :
    jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase ℓ C)) x y =ᶠ[𝓝 p]
        jointElapsedPhase backward (chartPhase (radialChart a ha.ne' C)) x y := by
  have hn : SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase ℓ C) =
      ConicPhase.curriedPhase ℓ C :=
    ConicPhase.normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) hRf
  rw [hn]
  have he := conicPhase_eventuallyEq_radialChart ℓ ha C
    (elapsedChartPoint p.1 p.2.1.1 p.2.2.1) hlocal
  have hb : SymbolBudgets.jointPhase (ConicPhase.curriedPhase ℓ C) =ᶠ[
      𝓝 (elapsedJointCoordinates p)] SymbolBudgets.jointPhase (chartPhase (radialChart a ha.ne' C)) :=
    he.comp_tendsto (ConicPhase.budgetCoordinates.continuous.tendsto (elapsedJointCoordinates p))
  exact jointElapsedPhase_eventuallyEq_of_twoTimePhase backward (chartPhase (radialChart a ha.ne' C))
    (ConicPhase.curriedPhase ℓ C) x y p hb

/-- The full squared-gradient gap of the transported chart is exactly the
one required for the original normalized conic phase, with no radial loss.
Consumer: the interior part of `app:ch_regular:eq:chain-tail`. -/
theorem phaseGradientSquare_normalized_conic_eq_radialChart
    {κ : Type*} [Fintype κ] (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (ℓ : Euclidean d →L[ℝ] ℝ) {a Rf : ℝ} (ha : 0 < a) (hRf : 0 < Rf)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hlocal : ConicPhase.phase ℓ C =ᶠ[𝓝 ((twoTimeRadialEquiv a ha.ne').symm
      (elapsedChartPoint p.1 p.2.1.1 p.2.2.1))] twoTimePhase C) :
    phaseGradientSquare eI (jointElapsedPhase backward
      (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase ℓ C)) x y) p =
      phaseGradientSquare eI (jointElapsedPhase backward (chartPhase (radialChart a ha.ne' C)) x y) p := by
  have he := jointElapsedPhase_normalized_conic_eventuallyEq_radialChart ℓ ha hRf C backward x y p hlocal
  simp only [phaseGradientSquare, he.fderiv_eq]

/-- Correct the actual conic endpoints to the copied zero-energy relation
with the SAME homogeneous root, elapsed interval, physical `W`, and full
segment restriction. The constant three is independent of coefficients,
radial scale, and orientation. The original chart's differential, inverse
clock and root-domain memberships come from `UniformGeometry.Construction`;
the local germ comes from `RadialRefinement`, and the whole segment transports
by `RadialSegments`. `MaskAssembly` instantiates the compact buffers and mask constructor
for the uniform gap
(`app:ch_regular:eq:joint-stationary`, `app:ch_regular:thm:no-return`). -/
theorem exists_nearby_conic_maskedZeroEnergyRelation_on_radialChart
    (ℓ : Euclidean d →L[ℝ] ℝ) {a Rf : ℝ} (ha : 0 < a) (hRf : 0 < Rf)
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {U K D : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))} {Δ : ℝ}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (hhom : ∀ w ∈ D, ∀ b : ℝ, 0 < b → h (w.1, (w.2.1, b • w.2.2)) = b * h w)
    (backward : Bool) (x y : Euclidean (d + 1)) {r : ℝ} (hr : r ∈ Icc 0 Δ)
    (p : JointVariables (Euclidean (d + 1)))
    (hq : (twoTimeRadialEquiv a ha.ne').symm (elapsedChartPoint r p.1.1 p.2.1) ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha.ne').symm
      (elapsedChartPoint r p.1.1 p.2.1)))).1 = p.1.1 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C
        ((twoTimeRadialEquiv a ha.ne').symm (elapsedChartPoint r p.1.1 p.2.1)))
      ((twoTimeRadialEquiv a ha.ne').symm (elapsedChartPoint r p.1.1 p.2.1)))
    (hin : (p.1.1 0 - r, ((C.symm ((twoTimeRadialEquiv a ha.ne').symm
      (elapsedChartPoint r p.1.1 p.2.1))).2.2.1, a⁻¹ • spatialPart p.2.1)) ∈ D)
    (hout : (p.1.1 0, (spatialPart p.1.1,
      (twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha.ne').symm
        (elapsedChartPoint r p.1.1 p.2.1)))).2.2)) ∈ D)
    (hlocal : ConicPhase.phase ℓ C =ᶠ[𝓝 ((twoTimeRadialEquiv a ha.ne').symm
      (elapsedChartPoint r p.1.1 p.2.1))] twoTimePhase C)
    (hsegment : ((elapsedInputBase (radialChart a ha.ne' C) r p.1.1 p.2.1, p.2.1), r) ∈
      elapsedSegmentCarrier e h (radialFlow a ha.ne' Φ) U K W) :
    ∃ u v, maskedZeroEnergyRelation e h (radialFlow a ha.ne' Φ) U K W
      (fun _ ↦ 1) (fun _ ↦ 1) Δ backward u v ∧
      dist (y, p.2.2.1) u ≤ 3 * ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase ℓ C)) x y) (r, p)‖ ∧
      dist (x, p.2.2.2) v ≤ 3 * ‖fderiv ℝ (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase ℓ C)) x y) (r, p)‖ := by
  have he := jointElapsedPhase_normalized_conic_eventuallyEq_radialChart ℓ ha hRf C backward x y
    (r, p) hlocal
  simp only [he.fderiv_eq]
  exact exists_nearby_maskedZeroEnergyRelation (radialChart_eq_twoTimeProjection a ha.ne' hC)
    backward x y hr p hq
    (radialChart_inverse_clock a ha.ne' Φ C (elapsedChartPoint r p.1.1 p.2.1) hclock)
    (hasFDerivAt_twoTimePhase_radialChart ha hhom (elapsedChartPoint r p.1.1 p.2.1)
      hphase hin hout) hsegment

/-- The full conic radial carrier has a coefficient-independent squared
full-gradient gap. The finite menu and initial cover are the actual output
of `exists_finite_radial_chart_buffers`; the only mask premise is precisely
`exists_uniform_nested_physicalDirectLocalizers`' unit-mask margin for that
expanded family. The original constructor supplies the source identity,
inverse segments, differential, domain and homogeneous root. There is no
local-target assumption on the original radial point.

Both orientations, the entire closed input shoulder, and the full output
complement are retained. The masks may include the elliptic diagonal and
source recutting, as in their producer. This is an independent deduction;
`MaskAssembly` discharges the expanded mask-constructor obligation
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_conic_interior_phaseGradientSquare_gap
    {J κ : Type*} [Fintype κ] {θ : ℝ} (hθ : 0 < θ)
    (eI : Module.Basis κ ℝ (ℝ × JointVariables (Euclidean (d + 1))))
    (n : J → ℕ) (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (z : J → RootState (Euclidean d)) (γ σ R a b : J → ℝ)
    (c : (j : J) → Fin (n j) → ℝ) (hc : ∀ j k, 0 < c j k)
    (U : (j : J) → Fin (n j) → Set (RootState (Euclidean d)))
    (hγ : ∀ j, 0 < γ j) (ha : ∀ j, 0 < a j) (hσR : ∀ j, σ j ≤ R j)
    (hcover : ∀ j η, η ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2 (γ j / 2) (a j) (b j) →
      ∃ k₀ : Fin (n j), (c j k₀)⁻¹ • η ∈ ball (z j).2.2 (γ j) ∧
        ∀ w ∈ closedBall (z j) (σ j), ∃ k : Fin (n j),
          c j k = c j k₀ ∧ rootRadialEquiv (c j k) (hc j k).ne' w ∈ U j k) :
    ∃ δI > 0,
    ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
      (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (C : J → OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
      (D : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1))) (Δ : ℝ),
      (∀ j, (C j : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection (Φ j)) →
      (∀ j, (C j).source = ball ((z j).1, z j) (σ j)) →
      (∀ j, closedBall ((z j).1, z j) (2 * γ j) ⊆ (C j).target) →
      (∀ j, closedBall (z j) (R j) ⊆ D j) →
      (∀ j w, w ∈ closedBall (z j) (R j) → (coordinateSplit (i j)).symm (w.1, w.2.1) ∈ W) →
      (∀ j w, w ∈ D j → ∀ s : ℝ, 0 < s → h j (w.1, (w.2.1, s • w.2.2)) = s * h j w) →
      (∀ j q, q ∈ (C j).target →
        HasFDerivAt (twoTimePhase (C j)) (twoTimePhaseDifferential (h j) (Φ j) (C j) q) q) →
      (∀ j q, q ∈ (C j).target → ∀ t ∈ uIcc q.2.1 q.1,
        twoTimeState (Φ j) (t, ((C j).symm q).2) ∈ closedBall (z j) (R j) ∧
          (twoTimeState (Φ j) (t, ((C j).symm q).2)).1 = t) →
    ∀ (mi mo : LocalizerSymbol (d + 1)),
      (∀ u ∈ cthickening θ (tsupport mi), ∀ v,
        u = v ∨ physicalDirectRelation (fun k : (j : J) × Fin (n j) ↦ i k.1)
          (fun k ↦ h k.1) (fun k ↦ radialFlow (c k.1 k.2) (hc k.1 k.2).ne' (Φ k.1))
          (fun k ↦ U k.1 k.2)
          (fun k ↦ rootRadialEquiv (c k.1 k.2) (hc k.1 k.2).ne' '' closedBall (z k.1) (R k.1))
          W (fun _ _ ↦ 1) (fun _ _ ↦ 1) Δ u v →
            closedBall v θ ⊆ interior {q | mo q = 1}) →
    ∀ (j : J) (backward : Bool) (Rf : ℝ), 0 < Rf →
    ∀ (x y : Euclidean (d + 1)) (r : ℝ) (p : JointVariables (Euclidean (d + 1))),
      r ∈ Icc 0 Δ → r ≤ γ j →
      p.1.1 0 ∈ closedBall (z j).1 (γ j / 2) →
      spatialPart p.1.1 ∈ closedBall (z j).2.1 (γ j / 2) →
      spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (ℓ j) (z j).2.2 (γ j / 2) (a j) (b j) →
      (y, p.2.2.1) ∈ cthickening (θ / 2)
        (tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi)) →
      (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - canonicalProofLocalizer (coordinateSplit (i j)) mo q) →
      δI ≤ phaseGradientSquare eI (jointElapsedPhase backward
        (SymbolBudgets.normalizedTwoTimePhase Rf (ConicPhase.curriedPhase (ℓ j) (C j))) x y) (r, p) := by
  obtain ⟨δI, hδI, hgap⟩ := exists_uniform_interior_phaseGradientSquare_gap
    (J := (j : J) × Fin (n j)) hθ eI
  refine ⟨δI, hδI, ?_⟩
  intro i h Φ C D W Δ hC hsource htarget hRD hphysical hhom hdiff hsegments
    mi mo hbuffer j backward Rf hRf x y r p hr hrγ ht hy hη hin hout
  let q := elapsedChartPoint r p.1.1 p.2.1
  obtain ⟨k₀, hk₀, hchoose⟩ := hcover j _ hη
  have hlocal₀ := radialChart_elapsedPoint_target_and_germ (ℓ j) (hγ j) (ha j) (hc j k₀)
    (htarget j) (hdiff j) ⟨hr.1, hrγ⟩ p.1.1 (spatialPart p.2.1) ht hy hη hk₀
  have hq₀ : (twoTimeRadialEquiv (c j k₀) (hc j k₀).ne').symm q ∈ (C j).target := hlocal₀.1
  have hw₀ := inverse_initial_mem_closedBall (hsource j) hq₀
  obtain ⟨k, hscale, hwk⟩ := hchoose _ hw₀
  have hk : (c j k)⁻¹ • spatialPart p.2.1 ∈ ball (z j).2.2 (γ j) := by
    simpa only [hscale] using hk₀
  have hlocal := radialChart_elapsedPoint_target_and_germ (ℓ j) (hγ j) (ha j) (hc j k)
    (htarget j) (hdiff j) ⟨hr.1, hrγ⟩ p.1.1 (spatialPart p.2.1) ht hy hη hk
  have hq : (twoTimeRadialEquiv (c j k) (hc j k).ne').symm q ∈ (C j).target := hlocal.1
  have hinit : rootRadialEquiv (c j k) (hc j k).ne'
      ((C j).symm ((twoTimeRadialEquiv (c j k) (hc j k).ne').symm q)).2 ∈ U j k := by
    simpa only [rootRadialEquiv_apply, twoTimeRadialEquiv_symm_apply, hscale] using hwk
  have hs := hsegments j _ hq
  have hi := twoTimeChart_inverse_coordinates (hC j) hq
  have htime : (q.1, ((C j).symm ((twoTimeRadialEquiv (c j k) (hc j k).ne').symm q)).2) =
      (C j).symm ((twoTimeRadialEquiv (c j k) (hc j k).ne').symm q) := Prod.ext hi.1.symm rfl
  have hend := hs q.1 right_mem_uIcc
  rw [htime] at hend
  have hstart := inverse_initial_mem_closedBall (hsource j) hq
  have hd := radialChart_differential_of_inverse_controls (hc j k) (hC j) (hhom j) hq
    (hRD j (closedBall_subset_closedBall (hσR j) hstart)) (hRD j hend.1) hend.2 (hdiff j _ hq)
  have hseg := radialChart_elapsedSegmentCarrier_of_inverse_controls (h := h j) (c j k) (hc j k).ne'
    (hC j) hq hinit (fun t ht' ↦ (hs t ht').1) (hphysical j)
  rw [phaseGradientSquare_normalized_conic_eq_radialChart eI (ℓ j) (hc j k) hRf (C j)
    backward x y (r, p) hlocal.2.1]
  exact hgap (fun k ↦ i k.1) (fun k ↦ h k.1)
    (fun k ↦ radialFlow (c k.1 k.2) (hc k.1 k.2).ne' (Φ k.1))
    (fun k ↦ U k.1 k.2)
    (fun k ↦ rootRadialEquiv (c k.1 k.2) (hc k.1 k.2).ne' '' closedBall (z k.1) (R k.1))
    W Δ mi mo hbuffer ⟨j, k⟩ (radialChart (c j k) (hc j k).ne' (C j))
    (radialChart_eq_twoTimeProjection _ _ (hC j)) backward x y r hr p hlocal.1
    hd.1 hd.2 hseg hin hout

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
