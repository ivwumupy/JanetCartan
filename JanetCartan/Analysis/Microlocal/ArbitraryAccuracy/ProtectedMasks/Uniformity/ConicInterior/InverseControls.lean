module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialDifferential
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialSegments

/-!
# Inverse states and whole segments in the radial buffers

These deductions use the source identity and inverse-segment conclusions of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`. No containment of
the unscaled radial band in the original target is assumed.
Consumer: the conic interior gap in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic EvolutionIntegratedLocalization

variable {d : ℕ}

/-- The actual inverse initial state is in the original closed source buffer.
This closes the initial-state input to the finite radial buffer cover
(`app:ch_regular:lem:finite-chain`). -/
theorem inverse_initial_mem_closedBall
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {z : RootState (Euclidean d)} {σ : ℝ}
    (hsource : C.source = ball (z.1, z) σ)
    {q : TwoTimePoint (Euclidean d)} (hq : q ∈ C.target) :
    (C.symm q).2 ∈ closedBall z σ := by
  have hs := C.map_target hq
  rw [hsource, mem_ball, Prod.dist_eq, max_lt_iff] at hs
  exact hs.2.le

/-- Derive the copied phase differential and clock from the original inverse
coordinates and whole-segment bounds. All root evaluations stay in the
original domain; homogeneity is the constructor's global root identity
(`app:ch_regular:eq:joint-stationary`). -/
theorem radialChart_differential_of_inverse_controls
    {a : ℝ} (ha : 0 < a)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {D : Set (RootState (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (hhom : ∀ w ∈ D, ∀ b : ℝ, 0 < b → h (w.1, (w.2.1, b • w.2.2)) = b * h w)
    {q : TwoTimePoint (Euclidean d)}
    (hq : (twoTimeRadialEquiv a ha.ne').symm q ∈ C.target)
    (hin : (C.symm ((twoTimeRadialEquiv a ha.ne').symm q)).2 ∈ D)
    (hout : twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha.ne').symm q)) ∈ D)
    (hclock : (twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha.ne').symm q))).1 = q.1)
    (hdiff : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C ((twoTimeRadialEquiv a ha.ne').symm q))
      ((twoTimeRadialEquiv a ha.ne').symm q)) :
    (twoTimeState (radialFlow a ha.ne' Φ) ((radialChart a ha.ne' C).symm q)).1 = q.1 ∧
    HasFDerivAt (twoTimePhase (radialChart a ha.ne' C))
      (twoTimePhaseDifferential h (radialFlow a ha.ne' Φ) (radialChart a ha.ne' C) q) q := by
  have hi := twoTimeChart_inverse_coordinates hC hq
  refine ⟨radialChart_inverse_clock a ha.ne' Φ C q hclock,
    hasFDerivAt_twoTimePhase_radialChart ha hhom q hdiff ?_ ?_⟩
  · convert hin using 1
    exact Prod.ext hi.2.1.symm (Prod.ext rfl hi.2.2.1.symm)
  · convert hout using 1
    exact Prod.ext hclock.symm (Prod.ext hi.2.2.2.symm rfl)

/-- Selecting one compact initial piece preserves the entire original
physical segment, its elapsed interval and physical buffer. `hinitial` is
supplied by `exists_finite_radial_chart_buffers` and the preceding source
bound. `hsegment` and `hphysical` are the original constructor's inverse
segment and physical closed-ball controls
(`app:ch_regular:thm:no-return`). -/
theorem radialChart_elapsedSegmentCarrier_of_inverse_controls
    (a : ℝ) (ha : a ≠ 0)
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {x ξ : Euclidean (d + 1)}
    (hq : (twoTimeRadialEquiv a ha).symm (elapsedChartPoint r x ξ) ∈ C.target)
    (hinitial : rootRadialEquiv a ha
      (C.symm ((twoTimeRadialEquiv a ha).symm (elapsedChartPoint r x ξ))).2 ∈ U)
    (hsegment : ∀ t ∈ uIcc (x 0 - r) (x 0),
      twoTimeState Φ (t, (C.symm ((twoTimeRadialEquiv a ha).symm
        (elapsedChartPoint r x ξ))).2) ∈ K)
    (hphysical : ∀ w ∈ K, e.symm (w.1, w.2.1) ∈ W) :
    ((elapsedInputBase (radialChart a ha C) r x ξ, ξ), r) ∈
      elapsedSegmentCarrier e h (radialFlow a ha Φ) U (rootRadialEquiv a ha '' K) W := by
  have hq' : elapsedChartPoint r x ξ ∈ (radialChart a ha C).target := hq
  have hi := twoTimeChart_inverse_coordinates (radialChart_eq_twoTimeProjection a ha hC) hq'
  have hstate : spacetimeRootState (elapsedInputBase (radialChart a ha C) r x ξ, ξ) =
      ((radialChart a ha C).symm (elapsedChartPoint r x ξ)).2 := by
    apply Prod.ext
    · simpa [spacetimeRootState, elapsedInputBase, elapsedChartPoint] using hi.2.1.symm
    · apply Prod.ext
      · simp [spacetimeRootState, elapsedInputBase]
      · exact hi.2.2.1.symm
  change spacetimeRootState _ ∈ U ∧ _
  rw [hstate]
  refine ⟨hinitial, ?_⟩
  intro t ht
  have ht' : x 0 - r + t ∈ uIcc (x 0 - r) (x 0) :=
    Icc_subset_uIcc ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hi₀ := twoTimeChart_inverse_coordinates hC hq
  have he : radialFlow a ha Φ
      (((radialChart a ha C).symm (elapsedChartPoint r x ξ)).2, t) =
      rootRadialEquiv a ha (twoTimeState Φ
        (x 0 - r + t, (C.symm ((twoTimeRadialEquiv a ha).symm
          (elapsedChartPoint r x ξ))).2)) := by
    simp only [radialChart_symm_apply, twoTimeRadialEquiv_apply,
      ← rootRadialEquiv_apply a ha, radialFlow_apply_rootRadialEquiv, twoTimeState]
    rw [hi₀.2.1]
    congr 3
    change t = x 0 - r + t - (x 0 - r)
    ring
  rw [he]
  have hp := hphysical _ (hsegment _ ht')
  exact ⟨mem_image_of_mem _ (hsegment _ ht'), hp⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
