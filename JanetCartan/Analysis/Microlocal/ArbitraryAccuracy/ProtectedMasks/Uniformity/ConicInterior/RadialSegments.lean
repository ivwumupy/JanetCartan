module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialCharts
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Relations

/-!
# Whole physical segments under radial conjugacy

The radial copy follows exactly the original trajectory with its momentum
scaled. Its physical position and elapsed interval are unchanged, so the
original physical buffer `W` and both physical factor masks are retained.
The root ODE for the conjugated trajectory is a separate analytic obligation.

Consumer: the segment input to the conic zero-energy correction in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization

variable {d : ℕ}

/-- The transported trajectory is the exact dilation of the original
trajectory at every elapsed time (`app:ch_regular:lem:finite-chain`). -/
theorem radialFlow_apply_rootRadialEquiv (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (v : RootState (Euclidean d)) (t : ℝ) :
    radialFlow a ha Φ (rootRadialEquiv a ha v, t) = rootRadialEquiv a ha (Φ (v, t)) := by
  unfold radialFlow
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Radial conjugacy leaves the physical base of every root state unchanged.
Consumer: the original `W` and physical factor masks in
`app:ch_regular:lem:finite-chain`. -/
theorem physicalPencilRootState_radial_fst
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (a : ℝ) (ha : a ≠ 0)
    (v : RootState (Euclidean d)) :
    (physicalPencilRootState e h (rootRadialEquiv a ha v)).1 =
      (physicalPencilRootState e h v).1 := rfl

/-- Transport the ENTIRE closed physical segment to the image root buffers,
with the original elapsed time and physical buffer. The temporal covector is
irrelevant to the segment restriction. Consumer: construction of the radial
family's actual supported relation (`app:ch_regular:lem:finite-chain`). -/
theorem elapsedSegmentCarrier_radial
    {e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)}
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    (a : ℝ) (ha : a ≠ 0)
    {z : Euclidean (d + 1) × Euclidean (d + 1)} {r : ℝ}
    (hz : (z, r) ∈ elapsedSegmentCarrier e h Φ U K W) :
    ((z.1, a • z.2), r) ∈ elapsedSegmentCarrier e h (radialFlow a ha Φ)
      (rootRadialEquiv a ha '' U) (rootRadialEquiv a ha '' K) W := by
  have hs : spacetimeRootState (z.1, a • z.2) =
      rootRadialEquiv a ha (spacetimeRootState z) := rfl
  change spacetimeRootState (z.1, a • z.2) ∈ rootRadialEquiv a ha '' U ∧ _
  rw [hs]
  refine ⟨mem_image_of_mem _ hz.1, ?_⟩
  intro t ht
  rw [radialFlow_apply_rootRadialEquiv]
  exact ⟨mem_image_of_mem _ (hz.2 t ht).1, (hz.2 t ht).2⟩

/-- The original inverse-segment conclusion directly supplies the radial
copy's whole segment, without an extension assumption on the old flow.
Consumer: the primitive root-buffer inputs of the expanded finite family
for `app:ch_regular:thm:no-return`. -/
theorem radialChart_inverse_segment
    (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {K : Set (RootState (Euclidean d))} (q : TwoTimePoint (Euclidean d))
    (hsegment : ∀ t ∈ uIcc q.2.1 q.1,
      twoTimeState Φ (t, (C.symm ((twoTimeRadialEquiv a ha).symm q)).2) ∈ K ∧
        (twoTimeState Φ (t, (C.symm ((twoTimeRadialEquiv a ha).symm q)).2)).1 = t) :
    ∀ t ∈ uIcc q.2.1 q.1,
      twoTimeState (radialFlow a ha Φ) (t, ((radialChart a ha C).symm q).2) ∈
        rootRadialEquiv a ha '' K ∧
      (twoTimeState (radialFlow a ha Φ) (t, ((radialChart a ha C).symm q).2)).1 = t := by
  intro t ht
  have he : twoTimeState (radialFlow a ha Φ) (t, ((radialChart a ha C).symm q).2) =
      rootRadialEquiv a ha (twoTimeState Φ
        (t, (C.symm ((twoTimeRadialEquiv a ha).symm q)).2)) := by
    simp [twoTimeState, radialFlow, ha]
  rw [he]
  exact ⟨mem_image_of_mem _ (hsegment t ht).1, (hsegment t ht).2⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
