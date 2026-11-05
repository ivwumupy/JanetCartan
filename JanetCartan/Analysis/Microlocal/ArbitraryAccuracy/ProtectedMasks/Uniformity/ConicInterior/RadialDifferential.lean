module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialCharts

/-!
# Full phase differential of a radial copy

Root homogeneity transports both time terms as well as the spatial terms.
The root remains the very same function. The only root-domain memberships
are those of the original local initial and final states, supplied by the
inverse-segment conclusions of `UniformGeometry.Construction`.

Consumer: the full elapsed endpoint correction for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:joint-stationary`.
-/

@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic

variable {d : ℕ}

/-- Transport the full local phase differential using the SAME homogeneous
root. The memberships are primitive inverse-segment outputs, not an assumed
conic eikonal equation (`app:ch_regular:eq:joint-stationary`). -/
theorem hasFDerivAt_twoTimePhase_radialChart
    {a : ℝ} (ha : 0 < a)
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {D : Set (RootState (Euclidean d))}
    (hhom : ∀ w ∈ D, ∀ b : ℝ, 0 < b → h (w.1, (w.2.1, b • w.2.2)) = b * h w)
    (q : TwoTimePoint (Euclidean d))
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C ((twoTimeRadialEquiv a ha.ne').symm q))
      ((twoTimeRadialEquiv a ha.ne').symm q))
    (hin : (q.2.1, ((C.symm ((twoTimeRadialEquiv a ha.ne').symm q)).2.2.1,
      a⁻¹ • q.2.2.2)) ∈ D)
    (hout : (q.1, (q.2.2.1,
      (twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha.ne').symm q))).2.2)) ∈ D) :
    HasFDerivAt (twoTimePhase (radialChart a ha.ne' C))
      (twoTimePhaseDifferential h (radialFlow a ha.ne' Φ) (radialChart a ha.ne' C) q) q := by
  have hd := (hphase.comp q (twoTimeRadialEquiv a ha.ne').symm.hasFDerivAt).const_mul a
  dsimp only [Function.comp_def] at hd
  have heq : (fun w ↦ a * twoTimePhase C ((twoTimeRadialEquiv a ha.ne').symm w)) =
      twoTimePhase (radialChart a ha.ne' C) := by
    funext w
    exact (twoTimePhase_radialChart a ha.ne' C w).symm
  rw [heq] at hd
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  have hhi := hhom _ hin a ha
  have hho := hhom _ hout a ha
  dsimp only at hhi hho
  simp only [smul_inv_smul₀ ha.ne'] at hhi
  dsimp only [twoTimePhaseDifferential]
  simp only [twoTimeState_radialFlow_inverse]
  simp only [rootRadialEquiv_apply, hho, radialChart_symm_apply,
    twoTimeRadialEquiv_apply, hhi]
  simp [mul_sub, ha.ne']
  ring

/-- The full inverse-trajectory clock is unchanged by radial conjugacy.
The producer is the original chart's inverse-segment clock in `RootFlow`.
Consumer: the conic zero-energy endpoint correction
(`app:ch_regular:eq:joint-stationary`). -/
theorem radialChart_inverse_clock
    (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d))
    (hclock : (twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha).symm q))).1 = q.1) :
    (twoTimeState (radialFlow a ha Φ) ((radialChart a ha C).symm q)).1 = q.1 := by
  simpa only [twoTimeState_radialFlow_inverse, rootRadialEquiv_apply] using hclock

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
