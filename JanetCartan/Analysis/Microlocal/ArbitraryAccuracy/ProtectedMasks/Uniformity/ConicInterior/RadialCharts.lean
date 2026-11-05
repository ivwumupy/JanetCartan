module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Differential
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Radial copies of the same characteristic chart

These are literal conjugates of the flow and inverse chart returned by
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry`. They do not run
another ODE construction. A local overlap germ pulls back to a germ of the
original conic phase at the corresponding radial point.

Consumer: the finite radial refinement of the interior relation in
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:joint-stationary`.
The ODE and protected-segment controls for these copies are separate obligations.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic

variable {d : ℕ}

/-- Scale only the spatial covector, retaining time and position.
Consumer: the transported root flow for `app:ch_regular:lem:finite-chain`. -/
def rootRadialEquiv (a : ℝ) (ha : a ≠ 0) :
    RootState (Euclidean d) ≃L[ℝ] RootState (Euclidean d) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.refl ℝ (Euclidean d)).prodCongr
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Euclidean d) (Units.mk0 a ha)))

@[simp] theorem rootRadialEquiv_apply (a : ℝ) (ha : a ≠ 0)
    (w : RootState (Euclidean d)) :
    rootRadialEquiv a ha w = (w.1, (w.2.1, a • w.2.2)) := rfl

@[simp] theorem rootRadialEquiv_symm_apply (a : ℝ) (ha : a ≠ 0)
    (w : RootState (Euclidean d)) :
    (rootRadialEquiv a ha).symm w = (w.1, (w.2.1, a⁻¹ • w.2.2)) := rfl

/-- The same radial change in the two-time projection coordinates.
Consumer: the inverse chart in `app:ch_regular:eq:joint-stationary`. -/
def twoTimeRadialEquiv (a : ℝ) (ha : a ≠ 0) :
    TwoTimePoint (Euclidean d) ≃L[ℝ] TwoTimePoint (Euclidean d) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (rootRadialEquiv a ha)

@[simp] theorem twoTimeRadialEquiv_apply (a : ℝ) (ha : a ≠ 0)
    (q : TwoTimePoint (Euclidean d)) :
    twoTimeRadialEquiv a ha q = (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) := rfl

@[simp] theorem twoTimeRadialEquiv_symm_apply (a : ℝ) (ha : a ≠ 0)
    (q : TwoTimePoint (Euclidean d)) :
    (twoTimeRadialEquiv a ha).symm q = (q.1, (q.2.1, (q.2.2.1, a⁻¹ • q.2.2.2))) := rfl

/-- Conjugate the original flow, keeping its elapsed time unchanged.
The Hamilton ODE for this function must be proved from root homogeneity;
it is not included in the definition (`app:ch_regular:lem:finite-chain`). -/
def radialFlow (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (wt : RootState (Euclidean d) × ℝ) : RootState (Euclidean d) :=
  rootRadialEquiv a ha (Φ ((rootRadialEquiv a ha).symm wt.1, wt.2))

/-- Conjugate both sides of the original partial homeomorphism.
Consumer: radial refinement without changing the actual conic phase
(`app:ch_regular:lem:finite-chain`). -/
def radialChart (a : ℝ) (ha : a ≠ 0)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))) :
    OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)) :=
  ((twoTimeRadialEquiv a ha).symm.toHomeomorph.transOpenPartialHomeomorph C).transHomeomorph
    (twoTimeRadialEquiv a ha).toHomeomorph

@[simp] theorem radialChart_apply (a : ℝ) (ha : a ≠ 0)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d)) :
    radialChart a ha C q = twoTimeRadialEquiv a ha (C ((twoTimeRadialEquiv a ha).symm q)) := rfl

@[simp] theorem radialChart_symm_apply (a : ℝ) (ha : a ≠ 0)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d)) :
    (radialChart a ha C).symm q =
      twoTimeRadialEquiv a ha (C.symm ((twoTimeRadialEquiv a ha).symm q)) := rfl

@[simp] theorem radialChart_source (a : ℝ) (ha : a ≠ 0)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))) :
    (radialChart a ha C).source = (twoTimeRadialEquiv a ha).symm ⁻¹' C.source := rfl

@[simp] theorem radialChart_target (a : ℝ) (ha : a ≠ 0)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))) :
    (radialChart a ha C).target = (twoTimeRadialEquiv a ha).symm ⁻¹' C.target := rfl

/-- The two-time state of a radial copy uses the original elapsed time.
Consumer: transport of whole protected segments in `app:ch_regular:lem:finite-chain`. -/
theorem twoTimeState_radialFlow (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (q : TwoTimePoint (Euclidean d)) :
    twoTimeState (radialFlow a ha Φ) q =
      rootRadialEquiv a ha (twoTimeState Φ ((twoTimeRadialEquiv a ha).symm q)) := rfl

/-- Evaluation through the transported inverse uses the same original
trajectory. Consumer: both time terms of the phase differential and whole
segments in `app:ch_regular:eq:joint-stationary`. -/
theorem twoTimeState_radialFlow_inverse (a : ℝ) (ha : a ≠ 0)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d)) :
    twoTimeState (radialFlow a ha Φ) ((radialChart a ha C).symm q) =
      rootRadialEquiv a ha (twoTimeState Φ (C.symm ((twoTimeRadialEquiv a ha).symm q))) := by
  rw [twoTimeState_radialFlow, radialChart_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The transported chart projects the transported flow exactly, including
outside the restricted chart source. Consumer: the existing local endpoint
correction in `app:ch_regular:eq:joint-stationary`. -/
theorem radialChart_eq_twoTimeProjection (a : ℝ) (ha : a ≠ 0)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ) :
    (radialChart a ha C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) =
      twoTimeProjection (radialFlow a ha Φ) := by
  funext q
  simp [hC, twoTimeProjection, twoTimeState, radialFlow, ha]

/-- The literal inverse-chart phase of the radial copy. This identity is
algebraic and uses no new phase or flow hypothesis
(`app:ch_regular:eq:joint-stationary`). -/
theorem twoTimePhase_radialChart (a : ℝ) (ha : a ≠ 0)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d)) :
    twoTimePhase (radialChart a ha C) q =
      a * twoTimePhase C ((twoTimeRadialEquiv a ha).symm q) := by
  simp [twoTimePhase, inner_smul_right, ha]

/-- Pull the constructor's original local overlap germ to the radial copy.
Only the inverse-dilated point must lie in that overlap. The full radial point
need not belong to the original chart target. Consumer: the full-gradient
interior gap across the fixed radial carrier (`app:ch_regular:eq:chain-tail`). -/
theorem conicPhase_eventuallyEq_radialChart
    (ℓ : Euclidean d →L[ℝ] ℝ) {a : ℝ} (ha : 0 < a)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d))
    (hlocal : ConicPhase.phase ℓ C =ᶠ[𝓝 ((twoTimeRadialEquiv a ha.ne').symm q)]
      twoTimePhase C) :
    ConicPhase.phase ℓ C =ᶠ[𝓝 q] twoTimePhase (radialChart a ha.ne' C) := by
  have he := hlocal.comp_tendsto ((twoTimeRadialEquiv a ha.ne').symm.continuous.tendsto q)
  filter_upwards [he] with w hw
  dsimp only [Function.comp_apply] at hw
  rw [twoTimePhase_radialChart, ← hw]
  have hh := ConicPhase.extend_smul ℓ (twoTimePhase C)
    ((twoTimeRadialEquiv a ha.ne').symm w) ha
  simpa only [ConicPhase.phase, twoTimeRadialEquiv_symm_apply, smul_inv_smul₀ ha.ne', Prod.eta]
    using hh

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
