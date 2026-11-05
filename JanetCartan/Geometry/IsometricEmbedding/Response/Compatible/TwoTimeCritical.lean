module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.TwoTimeEikonal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation

/-!
# The critical relation of the direct modulated kernel

For `paper-v2.tex`, `app:ch_response:lem:energy-carrier-jets`, use the literal
two-time phase and its actual inverse chart. We identify stationarity in BOTH
source position and covector, and use the root eikonal graph theorem to prove
zero critical value. There is no replacement by the old transverse retarded
phase. The common-root, finite-patch and whole-segment inputs remain explicit;
this is not an existence theorem for the fixed response operator.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- The source/covector phase after removing the SAME primary oscillation.
The parameter of the primary phase is fixed only for notation; no frequency or
sample is chosen (`app:ch_response:lem:energy-carrier-jets`). -/
def elapsedModulatedPhase
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r : ℝ) (φ : Euclidean (d + 1) → ℝ) (x : Euclidean (d + 1))
    (w : Euclidean (d + 1) × Euclidean (d + 1)) : ℝ :=
  elapsedPhase (chartPhase C) r x w.2 - ⟪w.1, w.2⟫_ℝ + φ w.1 - φ x

/-- The full source/covector differential of the actual modulated phase.
Its two components are `dφ(z)-θ` and `∂θΘ-z`
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem hasFDerivAt_elapsedModulatedPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {φ : Euclidean (d + 1) → ℝ} {x z θ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x θ)) (elapsedChartPoint r x θ))
    (hφ : DifferentiableAt ℝ φ z) :
    HasFDerivAt (elapsedModulatedPhase C r φ x)
      (((innerSL ℝ (gradient φ z - θ)).comp
        (ContinuousLinearMap.fst ℝ (Euclidean (d + 1)) (Euclidean (d + 1)))) +
       ((innerSL ℝ (elapsedInputBase C r x θ - z)).comp
        (ContinuousLinearMap.snd ℝ (Euclidean (d + 1)) (Euclidean (d + 1))))) (z, θ) := by
  have hz := (ContinuousLinearMap.fst ℝ (Euclidean (d + 1)) (Euclidean (d + 1))).hasFDerivAt
    (x := (z, θ))
  have hθ := (ContinuousLinearMap.snd ℝ (Euclidean (d + 1)) (Euclidean (d + 1))).hasFDerivAt
    (x := (z, θ))
  have hd := ((((hasFDerivAt_elapsedChartPhase_covector hphase).comp (z, θ) hθ).sub
    (hz.inner ℝ hθ)).add (hφ.hasFDerivAt.comp (z, θ) hz)).sub_const (φ x)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, innerSL_apply_apply,
    inner_sub_left, ← inner_gradient_left]
  change ⟪gradient φ z, v.1⟫_ℝ - ⟪θ, v.1⟫_ℝ +
      (⟪elapsedInputBase C r x θ, v.2⟫_ℝ - ⟪z, v.2⟫_ℝ) =
    ⟪elapsedInputBase C r x θ, v.2⟫_ℝ -
      (⟪z, v.2⟫_ℝ + ⟪v.1, θ⟫_ℝ) + ⟪gradient φ z, v.1⟫_ℝ
  rw [real_inner_comm θ v.1]
  ring

/-- Stationarity is exactly the initial differential graph and the full
source-base equation of the direct elapsed graph, including source time
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem elapsedModulatedPhase_stationary_iff
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {r : ℝ} {φ : Euclidean (d + 1) → ℝ} {x z θ : Euclidean (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x θ)) (elapsedChartPoint r x θ))
    (hφ : DifferentiableAt ℝ φ z) :
    fderiv ℝ (elapsedModulatedPhase C r φ x) (z, θ) = 0 ↔
      θ = gradient φ z ∧ z = elapsedInputBase C r x θ := by
  rw [(hasFDerivAt_elapsedModulatedPhase hphase hφ).fderiv]
  constructor
  · intro hd
    have hz : innerSL ℝ (gradient φ z - θ) = 0 := by
      ext v
      have he := congrArg (fun L : (Euclidean (d + 1) × Euclidean (d + 1)) →L[ℝ] ℝ ↦
        L (v, 0)) hd
      simpa using he
    have hθ : innerSL ℝ (elapsedInputBase C r x θ - z) = 0 := by
      ext v
      have he := congrArg (fun L : (Euclidean (d + 1) × Euclidean (d + 1)) →L[ℝ] ℝ ↦
        L (0, v)) hd
      simpa using he
    have hz' : gradient φ z - θ = 0 := by
      apply (innerSL_inj (𝕜 := ℝ)).mp
      change innerSL ℝ (gradient φ z - θ) = innerSL ℝ (0 : Euclidean (d + 1))
      simpa only [map_zero] using hz
    have hθ' : elapsedInputBase C r x θ - z = 0 := by
      apply (innerSL_inj (𝕜 := ℝ)).mp
      change innerSL ℝ (elapsedInputBase C r x θ - z) = innerSL ℝ (0 : Euclidean (d + 1))
      simpa only [map_zero] using hθ
    exact ⟨(sub_eq_zero.mp hz').symm, (sub_eq_zero.mp hθ').symm⟩
  · rintro ⟨hθ, hz⟩
    rw [sub_eq_zero.mpr hθ.symm, sub_eq_zero.mpr hz.symm]
    simp

/-- The explicit two-time phase equals the pairing with its actual initial
base, at every elapsed time and every temporal energy. This is an identity
of the constructed formula, not an assumed action normalization
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem elapsedChartPhase_eq_input_pairing
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r : ℝ) (x θ : Euclidean (d + 1)) :
    elapsedPhase (chartPhase C) r x θ = ⟪elapsedInputBase C r x θ, θ⟫_ℝ := by
  simp [elapsedPhase, chartPhase, twoTimePhase, elapsedInputBase,
    elapsedChartPoint, inner_eq_time_add_spatial]

/-- At its full source-base equation the remaining modulated phase is the
primary value difference. `elapsedModulatedPhase_critical_value` below proves
that this difference is zero using the actual root evolution
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem elapsedModulatedPhase_eq_primary_difference
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r : ℝ) (φ : Euclidean (d + 1) → ℝ) (x z θ : Euclidean (d + 1))
    (hz : z = elapsedInputBase C r x θ) :
    elapsedModulatedPhase C r φ x (z, θ) = φ z - φ x := by
  simp only [elapsedModulatedPhase, elapsedChartPhase_eq_input_pairing, ← hz,
    sub_self, zero_add]

private theorem zero_root_lift {h : RootState (Euclidean d) → ℝ}
    {z θ : Euclidean (d + 1)} (he : rootSuspension h (z, θ) = 0) :
    rootSuspensionState h 0 (spacetimeRootState (z, θ)) = (z, θ) := by
  have hh : h (spacetimeRootState (z, θ)) = θ 0 := (sub_eq_zero.mp he).symm
  apply Prod.ext
  · exact timeSpacePoint_coordinates z
  · change timeSpacePoint (0 + h (spacetimeRootState (z, θ))) (spatialPart θ) = θ
    rw [zero_add, hh]
    exact timeSpacePoint_coordinates θ

/-- At every critical point of the actual direct modulated kernel, the
outgoing covector is the SAME primary gradient and the critical value is
exactly zero. This instantiates the graph and phase conservation theorem with
the flow and inverse chart occurring in `Θ_r` itself. The whole interval
`uIcc 0 r` is retained, so both orientations are covered.

The smooth root/phase, common-root eikonal equation and common buffers are
primitive inputs, produced respectively by `PencilRoot`, the selected primary
chart and their finite common-domain construction. No graph preservation,
action equality, or zero critical value is assumed. Critical-point existence,
uniqueness and quantitative Hessian gaps are separate obligations of
`app:ch_response:lem:energy-carrier-jets`. -/
theorem elapsedModulatedPhase_critical_value
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {Ω W Y P : Set (Euclidean (d + 1))} {φ : Euclidean (d + 1) → ℝ}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ c : ℝ in 𝓝 1, h (z.1, (z.2.1, c • z.2.2)) = c * h z)
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ φ Ω) (hW : IsOpen W)
    (hY : IsCompact Y) (hP : IsCompact P) (hWY : W ⊆ Y) (hYΩ : Y ⊆ Ω)
    (hprod : MapsTo spacetimeRootState (Y ×ˢ P) D)
    (hgP : MapsTo (gradient φ) W P)
    (he : ∀ x ∈ W, rootSuspension h (x, gradient φ x) = 0)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {r : ℝ} {x z θ : Euclidean (d + 1)} (hz : z ∈ W)
    (hq : elapsedChartPoint r x θ ∈ C.target)
    (hclock : (twoTimeState Φ (C.symm (elapsedChartPoint r x θ))).1 = x 0)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x θ)) (elapsedChartPoint r x θ))
    (hi : Φ (spacetimeRootState (z, θ), 0) = spacetimeRootState (z, θ))
    (hΦ : ∀ u ∈ uIcc 0 r, HasDerivAt (fun v ↦ Φ (spacetimeRootState (z, θ), v))
      (rootHamiltonField h (Φ (spacetimeRootState (z, θ), u))) u)
    (hΦW : ∀ u ∈ uIcc 0 r, (rootSuspensionState h 0 (Φ (spacetimeRootState (z, θ), u))).1 ∈ W)
    (hΦP : ∀ u ∈ uIcc 0 r, (rootSuspensionState h 0 (Φ (spacetimeRootState (z, θ), u))).2 ∈ P)
    (hstationary : fderiv ℝ (elapsedModulatedPhase C r φ x) (z, θ) = 0) :
    FiniteChain.Graph.ForwardRelation (elapsedPhase (chartPhase C) r)
      z θ x (gradient φ x) ∧ elapsedModulatedPhase C r φ x (z, θ) = 0 := by
  obtain ⟨hθ, hbase⟩ := (elapsedModulatedPhase_stationary_iff hphase
    ((hφ.contDiffAt (hΩ.mem_nhds (hYΩ (hWY hz)))).differentiableAt (by simp))).mp hstationary
  have henergy : rootSuspension h (z, θ) = 0 := by rw [hθ]; exact he z hz
  have hstart : rootSuspensionState h 0 (Φ (spacetimeRootState (z, θ), 0)) = (z, θ) := by
    rw [hi]
    exact zero_root_lift henergy
  have hrel := (forwardRelation_elapsedChartPhase_iff hphase).mpr ⟨hbase, rfl⟩
  have hend := (forwardRelation_elapsedChartPhase_flow hC hq hclock hphase hrel).1
  rw [henergy] at hend
  have hp := root_characteristic_preserves_primary_phase hD hh hhom hΩ hφ hW hY hP
    hWY hYΩ hprod hgP he (show 0 ∈ uIcc (0 : ℝ) r from left_mem_uIcc)
    hΦ hΦW hΦP (by simpa only [hstart] using hθ) r right_mem_uIcc
  have hout : elapsedOutputCovector h Φ C r x θ = gradient φ x := by
    simpa only [← hend] using hp.1
  have hvalue : φ x = φ z := by simpa only [← hend, hstart] using hp.2
  refine ⟨(forwardRelation_elapsedChartPhase_iff hphase).mpr ⟨hbase, hout.symm⟩, ?_⟩
  rw [elapsedModulatedPhase_eq_primary_difference C r φ x z θ hbase, hvalue, sub_self]

end JanetCartan.CompatibleResponse
