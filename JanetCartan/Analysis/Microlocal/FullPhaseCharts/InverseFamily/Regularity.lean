module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.JacobianBounds
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Gluing the parameter-dependent phase inverses

The local uniqueness argument in `app:ch_seed:prop:seed-phase-charts`.
The inverse is chosen fiberwise on the open data domain; no regularity of
that choice is assumed. The implicit function theorem proves its joint
smoothness on an open parameter neighborhood, including epsilon endpoints.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FullPhaseCharts

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Fiberwise choice of the inverse used in `app:ch_seed:prop:seed-phase-charts`.
Values outside the image are irrelevant; regularity is proved below. -/
def phaseChartInverse (f : P → E → E) (D : Set E) (p : P) (v : E) : E :=
  Function.invFunOn (f p) D v

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The right inverse and image containment from the common image condition
in `app:ch_seed:prop:seed-phase-charts`. -/
theorem phaseChartInverse_spec {f : P → E → E} {D : Set E} {p : P} {v : E}
    (hv : v ∈ f p '' D) :
    phaseChartInverse f D p v ∈ D ∧ f p (phaseChartInverse f D p v) = v :=
  Function.invFunOn_pos hv

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Global injectivity identifies every inverse choice on the data chart
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem phaseChartInverse_apply {f : P → E → E} {D : Set E} {p : P}
    (hi : InjOn (f p) D) {u : E} (hu : u ∈ D) :
    phaseChartInverse f D p (f p u) = u :=
  hi.leftInvOn_invFunOn hu

/-- The chosen common inverse is jointly smooth in every parameter. The only
inputs are smoothness of the forward map, injectivity, common image containment,
and invertible data derivatives. All four are provided by the quotient and gap
deductions for `app:ch_seed:prop:seed-phase-charts`. -/
theorem contDiffOn_phaseChartInverse {f : P → E → E} {U : Set P} {D V : Set E}
    (hU : IsOpen U) (hD : IsOpen D) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    (hi : ∀ p ∈ U, InjOn (f p) D)
    (himage : ∀ p ∈ U, V ⊆ f p '' D)
    (hj : ∀ p ∈ U, ∀ u ∈ D, Function.Bijective (fderiv ℝ (f p) u)) :
    ContDiffOn ℝ ∞ (Function.uncurry (phaseChartInverse f D)) (U ×ˢ V) := by
  intro q hq
  let u := phaseChartInverse f D q.1 q.2
  obtain ⟨hu, he⟩ := phaseChartInverse_spec (himage q.1 hq.1 hq.2)
  let H : (P × E) × E → E := fun a ↦ f a.1.1 a.2 - a.1.2
  have hforward := hf.contDiffAt (x := (q.1, u)) ((hU.prod hD).mem_nhds ⟨hq.1, hu⟩)
  have hH : ContDiffAt ℝ ∞ H (q, u) :=
    (hforward.comp (q, u) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub
      contDiffAt_fst.snd
  have hd : fderiv ℝ H (q, u) ∘L ContinuousLinearMap.inr ℝ (P × E) E =
      fderiv ℝ (f q.1) u := by
    have h := ((hH.differentiableAt (by simp)).hasFDerivAt.comp u
      (hasFDerivAt_prodMk_right q u)).fderiv
    simpa [H, Function.comp_def, fderiv_sub_const] using h.symm
  have hinvert : (fderiv ℝ H (q, u) ∘L
      ContinuousLinearMap.inr ℝ (P × E) E).IsInvertible := by
    rw [hd]
    let e := (LinearEquiv.ofBijective (fderiv ℝ (f q.1) u).toLinearMap
      (hj q.1 hq.1 u hu)).toContinuousLinearEquiv
    exact ⟨e, rfl⟩
  let g := hH.implicitFunction (by simp) hinvert
  have hg : ContDiffAt ℝ ∞ g q := hH.contDiffAt_implicitFunction (by simp) hinvert
  have hgu : g q = u := hH.implicitFunction_apply_self (by simp) hinvert
  have hmem : ∀ᶠ a in 𝓝 q, g a ∈ D :=
    hg.continuousAt (hD.mem_nhds (hgu.symm ▸ hu))
  have hagree : (Function.uncurry (phaseChartInverse f D)) =ᶠ[𝓝 q] g := by
    filter_upwards [hmem, hH.eventually_apply_implicitFunction (by simp) hinvert,
      (hU.prod hV).mem_nhds hq] with a ha heq haU
    have hzero : H (q, u) = 0 := sub_eq_zero.mpr he
    have he' : f a.1 (g a) = a.2 := sub_eq_zero.mp (heq.trans hzero)
    change phaseChartInverse f D a.1 a.2 = g a
    rw [← he']
    exact phaseChartInverse_apply (hi a.1 haU.1) ha
  exact (hg.congr_of_eventuallyEq hagree).contDiffWithinAt

end JanetCartan.FullPhaseCharts
