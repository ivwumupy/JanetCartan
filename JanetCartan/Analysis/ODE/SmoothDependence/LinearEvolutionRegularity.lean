module

public import JanetCartan.Analysis.ODE.SmoothDependence.LinearEvolutionRegularity.Volterra
public import JanetCartan.Analysis.ODE.SmoothDependence.LinearEvolutionRegularity.CompactCurrying

/-!
# Regularity of parameterized linear evolution

For `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`, a jointly `Cⁿ` coefficient gives a jointly `Cⁿ`
linear evolution on the entire original time interval. Rescale each segment
from the initial time to the evaluation time onto `[0,1]`, curry the coefficient
into the Banach space of continuous curves, and apply the smooth inverse
Volterra operator. The fundamental theorem of calculus identifies its solution
with the given evolution, without assuming parameter derivatives of that evolution.
-/

@[expose] public section

open Set
open scoped Topology

namespace JanetCartan.ODE.LinearEvolutionRegularity

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedAddCommGroup (OperatorCurve E) := inferInstance
noncomputable local instance : NormedSpace ℝ (OperatorCurve E) := inferInstance

private lemma rescaled_time_mem {a b t₀ t u : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) (hu : u ∈ Icc (0 : ℝ) 1) :
    t₀ + u * (t - t₀) ∈ Ioo a b := by
  rcases le_total t₀ t with h | h
  · have hlo := mul_nonneg hu.1 (sub_nonneg.mpr h)
    have hhi := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h)
    constructor <;> nlinarith [ht₀.1, ht.2]
  · have hlo := mul_nonneg hu.1 (sub_nonneg.mpr h)
    have hhi := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h)
    constructor <;> nlinarith [ht.1, ht₀.2]

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: finite-order joint regularity of a parameterized
linear evolution with identity initial value. A continuous solution of
`∂ₜ J(p,t) = A(p,t) ∘ J(p,t)` inherits the joint `Cⁿ` regularity of `A` on the full
open product domain. Only time differentiability of `J` is assumed; the
parameter space need not be finite dimensional or complete. -/
theorem contDiffOn_linearEvolution (n : ℕ) {s : Set P} (hs : IsOpen s)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {A J : P × ℝ → E →L[ℝ] E}
    (hA : ContDiffOn ℝ n A (s ×ˢ Ioo a b))
    (hJ : ContinuousOn J (s ×ˢ Ioo a b))
    (hinit : ∀ p ∈ s, J (p, t₀) = ContinuousLinearMap.id ℝ E)
    (hd : ∀ p ∈ s, ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ ↦ J (p, τ)) ((A (p, t)).comp (J (p, t))) t) :
    ContDiffOn ℝ n J (s ×ˢ Ioo a b) := by
  let R : (P × ℝ) × ℝ → P × ℝ := fun z ↦
    (z.1.1, t₀ + z.2 * (z.1.2 - t₀))
  have hR : ContDiff ℝ n R :=
    (contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_const.add (contDiff_snd.mul
        ((contDiff_snd.comp contDiff_fst).sub contDiff_const)))
  let U := R ⁻¹' (s ×ˢ Ioo a b)
  have hU : IsOpen U := (hs.prod isOpen_Ioo).preimage hR.continuous
  have hSU : (s ×ˢ Ioo a b) ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    rintro ⟨⟨p, t⟩, u⟩ ⟨⟨hp, ht⟩, hu⟩
    exact ⟨hp, rescaled_time_mem ht₀ ht hu⟩
  let B : (P × ℝ) × ℝ → E →L[ℝ] E := fun z ↦
    (z.1.2 - t₀) • A (R z)
  have hB : ContDiffOn ℝ n B U :=
    ((contDiff_snd.comp contDiff_fst).sub contDiff_const).contDiffOn.smul
      (hA.comp hR.contDiffOn (fun _ hz ↦ hz))
  let C : P × ℝ → OperatorCurve E := fun z ↦
    ContinuousMap.mkD (fun u ↦ B (z, u)) 0
  have hC (z : P × ℝ) (hz : z ∈ s ×ˢ Ioo a b) (u : Icc (0 : ℝ) 1) :
      C z u = B (z, u) := by
    apply ContinuousMap.mkD_apply_of_continuous
    exact hB.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun v ↦ hSU ⟨hz, v.2⟩)
  have hCs : ContDiffOn ℝ n C (s ×ˢ Ioo a b) :=
    contDiffOn_curve_curry n (hs.prod isOpen_Ioo) hU hSU hB hC
  let q : OperatorCurve E := ContinuousMap.const _ (ContinuousLinearMap.id ℝ E)
  let endpoint : Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  let ev : OperatorCurve E →L[ℝ] (E →L[ℝ] E) := ContinuousMap.evalCLM ℝ endpoint
  have hev : ContDiff ℝ n ev := ev.contDiff
  have hsolve :=
    (contDiff_solve (E := E) n).comp_contDiffOn
      (hCs.prodMk (contDiffOn_const (c := q)))
  have hsol := hev.comp_contDiffOn hsolve
  apply hsol.congr
  rintro ⟨p, t⟩ ⟨hp, ht⟩
  change J (p, t) = solve (C (p, t)) q endpoint
  let y : ℝ → E →L[ℝ] E := fun u ↦ J (p, t₀ + u * (t - t₀))
  have hyc : Continuous (fun u : Icc (0 : ℝ) 1 ↦ y u) :=
    hJ.comp_continuous
      (continuous_const.prodMk (continuous_const.add
        (continuous_subtype_val.mul continuous_const)))
      (fun u ↦ ⟨hp, rescaled_time_mem ht₀ ht u.2⟩)
  let Y : OperatorCurve E := ⟨fun u ↦ y u, hyc⟩
  have hyd (u : Icc (0 : ℝ) 1) : HasDerivAt y
      ((C (p, t) u).comp (Y u)) u := by
    have hlin : HasDerivAt (fun v : ℝ ↦ t₀ + v * (t - t₀)) (t - t₀) u := by
      simpa using ((hasDerivAt_id (u : ℝ)).mul_const (t - t₀)).const_add t₀
    have h := (hd p hp _ (rescaled_time_mem ht₀ ht u.2)).scomp (u : ℝ) hlin
    simpa only [hC (p, t) ⟨hp, ht⟩ u, B, R, ContinuousLinearMap.smul_comp,
      Y, y, Function.comp_def, ContinuousMap.coe_mk] using h
  have heq := solve_const_eq_of_hasDerivAt (C (p, t)) Y y (fun _ ↦ rfl) hyd
  have hy0 : y 0 = ContinuousLinearMap.id ℝ E := by simpa [y] using hinit p hp
  rw [hy0] at heq
  have hend := congrArg (fun g : OperatorCurve E ↦ g endpoint) heq
  simpa [q, Y, y, endpoint] using hend.symm

end JanetCartan.ODE.LinearEvolutionRegularity
