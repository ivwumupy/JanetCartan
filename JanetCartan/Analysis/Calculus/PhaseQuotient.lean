module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.ProjIcc

/-!
# Exact phase differences and their integral quotients

The segment identities in `app:ch_regular_base:eq:averaged-gradient` and
`app:ch_seed:eq:seed-quotient-integral` of paper.tex. The arbitrary parameter type `P`
retains all spectator variables (physical points, coefficients, and data labels).
The differentiated variable belongs to a real Hilbert space; in particular these
results apply to the manuscript's Euclidean spaces without changing their norms.

These are calculus identities conditional on phase regularity on the indicated
charts. They do not construct Hamilton phases or prove inverse-chart estimates.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan

variable {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `app:ch_regular_base:eq:averaged-gradient`: average the partial gradient on the
segment from `y` to `x`, keeping every spectator parameter fixed. -/
def averagedPhaseGradient (S : P → E → ℝ) (p : P) (x y : E) : E :=
  ∫ t : ℝ in 0..1, gradient (S p) (y + t • (x - y))

/-- `app:ch_seed:eq:seed-quotient-integral`: the integral extension of the parameter
shift quotient, defined also at `h = 0`. Here `z` may itself depend on spectators. -/
def phaseShiftQuotient (S : P → E → ℝ) (p : P) (z v : E) (h : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, inner ℝ (gradient (S p) (z + (t * h) • v)) v

/-- C¹ regularity on an open chart gives the continuous partial gradient needed in
`app:ch_regular_base:eq:averaged-gradient`. -/
theorem continuousOn_gradient_of_contDiffOn {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (gradient f) U :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl)

/-- `app:ch_regular_base:eq:averaged-gradient`: the averaged gradient gives the
exact two-point phase difference on an open convex C¹ chart. -/
theorem phase_sub_eq_inner_averagedPhaseGradient {S : P → E → ℝ} {p : P}
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hS : ContDiffOn ℝ 1 (S p) U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    S p x - S p y = inner ℝ (averagedPhaseGradient S p x y) (x - y) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : y + t • (x - y) ∈ U :=
    hconv.add_smul_sub_mem hy hx ht
  have hgrad : ContinuousOn (fun t : ℝ ↦ gradient (S p) (y + t • (x - y)))
      (Icc 0 1) :=
    (continuousOn_gradient_of_contDiffOn hU hS).comp
      (by fun_prop) hmem
  have hint := hgrad.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ S p (y + t • (x - y)))
        (inner ℝ (gradient (S p) (y + t • (x - y))) (x - y)) t := by
    have hm := hmem t (by simpa using ht)
    have hf := ((hS _ hm).contDiffAt (hU.mem_nhds hm)).differentiableAt one_ne_zero
    convert hf.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (x - y)).const_add y) using 1 <;>
      simp only [Function.comp_def, id_eq, inner_gradient_left, one_smul]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hgrad.inner continuousOn_const).intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  have hlin := (innerSL ℝ (x - y)).intervalIntegral_comp_comm hint
  simp_rw [innerSL_apply_apply, real_inner_comm _ (x - y)] at hlin
  simpa only [averagedPhaseGradient, zero_smul, one_smul, add_zero, add_sub_cancel]
    using hFTC.symm.trans hlin

/-- The diagonal value in `app:ch_regular_base:eq:averaged-gradient`. -/
@[simp] theorem averagedPhaseGradient_self (S : P → E → ℝ) (p : P) (x : E) :
    averagedPhaseGradient S p x x = gradient (S p) x := by
  simp [averagedPhaseGradient]

/-- `app:ch_seed:eq:seed-quotient-integral` written using the averaged gradient. -/
theorem phaseShiftQuotient_eq_inner_averagedPhaseGradient {S : P → E → ℝ} {p : P}
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hS : ContDiffOn ℝ 1 (S p) U) {z v : E} {h : ℝ}
    (hz : z ∈ U) (hshift : z + h • v ∈ U) :
    phaseShiftQuotient S p z v h =
      inner ℝ (averagedPhaseGradient S p (z + h • v) z) v := by
  have hgrad : ContinuousOn (fun t : ℝ ↦ gradient (S p) (z + t • ((z + h • v) - z)))
      (Icc 0 1) :=
    (continuousOn_gradient_of_contDiffOn hU hS).comp (by fun_prop)
      (fun _ ht ↦ hconv.add_smul_sub_mem hz hshift ht)
  have hlin := (innerSL ℝ v).intervalIntegral_comp_comm
    (hgrad.intervalIntegrable_of_Icc (μ := volume) zero_le_one)
  simpa only [phaseShiftQuotient, averagedPhaseGradient, add_sub_cancel_left,
    smul_smul, innerSL_apply_apply, real_inner_comm] using hlin

/-- The exact parameter-shift identity, including `h = 0`, from
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem phase_shift_sub_eq_mul_quotient {S : P → E → ℝ} {p : P}
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hS : ContDiffOn ℝ 1 (S p) U) {z v : E} {h : ℝ}
    (hz : z ∈ U) (hshift : z + h • v ∈ U) :
    S p (z + h • v) - S p z = h * phaseShiftQuotient S p z v h := by
  rw [phase_sub_eq_inner_averagedPhaseGradient hU hconv hS hshift hz,
    phaseShiftQuotient_eq_inner_averagedPhaseGradient hU hconv hS hz hshift]
  simp [inner_smul_right]

/-- `app:ch_seed:eq:seed-exact-phase-quotient` agrees with its integral extension
`app:ch_seed:eq:seed-quotient-integral` for every nonzero shift of either sign. -/
theorem phase_div_eq_phaseShiftQuotient {S : P → E → ℝ} {p : P}
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hS : ContDiffOn ℝ 1 (S p) U) {z v : E} {h : ℝ}
    (hz : z ∈ U) (hshift : z + h • v ∈ U) (hh : h ≠ 0) :
    (S p (z + h • v) - S p z) / h = phaseShiftQuotient S p z v h := by
  rw [phase_shift_sub_eq_mul_quotient hU hconv hS hz hshift]
  exact mul_div_cancel_left₀ _ hh

/-- The value at zero in `app:ch_seed:eq:seed-quotient-integral`. -/
@[simp] theorem phaseShiftQuotient_zero (S : P → E → ℝ) (p : P) (z v : E) :
    phaseShiftQuotient S p z v 0 = inner ℝ (gradient (S p) z) v := by
  simp [phaseShiftQuotient]

section NormedParameters

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [CompleteSpace E] in
/-- Restrict the joint C¹ phase to a fixed spectator, as used in
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem contDiffOn_phase_slice {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hS : ContDiffOn ℝ 1 (Function.uncurry S) (V ×ˢ U)) {p : P} (hp : p ∈ V) :
    ContDiffOn ℝ 1 (S p) U := by
  exact hS.comp (f := fun x : E ↦ (p, x))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨hp, hx⟩)

/-- Joint C¹ regularity on open charts supplies the joint partial-gradient
continuity used in `app:ch_regular_base:eq:averaged-gradient` and
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem continuousOn_phaseGradient_of_contDiffOn {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hV : IsOpen V) (hU : IsOpen U)
    (hS : ContDiffOn ℝ 1 (Function.uncurry S) (V ×ˢ U)) :
    ContinuousOn (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U) := by
  have hfd : ContinuousOn
      (fun q : P × E ↦ (fderiv ℝ (Function.uncurry S) q).comp
        (ContinuousLinearMap.inr ℝ P E)) (V ×ˢ U) :=
    (hS.continuousOn_fderiv_of_isOpen (hV.prod hU) le_rfl).clm_comp continuousOn_const
  have hgrad := (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn hfd
  apply hgrad.congr
  intro q hq
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (S q.1) q.2) = _
  congr 1
  have htotal := ((hS q hq).contDiffAt ((hV.prod hU).mem_nhds hq)).differentiableAt
    one_ne_zero
  have hpair : HasFDerivAt (fun x : E ↦ (q.1, x)) (ContinuousLinearMap.inr ℝ P E) q.2 := by
    convert (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2) using 1 <;>
      ext v <;> simp
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using (htotal.hasFDerivAt.comp q.2 hpair).fderiv

end NormedParameters

private theorem continuousOn_unitIntervalIntegral
    {A F : Type*} [TopologicalSpace A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → ℝ → F} {s : Set A}
    (hf : ContinuousOn (Function.uncurry f) (s ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun a ↦ ∫ t : ℝ in 0..1, f a t) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  let g (a : s) (t : ℝ) := f a (projIcc 0 1 zero_le_one t)
  have hg : Continuous (Function.uncurry g) := by
    exact hf.comp_continuous (f := fun q : s × ℝ ↦
      ((q.1 : A), (projIcc 0 1 zero_le_one q.2 : ℝ))) (by fun_prop)
      (fun q ↦ ⟨q.1.property, (projIcc 0 1 zero_le_one q.2).property⟩)

  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hg 0 1
  apply hi.congr
  intro a
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp [g]
  rw [projIcc_of_mem zero_le_one (by simpa using ht)]

section TopologicalParameters

variable [TopologicalSpace P]

/-- Joint continuity in the endpoints and every spectator, on the convex chart of
`app:ch_regular_base:eq:averaged-gradient`. Only joint continuity of the partial
gradient is required; no differentiability in the spectator type is assumed. -/
theorem continuousOn_averagedPhaseGradient {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hconv : Convex ℝ U)
    (hG : ContinuousOn (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U)) :
    ContinuousOn (fun q : P × E × E ↦ averagedPhaseGradient S q.1 q.2.1 q.2.2)
      (V ×ˢ U ×ˢ U) := by
  apply continuousOn_unitIntervalIntegral
  exact hG.comp (f := fun q : (P × E × E) × ℝ ↦
    (q.1.1, q.1.2.2 + q.2 • (q.1.2.1 - q.1.2.2))) (by fun_prop)
    (fun q hq ↦ ⟨hq.1.1, hconv.add_smul_sub_mem hq.1.2.2 hq.1.2.1 hq.2⟩)

/-- The diagonal limit of `app:ch_regular_base:eq:averaged-gradient`, allowing both
endpoints and all spectators to vary along an arbitrary filter. -/
theorem tendsto_averagedPhaseGradient_diagonal
    {S : P → E → ℝ} {V : Set P} {U : Set E} (hconv : Convex ℝ U)
    (hG : ContinuousOn (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U))
    {A : Type*} {l : Filter A} {p : A → P} {x y : A → E} {p₀ : P} {x₀ : E}
    (hp₀ : p₀ ∈ V) (hx₀ : x₀ ∈ U)
    (hp : Tendsto p l (𝓝 p₀)) (hx : Tendsto x l (𝓝 x₀))
    (hy : Tendsto y l (𝓝 x₀))
    (hmem : ∀ᶠ a in l, p a ∈ V ∧ x a ∈ U ∧ y a ∈ U) :
    Tendsto (fun a ↦ averagedPhaseGradient S (p a) (x a) (y a)) l
      (𝓝 (gradient (S p₀) x₀)) := by
  have hc := continuousOn_averagedPhaseGradient hconv hG (p₀, x₀, x₀)
    ⟨hp₀, hx₀, hx₀⟩
  have ht : Tendsto (fun a ↦ (p a, x a, y a)) l (𝓝[V ×ˢ U ×ˢ U] (p₀, x₀, x₀)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp.prodMk_nhds (hx.prodMk_nhds hy), hmem⟩
  simpa only [Function.comp_def, averagedPhaseGradient_self] using hc.tendsto.comp ht

/-- Joint continuity of the integral extension in
`app:ch_seed:eq:seed-quotient-integral`, including zero shift, on the domain where
both segment endpoints lie in the convex chart. -/
theorem continuousOn_phaseShiftQuotient {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hconv : Convex ℝ U)
    (hG : ContinuousOn (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U)) :
    ContinuousOn (fun q : P × E × E × ℝ ↦ phaseShiftQuotient S q.1 q.2.1 q.2.2.1 q.2.2.2)
      {q | q.1 ∈ V ∧ q.2.1 ∈ U ∧ q.2.1 + q.2.2.2 • q.2.2.1 ∈ U} := by
  apply continuousOn_unitIntervalIntegral
  refine (hG.comp (f := fun q : (P × E × E × ℝ) × ℝ ↦
    (q.1.1, q.1.2.1 + (q.2 * q.1.2.2.2) • q.1.2.2.1)) (by fun_prop) ?_).inner
      (by fun_prop)
  intro q hq
  refine ⟨hq.1.1, ?_⟩
  simpa only [add_sub_cancel_left, smul_smul] using
    hconv.add_smul_sub_mem hq.1.2.1 hq.1.2.2 hq.2

/-- The zero-shift limit in `app:ch_seed:eq:seed-quotient-integral`, with simultaneous
variation of the spectators, base point, and shift direction. -/
theorem tendsto_phaseShiftQuotient_zero
    {S : P → E → ℝ} {V : Set P} {U : Set E} (hconv : Convex ℝ U)
    (hG : ContinuousOn (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U))
    {A : Type*} {l : Filter A} {p : A → P} {z v : A → E} {h : A → ℝ}
    {p₀ : P} {z₀ v₀ : E} (hp₀ : p₀ ∈ V) (hz₀ : z₀ ∈ U)
    (hp : Tendsto p l (𝓝 p₀)) (hz : Tendsto z l (𝓝 z₀))
    (hv : Tendsto v l (𝓝 v₀)) (hh : Tendsto h l (𝓝 0))
    (hmem : ∀ᶠ a in l, p a ∈ V ∧ z a ∈ U ∧ z a + h a • v a ∈ U) :
    Tendsto (fun a ↦ phaseShiftQuotient S (p a) (z a) (v a) (h a)) l
      (𝓝 (inner ℝ (gradient (S p₀) z₀) v₀)) := by
  have hc := continuousOn_phaseShiftQuotient hconv hG (p₀, z₀, v₀, 0)
    (by simpa using And.intro hp₀ (And.intro hz₀ hz₀))
  have ht : Tendsto (fun a ↦ (p a, z a, v a, h a)) l
      (𝓝[{q : P × E × E × ℝ |
        q.1 ∈ V ∧ q.2.1 ∈ U ∧ q.2.1 + q.2.2.2 • q.2.2.1 ∈ U}] (p₀, z₀, v₀, 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hp.prodMk_nhds (hz.prodMk_nhds (hv.prodMk_nhds hh)), hmem⟩
  simpa only [Function.comp_def, phaseShiftQuotient_zero] using hc.tendsto.comp ht

/-- The actual quotient of `app:ch_seed:eq:seed-exact-phase-quotient` has the
zero-shift limit given by `app:ch_seed:eq:seed-quotient-integral`. Openness supplies
eventual containment of the shifted points. Nonzero shifts may approach from either side. -/
theorem tendsto_phase_div_zero
    {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hS : ∀ p ∈ V, ContDiffOn ℝ 1 (S p) U)
    (hG : ContinuousOn (fun q : P × E ↦ gradient (S q.1) q.2) (V ×ˢ U))
    {A : Type*} {l : Filter A} {p : A → P} {z v : A → E} {h : A → ℝ}
    {p₀ : P} {z₀ v₀ : E} (hp₀ : p₀ ∈ V) (hz₀ : z₀ ∈ U)
    (hp : Tendsto p l (𝓝 p₀)) (hz : Tendsto z l (𝓝 z₀))
    (hv : Tendsto v l (𝓝 v₀)) (hh : Tendsto h l (𝓝 0))
    (hpmem : ∀ᶠ a in l, p a ∈ V) (hne : ∀ᶠ a in l, h a ≠ 0) :
    Tendsto (fun a ↦ (S (p a) (z a + h a • v a) - S (p a) (z a)) / h a) l
      (𝓝 (inner ℝ (gradient (S p₀) z₀) v₀)) := by
  have hshift : Tendsto (fun a ↦ z a + h a • v a) l (𝓝 z₀) := by
    simpa using hz.add (hh.smul hv)
  have hmem : ∀ᶠ a in l, p a ∈ V ∧ z a ∈ U ∧ z a + h a • v a ∈ U :=
    hpmem.and ((hz.eventually (hU.mem_nhds hz₀)).and
      (hshift.eventually (hU.mem_nhds hz₀)))
  apply (tendsto_phaseShiftQuotient_zero hconv hG hp₀ hz₀ hp hz hv hh hmem).congr'
  filter_upwards [hmem, hne] with a ha hha
  exact (phase_div_eq_phaseShiftQuotient hU hconv (hS (p a) ha.1)
    ha.2.1 ha.2.2 hha).symm

end TopologicalParameters

section NormedParameters

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The quotient limit of `app:ch_seed:eq:seed-quotient-integral` directly from joint
C¹ regularity on open charts. The partial-gradient and eventual-domain hypotheses
of the general limit theorem are discharged here. -/
theorem tendsto_phase_div_zero_of_contDiffOn {S : P → E → ℝ} {V : Set P} {U : Set E}
    (hV : IsOpen V) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hS : ContDiffOn ℝ 1 (Function.uncurry S) (V ×ˢ U))
    {A : Type*} {l : Filter A} {p : A → P} {z v : A → E} {h : A → ℝ}
    {p₀ : P} {z₀ v₀ : E} (hp₀ : p₀ ∈ V) (hz₀ : z₀ ∈ U)
    (hp : Tendsto p l (𝓝 p₀)) (hz : Tendsto z l (𝓝 z₀))
    (hv : Tendsto v l (𝓝 v₀)) (hh : Tendsto h l (𝓝 0))
    (hne : ∀ᶠ a in l, h a ≠ 0) :
    Tendsto (fun a ↦ (S (p a) (z a + h a • v a) - S (p a) (z a)) / h a) l
      (𝓝 (inner ℝ (gradient (S p₀) z₀) v₀)) :=
  tendsto_phase_div_zero hU hconv (fun _ hp ↦ contDiffOn_phase_slice hS hp)
    (continuousOn_phaseGradient_of_contDiffOn hV hU hS) hp₀ hz₀ hp hz hv hh
    (hp.eventually (hV.mem_nhds hp₀)) hne

end NormedParameters

end JanetCartan
