module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.Kernel
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Compact smooth Euclidean graph data

The dense test domain for `app:ch_regular_base:thm:actual-calculus`, Step 1.
Both the input and output measures are Euclidean Lebesgue measure.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.FourierIntegral

variable (n r : ℕ)

/-- Compact smooth vector data for `app:ch_regular_base:eq:fio-input`. -/
def graphTestSpace : Submodule ℂ (Euclidean n → EuclideanSpace ℂ (Fin r)) where
  carrier := {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' hu hv := ⟨hu.1.add hv.1, hu.2.add hv.2⟩
  smul_mem' c _u hu := ⟨hu.1.const_smul c, hu.2.smul_left⟩

variable {n r}

/-- Test functions belong to L² (`app:ch_regular_base:eq:fio-input`). -/
theorem graphTest_memLp (u : graphTestSpace n r) : MemLp u.val 2 volume :=
  u.property.1.continuous.memLp_of_hasCompactSupport u.property.2

/-- Inclusion of actual test functions in Euclidean L², for the extension in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def graphTestToLp : graphTestSpace n r →ₗ[ℂ]
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) where
  toFun u := (graphTest_memLp u).toLp u.val
  map_add' u v := MemLp.toLp_add (graphTest_memLp u) (graphTest_memLp v)
  map_smul' c u := by
    exact MemLp.toLp_const_smul c (graphTest_memLp u)

/-- Compact smooth density for the actual Lebesgue data of
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem denseRange_graphTestToLp : DenseRange (graphTestToLp (n := n) (r := r)) := by
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hc, hg, he⟩ := MemLp.exist_eLpNorm_sub_le
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp v)
    (show (0 : ℝ) < ε / 2 by positivity)
  let u : graphTestSpace n r := ⟨g, hg, hc⟩
  refine ⟨graphTestToLp u, ⟨u, rfl⟩, ?_⟩
  rw [Lp.dist_def]
  have hae : (⇑v - ⇑(graphTestToLp u)) =ᵐ[volume] (⇑v - g) := by
    filter_upwards [(graphTest_memLp u).coeFn_toLp] with x hx
    exact congrArg (v x - ·) hx
  rw [eLpNorm_congr_ae hae]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) he).trans_lt (by linarith)

end JanetCartan.FourierIntegral
