module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Compact smooth initial carrier data

The dense test domain for `app:ch_background:prop:bg-frame`, Step 1.
This uses the same smooth approximation argument as `FourierIntegral.L2Realization.Tests`,
on the literal product measure `dz dη` of `app:ch_background:eq:bg-T`.
Consumer: `exists_carrierL2Extension` and the continuum initial adjoint.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.ContinuumRow

variable (n : ℕ)

/-- Compact smooth complex scalar data for `app:ch_background:eq:bg-T`. -/
def carrierInitialTestSpace : Submodule ℂ (CarrierVariable n → ℂ) where
  carrier := {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' hu hv := ⟨hu.1.add hv.1, hu.2.add hv.2⟩
  smul_mem' c _u hu := ⟨hu.1.const_smul c, hu.2.smul_left⟩

variable {n}

/-- The literal initial measure is finite on compact sets (`app:ch_background:eq:bg-T`). -/
instance carrierMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (carrierMeasure n) := by
  unfold carrierMeasure
  infer_instance

/-- Test functions belong to L² (`app:ch_background:eq:bg-T`). -/
theorem carrierInitialTest_memLp (u : carrierInitialTestSpace n) : MemLp u.val 2 (carrierMeasure n) :=
  u.property.1.continuous.memLp_of_hasCompactSupport u.property.2

/-- Inclusion of actual test functions in initial-variable L², for the extension in
`app:ch_background:prop:bg-frame`, Step 1. -/
def carrierInitialTestToLp : carrierInitialTestSpace n →ₗ[ℂ]
    CarrierL2 n where
  toFun u := (carrierInitialTest_memLp u).toLp u.val
  map_add' u v := MemLp.toLp_add (carrierInitialTest_memLp u) (carrierInitialTest_memLp v)
  map_smul' c u := by
    exact MemLp.toLp_const_smul c (carrierInitialTest_memLp u)

/-- Compact smooth density for the actual Lebesgue data of
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem denseRange_carrierInitialTestToLp : DenseRange (carrierInitialTestToLp (n := n)) := by
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hc, hg, he⟩ := MemLp.exist_eLpNorm_sub_le
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (Lp.memLp v)
    (show (0 : ℝ) < ε / 2 by positivity)
  let u : carrierInitialTestSpace n := ⟨g, hg, hc⟩
  refine ⟨carrierInitialTestToLp u, ⟨u, rfl⟩, ?_⟩
  rw [Lp.dist_def]
  have hae : (⇑v - ⇑(carrierInitialTestToLp u)) =ᵐ[carrierMeasure n] (⇑v - g) := by
    filter_upwards [(carrierInitialTest_memLp u).coeFn_toLp] with x hx
    exact congrArg (v x - ·) hx
  rw [eLpNorm_congr_ae hae]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) he).trans_lt (by linarith)

end JanetCartan.ContinuumRow
