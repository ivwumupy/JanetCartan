module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.Bounds

/-!
# Linearity in the compact kernel

Kernel remainders represent operator remainders exactly in the parameter
calculus of `app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.NormalComparison

open AmplitudeBound

variable {d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)
variable {μ : Measure (EuclideanSpace ℝ (Fin m))}
  {ν : Measure (EuclideanSpace ℝ (Fin d))}
  [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [SFinite μ] [SFinite ν]

/-- Exact correspondence between kernel and operator remainders in
`app:ch_osc:prop:osc-normal`. The kernel equality is pointwise algebra. -/
theorem compactKernelOperator_remainder {t v w R : E → U → ℂ}
    (ht : Continuous (Function.uncurry t)) (hv : Continuous (Function.uncurry v))
    (hw : Continuous (Function.uncurry w)) (hR : Continuous (Function.uncurry R))
    (hts : HasCompactSupport (Function.uncurry t))
    (hvs : HasCompactSupport (Function.uncurry v))
    (hws : HasCompactSupport (Function.uncurry w))
    (hRs : HasCompactSupport (Function.uncurry R))
    (c : ℝ) (hkernel : ∀ x u, R x u = t x u - v x u - c • w x u) :
    compactKernelOperator (μ := μ) (ν := ν) (t := R) hR hRs =
      compactKernelOperator (μ := μ) (ν := ν) (t := t) ht hts -
      compactKernelOperator (μ := μ) (ν := ν) (t := v) hv hvs -
      c • compactKernelOperator (μ := μ) (ν := ν) (t := w) hw hws := by
  apply ContinuousLinearMap.ext
  intro h
  apply Lp.ext
  have htI := compactKernelOperator_ae_integral (ν := ν) (t := t) ht hts h
  have hvI := compactKernelOperator_ae_integral (ν := ν) (t := v) hv hvs h
  have hwI := compactKernelOperator_ae_integral (ν := ν) (t := w) hw hws h
  have hRI := compactKernelOperator_ae_integral (ν := ν) (t := R) hR hRs h
  let T := compactKernelOperator (μ := μ) (ν := ν) (t := t) ht hts h
  let V := compactKernelOperator (μ := μ) (ν := ν) (t := v) hv hvs h
  let W := compactKernelOperator (μ := μ) (ν := ν) (t := w) hw hws h
  filter_upwards [htI, hvI, hwI, hRI, Lp.coeFn_sub T V,
    Lp.coeFn_smul c W, Lp.coeFn_sub (T - V) (c • W)] with x hxT hxV hxW hxR hxTV hxCW hxall
  change compactKernelOperator (μ := μ) (ν := ν) (t := R) hR hRs h x = (T - V - c • W) x
  rw [hxR, hxall, Pi.sub_apply, hxTV, hxCW, Pi.sub_apply, Pi.smul_apply]
  change _ = T x - V x - c • W x
  have htv : Integrable (fun u ↦ t x u * h u - v x u * h u) μ := by
    convert (integrable_compactKernel_mul_L2 ht hts h x).sub
      (integrable_compactKernel_mul_L2 hv hvs h x) using 1
  have hcw : Integrable (fun u ↦ c • (w x u * h u)) μ := by
    convert (integrable_compactKernel_mul_L2 hw hws h x).smul c using 1
  rw [hxT, hxV, hxW, ← integral_smul, ← integral_sub
    (integrable_compactKernel_mul_L2 ht hts h x)
    (integrable_compactKernel_mul_L2 hv hvs h x), ← integral_sub htv hcw]
  apply integral_congr_ae
  exact Eventually.of_forall fun u ↦ by
    dsimp only
    rw [hkernel x u]
    simp only [sub_mul, smul_mul_assoc]

end JanetCartan.NormalComparison
