module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullNormalKernel.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Construction of compact scalar kernel operators

The actual L² operator underlying `app:ch_osc:prop:osc-normal`. Continuity and
compact support suffice, even when the input domain has infinite measure.
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
  [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
  {t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ}

/-- The integral representative as a linear map, before applying the closed
graph theorem (`app:ch_osc:prop:osc-normal`). -/
def compactKernelLinearMap (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν where
  toFun h := (memLp_compactKernel_integral_L2 (ν := ν) ht hs h).toLp
    (fun x ↦ ∫ u, t x u * h u ∂μ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_compactKernel_integral_L2 (ν := ν) ht hs (f + g)).coeFn_toLp,
      (memLp_compactKernel_integral_L2 (ν := ν) ht hs f).coeFn_toLp,
      (memLp_compactKernel_integral_L2 (ν := ν) ht hs g).coeFn_toLp,
      Lp.coeFn_add ((memLp_compactKernel_integral_L2 (ν := ν) ht hs f).toLp _)
        ((memLp_compactKernel_integral_L2 (ν := ν) ht hs g).toLp _)] with x hx hf hg ha
    rw [hx, ha, Pi.add_apply, hf, hg, ← integral_add
      (integrable_compactKernel_mul_L2 ht hs f x)
      (integrable_compactKernel_mul_L2 ht hs g x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with u hu
    rw [hu, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_compactKernel_integral_L2 (ν := ν) ht hs (c • f)).coeFn_toLp,
      (memLp_compactKernel_integral_L2 (ν := ν) ht hs f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_compactKernel_integral_L2 (ν := ν) ht hs f).toLp _)]
      with x hx hf hc
    simp only [RingHom.id_apply]
    rw [hx, hc, Pi.smul_apply, hf, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with u hu
    rw [hu, Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

/-- The constructed linear map has the prescribed input integral, as required
in `app:ch_osc:prop:osc-normal`. -/
theorem compactKernelLinearMap_ae_integral
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (h : Lp ℂ 2 μ) :
    compactKernelLinearMap (ν := ν) ht hs h =ᵐ[ν] fun x ↦ ∫ u, t x u * h u ∂μ :=
  (memLp_compactKernel_integral_L2 ht hs h).coeFn_toLp

/-- The integral pairing with the conjugate transposed kernel, prior to
boundedness or adjoints (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem compactKernelLinearMap_inner [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (h : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    inner ℂ (compactKernelLinearMap ht hs h) f =
      inner ℂ h ((memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f).toLp _) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (compactKernelLinearMap ht hs h x) (f x) ∂ν) =
        ∫ x, ∫ u, star (t x u) * f x * star (h u) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [compactKernelLinearMap_ae_integral (ν := ν) ht hs h] with x hx
      rw [hx, RCLike.inner_apply, ← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun u ↦ by
        simp only [map_mul, starRingEnd_apply]
        ring
    _ = ∫ u, ∫ x, star (t x u) * f x * star (h u) ∂ν ∂μ :=
      integral_integral_swap (integrable_compactKernel_L2_pairing ht hs f h)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f).coeFn_toLp]
        with u hu
      rw [hu, RCLike.inner_apply, integral_mul_const, starRingEnd_apply]

/-- Compact kernels act continuously on the entire L² input space. The proof
uses the closed graph theorem and the absolutely convergent adjoint pairing,
not an assumed operator bound (`app:ch_osc:prop:osc-normal`). -/
theorem continuous_compactKernelLinearMap [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t)) :
    Continuous (compactKernelLinearMap (μ := μ) (ν := ν) ht hs) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro v h g hv hTv
  apply ext_inner_right ℂ
  intro f
  have hlim := hv.inner (𝕜 := ℂ) (tendsto_const_nhds (x :=
    (memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f).toLp _))
  simp_rw [← compactKernelLinearMap_inner ht hs] at hlim
  exact tendsto_nhds_unique (hTv.inner (𝕜 := ℂ) tendsto_const_nhds) hlim

/-- The actual bounded scalar integral operator of
`app:ch_osc:prop:osc-normal`, constructed from continuity and compact support. -/
def compactKernelOperator [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  ⟨compactKernelLinearMap ht hs, continuous_compactKernelLinearMap ht hs⟩

/-- Input integral identity for the constructed bounded operator in
`app:ch_osc:prop:osc-normal`. -/
theorem compactKernelOperator_ae_integral [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (h : Lp ℂ 2 μ) :
    compactKernelOperator (ν := ν) ht hs h =ᵐ[ν] fun x ↦ ∫ u, t x u * h u ∂μ :=
  compactKernelLinearMap_ae_integral ht hs h

/-- Actual Hilbert adjoint of the constructed operator, with no additional
kernel-identity premise (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem compactKernelOperator_adjoint_ae_integral [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp ℂ 2 ν) :
    (compactKernelOperator (μ := μ) ht hs).adjoint f =ᵐ[μ]
      fun u ↦ ∫ x, star (t x u) * f x ∂ν :=
  adjoint_eq_integral_of_compactKernel ht hs (compactKernelOperator ht hs)
    (compactKernelOperator_ae_integral ht hs) f

end JanetCartan.NormalComparison
