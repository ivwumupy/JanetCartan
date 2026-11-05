module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Modulations
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowSeries.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Literal kernels of the original finite row operators

The source symbols and output symbols are supplied unchanged. Their existing
almost-everywhere realizations identify the actual finite operator sum with
its finite row kernel. The kernel identity is required only for the
coefficient-weighted inputs of one fixed datum, not for all of L².
No finiteness assumption on the source measure is used.
Consumer: the sharp row kernel in `app:ch_osc:eq:amplitude-row`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace JanetCartan.AmplitudeBound.RowKernel

open PaperEstimates

variable {n : ℕ} {X κ : Type*} [MeasurableSpace X] [Countable κ] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp ℂ 2 μ
local notation "L" => Lp ℂ 2 (volume : Measure E)

/-- Literal realization of the supplied finite row operator, on the natural
kernel domain of one fixed input. The same coefficient multipliers occur on
both sides (`app:ch_osc:lem:osc-amplitude`). -/
theorem finite_row_operator_ae_kernel
    (T : H →L[ℂ] L) (a : κ → Lp ℂ ∞ μ)
    (m : κ → Lp ℂ ∞ (volume : Measure E))
    (β : κ → X → ℂ) (hβ : ∀ k, AEStronglyMeasurable (β k) μ)
    (C : ℝ) (hβbound : ∀ k, ∀ᵐ u ∂μ, ‖β k u‖ ≤ C)
    (ψ : κ → E → ℂ)
    (ha : ∀ k, a k =ᵐ[μ] β k) (hm : ∀ k, m k =ᵐ[volume] ψ k)
    (K : E → X → ℂ) (f : H)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u*f u) μ)
    (hT : ∀ k, T (multiplicationOperator (a k) f) =ᵐ[volume]
      fun x ↦ ∫ u, K x u*(multiplicationOperator (a k) f) u ∂μ)
    (s : Finset κ) :
    finiteRowAmplitudeOperator (fun k ↦ multiplicationOperator (m k)) T a s f =ᵐ[volume]
      fun x ↦ ∫ u, (∑ k ∈ s, ψ k x*β k u)*K x u*f u ∂μ := by
  classical
  change (∑ k ∈ s, (multiplicationOperator (m k)).comp
    (T.comp (multiplicationOperator (a k)))) f =ᵐ[volume] _
  have hsource k : multiplicationOperator (a k) f =ᵐ[μ] fun u ↦ β k u*f u := by
    filter_upwards [multiplicationOperator_coeFn (a k) f,ha k] with u hu hua
    exact hu.trans (congrArg (fun z ↦ z*f u) hua)
  have hone k : multiplicationOperator (m k) (T (multiplicationOperator (a k) f)) =ᵐ[volume]
      fun x ↦ ∫ u, ψ k x*β k u*K x u*f u ∂μ := by
    filter_upwards [multiplicationOperator_coeFn (m k) (T (multiplicationOperator (a k) f)),
      hm k,hT k] with x hx hxm hxt
    rw [hx,hxm,hxt,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hsource k] with u hu
    rw [hu]
    ring
  have he : (∑ k ∈ s, (multiplicationOperator (m k)).comp
      (T.comp (multiplicationOperator (a k)))) f =
      ∑ k ∈ s, multiplicationOperator (m k) (T (multiplicationOperator (a k) f)) := by
    simp only [sum_apply,ContinuousLinearMap.comp_apply]
  rw [he]
  filter_upwards [Lp.coeFn_fun_finsetSum s
    (fun k ↦ multiplicationOperator (m k) (T (multiplicationOperator (a k) f))),
    ae_all_iff.mpr hone,hKint] with x hx honeX hKx
  rw [hx]
  have hint k : Integrable (fun u ↦ ψ k x*β k u*K x u*f u) μ := by
    apply ((hKx.bdd_mul (hβ k) (hβbound k)).const_mul (ψ k x)).congr
    exact ae_of_all _ (fun u ↦ by ring)
  calc
    _ = ∑ k ∈ s, ∫ u, ψ k x*β k u*K x u*f u ∂μ :=
      Finset.sum_congr rfl (fun k _ ↦ honeX k)
    _ = ∫ u, ∑ k ∈ s, ψ k x*β k u*K x u*f u ∂μ :=
      (integral_finsetSum s (fun k _ ↦ hint k)).symm
    _ = ∫ u, (∑ k ∈ s, ψ k x*β k u)*K x u*f u ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u ↦ by simp only [Finset.sum_mul])

end JanetCartan.AmplitudeBound.RowKernel
