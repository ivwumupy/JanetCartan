module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowKernel.Limits

/-!
# Literal row kernels for the actual cutoff modulations

The finite operators are the shared `finiteRowAmplitudeOperator`, with the
original coefficient symbols and the existing `cutoffModulation`. Their
supplied strong limit has the literal amplitude-multiplied kernel on its
natural input domain. In particular the L¹∩L² version applies to inverse
Fourier kernels. The original source measure is arbitrary throughout.

The weighted-column and diagonal-trace producer supplies the strong limit;
this module proves its kernel identity, not the sharp operator norm.
Consumer: part (i) of `app:ch_osc:lem:osc-amplitude`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace JanetCartan.AmplitudeBound.RowKernel

open PaperEstimates

variable {n d : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp ℂ 2 μ
local notation "L" => Lp ℂ 2 (volume : Measure E)
local notation "Mode" => Fin d → ℤ

/-- Exact kernel identification for the actual Fourier cutoff modulations
and supplied coefficient symbols. For `a k = boundedSymbol (β k) ...`, the
input `ha` is precisely `boundedSymbol_coeFn`; no different symbol is chosen.
The identity for `T` is needed only at this datum's multiplied inputs
(`app:ch_osc:eq:amplitude-row`). -/
theorem cutoff_row_operator_ae_kernel_of_strong_limit
    (T A : H →L[ℂ] L) (a : Mode → Lp ℂ ∞ μ)
    (β : Mode → X → ℂ) (hβ : ∀ k, AEStronglyMeasurable (β k) μ)
    (B : ℝ) (hβsum : ∀ u, Summable (fun k ↦ ‖β k u‖))
    (hβbound : ∀ u, (∑' k, ‖β k u‖) ≤ B) (ha : ∀ k, a k =ᵐ[μ] β k)
    (q : E → Torus d) (hq : Measurable q)
    (χ : E → ℂ) (hχ : AEStronglyMeasurable χ volume)
    (hχbound : ∀ᵐ x ∂volume, ‖χ x‖ ≤ 1)
    (b : X → E → ℂ)
    (hb : ∀ u x, HasSum (fun k ↦ χ x*UnitAddTorus.mFourier k (q x)*β k u) (b u x))
    (s : ℕ → Finset Mode) (hs : Tendsto s atTop atTop)
    (K : E → X → ℂ) (f : H)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u*f u) μ)
    (hT : ∀ k, T (multiplicationOperator (a k) f) =ᵐ[volume]
      fun x ↦ ∫ u, K x u*(multiplicationOperator (a k) f) u ∂μ)
    (hstrong : Tendsto (fun N ↦ finiteRowAmplitudeOperator
      (cutoffModulation q hq χ hχ hχbound) T a (s N) f) atTop (𝓝 (A f))) :
    A f =ᵐ[volume] fun x ↦ ∫ u, b u x*K x u*f u ∂μ := by
  apply row_operator_ae_kernel_of_strong_limit T A a
    (cutoffModulationSymbol q hq χ hχ hχbound) β hβ B hβsum hβbound
    (fun k x ↦ χ x*UnitAddTorus.mFourier k (q x)) ?_ ha ?_ b hb s hs K f hKint hT hstrong
  · intro k
    filter_upwards [hχbound] with x hx
    rw [norm_mul]
    exact (mul_le_mul hx (norm_mFourier_apply_le_one k (q x))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k
    exact boundedSymbol_coeFn _ _ _ _

/-- Natural L¹∩L²-core version of the same row identity. Bounded coefficient
multiplication preserves integrability, so the original core kernel formula
for `T` supplies every finite-mode identity. This covers inverse Fourier
without requiring absolute convergence on all of L²
(`app:ch_osc:lem:osc-amplitude`). -/
theorem cutoff_row_operator_ae_kernel_on_L1_core
    (T A : H →L[ℂ] L) (a : Mode → Lp ℂ ∞ μ)
    (β : Mode → X → ℂ) (hβ : ∀ k, AEStronglyMeasurable (β k) μ)
    (B : ℝ) (hβsum : ∀ u, Summable (fun k ↦ ‖β k u‖))
    (hβbound : ∀ u, (∑' k, ‖β k u‖) ≤ B) (ha : ∀ k, a k =ᵐ[μ] β k)
    (q : E → Torus d) (hq : Measurable q)
    (χ : E → ℂ) (hχ : AEStronglyMeasurable χ volume)
    (hχbound : ∀ᵐ x ∂volume, ‖χ x‖ ≤ 1)
    (b : X → E → ℂ)
    (hb : ∀ u x, HasSum (fun k ↦ χ x*UnitAddTorus.mFourier k (q x)*β k u) (b u x))
    (s : ℕ → Finset Mode) (hs : Tendsto s atTop atTop)
    (K : E → X → ℂ)
    (hT : ∀ g : H, Integrable (g : X → ℂ) μ →
      T g =ᵐ[volume] fun x ↦ ∫ u, K x u*g u ∂μ)
    (f : H) (hf : Integrable (f : X → ℂ) μ)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u*f u) μ)
    (hstrong : Tendsto (fun N ↦ finiteRowAmplitudeOperator
      (cutoffModulation q hq χ hχ hχbound) T a (s N) f) atTop (𝓝 (A f))) :
    A f =ᵐ[volume] fun x ↦ ∫ u, b u x*K x u*f u ∂μ := by
  apply cutoff_row_operator_ae_kernel_of_strong_limit T A a β hβ B hβsum hβbound ha
    q hq χ hχ hχbound b hb s hs K f hKint ?_ hstrong
  intro k
  apply hT
  exact (hf.mul_of_top_right (Lp.memLp (a k))).congr
    (multiplicationOperator_coeFn (a k) f).symm

end JanetCartan.AmplitudeBound.RowKernel
