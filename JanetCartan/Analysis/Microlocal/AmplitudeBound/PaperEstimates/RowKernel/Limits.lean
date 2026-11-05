module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowKernel.Finite
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The literal kernel of a supplied strong row limit

Pointwise absolute summability of the scalar row coefficients supplies one
integrable majorant `B * ‖Kf‖`. Dominated convergence identifies the integrals
of the original finite rows. Strong L² convergence has an almost-everywhere
convergent subsequence, whose uniqueness identifies the supplied operator.
This is a deduction from the actual strong limit, not a row-norm estimate.
Consumer: `app:ch_osc:eq:amplitude-row`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace JanetCartan.AmplitudeBound.RowKernel

open PaperEstimates

private theorem norm_finite_row_sum_le {ι : Type*}
    (γ z : ι → ℂ) (hγ : Summable (fun k ↦ ‖γ k‖))
    {B : ℝ} (hB : (∑' k, ‖γ k‖) ≤ B) (hz : ∀ k, ‖z k‖ ≤ 1) (s : Finset ι) :
    ‖∑ k ∈ s, z k*γ k‖ ≤ B := by
  calc
    _ ≤ ∑ k ∈ s, ‖z k*γ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖γ k‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hz k) (norm_nonneg (γ k))
    _ ≤ ∑' k, ‖γ k‖ := hγ.sum_le_tsum s (fun k _ ↦ norm_nonneg _)
    _ ≤ B := hB

variable {n : ℕ} {X κ : Type*} [MeasurableSpace X] [Countable κ] {μ : Measure X}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "H" => Lp ℂ 2 μ
local notation "L" => Lp ℂ 2 (volume : Measure E)

/-- On one fixed kernel-domain input, the GIVEN strong L² limit of the
original finite row operators has the literal amplitude-multiplied kernel.
Only the weighted inputs require a kernel identity for `T`; no absolute
kernel formula on all of L², row-output norm estimate, source derivatives,
or finiteness condition on the source measure is assumed
(`app:ch_osc:lem:osc-amplitude`). -/
theorem row_operator_ae_kernel_of_strong_limit
    (T A : H →L[ℂ] L) (a : κ → Lp ℂ ∞ μ)
    (m : κ → Lp ℂ ∞ (volume : Measure E))
    (β : κ → X → ℂ) (hβ : ∀ k, AEStronglyMeasurable (β k) μ)
    (B : ℝ) (hβsum : ∀ u, Summable (fun k ↦ ‖β k u‖))
    (hβbound : ∀ u, (∑' k, ‖β k u‖) ≤ B)
    (ψ : κ → E → ℂ) (hψ : ∀ k, ∀ᵐ x ∂volume, ‖ψ k x‖ ≤ 1)
    (ha : ∀ k, a k =ᵐ[μ] β k) (hm : ∀ k, m k =ᵐ[volume] ψ k)
    (b : X → E → ℂ) (hb : ∀ u x, HasSum (fun k ↦ ψ k x*β k u) (b u x))
    (s : ℕ → Finset κ) (hs : Tendsto s atTop atTop)
    (K : E → X → ℂ) (f : H)
    (hKint : ∀ᵐ x ∂volume, Integrable (fun u ↦ K x u*f u) μ)
    (hT : ∀ k, T (multiplicationOperator (a k) f) =ᵐ[volume]
      fun x ↦ ∫ u, K x u*(multiplicationOperator (a k) f) u ∂μ)
    (hstrong : Tendsto (fun N ↦ finiteRowAmplitudeOperator
      (fun k ↦ multiplicationOperator (m k)) T a (s N) f) atTop (𝓝 (A f))) :
    A f =ᵐ[volume] fun x ↦ ∫ u, b u x*K x u*f u ∂μ := by
  classical
  have hβone k u : ‖β k u‖ ≤ B := by
    have hh := (hβsum u).sum_le_tsum ({k} : Finset κ) (fun j _ ↦ norm_nonneg (β j u))
    simpa only [Finset.sum_singleton] using hh.trans (hβbound u)
  have hfinite N := finite_row_operator_ae_kernel T a m β hβ B
    (fun k ↦ ae_of_all _ (hβone k)) ψ ha hm K f hKint hT (s N)
  obtain ⟨ns,hns,hseq⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  filter_upwards [hKint,ae_all_iff.mpr hψ,ae_all_iff.mpr hfinite,hseq]
    with x hKx hψx hfiniteX hseqX
  have hlim : Tendsto (fun N ↦ ∫ u, (∑ k ∈ s N, ψ k x*β k u)*K x u*f u ∂μ)
      atTop (𝓝 (∫ u, b u x*K x u*f u ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun u ↦ B*‖K x u*f u‖)
    · intro N
      have hh := (Finset.aestronglyMeasurable_fun_sum (s N)
        (fun k _ ↦ (hβ k).const_mul (ψ k x))).mul hKx.aestronglyMeasurable
      simpa only [Pi.mul_def,mul_assoc] using hh
    · exact hKx.norm.const_mul B
    · intro N
      apply ae_of_all
      intro u
      rw [mul_assoc,norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_finite_row_sum_le (fun k ↦ β k u) (fun k ↦ ψ k x)
          (hβsum u) (hβbound u) hψx (s N)) (norm_nonneg _)
    · apply ae_of_all
      intro u
      have hc : Tendsto (fun N ↦ ∑ k ∈ s N, ψ k x*β k u) atTop (𝓝 (b u x)) :=
        (hb u x).comp hs
      exact (hc.mul_const (K x u)).mul_const (f u)
  have hseqIntegral := Filter.Tendsto.congr'
    (Filter.Eventually.of_forall (fun j ↦ hfiniteX (ns j))) hseqX
  exact tendsto_nhds_unique hseqIntegral (hlim.comp hns.tendsto_atTop)

end JanetCartan.AmplitudeBound.RowKernel
