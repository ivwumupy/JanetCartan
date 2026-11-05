module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Absolutely summable two-position operator series

The operator-series step of `app:ch_osc:lem:osc-amplitude` in `paper.tex`.
The index type can be the pair of physical Fourier frequencies. The left and right
operators are the cutoff modulations, and the middle operators are Fourier multipliers.
The coefficient bounds and their summability are explicit inputs here; this file does
not derive them from derivatives of a smooth amplitude or identify an integral kernel.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan.AmplitudeBound

variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- One cutoff-modulated coefficient in `app:ch_osc:lem:osc-amplitude`. -/
def modulatedTerm (L R C : ι → H →L[ℂ] H) (i : ι) : H →L[ℂ] H :=
  (L i).comp ((C i).comp (R i))

/-- Finite physical Fourier regularization of the series in
`app:ch_osc:lem:osc-amplitude`. Frequency regularization can be included in `C`. -/
def finiteAmplitudeOperator (L R C : ι → H →L[ℂ] H) (s : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ s, modulatedTerm L R C i

/-- The operator-norm sum in `app:ch_osc:lem:osc-amplitude`.
Use the summability theorems below before interpreting this as a Fourier expansion. -/
def amplitudeOperator (L R C : ι → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑' i, modulatedTerm L R C i

/-- Contractive cutoff modulations preserve the coefficient bound in
`app:ch_osc:lem:osc-amplitude`. -/
theorem norm_modulatedTerm_le (L R C : ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (i : ι) : ‖modulatedTerm L R C i‖ ≤ c i := by
  have hc : 0 ≤ c i := (norm_nonneg _).trans (hC i)
  calc
    ‖modulatedTerm L R C i‖ ≤ ‖L i‖ * ‖(C i).comp (R i)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (c i * 1) := mul_le_mul (hL i)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hC i) (hR i) (norm_nonneg _) hc)) (norm_nonneg _) zero_le_one
    _ = c i := by ring

/-- Absolute convergence of the operator expansion in `app:ch_osc:lem:osc-amplitude`. -/
theorem summable_norm_modulatedTerm (L R C : ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) : Summable (fun i ↦ ‖modulatedTerm L R C i‖) :=
  hc.of_norm_bounded (by simpa only [norm_norm] using norm_modulatedTerm_le L R C c hL hR hC)

/-- The series bound in `app:ch_osc:lem:osc-amplitude`, independent of frequency support. -/
theorem norm_amplitudeOperator_le (L R C : ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) : ‖amplitudeOperator L R C‖ ≤ ∑' i, c i := by
  have hs := summable_norm_modulatedTerm L R C c hL hR hC hc
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (norm_modulatedTerm_le L R C c hL hR hC) hc)

/-- Every finite regularization satisfies the same bound as the full series;
this is the uniformity needed in `app:ch_osc:lem:osc-amplitude`. -/
theorem norm_finiteAmplitudeOperator_le (L R C : ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) (s : Finset ι) :
    ‖finiteAmplitudeOperator L R C s‖ ≤ ∑' i, c i := by
  calc
    ‖finiteAmplitudeOperator L R C s‖ ≤ ∑ i ∈ s, ‖modulatedTerm L R C i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, c i := Finset.sum_le_sum fun i _ ↦
      norm_modulatedTerm_le L R C c hL hR hC i
    _ ≤ ∑' i, c i := hc.sum_le_tsum s (fun i _ ↦ (norm_nonneg _).trans (hC i))

variable [CompleteSpace H]

/-- Finite physical Fourier regularizations converge in operator norm in
`app:ch_osc:lem:osc-amplitude`. -/
theorem hasSum_modulatedTerm (L R C : ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) : HasSum (modulatedTerm L R C) (amplitudeOperator L R C) :=
  (summable_norm_modulatedTerm L R C c hL hR hC hc).of_norm.hasSum

/-- Evaluation of the absolutely convergent expansion in `app:ch_osc:lem:osc-amplitude`. -/
theorem amplitudeOperator_apply (L R C : ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) (f : H) :
    amplitudeOperator L R C f = ∑' i, L i (C i (R i f)) :=
  tsum_apply (summable_norm_modulatedTerm L R C c hL hR hC hc).of_norm f

/-- Strong convergence of coefficient regularizations passes through the two-position
series in `app:ch_osc:lem:osc-amplitude`. Operator-norm convergence of each multiplier
is not required, so expanding frequency cutoffs are allowed. -/
theorem tendsto_amplitudeOperator_apply {α : Type*} {l : Filter α}
    (L R C : ι → H →L[ℂ] H) (Creg : α → ι → H →L[ℂ] H) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) (hreg : ∀ a i, ‖Creg a i‖ ≤ c i)
    (hlim : ∀ i f, Tendsto (fun a ↦ Creg a i f) l (𝓝 (C i f))) (f : H) :
    Tendsto (fun a ↦ amplitudeOperator L R (Creg a) f) l
      (𝓝 (amplitudeOperator L R C f)) := by
  simp_rw [amplitudeOperator_apply L R _ c hL hR (hreg _) hc,
    amplitudeOperator_apply L R C c hL hR hC hc]
  apply tendsto_tsum_of_dominated_convergence (hc.mul_right ‖f‖)
  · intro i
    exact (L i).continuous.continuousAt.tendsto.comp (hlim i (R i f))
  · exact Filter.Eventually.of_forall fun a i ↦
      ((modulatedTerm L R (Creg a) i).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right
          (norm_modulatedTerm_le L R (Creg a) c hL hR (hreg a) i) (norm_nonneg f))

/-- Simultaneously removing a finite physical Fourier truncation and strongly
convergent coefficient regularizations in `app:ch_osc:lem:osc-amplitude`.
Each fixed physical mode must eventually be included. -/
theorem tendsto_finiteAmplitudeOperator_apply {α : Type*} {l : Filter α}
    (L R C : ι → H →L[ℂ] H) (Creg : α → ι → H →L[ℂ] H)
    (s : α → Finset ι) (c : ι → ℝ)
    (hL : ∀ i, ‖L i‖ ≤ 1) (hR : ∀ i, ‖R i‖ ≤ 1) (hC : ∀ i, ‖C i‖ ≤ c i)
    (hc : Summable c) (hreg : ∀ j i, ‖Creg j i‖ ≤ c i)
    (hlim : ∀ i f, Tendsto (fun j ↦ Creg j i f) l (𝓝 (C i f)))
    (hexhaust : ∀ i, ∀ᶠ j in l, i ∈ s j) (f : H) :
    Tendsto (fun j ↦ finiteAmplitudeOperator L R (Creg j) (s j) f) l
      (𝓝 (amplitudeOperator L R C f)) := by
  classical
  have hsum (j : α) : finiteAmplitudeOperator L R (Creg j) (s j) f =
      ∑' i, if i ∈ s j then L i (Creg j i (R i f)) else 0 := by
    rw [tsum_eq_sum (s := s j) (fun i hi ↦ ite_eq_right hi)]
    simp [finiteAmplitudeOperator, modulatedTerm]
  simp_rw [hsum, amplitudeOperator_apply L R C c hL hR hC hc]
  apply tendsto_tsum_of_dominated_convergence (hc.mul_right ‖f‖)
  · intro i
    apply ((L i).continuous.continuousAt.tendsto.comp (hlim i (R i f))).congr'
    exact (hexhaust i).mono fun j hj ↦ (ite_eq_left hj).symm
  · apply Eventually.of_forall
    intro j i
    split_ifs
    · exact ((modulatedTerm L R (Creg j) i).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right
          (norm_modulatedTerm_le L R (Creg j) c hL hR (hreg j) i) (norm_nonneg f))
    · simp only [norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hC i)) (norm_nonneg f)

end JanetCartan.AmplitudeBound
