module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Repeated transposed integration by parts

The integration identity in `app:ch_osc:prop:osc-source-shell`, for a finite family
of directions and complex coefficients. All differentiability and integrability
inputs are explicit. The identity does not assume bounds for derivatives of the
coefficients: proving those bounds for the reciprocal of the phase gradient is
a separate analytic step.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.Localization

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- `app:ch_osc:prop:osc-source-shell`: the formal transpose of
`∑ i, bᵢ ∂_{eᵢ}` acting on an amplitude. -/
def transposeAmplitude (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ) (x : E) : ℂ :=
  -∑ i, fderiv ℝ (fun y ↦ b i y * a y) x (e i)

/-- `app:ch_osc:prop:osc-source-shell`: transposition does not enlarge the
closed support of the amplitude, even before regularity is imposed. -/
theorem tsupport_transposeAmplitude_subset (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ) :
    tsupport (transposeAmplitude e b a) ⊆ tsupport a := by
  apply closure_minimal ?_ (isClosed_tsupport a)
  intro x hx
  by_contra hxa
  change transposeAmplitude e b a x ≠ 0 at hx
  apply hx
  have hd (i : ι) : fderiv ℝ (fun y ↦ b i y * a y) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (by
      intro h
      exact hxa (tsupport_mul_subset_right h))
  simp [transposeAmplitude, hd]

/-- `app:ch_osc:prop:osc-source-shell`: all orders use the original common
compact support, rather than an order-dependent enlargement. -/
theorem tsupport_iterate_transposeAmplitude_subset
    (e : ι → E) (b : ι → E → ℂ) (a : E → ℂ) (q : ℕ) :
    tsupport ((transposeAmplitude e b)^[q] a) ⊆ tsupport a := by
  induction q with
  | zero => exact Set.Subset.refl _
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact (tsupport_transposeAmplitude_subset e b _).trans ih

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- `app:ch_osc:prop:osc-source-shell`: one transposed integration by parts.
The normalization says that the differential operator sends `f` to itself.
It is a pointwise differential identity, not an assumed integral identity.
The integrability inputs justify the absence of boundary terms. -/
theorem integral_eq_integral_transposeAmplitude
    (e : ι → E) (b : ι → E → ℂ) (f a : E → ℂ)
    (hnormalize : ∀ x, a x ≠ 0 → ∑ i, b i x * fderiv ℝ f x (e i) = f x)
    (hleft : ∀ i, Integrable
      (fun x ↦ fderiv ℝ (fun y ↦ b i y * a y) x (e i) * f x) μ)
    (hright : ∀ i, Integrable (fun x ↦ (b i x * a x) * fderiv ℝ f x (e i)) μ)
    (hprod : ∀ i, Integrable (fun x ↦ (b i x * a x) * f x) μ)
    (hba : ∀ i x, x ∈ tsupport f → DifferentiableAt ℝ (fun y ↦ b i y * a y) x)
    (hf : ∀ i x, x ∈ tsupport (fun y ↦ b i y * a y) → DifferentiableAt ℝ f x) :
    (∫ x, f x * a x ∂μ) = ∫ x, f x * transposeAmplitude e b a x ∂μ := by
  calc
    (∫ x, f x * a x ∂μ) =
        ∫ x, ∑ i, (b i x * a x) * fderiv ℝ f x (e i) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : a x = 0
      · simp [hx]
      rw [← hnormalize x hx, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ = ∑ i, ∫ x, (b i x * a x) * fderiv ℝ f x (e i) ∂μ :=
      integral_finsetSum _ (fun i _ ↦ hright i)
    _ = ∑ i, -(∫ x, fderiv ℝ (fun y ↦ b i y * a y) x (e i) * f x ∂μ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hleft i) (hright i) (hprod i) (hba i) (hf i)
    _ = ∫ x, f x * transposeAmplitude e b a x ∂μ := by
      simp only [transposeAmplitude, mul_neg, Finset.mul_sum, integral_neg,
        Finset.sum_neg_distrib]
      congr 1
      rw [integral_finsetSum _ (fun i _ ↦ by simpa only [mul_comm] using hleft i)]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext x
      exact mul_comm _ _

/-- `app:ch_osc:prop:osc-source-shell`: the exact identity after `q` integrations
by parts. The same differential operator is used at every order. -/
theorem integral_eq_integral_iterate_transposeAmplitude
    (e : ι → E) (b : ι → E → ℂ) (f a : E → ℂ) (q : ℕ)
    (hnormalize : ∀ k < q, ∀ x, ((transposeAmplitude e b)^[k] a) x ≠ 0 →
      ∑ i, b i x * fderiv ℝ f x (e i) = f x)
    (hleft : ∀ k < q, ∀ i, Integrable
      (fun x ↦ fderiv ℝ (fun y ↦ b i y * ((transposeAmplitude e b)^[k] a) y)
        x (e i) * f x) μ)
    (hright : ∀ k < q, ∀ i, Integrable
      (fun x ↦ (b i x * ((transposeAmplitude e b)^[k] a) x) *
        fderiv ℝ f x (e i)) μ)
    (hprod : ∀ k < q, ∀ i, Integrable
      (fun x ↦ (b i x * ((transposeAmplitude e b)^[k] a) x) * f x) μ)
    (hba : ∀ k < q, ∀ i x, x ∈ tsupport f → DifferentiableAt ℝ
      (fun y ↦ b i y * ((transposeAmplitude e b)^[k] a) y) x)
    (hf : ∀ k < q, ∀ i x,
      x ∈ tsupport (fun y ↦ b i y * ((transposeAmplitude e b)^[k] a) y) →
        DifferentiableAt ℝ f x) :
    (∫ x, f x * a x ∂μ) =
      ∫ x, f x * ((transposeAmplitude e b)^[q] a) x ∂μ := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [ih (fun k hk ↦ hnormalize k (Nat.lt_succ_of_lt hk))
      (fun k hk ↦ hleft k (Nat.lt_succ_of_lt hk))
      (fun k hk ↦ hright k (Nat.lt_succ_of_lt hk))
      (fun k hk ↦ hprod k (Nat.lt_succ_of_lt hk))
      (fun k hk ↦ hba k (Nat.lt_succ_of_lt hk))
      (fun k hk ↦ hf k (Nat.lt_succ_of_lt hk))]
    rw [Function.iterate_succ_apply']
    exact integral_eq_integral_transposeAmplitude e b f _ (hnormalize q (Nat.lt_succ_self q))
      (hleft q (Nat.lt_succ_self q)) (hright q (Nat.lt_succ_self q))
      (hprod q (Nat.lt_succ_self q)) (hba q (Nat.lt_succ_self q))
      (hf q (Nat.lt_succ_self q))

/-- `app:ch_osc:prop:osc-source-shell`: repeated integration by parts bounds
an oscillatory integral by the L¹ size of the actual transposed amplitude.
Derivative bounds for that amplitude are still required to obtain a power of
the frequency gap. -/
theorem norm_integral_le_integral_norm_iterate_transposeAmplitude
    (e : ι → E) (b : ι → E → ℂ) (f a : E → ℂ) (q : ℕ)
    (hnormalize : ∀ k < q, ∀ x, ((transposeAmplitude e b)^[k] a) x ≠ 0 →
      ∑ i, b i x * fderiv ℝ f x (e i) = f x)
    (hleft : ∀ k < q, ∀ i, Integrable
      (fun x ↦ fderiv ℝ (fun y ↦ b i y * ((transposeAmplitude e b)^[k] a) y)
        x (e i) * f x) μ)
    (hright : ∀ k < q, ∀ i, Integrable
      (fun x ↦ (b i x * ((transposeAmplitude e b)^[k] a) x) *
        fderiv ℝ f x (e i)) μ)
    (hprod : ∀ k < q, ∀ i, Integrable
      (fun x ↦ (b i x * ((transposeAmplitude e b)^[k] a) x) * f x) μ)
    (hba : ∀ k < q, ∀ i x, x ∈ tsupport f → DifferentiableAt ℝ
      (fun y ↦ b i y * ((transposeAmplitude e b)^[k] a) y) x)
    (hf : ∀ k < q, ∀ i x,
      x ∈ tsupport (fun y ↦ b i y * ((transposeAmplitude e b)^[k] a) y) →
        DifferentiableAt ℝ f x)
    (hunit : ∀ x, ‖f x‖ ≤ 1)
    (hfinal : Integrable ((transposeAmplitude e b)^[q] a) μ) :
    ‖∫ x, f x * a x ∂μ‖ ≤ ∫ x, ‖((transposeAmplitude e b)^[q] a) x‖ ∂μ := by
  rw [integral_eq_integral_iterate_transposeAmplitude e b f a q hnormalize
    hleft hright hprod hba hf]
  apply norm_integral_le_of_norm_le hfinal.norm
  filter_upwards [] with x
  rw [norm_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hunit x) (norm_nonneg _)

end JanetCartan.Localization
