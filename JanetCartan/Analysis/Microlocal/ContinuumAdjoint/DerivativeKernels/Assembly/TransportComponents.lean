module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Periodic

/-!
# The actual scalar transport in the literal adjoint components

The normal field in `app:ch_background:defn:bg-carriers` contains the scalar
r(z,Y) times its flow factor. The literal amplitude contains the square of
the normal norm. This module retains both scalar copies and proves their
fixed-baseline jet profiles from the original scalar, before composition.
Its consumer is the periodic raw estimate in `Assembly.ScalarTransport`.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow
variable {n N : ℕ}

/-- Geometry and measurement factor after removing the transported scalar
from the normal field (`app:ch_background:eq:bg-T`). -/
def carrierChartGeometryComponent (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N) (j : Fin n) : AdjointJetPoint n → ℂ :=
  fun p ↦ (χ p.2 * ‖ν p‖ ^ 2 * reducedCovector d p.2 (d.covector p.2 p.1) j : ℝ)

/-- Exact factorization of the literal full normalized component. The input
is the primitive transport formula for the normal field, not an amplitude
or operator estimate. In particular both copies of r(z,Y) and of the flow
factor remain in the norm square (`app:ch_background:prop:bg-adjoint`). -/
theorem carrierChartNormalizedComponent_eq_scalarTransport
    (d : CarrierData n N) (χ : Euclidean n → ℝ)
    (ν : AdjointJetPoint n → Euclidean N)
    (r : CarrierParameter × Euclidean (n-1) → ℝ) (flow : AdjointJetPoint n → ℝ)
    (hν : ∀ z x, d.normalField x z =
      (r (z, d.transportedPosition x z) * flow (z,x)) • ν (z,x)) (j : Fin n) :
    carrierChartNormalizedComponent d χ j = normalizedTransportAmplitude
      (carrierChartGeometryComponent d χ ν j)
      (fun z θ ↦ (d.angularCutoff z θ : ℂ)) (fun p ↦ (r p : ℂ) ^ 2)
      (fun p ↦ d.transportedPosition p.2 p.1) (fun p ↦ (flow p : ℂ) ^ 2) := by
  funext z x η
  simp only [carrierChartNormalizedComponent, normalizedTransportAmplitude,
    carrierChartGeometryComponent, hν, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

private theorem scalar_product_reserve_profile {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} (p : E) (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (Q q : ℕ) (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    {H T : ℝ} (hH : 1 ≤ H) (hT : 0 < T)
    (hfa : ∀ i ≤ q, ‖iteratedFDeriv ℝ i f p‖ ≤ A i * H ^ (((i - Q : ℕ) : ℝ) / T))
    (hgb : ∀ i ≤ q, ‖iteratedFDeriv ℝ i g p‖ ≤ B i * H ^ (((i - Q : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p ↦ f p * g p) p‖ ≤
      adjointLeibnizBudget A B q * H ^ (((q - Q : ℕ) : ℝ) / T) := by
  apply (adjoint_local_product_jet_bound q hf hg).trans
  unfold adjointLeibnizBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ ≤ (q.choose i : ℝ) * (A i * H ^ (((i - Q : ℕ) : ℝ) / T)) *
        (B (q-i) * H ^ (((q-i-Q : ℕ) : ℝ) / T)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfa i hiq) (Nat.cast_nonneg _))
        (hgb (q-i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (Real.rpow_nonneg (le_trans zero_le_one hH) _)))
    _ = ((q.choose i : ℝ) * A i * B (q-i)) *
        (H ^ (((i-Q : ℕ) : ℝ) / T) * H ^ (((q-i-Q : ℕ) : ℝ) / T)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB (q-i)))
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hH), ← add_div, ← Nat.cast_add]
      apply Real.rpow_le_rpow_of_exponent_le hH
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast (show (i-Q) + (q-i-Q) ≤ q-Q by omega)

/-- Squaring the original scalar preserves a single high-budget exponent.
This supplies the two scalar copies in the literal normal-field square,
without assuming jets of r(z,Y) (`app:ch_background:prop:bg-adjoint`). -/
theorem adjoint_scalar_square_reserve_profile {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} (p : E) (hf : ContDiffAt ℝ ∞ f p)
    (Q q : ℕ) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) {H T : ℝ}
    (hH : 1 ≤ H) (hT : 0 < T)
    (hfa : ∀ i ≤ q, ‖iteratedFDeriv ℝ i f p‖ ≤
      A i * H ^ (((i - Q : ℕ) : ℝ) / T)) :
    ‖iteratedFDeriv ℝ q (fun p ↦ f p ^ 2) p‖ ≤
      adjointLeibnizBudget A A q * H ^ (((q - Q : ℕ) : ℝ) / T) := by
  simpa only [pow_two] using
    scalar_product_reserve_profile p hf hf Q q A A hA hA hH hT hfa hfa

end JanetCartan.ContinuumAdjoint.DerivativeKernels
