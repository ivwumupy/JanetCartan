module

public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Finite-order differentiation of atomic integrals

The finite-order integration argument of `app:ch_lag:prop:lag-envelopes`.
Domination and smoothness hold on a common open neighborhood. No derivative
interchange is assumed: it is proved by induction from dominated differentiation.
The results hold in arbitrary real Banach spaces, hence in the finite-dimensional
coordinate spaces of the paper and for its chosen Frobenius matrix norm.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace JanetCartan
namespace MeasureEnvelopes

section Real

variable {α X E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {A : α → X → E} {s : Set X} {r : ℕ} {b : ℕ → α → ℝ}

/-- `app:ch_lag:prop:lag-envelopes`: all derivatives through a fixed order commute
with the genuine integral, under integrable bounds on a common open neighborhood. -/
theorem iteratedFDeriv_integral_of_dominated (hs : IsOpen s)
    (hA : ∀ᵐ t ∂μ, ∀ x ∈ s, ContDiffAt ℝ r (A t) x)
    (hm : ∀ j ≤ r, ∀ x ∈ s,
      AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ j (A t) x) μ)
    (hi : ∀ j ≤ r, Integrable (b j) μ)
    (hb : ∀ j ≤ r, ∀ᵐ t ∂μ, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (A t) x‖ ≤ b j t)
    {j : ℕ} (hj : j ≤ r) {x : X} (hx : x ∈ s) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ t, A t y ∂μ) x =
      ∫ t, iteratedFDeriv ℝ j (A t) x ∂μ := by
  have hint : ∀ k ≤ r, ∀ y ∈ s, Integrable (fun t ↦ iteratedFDeriv ℝ k (A t) y) μ := by
    intro k hk y hy
    exact (hi k hk).mono' (hm k hk y hy) ((hb k hk).mono fun t ht ↦ ht y hy)
  induction j generalizing x with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ X E).symm
    exact (L.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih =>
    have hjr : j ≤ r := Nat.le_trans (Nat.le_succ j) hj
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) E
    have hd : HasFDerivAt (fun y ↦ ∫ t, iteratedFDeriv ℝ j (A t) y ∂μ)
        (∫ t, fderiv ℝ (iteratedFDeriv ℝ j (A t)) x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (hs.mem_nhds hx)
      · exact (Filter.mem_of_superset (hs.mem_nhds hx)) fun y hy ↦ hm j hjr y hy
      · exact hint j hjr x hx
      · exact L.continuous.comp_aestronglyMeasurable (hm (j + 1) hj x hx)
      · simpa only [norm_fderiv_iteratedFDeriv] using hb (j + 1) hj
      · exact hi (j + 1) hj
      · filter_upwards [hA] with t ht y hy
        exact ((ht y hy).differentiableAt_iteratedFDeriv
          (by exact_mod_cast (Nat.lt_of_succ_le hj))).hasFDerivAt
    have heq : iteratedFDeriv ℝ j (fun y ↦ ∫ t, A t y ∂μ) =ᶠ[𝓝 x]
        (fun y ↦ ∫ t, iteratedFDeriv ℝ j (A t) y ∂μ) :=
      (Filter.mem_of_superset (hs.mem_nhds hx)) fun y hy ↦ ih hjr hy
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq, hd.fderiv]
    exact (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ)
      (E := X →L[ℝ] (X [×j]→L[ℝ] E)) (F := X [×(j + 1)]→L[ℝ] E)
      L.symm.toContinuousLinearEquiv
      (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ j (A t)) x)).symm

/-- `app:ch_lag:prop:lag-envelopes`: dominated derivative bounds control the sum-of-suprema
seminorm on every subset of the common neighborhood. -/
theorem cNorm_integral_le (hs : IsOpen s)
    (hA : ∀ᵐ t ∂μ, ∀ x ∈ s, ContDiffAt ℝ r (A t) x)
    (hm : ∀ j ≤ r, ∀ x ∈ s,
      AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ j (A t) x) μ)
    (hi : ∀ j ≤ r, Integrable (b j) μ)
    (hb : ∀ j ≤ r, ∀ᵐ t ∂μ, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (A t) x‖ ≤ b j t)
    (hb₀ : ∀ j ≤ r, ∀ᵐ t ∂μ, 0 ≤ b j t) {K : Set X} (hK : K ⊆ s) :
    cNorm K r (fun y ↦ ∫ t, A t y ∂μ) ≤ ∑ j ∈ Finset.range (r + 1), ∫ t, b j t ∂μ := by
  apply cNorm_le_sum_of_bounds (fun j hj ↦ integral_nonneg_of_ae (hb₀ j hj))
  intro j hj x hx
  rw [iteratedFDeriv_integral_of_dominated hs hA hm hi hb hj (hK hx)]
  exact norm_integral_le_of_norm_le (hi j hj) ((hb j hj).mono fun t ht ↦ ht x (hK hx))

end Real

section Complex

variable {α X E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {μ : Measure α} {ρ : α → ℂ} {A : α → X → E} {s : Set X} {r : ℕ} {C : ℕ → ℝ}

/-- `app:ch_lag:prop:lag-envelopes`: finite-order derivative interchange for an integrable
complex density and uniformly bounded atomic derivatives on a common open neighborhood. -/
theorem iteratedFDeriv_synthesis (hs : IsOpen s) (hρ : Integrable ρ μ)
    (hA : ∀ᵐ t ∂μ, ∀ x ∈ s, ContDiffAt ℝ r (A t) x)
    (hm : ∀ j ≤ r, ∀ x ∈ s,
      AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ j (A t) x) μ)
    (hb : ∀ j ≤ r, ∀ᵐ t ∂μ, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (A t) x‖ ≤ C j)
    {j : ℕ} (hj : j ≤ r) {x : X} (hx : x ∈ s) :
    iteratedFDeriv ℝ j (fun y ↦ synthesis μ ρ (fun t ↦ A t y)) x =
      synthesis μ ρ (fun t ↦ iteratedFDeriv ℝ j (A t) x) := by
  have heq : ∀ k ≤ r, ∀ y ∈ s,
      (fun t ↦ iteratedFDeriv ℝ k (fun z ↦ ρ t • A t z) y) =ᵐ[μ]
        (fun t ↦ ρ t • iteratedFDeriv ℝ k (A t) y) := by
    intro k hk y hy
    filter_upwards [hA] with t ht
    exact iteratedFDeriv_const_smul_apply' ((ht y hy).of_le (by exact_mod_cast hk))
  have hm' : ∀ k ≤ r, ∀ y ∈ s,
      AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ k (fun z ↦ ρ t • A t z) y) μ := by
    intro k hk y hy
    exact (hρ.aestronglyMeasurable.smul (hm k hk y hy)).congr (heq k hk y hy).symm
  have hb' : ∀ k ≤ r, ∀ᵐ t ∂μ, ∀ y ∈ s,
      ‖iteratedFDeriv ℝ k (fun z ↦ ρ t • A t z) y‖ ≤ ‖ρ t‖ * C k := by
    intro k hk
    filter_upwards [hA, hb k hk] with t ht ht' y hy
    rw [iteratedFDeriv_const_smul_apply' ((ht y hy).of_le (by exact_mod_cast hk)), norm_smul]
    exact mul_le_mul_of_nonneg_left (ht' y hy) (norm_nonneg _)
  calc
    _ = ∫ t, iteratedFDeriv ℝ j (fun y ↦ ρ t • A t y) x ∂μ :=
      iteratedFDeriv_integral_of_dominated hs
        (hA.mono fun t ht y hy ↦ (ht y hy).const_smul (ρ t)) hm'
        (fun k _ ↦ hρ.norm.mul_const (C k)) hb' hj hx
    _ = _ := integral_congr_ae (heq j hj x hx)

/-- `app:ch_lag:prop:lag-envelopes`: synthesis preserves each finite derivative budget,
with only the integral of the density norm as the multiplicative cost. -/
theorem cNorm_synthesis_le (hs : IsOpen s) (hρ : Integrable ρ μ)
    (hA : ∀ᵐ t ∂μ, ∀ x ∈ s, ContDiffAt ℝ r (A t) x)
    (hm : ∀ j ≤ r, ∀ x ∈ s,
      AEStronglyMeasurable (fun t ↦ iteratedFDeriv ℝ j (A t) x) μ)
    (hb : ∀ j ≤ r, ∀ᵐ t ∂μ, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (A t) x‖ ≤ C j)
    (hC : ∀ j ≤ r, 0 ≤ C j) {K : Set X} (hK : K ⊆ s) :
    cNorm K r (fun y ↦ synthesis μ ρ (fun t ↦ A t y)) ≤
      densityMass μ ρ * ∑ j ∈ Finset.range (r + 1), C j := by
  rw [Finset.mul_sum]
  apply cNorm_le_sum_of_bounds (fun j hj ↦ mul_nonneg (densityMass_nonneg μ ρ) (hC j hj))
  intro j hj x hx
  rw [iteratedFDeriv_synthesis hs hρ hA hm hb hj (hK hx)]
  exact norm_synthesis_le hρ ((hb j hj).mono fun t ht ↦ ht x (hK hx))

end Complex

end MeasureEnvelopes
end JanetCartan
