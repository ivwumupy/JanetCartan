module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly

import Mathlib.Tactic.Ring

/-!
# Choosing the accuracy of an individual localized factor

The scalar step in `app:ch_regular:eq:chain-tail`, consumed by
`finiteChain_sub_localized_rapidDecayAt`. The input estimate is the output of
`FiniteChain.Graph`, `FiniteChain.Retarded`, or `EvolutionIntegratedLocalization`.
Its frequency and slow-scale losses are fixed before the integration order.
No estimate for a composed chain is assumed here.
-/

@[expose] public noncomputable section

namespace JanetCartan.ArbitraryAccuracy

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Absorb the fixed losses in `app:ch_regular:eq:chain-tail`. Constants may
vary with integration order, while the vector family, domains, and losses do
not. This uses the existing finite-Neumann scale calculation. -/
theorem rapidDecayAt_of_factor_bounds
    (G : GradedScale F) (s : ℕ) (ρ L A : ι → ℝ) (v : ι → F)
    (σ c : ℝ) (b : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 0 ≤ L i) (hσ : 0 < σ)
    (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - σ)) (hA : ∀ i, 0 ≤ A i)
    (hbound : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      v i ∈ G.level s ∧ G.gradeNorm s (v i) ≤
        C * A i * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q) :
    RapidDecayAt G s ρ A v := by
  intro Q
  obtain ⟨q, _, hq⟩ := exists_finite_neumann_order hσ c Q b
  obtain ⟨C, hC, hv⟩ := hbound q
  refine ⟨C, hC, fun i ↦ ⟨(hv i).1, (hv i).2.trans ?_⟩⟩
  calc
    C * A i * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q =
        C * A i * ((ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q) := by ring
    _ ≤ C * A i * (ρ i) ^ (c + (b : ℝ) - σ * q) :=
      mul_le_mul_of_nonneg_left
        (finite_neumann_scale_bound (hρ i) (hL i) hσ.le (hscale i) b q)
        (mul_nonneg hC (hA i))
    _ ≤ C * A i * (ρ i) ^ (-Q) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hρ i) hq) (mul_nonneg hC (hA i))

/-- Apply a localized `L² → Hˢ` factor estimate to a family with a polynomial
L² bound. This pays for the preceding finitely many factors without
requiring a negative Sobolev estimate for their outputs
(`app:ch_regular:lem:finite-chain`). -/
theorem rapidDecayAt_localized_factor
    (G : GradedScale F) (s : ℕ) (ρ L A : ι → ℝ)
    (T : ι → E →ₗ[ℝ] F) (u : ι → E) (σ c : ℝ) (b : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 0 ≤ L i) (hσ : 0 < σ)
    (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - σ)) (hA : ∀ i, 0 ≤ A i)
    (hu : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖u i‖ ≤ D * A i * (ρ i) ^ a)
    (hbound : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
      T i v ∈ G.level s ∧ G.gradeNorm s (T i v) ≤
        C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖v‖) :
    RapidDecayAt G s ρ A (fun i ↦ T i (u i)) := by
  obtain ⟨D, a, hD, hu⟩ := hu
  apply rapidDecayAt_of_factor_bounds G s ρ L A _ σ (c + a) b hρ hL hσ hscale hA
  intro q
  obtain ⟨C, hC, hT⟩ := hbound q
  refine ⟨C * D, mul_nonneg hC hD, fun i ↦ ⟨(hT i (u i)).1, ?_⟩⟩
  have hρpos : 0 < ρ i := lt_of_lt_of_le zero_lt_one (hρ i)
  have hLi := hL i
  calc
    G.gradeNorm s (T i (u i)) ≤
        C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q * ‖u i‖ := (hT i (u i)).2
    _ ≤ C * (ρ i) ^ c * L i ^ b * (L i / ρ i) ^ q *
        (D * A i * (ρ i) ^ a) := mul_le_mul_of_nonneg_left (hu i) (by positivity)
    _ = (C * D) * A i * (ρ i) ^ (c + a) * L i ^ b * (L i / ρ i) ^ q := by
      rw [Real.rpow_add hρpos]
      ring

end JanetCartan.ArbitraryAccuracy
