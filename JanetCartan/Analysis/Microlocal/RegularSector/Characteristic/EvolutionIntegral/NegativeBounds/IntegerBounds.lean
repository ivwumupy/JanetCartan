module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.VectorDuality

/-!
# Negative integer estimates from both positive retarded estimates

The positive premise below is exactly the conclusion supplied by
`exists_retardedOperator_integer_bounds_of_primitive_data`. The companion
primitive specialization discharges it for that constructor's SAME operator.
Source: `app:ch_regular_base:eq:negative-duality`; consumers are the original
sector residual and the remaining inverse estimate.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral
open Pseudodifferential
variable {n q : ℕ}
local notation "L²" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure (Euclidean n))

/-- Both positive estimates of the retarded constructor give both negative
estimates, with the literal Hilbert adjoint and one high quantity. For spatial
order `-o`, the fixed reserve becomes `μ+o`, and integration still costs `Δ`.
Source: `app:ch_regular_base:eq:negative-duality`. This implication alone is
conditional; `exists_retardedOperator_signed_integer_bounds_of_primitive_data`
supplies its actual primitive instantiation.
-/
theorem retarded_negative_integer_bounds_of_positive
    (Q : L² →L[ℂ] L²) (o μ : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (C H : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s) (hH : ∀ s, 0 ≤ H s)
    (hpos : ∀ s : ℕ, ∀ W : L² →L[ℂ] L², (W = Q ∨ W = Q.adjoint) →
      ∀ u, MemVectorFourierSobolev ((s-o : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤ (Δ * C s) *
            (vectorFourierSobolevNorm ((s-o : ℕ) : ℝ) u + H (s+μ) * ‖u‖))
    (k : ℕ) (W : L² →L[ℂ] L²) (hW : W = Q ∨ W = Q.adjoint) (u : L²) :
    MemVectorFourierSobolev (-(k : ℝ)) (W u) ∧
      vectorFourierSobolevNorm (-(k : ℝ)) (W u) ≤
        ((q : ℝ) * q * (Δ * C (k+o))) * (1 + H (k+o+μ)) *
          vectorFourierSobolevNorm (-((k+o : ℕ) : ℝ)) u := by
  have hWa : W.adjoint = Q ∨ W.adjoint = Q.adjoint := by
    rcases hW with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (ContinuousLinearMap.adjoint_adjoint Q)
  apply negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg k)
    (Nat.cast_nonneg (k+o)) (mul_nonneg hΔ (hC _)) (hH _) W _ u
  intro g hg
  simpa only [Nat.add_sub_cancel] using hpos (k+o) W.adjoint hWa g
    (by simpa only [Nat.add_sub_cancel] using hg)

/-- The `k=0`, gain-one endpoint on actual vector L² data, for both `R` and
`R*` in `app:ch_regular_base:eq:negative-duality`. No completion extension is
asserted: the right side is the genuine negative Fourier norm of the L² datum.
-/
theorem retarded_negative_one_to_L2_of_positive
    (Q : L² →L[ℂ] L²) (μ : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (C H : ℕ → ℝ) (hC : ∀ s, 0 ≤ C s) (hH : ∀ s, 0 ≤ H s)
    (hpos : ∀ s : ℕ, ∀ W : L² →L[ℂ] L², (W = Q ∨ W = Q.adjoint) →
      ∀ u, MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤ (Δ * C s) *
            (vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u + H (s+μ) * ‖u‖))
    (W : L² →L[ℂ] L²) (hW : W = Q ∨ W = Q.adjoint) (u : L²) :
    ‖W u‖ ≤ ((q : ℝ) * q * (Δ * C 1)) * (1 + H (1+μ)) *
      vectorFourierSobolevNorm (-1) u := by
  simpa only [Nat.zero_add, Nat.cast_zero, neg_zero, vectorFourierSobolevNorm_zero,
    Nat.cast_one] using
    (retarded_negative_integer_bounds_of_positive Q 1 μ hΔ C H hC hH hpos 0 W hW u).2

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral
