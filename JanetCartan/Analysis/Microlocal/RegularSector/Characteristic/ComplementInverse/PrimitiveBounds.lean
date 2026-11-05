module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.PrimitiveBounds.Smoothness
public import JanetCartan.Analysis.ContDiff.Norm.Composition

/-!
# Primitive quantitative bounds for the characteristic complement inverse

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:complement-inverse`, the original matrix bound, selected
minor gap, and unnormalized transport gap determine a common displacement
interval and positive completion/bordered determinant gaps. They are chosen
before any smooth coefficient array `U = ((H,A),e)`.

On a fixed positive-radius closed ball, the literal map `minorComplementInverse`
has a single-high bound `C j * (1 + cNorm K j U)`. Compact-range composition
supplies the low norm and all outer derivative bounds, so no completion gap or
inverse budget is assumed. A primitive profile `P j * T ^ (j - R)` gives the
same profile for the inverse, with reserve loss zero, uniformly in the finite
jet order, reserve, scale, and array. Norms of all matrices are Frobenius norms.

Consumers: the parent construction of `W₁` and `Op(b₋₁ α)` in
`app:ch_regular_base:eq:complement-symbol`. That construction still supplies
its actual primitive arrays, original gaps, range inclusion and primitive jets.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Uniform single-high bounds for the same complement inverse, with no
derivative shift (`app:ch_regular_base:eq:complement-inverse`). The interval,
both determinant gaps, and all constants precede the primitive array. The
compact range lies in the open smooth domain of `minorComplementDomain_regular`.
Only the original minor/transport gaps and primitive matrix bound are inputs. -/
theorem exists_minorComplementInverse_primitive_tame (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (r c : ι) (M : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℕ → ℝ,
      (∀ j, 0 < C j) ∧
      (∀ p ∈ minorCoefficientClass r c M μ ν, ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det|) ∧
      (minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε ⊆
        minorComplementDomain r c) ∧
      ∀ j : ℕ, ∀ U : E → (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ,
        ContDiff ℝ ∞ U →
        MapsTo U (Metric.closedBall x ρ)
          (minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε) →
        cNorm (Metric.closedBall x ρ) j
          (fun y ↦ minorComplementInverse (U y).1.1 (U y).1.2 r c (U y).2) ≤
            C j * (1 + cNorm (Metric.closedBall x ρ) j U) := by
  obtain ⟨ε, hε, δ, hδ, hgap⟩ :=
    exists_minorCoefficientClass_determinant_gaps r c M hμ hν
  let t := minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε
  have ht : IsCompact t := (isCompact_minorCoefficientClass r c M μ ν).prod
    (isCompact_closedBall (0 : ℝ) ε)
  have hdomain : t ⊆ minorComplementDomain r c := by
    intro p hp
    refine ⟨⟨abs_pos.mp (hμ.trans_le hp.1.2.2.2.1),
      abs_pos.mp (hν.trans_le hp.1.2.2.2.2)⟩, ?_⟩
    exact abs_pos.mp (hδ.trans_le (hgap p.1 hp.1 p.2
      (by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        using hp.2)).1)
  have hconstants (j : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ U : E → (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ, ContDiff ℝ ∞ U →
        MapsTo U (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) j
          (fun y ↦ minorComplementInverse (U y).1.1 (U y).1.2 r c (U y).2) ≤
            C * (1 + cNorm (Metric.closedBall x ρ) j U) := by
    obtain ⟨C, hC, hbound⟩ := exists_cNorm_comp_le_tame_closedBall_of_compact_range
      (g := fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
        minorComplementInverse p.1.1 p.1.2 r c p.2)
      (r := j) (k := j) x hρ ht le_rfl
      (fun p hp ↦ (minorComplementDomain_regular r c).2.contDiffAt
        ((minorComplementDomain_regular r c (m := j)).1.mem_nhds (hdomain hp)))
    exact ⟨C, hC, hbound⟩
  choose C hC hbound using hconstants
  exact ⟨ε, hε, δ, hδ, C, hC, hgap, hdomain, hbound⟩

/-- Graded finite-jet bounds with fixed reserve loss zero for the actual
inverse (`app:ch_regular_base:lem:characteristic-kernel`). For every primitive
profile `P`, constants are chosen before the reserve `R`, truncation `N`, scale
`T ≥ 1`, and coefficient array. In particular no order-dependent reserve loss
or polynomial in the high norm is substituted for the single-high estimate. -/
theorem exists_minorComplementInverse_primitive_graded (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (r c : ι) (M : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) :
    ∃ ε > 0, ∃ δ > 0, ∃ D : ℕ → ℝ,
      (∀ j, 0 < D j) ∧
      (∀ p ∈ minorCoefficientClass r c M μ ν, ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det|) ∧
      (minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε ⊆
        minorComplementDomain r c) ∧
      ∀ R N : ℕ, ∀ T : ℝ, 1 ≤ T →
        ∀ U : E → (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ,
        ContDiff ℝ ∞ U →
        MapsTo U (Metric.closedBall x ρ)
          (minorCoefficientClass r c M μ ν ×ˢ Metric.closedBall (0 : ℝ) ε) →
        (∀ j ≤ N, cNorm (Metric.closedBall x ρ) j U ≤ P j * T ^ (j - R)) →
        ∀ j ≤ N, cNorm (Metric.closedBall x ρ) j
          (fun y ↦ minorComplementInverse (U y).1.1 (U y).1.2 r c (U y).2) ≤
            D j * T ^ (j - R) := by
  obtain ⟨ε, hε, δ, hδ, C, hC, hgap, hdomain, hbound⟩ :=
    exists_minorComplementInverse_primitive_tame x hρ r c M hμ hν
  refine ⟨ε, hε, δ, hδ, fun j ↦ C j * (1 + P j),
    fun j ↦ mul_pos (hC j) (by linarith [hP j]), hgap, hdomain, ?_⟩
  intro R N T hT U hU hUt hprofile j hj
  have hpow : 1 ≤ T ^ (j - R) := one_le_pow₀ hT
  calc
    _ ≤ C j * (1 + cNorm (Metric.closedBall x ρ) j U) := hbound j U hU hUt
    _ ≤ C j * (1 + P j * T ^ (j - R)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (hprofile j hj)) (hC j).le
    _ ≤ C j * ((1 + P j) * T ^ (j - R)) := by
      apply mul_le_mul_of_nonneg_left _ (hC j).le
      nlinarith
    _ = _ := by ring

end JanetCartan.RegularSector.Characteristic
