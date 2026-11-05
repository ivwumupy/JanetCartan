module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointFrequency

/-!
# Joint derivative bounds for the full diagonal remainder

For `app:ch_regular_base:eq:actual-pdo-remainder`, all three variables are
retained. Order `n` uses primitive derivatives only through `n + 2`, a fixed
shift independent of `n`. These statements concern actual constructed amplitudes;
they do not assume a bound for the remainder itself.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
universe u v
namespace JanetCartan.Pseudodifferential
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the full remainder is jointly smooth. -/
theorem contDiff_diagonalRemainderAmplitude_joint
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2)) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun p : V × V × V ↦ diagonalRemainderAmplitude b c β p.1 p.2.1 p.2.2) := by
  exact (contDiff_frequencyDivergence_joint b _ (contDiff_fullTaylorCoefficient_joint c β hc hβ)).const_smul
    (2 * Real.pi * Complex.I)⁻¹

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the complete remainder has joint derivative shift two, retaining every source-cutoff derivative. -/
theorem norm_iteratedFDeriv_diagonalRemainderAmplitude_joint_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (p : V × V × V) (n : ℕ) (M : ℕ → ℝ)
    (hM : ∀ k ≤ n + 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (k + 1) (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2)
        (sourceSegmentMap t p)‖ ≤ M k) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦ diagonalRemainderAmplitude b c β q.1 q.2.1 q.2.2) p‖ ≤
      ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) *
          ‖iteratedFDeriv ℝ i β p.2.1‖ * M (n + 1 - i) := by
  apply (norm_iteratedFDeriv_normalizedFrequencyDivergence_joint_le b _
    (contDiff_fullTaylorCoefficient_joint c β hc hβ) n p).trans
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_fullTaylorCoefficient_joint_le c β hc hβ p (n + 1) M hM)
    (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
end JanetCartan.Pseudodifferential
