module
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Rescaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Finite symbol bounds on frequency shells

For `app:ch_regular_base:eq:actual-pdo-remainder`, rescaled joint derivatives
measure both physical positions and the frequency on the fixed annulus
`1 ≤ ‖ξ‖ ≤ 2`. The full remainder lowers the order from `m` to `m - 1`
and uses primitive jets only through `n + 2`. The constant is linear in the
primitive bound; the fixed cutoff contributes derivatives through `n + 1`.

These estimates concern the actual Taylor/divergence amplitude. The existence
and identities of unregularized oscillatory operators remain separate.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
universe u v
namespace JanetCartan.Pseudodifferential
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The rescaled joint derivative bounds of
`app:ch_regular_base:setup:finite-calculus`, on all shells of radius at least one.
Physical positions range over the whole chart representatives. Low frequencies
are covered separately by the unweighted joint bounds. -/
def HasAmplitudeShellBound (c : V → V → V → F) (m : ℝ) (n : ℕ) (A : ℝ) : Prop :=
  ∀ ρ : ℝ, 1 ≤ ρ → ∀ p : V × V × V, 1 ≤ ‖p.2.2‖ → ‖p.2.2‖ ≤ 2 →
    ∀ k ≤ n, ‖iteratedFDeriv ℝ k (fun q : V × V × V ↦ c q.1 q.2.1 (ρ • q.2.2)) p‖ ≤ ρ ^ m * A

variable [FiniteDimensional ℝ V]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the explicit full remainder has
order `m - 1`, fixed shift two, and a constant linear in the primitive amplitude
bound. Every derivative of the fixed source cutoff is included. -/
theorem HasAmplitudeShellBound.diagonalRemainderAmplitude
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (m : ℝ) (n : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcBound : HasAmplitudeShellBound c m (n + 2) A)
    (hβBound : ∀ i ≤ n + 1, ∀ y, ‖iteratedFDeriv ℝ i β y‖ ≤ B) :
    HasAmplitudeShellBound (diagonalRemainderAmplitude b c β) (m - 1) n
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * 2 ^ (n + 1) * B * A) := by
  intro ρ hρ p hp₁ hp₂ k hk
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hpow : 0 ≤ ρ ^ m * A := mul_nonneg (Real.rpow_nonneg hρpos.le _) hA
  have hM : ∀ j ≤ k + 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (j + 1) (fun q : V × V × V ↦ c q.1 q.2.1 (ρ • q.2.2))
        (sourceSegmentMap t p)‖ ≤ ρ ^ m * A := by
    intro j hj t _
    exact hcBound ρ hρ (sourceSegmentMap t p) hp₁ hp₂ (j + 1) (by omega)
  have hsum : (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) *
      ‖iteratedFDeriv ℝ i β p.2.1‖ * (ρ ^ m * A)) ≤
      2 ^ (k + 1) * B * (ρ ^ m * A) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * B * (ρ ^ m * A) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_right _ hpow
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact hβBound i (by have := Finset.mem_range.mp hi; omega) p.2.1
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose (k + 1)
  calc
    _ ≤ ρ⁻¹ * (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) *
          ‖iteratedFDeriv ℝ i β p.2.1‖ * (ρ ^ m * A)) :=
      norm_iteratedFDeriv_diagonalRemainderAmplitude_rescaled_le b c β hc hβ ρ hρpos p k
        (fun _ ↦ ρ ^ m * A) hM
    _ ≤ ρ⁻¹ * (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        (2 ^ (k + 1) * B * (ρ ^ m * A))) := by gcongr
    _ = ρ ^ (m - 1) *
        (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * 2 ^ (k + 1) * B * A) := by
      rw [Real.rpow_sub_one hρpos.ne']
      ring
    _ ≤ _ := by
      gcongr
      norm_num
end JanetCartan.Pseudodifferential
