module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Integration
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh

/-!
# The fixed nonlinear operation in the transport density

The consumer is the normalized-shell estimate for
`app:ch_background:eq:bg-full-complex-amplitude`. The array contains primitive
values only; neither a density nor a reciprocal Jacobian is an array entry.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol

/-- Primitive values, ordered as the two measurements, angular and high masks,
Jacobian, covector, two normals, and two reduced covectors. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
abbrev ShellPrimitiveValues (n N : ℕ) :=
  (ℝ × ℝ × ℝ × ℝ × ℝ) ×
    (Euclidean (n - 1) × Euclidean N × Euclidean N × (Fin n → ℝ) × (Fin n → ℝ))

/-- The primitive evaluation array before inverse substitution. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
def shellPrimitiveValues {n N : ℕ} (a : Coefficients n N)
    (J : InputVariables n → ℝ) (p : InputVariables n) : ShellPrimitiveValues n N :=
  ((a.measurement p.1.1, a.measurement p.1.2,
    a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2), a.high ‖p.2.2‖, J p),
    p.2.2, a.normal (p.1.1, p.2.1), a.normal (p.1.2, p.2.1),
    a.reduced (p.1.1, p.2.1), a.reduced (p.1.2, p.2.1))

/-- Fixed algebraic operation; the varying fields occur only in its input.
Source: `app:ch_regular_base:eq:joint-primitive-product`. -/
def shellDensityCoefficient {n N : ℕ} (p : ShellPrimitiveValues n N) :
    Matrix (Fin n) (Fin n) ℝ :=
  (p.1.1 * p.1.2.1 * p.1.2.2.1 ^ 2 * p.1.2.2.2.1 ^ 2 *
    ‖p.2.1‖ / p.1.2.2.2.2 * ‖p.2.2.1‖ ^ 2 * ‖p.2.2.2.1‖ ^ 2) •
    Matrix.vecMulVec p.2.2.2.2.1 p.2.2.2.2.2

/-- This factorization is of the exact published density, retaining both
positions and every cutoff (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem inputDensity_eq_shellDensityCoefficient {n N : ℕ} (a : Coefficients n N)
    (J : InputVariables n → ℝ) :
    inputDensity a J = shellDensityCoefficient ∘ shellPrimitiveValues a J := rfl

/-- The coefficient operation is smooth away from the two actual gaps.
Source: `app:ch_background:eq:bg-jacobian`. -/
theorem shellDensityCoefficient_contDiffAt {n N : ℕ} {p : ShellPrimitiveValues n N}
    (hJ : p.1.2.2.2.2 ≠ 0) (hη : p.2.1 ≠ 0) :
    ContDiffAt ℝ ∞ (@shellDensityCoefficient n N) p := by
  have hw : ContDiffAt ℝ ∞ (fun p : ShellPrimitiveValues n N ↦
      p.1.1 * p.1.2.1 * p.1.2.2.1 ^ 2 * p.1.2.2.2.1 ^ 2 *
      ‖p.2.1‖ / p.1.2.2.2.2 * ‖p.2.2.1‖ ^ 2 * ‖p.2.2.2.1‖ ^ 2) p :=
    (((((contDiffAt_fst.fst.mul contDiffAt_fst.snd.fst).mul
      (contDiffAt_fst.snd.snd.fst.pow 2)).mul
      (contDiffAt_fst.snd.snd.snd.fst.pow 2)).mul
      (contDiffAt_snd.fst.norm ℝ hη)).div contDiffAt_fst.snd.snd.snd.snd hJ).mul
      (contDiffAt_snd.snd.fst.norm_sq ℝ) |>.mul (contDiffAt_snd.snd.snd.fst.norm_sq ℝ)
  let e : (Fin n × Fin n → ℝ) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun g i j ↦ g (i, j)
      invFun := fun A ij ↦ A ij.1 ij.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e.toContinuousLinearEquiv.contDiff.contDiffAt.comp p
    (contDiffAt_pi.mpr fun ij ↦ hw.mul
      ((contDiffAt_pi.mp contDiffAt_snd.snd.snd.snd.fst ij.1).mul
        (contDiffAt_pi.mp contDiffAt_snd.snd.snd.snd.snd ij.2)))

/-- Uniform finite jets of the fixed coefficient operation on a bounded
normalized shell, before any coefficient family varies. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_shellDensityCoefficient_jet_bound {n N : ℕ} (s : ℕ) (M : ℝ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C > 0, ∀ p : ShellPrimitiveValues n N, ‖p‖ ≤ M →
      δ ≤ |p.1.2.2.2.2| → ε ≤ ‖p.2.1‖ → ∀ k ≤ s,
      ‖iteratedFDeriv ℝ k shellDensityCoefficient p‖ ≤ C := by
  let K : Set (ShellPrimitiveValues n N) :=
    {p | ‖p‖ ≤ M ∧ δ ≤ |p.1.2.2.2.2| ∧ ε ≤ ‖p.2.1‖}
  have hc : IsCompact K := (isCompact_closedBall (0 : ShellPrimitiveValues n N) M).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter
        ((isClosed_le continuous_const continuous_fst.snd.snd.snd.snd.abs).inter
          (isClosed_le continuous_const continuous_snd.fst.norm)))
      (fun p hp ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1)
  have hb (k : ℕ) : ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (@shellDensityCoefficient n N) p‖ ≤ C := by
    apply hc.exists_bound_of_continuousOn
    intro p hp
    exact ((shellDensityCoefficient_contDiffAt
      (abs_pos.mp (hδ.trans_le hp.2.1))
      (norm_pos_iff.mp (hε.trans_le hp.2.2))).continuousAt_iteratedFDeriv
        (by simp)).continuousWithinAt
  choose C hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range (s + 1), |C k|, by positivity, ?_⟩
  intro p hp hJ hη k hk
  have ht := Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i))
    (Finset.mem_range.mpr (by omega : k < s + 1))
  have hh := hC k p ⟨hp, hJ, hη⟩
  linarith [le_abs_self (C k)]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
