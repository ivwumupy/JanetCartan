module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceMultiplier.OperatorLimit
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# A fixed family of smooth physical-frequency cutoffs

The regularization in `app:ch_regular_base:thm:actual-calculus`, Step 1,
uses a single fixed profile, dilated by `j + 1`. The cycle-frequency symbol
explicitly substitutes `η = 2πξ`. These definitions are shared by the
literal graph convergence and the multipliers on vector-valued Lebesgue L².
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff

variable {n r : ℕ}

/-- Fixed smooth profile with radii one and two for the frequency regularization
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def profile : ContDiffBump (0 : Euclidean n) := ⟨1, 2, by norm_num, by norm_num⟩

/-- Expanding physical-frequency radius for Step 1 of
`app:ch_regular_base:thm:actual-calculus`. -/
def radius (j : ℕ) : ℝ := (j : ℝ) + 1

/-- The regularization radius is positive (same Step 1). -/
theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

/-- The regularization never shrinks the fixed profile (same Step 1). -/
theorem one_le_radius (j : ℕ) : 1 ≤ radius j := by
  unfold radius
  linarith [Nat.cast_nonneg (α := ℝ) j]

/-- The actual real cutoff `χ_j(η)` used to remove frequency regularization
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def physicalCutoff (j : ℕ) (η : Euclidean n) : ℝ := profile ((radius j)⁻¹ • η)

/-- Smoothness of the actual cutoff (same Step 1). -/
theorem physicalCutoff_contDiff (j : ℕ) : ContDiff ℝ ∞ (physicalCutoff (n := n) j) :=
  profile.contDiff.comp (contDiff_id.const_smul _)

/-- The cutoff has compact frequency support; no source cutoff is introduced
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem physicalCutoff_hasCompactSupport (j : ℕ) :
    HasCompactSupport (physicalCutoff (n := n) j) := by
  let e : Euclidean n ≃L[ℝ] Euclidean n :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (radius j)⁻¹ (inv_ne_zero (radius_pos j).ne'))
  exact profile.hasCompactSupport.comp_homeomorph e.toHomeomorph

/-- Positivity of the cutoff gives real self-adjoint multipliers in Step 1
of `app:ch_regular_base:thm:actual-calculus`. -/
theorem physicalCutoff_nonneg (j : ℕ) (η : Euclidean n) : 0 ≤ physicalCutoff j η :=
  profile.nonneg

/-- The cutoff is bounded by one, giving contractions in the same Step 1. -/
theorem physicalCutoff_le_one (j : ℕ) (η : Euclidean n) : physicalCutoff j η ≤ 1 :=
  profile.le_one

/-- The cutoff is exactly one on the expanding closed ball (same Step 1). -/
theorem physicalCutoff_eq_one (j : ℕ) {η : Euclidean n} (hη : ‖η‖ ≤ radius j) :
    physicalCutoff j η = 1 := by
  apply profile.one_of_mem_closedBall
  change dist ((radius j)⁻¹ • η) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (radius_pos j).le)]
  exact (inv_mul_le_iff₀ (radius_pos j)).mpr (by simpa using hη)

/-- The cutoff vanishes outside twice the expanding radius (same Step 1). -/
theorem physicalCutoff_eq_zero (j : ℕ) {η : Euclidean n} (hη : 2 * radius j ≤ ‖η‖) :
    physicalCutoff j η = 0 := by
  apply profile.zero_of_le_dist
  change 2 ≤ dist ((radius j)⁻¹ • η) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (radius_pos j).le)]
  exact (le_inv_mul_iff₀ (radius_pos j)).mpr (by nlinarith)

/-- Eventual equality on each physical covector, used by dominated convergence
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem physicalCutoff_eventually_eq_one (η : Euclidean n) :
    ∀ᶠ j : ℕ in atTop, physicalCutoff j η = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖η‖
  filter_upwards [eventually_ge_atTop N] with j hj
  apply physicalCutoff_eq_one
  have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
  dsimp [radius]
  linarith

/-- The actual cutoffs converge pointwise to one (same Step 1). -/
theorem physicalCutoff_tendsto (η : Euclidean n) :
    Tendsto (fun j ↦ physicalCutoff j η) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (physicalCutoff_eventually_eq_one η))

/-- All derivatives obey the scaled bounds for the fixed profile. The constant
depends only on the derivative order and dimension, not on the radius, as needed
by the uniform normal estimate in `app:ch_regular_base:thm:actual-calculus`. -/
theorem physicalCutoff_scaled_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (η : Euclidean n),
      ‖iteratedFDeriv ℝ k (physicalCutoff j) η‖ ≤ (radius j)⁻¹ ^ k * C := by
  let f := (profile (n := n)).hasCompactSupport.toSchwartzMap profile.contDiff
  refine ⟨SchwartzMap.seminorm ℝ 0 k f, apply_nonneg _ _, fun j η ↦ ?_⟩
  change ‖iteratedFDeriv ℝ k (fun y : Euclidean n ↦ profile ((radius j)⁻¹ • y)) η‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul _ profile.contDiff, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (radius_pos j).le) _)]
  exact mul_le_mul_of_nonneg_left (f.norm_iteratedFDeriv_le_seminorm ℝ k _)
    (pow_nonneg (inv_nonneg.mpr (radius_pos j).le) _)

/-- Uniform symbol bounds for every finite derivative of the cutoff. This is the
weighted version consumed by the normal-amplitude low bound in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem physicalCutoff_uniform_symbol_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (η : Euclidean n),
      ‖iteratedFDeriv ℝ k (physicalCutoff j) η‖ * (1 + ‖η‖) ^ k ≤ C := by
  have hcont : Continuous (fun η : Euclidean n ↦
      ‖iteratedFDeriv ℝ k (profile (n := n)) η‖ * (1 + ‖η‖) ^ k) :=
    ((profile.contDiff : ContDiff ℝ ∞ (profile (n := n))).continuous_iteratedFDeriv (by simp)).norm.mul
      ((continuous_const.add continuous_norm).pow k)
  have hcompact : HasCompactSupport (fun η : Euclidean n ↦
      ‖iteratedFDeriv ℝ k (profile (n := n)) η‖ * (1 + ‖η‖) ^ k) :=
    (profile.hasCompactSupport.iteratedFDeriv k).norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
  refine ⟨max 0 C, le_max_left _ _, fun j η ↦ ?_⟩
  have hi : 0 ≤ (radius j)⁻¹ := inv_nonneg.mpr (radius_pos j).le
  have hi1 : (radius j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius j)
  change ‖iteratedFDeriv ℝ k (fun y : Euclidean n ↦ profile ((radius j)⁻¹ • y)) η‖ * _ ≤ _
  rw [iteratedFDeriv_comp_const_smul _ profile.contDiff, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hi _)]
  calc
    _ = ‖iteratedFDeriv ℝ k (profile (n := n)) ((radius j)⁻¹ • η)‖ *
        ((radius j)⁻¹ * (1 + ‖η‖)) ^ k := by rw [mul_pow]; ring
    _ ≤ ‖iteratedFDeriv ℝ k (profile (n := n)) ((radius j)⁻¹ • η)‖ *
        (1 + ‖(radius j)⁻¹ • η‖) ^ k := by
      gcongr
      rw [norm_smul, Real.norm_of_nonneg hi]
      nlinarith
    _ ≤ max 0 C := (le_abs_self _).trans ((hC _).trans (le_max_right _ _))

/-- Complex scalar form of the real physical cutoff, for the literal graph
amplitude in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def complexPhysicalCutoff (j : ℕ) (η : Euclidean n) : ℂ := physicalCutoff j η

/-- Smoothness of the complex scalar cutoff (same Step 1). -/
theorem complexPhysicalCutoff_contDiff (j : ℕ) :
    ContDiff ℝ ∞ (complexPhysicalCutoff (n := n) j) :=
  Complex.ofRealCLM.contDiff.comp (physicalCutoff_contDiff j)

/-- Compact physical frequency support of the complex cutoff (same Step 1). -/
theorem complexPhysicalCutoff_hasCompactSupport (j : ℕ) :
    HasCompactSupport (complexPhysicalCutoff (n := n) j) :=
  (physicalCutoff_hasCompactSupport j).comp_left (by simp)

/-- The complex cutoff has modulus at most one (same Step 1). -/
theorem complexPhysicalCutoff_norm_le (j : ℕ) (η : Euclidean n) :
    ‖complexPhysicalCutoff j η‖ ≤ 1 := by
  simpa [complexPhysicalCutoff, Complex.norm_real, Real.norm_of_nonneg
    (physicalCutoff_nonneg j η)] using physicalCutoff_le_one j η

/-- The complex physical cutoffs tend to one (same Step 1). -/
theorem complexPhysicalCutoff_tendsto (η : Euclidean n) :
    Tendsto (fun j ↦ complexPhysicalCutoff j η) atTop (𝓝 1) := by
  exact_mod_cast (Complex.continuous_ofReal.tendsto 1).comp (physicalCutoff_tendsto η)

/-- The multiplier symbol in Mathlib's cycle frequency: the physical covector
is exactly `η = 2πξ`, as required by `app:ch_regular_base:thm:actual-calculus`. -/
def cycleCutoff (j : ℕ) (ξ : Euclidean n) : ℂ :=
  complexPhysicalCutoff j ((2 * Real.pi) • ξ)

/-- Smoothness of the cycle-frequency multiplier symbol (same Step 1). -/
theorem cycleCutoff_contDiff (j : ℕ) : ContDiff ℝ ∞ (cycleCutoff (n := n) j) :=
  (complexPhysicalCutoff_contDiff j).comp (contDiff_id.const_smul _)

/-- The cycle-frequency symbol is compactly supported (same Step 1). -/
theorem cycleCutoff_hasCompactSupport (j : ℕ) :
    HasCompactSupport (cycleCutoff (n := n) j) := by
  let e : Euclidean n ≃L[ℝ] Euclidean n :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (2 * Real.pi) (by positivity))
  exact (complexPhysicalCutoff_hasCompactSupport j).comp_homeomorph e.toHomeomorph

/-- The smooth cycle symbol acts on Schwartz inputs (same Step 1). -/
theorem cycleCutoff_hasTemperateGrowth (j : ℕ) :
    (cycleCutoff (n := n) j).HasTemperateGrowth :=
  ((cycleCutoff_hasCompactSupport j).toSchwartzMap (cycleCutoff_contDiff j)).hasTemperateGrowth

/-- Modulus bound for the cycle multiplier, used for its L² contraction
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem cycleCutoff_norm_le (j : ℕ) (ξ : Euclidean n) : ‖cycleCutoff j ξ‖ ≤ 1 :=
  complexPhysicalCutoff_norm_le _ _

/-- Reality of the cycle symbol, used for its Hilbert adjoint (same Step 1). -/
theorem cycleCutoff_star (j : ℕ) (ξ : Euclidean n) : star (cycleCutoff j ξ) = cycleCutoff j ξ :=
  Complex.conj_ofReal _

/-- Pointwise convergence of the cycle symbol, used for strong L² convergence
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem cycleCutoff_tendsto (ξ : Euclidean n) :
    Tendsto (fun j ↦ cycleCutoff j ξ) atTop (𝓝 1) :=
  complexPhysicalCutoff_tendsto _

/-- Pointwise convergence of the literal source-first graph on Schwartz data,
for the actual constructed smooth cutoffs. This uses only continuity and a
polynomial amplitude bound, not a bounded graph operator. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphOperator_tendsto
    (S : Euclidean n → Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (u : SchwartzMap (Euclidean n) (Fin r → ℂ)) (x : Euclidean n)
    (hS : Continuous (S x)) (hA : Continuous (A x))
    (C : ℝ) (k : ℕ) (hbound : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    Tendsto (fun j ↦ graphOperator S (fun z _ η ↦ complexPhysicalCutoff j η • A z η) u x)
      atTop (𝓝 (graphOperator S (fun z _ η ↦ A z η) u x)) :=
  graphOperator_tendsto_frequencyCutoff S A u x hS hA C k hbound complexPhysicalCutoff
    (fun j ↦ (complexPhysicalCutoff_contDiff j).continuous)
    complexPhysicalCutoff_norm_le complexPhysicalCutoff_tendsto

end JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff
