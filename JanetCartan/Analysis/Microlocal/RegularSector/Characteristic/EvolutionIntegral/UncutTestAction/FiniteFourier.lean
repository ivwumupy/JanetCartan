module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.MultiplierBudget
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.MultiplierSlices
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.CompositionBounds

/-!
# Finite derivative budgets for the original multiplier

The multiplier times the Fourier transform of a test has integrable derivatives
up to the supplied finite reserve. The existing finite-regularity Fourier decay
estimate then gives integrable spatial restrictions of its inverse transform.
Consumer: literal uncut multiplier-slice inversion in
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Topology ContDiff

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

open FourierIntegral KernelIdentification Pseudodifferential SymbolBudgets
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Fin q → ℂ

/-- Bounded derivatives of the original multiplier through order `N` suffice
for integrability of the same derivatives of its test frequency datum.
The bounds are produced by `norm_iteratedFDeriv_multiplier_le_normalized_budgets`
at orders at most the parent's reserve. No Schwartz regularity of the product
is asserted. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_iteratedFDeriv_multiplier_schwartz
    {n : ℕ} (β : Euclidean n → ℂ) (hβ : ContDiff ℝ ∞ β)
    (f : SchwartzMap (Euclidean n) V) (N : ℕ) (C : ℕ → ℝ)
    (hbound : ∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ C k)
    (k : ℕ) (hk : k ≤ N) :
    Integrable (iteratedFDeriv ℝ k (fun ξ ↦ β ξ • f ξ)) := by
  have hi (j : ℕ) : Integrable (fun ξ ↦ ‖iteratedFDeriv ℝ j f ξ‖) := by
    simpa using f.integrable_pow_mul_iteratedFDeriv volume 0 j
  apply (integrable_finsetSum (Finset.range (k + 1)) (fun j _ ↦
    (hi (k-j)).const_mul ((k.choose j : ℝ) * C j))).mono'
      (((hβ.smul (f.smooth ⊤)).continuous_iteratedFDeriv (m := k) (by simp)).aestronglyMeasurable)
  filter_upwards [] with ξ
  apply (norm_iteratedFDeriv_smul_le hβ (f.smooth ⊤) ξ (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hbound j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hk) ξ)
      (by positivity)) (norm_nonneg _)

/-- The physical inverse integral exists as an ordinary function under finite
budgets. This reuses Mathlib's function-valued Fourier inverse, with the same
physical-to-cycle rescaling as `physicalInverseSchwartz`. Consumer: the
original `Bβ` in `app:ch_regular_base:eq:fixed-time-representation`. -/
def physicalMultiplierIntegral (β : E → ℂ) (v : SchwartzMap E V) : E → V :=
  𝓕⁻ (fun ξ : E ↦ β ((2 * Real.pi) • ξ) •
    sourceInputFourierTransform v ((2 * Real.pi) • ξ))

/-- Finite symbol bounds give absolute convergence of the rescaled uncut
frequency datum. Consumer: continuity and inversion of the original multiplier
in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_multiplierFrequencyData
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) :
    Integrable (fun ξ ↦ β ξ • sourceInputFourierTransform v ξ) := by
  apply ((sourceInputFourierTransform v).integrable.norm.const_mul C).mono'
    (hβ.smul (sourceInputFourierTransform v).continuous).aestronglyMeasurable
  filter_upwards [] with ξ
  change ‖β ξ • sourceInputFourierTransform v ξ‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg _)

/-- The actual finite-budget multiplier has exactly the original physical
Fourier integral and normalization. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalMultiplierIntegral_eq_integral
    (β : E → ℂ) (v : SchwartzMap E V) (x : E) :
    physicalMultiplierIntegral β v x = ((2 * Real.pi) ^ (d + 1) : ℂ)⁻¹ •
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        (β ξ • sourceInputFourierTransform v ξ) :=
  fourierInv_physicalRescale_eq_integral
    (fun ξ ↦ β ξ • sourceInputFourierTransform v ξ) x

/-- The function-valued multiplier agrees with the earlier Schwartz-valued
one whenever its stronger all-order hypothesis holds. Thus the finite-budget
construction retains the original operator. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem physicalMultiplierIntegral_eq_physicalMultiplier
    (β : E → ℂ) (hβ : β.HasTemperateGrowth) (v : SchwartzMap E V) :
    physicalMultiplierIntegral β v = (physicalMultiplier β v : E → V) := by
  funext x
  rw [physicalMultiplierIntegral_eq_integral, physicalMultiplier_eq_integral β hβ]

private theorem cycleMultiplierData_eq (β : E → ℂ) (v : SchwartzMap E V) :
    (fun ξ : E ↦ β ((2 * Real.pi) • ξ) •
      sourceInputFourierTransform v ((2 * Real.pi) • ξ)) =
    (fun ξ : E ↦ β ((2 * Real.pi) • ξ) • (𝓕 v) ξ) := by
  funext ξ
  congr 1
  change (𝓕 v) ((2 * Real.pi)⁻¹ • ((2 * Real.pi) • ξ)) = (𝓕 v) ξ
  rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

private theorem integrable_cycleMultiplierData_jets
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β) (v : SchwartzMap E V)
    (N : ℕ) (C : ℕ → ℝ)
    (hbound : ∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ C k)
    (k : ℕ) (hk : k ≤ N) :
    Integrable (iteratedFDeriv ℝ k
      (fun ξ : E ↦ β ((2 * Real.pi) • ξ) • (𝓕 v) ξ)) := by
  apply integrable_iteratedFDeriv_multiplier_schwartz _
    (hβ.comp (contDiff_id.const_smul (2 * Real.pi))) (𝓕 v) N
    (fun j ↦ (2 * Real.pi) ^ j * C j) _ k hk
  intro j hj ξ
  change ‖iteratedFDeriv ℝ j (fun ξ : E ↦ β ((2 * Real.pi) • ξ)) ξ‖ ≤ _
  rw [congrFun (iteratedFDeriv_comp_const_smul (2 * Real.pi)
    (hβ.of_le (show (j : ℕ∞ω) ≤ ∞ by simp))) ξ, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hbound j hj _) (by positivity)

/-- Only `d+2` bounded symbol derivatives give decay of the original
spacetime multiplier. This is less than the parent's `fullLowReserve (d+1)`;
the Schwartz seminorms belong to the original test, not to the multiplier.
Consumer: integrability of every spatial slice in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_decay_physicalMultiplierIntegral
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β) (v : SchwartzMap E V)
    (C : ℕ → ℝ)
    (hbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ C k) :
    ∃ B ≥ 0, ∀ x, ‖physicalMultiplierIntegral β v x‖ ≤
      B * (1 + ‖x‖) ^ (-((d : ℝ) + 2)) := by
  let f : E → V := fun ξ ↦ β ((2 * Real.pi) • ξ) • (𝓕 v) ξ
  have hf : ContDiff ℝ ∞ f :=
    (hβ.comp (contDiff_id.const_smul (2 * Real.pi))).smul ((𝓕 v).smooth ⊤)
  have hi := integrable_cycleMultiplierData_jets β hβ v (d + 2) C hbound
  refine ⟨2 ^ (d + 2 - 1) * (1 + 2 ^ (d + 2)) * sourceDerivativeMass f (d + 2),
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun _ ↦ norm_nonneg _), ?_⟩
  intro x
  unfold physicalMultiplierIntegral
  rw [cycleMultiplierData_eq, Real.fourierInv_eq_fourier_neg]
  simpa only [norm_neg, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, sub_zero] using
    norm_fourier_le_of_sourceDerivativeMass f 0 (d + 2) (hf.of_le (by simp)) hi
      (sourceDerivativeMass f (d + 2)) (-x) (by simp)

/-- The finite-budget inverse multiplier is continuous. Consumer: its actual
spatial slice in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_physicalMultiplierIntegral
    (β : E → ℂ) (hβ : Continuous β) (v : SchwartzMap E V)
    (C : ℝ) (hbound : ∀ ξ, ‖β ξ‖ ≤ C) :
    Continuous (physicalMultiplierIntegral β v) := by
  have hi := (integrable_multiplierFrequencyData β hβ v C hbound).comp_smul
    (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  change Continuous (fun x : E ↦ 𝓕⁻ (fun ξ : E ↦ β ((2 * Real.pi) • ξ) •
    sourceInputFourierTransform v ((2 * Real.pi) • ξ)) x)
  simp_rw [Real.fourierInv_eq_fourier_neg]
  exact
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi).comp continuous_neg

/-- Every spatial restriction of the actual multiplier is integrable, from
only the finite symbol reserve. This discharges the integrability input to
pointwise spatial Fourier inversion, including every fixed time, in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_physicalMultiplierIntegral_spatialSlice
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β) (v : SchwartzMap E V)
    (C : ℕ → ℝ)
    (hbound : ∀ k ≤ d + 2, ∀ ξ, ‖iteratedFDeriv ℝ k β ξ‖ ≤ C k)
    (s : ℝ) : Integrable (fun y ↦ physicalMultiplierIntegral β v (timeSpacePoint s y)) := by
  obtain ⟨B, hB, hb⟩ := exists_decay_physicalMultiplierIntegral β hβ v C hbound
  have hc := continuous_physicalMultiplierIntegral β hβ.continuous v (C 0)
    (fun ξ ↦ by simpa only [norm_iteratedFDeriv_zero] using hbound 0 (by omega) ξ)
  apply ((integrable_one_add_norm (μ := (volume : Measure (Euclidean d)))
    (r := (d : ℝ) + 2) (by simp [Euclidean])).const_mul B).mono'
    (hc.comp (continuous_timeSpacePoint.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  filter_upwards [] with y
  apply (hb (timeSpacePoint s y)).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
    (show 1 + ‖y‖ ≤ 1 + ‖timeSpacePoint s y‖ from
      add_le_add_right (by simpa using norm_spatialPart_le (timeSpacePoint s y)) 1)
  linarith [Nat.cast_nonneg (α := ℝ) d]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction
