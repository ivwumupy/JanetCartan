module

public import JanetCartan.Analysis.Microlocal.Localization.PhysicalPlancherel
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier

/-!
# Literal bounded Fourier masks on the original source

The inactive source factors in `app:ch_response:thm:response-literal-transfer`
act on Euclidean Lebesgue L². Their symbols are evaluated at the physical
covector `η = 2πξ`. Source and target physical multipliers retain their order.
No decay estimate is assumed in the construction.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "H" => Lp F 2 (volume : Measure E)

/-- A supplied bounded measurable scalar symbol in physical covectors, for
`app:ch_response:thm:response-literal-transfer`. Smoothness is unnecessary for
its L² realization. The same object also represents a physical cutoff. -/
structure BoundedMask (d : ℕ) where
  symbol : EuclideanSpace ℝ (Fin d) → ℂ
  measurable : StronglyMeasurable symbol
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ η, ‖symbol η‖ ≤ bound

namespace BoundedMask

/-- Bounded multiplication preserves genuine L² membership in
`app:ch_response:thm:response-literal-transfer`. -/
theorem memLp_smul (m : BoundedMask d) (f : H) :
    MemLp (fun x ↦ m.symbol x • f x) 2 volume := by
  apply ((Lp.memLp f).const_smul m.bound).mono
    (m.measurable.aestronglyMeasurable.smul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖m.symbol x • f x‖ ≤ ‖m.bound • f x‖
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg m.bound_nonneg] using
    mul_le_mul_of_nonneg_right (m.norm_le x) (norm_nonneg (f x))

/-- Literal multiplication on L² for the physical cutoffs in
`app:ch_response:thm:response-literal-transfer`. -/
def multiply (m : BoundedMask d) (f : H) : H := (m.memLp_smul f).toLp _

/-- The multiplication representative in
`app:ch_response:thm:response-literal-transfer`. -/
theorem multiply_ae (m : BoundedMask d) (f : H) :
    m.multiply f =ᵐ[volume] fun x ↦ m.symbol x • f x :=
  (m.memLp_smul f).coeFn_toLp

/-- The actual L² multiplication bound in
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_multiply_le (m : BoundedMask d) (f : H) :
    ‖m.multiply f‖ ≤ m.bound * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [m.multiply_ae f] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (m.norm_le x) (norm_nonneg _)

/-- Cutoff multiplication is linear on the actual L² space in
`app:ch_response:thm:response-literal-transfer`. -/
theorem multiply_sub (m : BoundedMask d) (f g : H) :
    m.multiply (f - g) = m.multiply f - m.multiply g := by
  apply Lp.ext
  filter_upwards [m.multiply_ae (f - g), m.multiply_ae f, m.multiply_ae g,
    Lp.coeFn_sub f g, Lp.coeFn_sub (m.multiply f) (m.multiply g)] with x h h₁ h₂ h₃ h₄
  simp only [h, h₁, h₂, h₃, h₄, Pi.sub_apply, smul_sub]

/-- Physical covectors and Mathlib frequencies are related by `η = 2πξ`
(`app:ch_response:thm:response-literal-transfer`). -/
def atUnitFrequency (m : BoundedMask d) : BoundedMask d where
  symbol ξ := m.symbol ((2 * Real.pi) • ξ)
  measurable := m.measurable.comp_measurable (by fun_prop)
  bound := m.bound
  bound_nonneg := m.bound_nonneg
  norm_le ξ := m.norm_le _

variable [CompleteSpace F]

/-- The actual Euclidean L² Fourier multiplier for the supplied physical mask
in `app:ch_response:thm:response-literal-transfer`. -/
def fourierMultiplier (m : BoundedMask d) (f : H) : H :=
  𝓕⁻ (m.atUnitFrequency.multiply (𝓕 f))

/-- Exact Fourier representative of the actual multiplier in
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourierMultiplier_fourier_ae (m : BoundedMask d) (f : H) :
    (𝓕 (m.fourierMultiplier f) : H) =ᵐ[volume]
      fun ξ ↦ m.symbol ((2 * Real.pi) • ξ) • (𝓕 f) ξ := by
  simpa only [fourierMultiplier, fourier_fourierInv_eq, atUnitFrequency] using
    m.atUnitFrequency.multiply_ae (𝓕 f)

/-- The bounded Fourier mask has the stated L² norm bound in
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_fourierMultiplier_le (m : BoundedMask d) (f : H) :
    ‖m.fourierMultiplier f‖ ≤ m.bound * ‖f‖ := by
  rw [← Lp.norm_fourier_eq (m.fourierMultiplier f)]
  simpa only [fourierMultiplier, fourier_fourierInv_eq, Lp.norm_fourier_eq, atUnitFrequency] using
    m.atUnitFrequency.norm_multiply_le (𝓕 f)

/-- The exact complementary symbol, including all shoulders, in
`app:ch_response:thm:response-literal-transfer`. -/
def complement (m : BoundedMask d) : BoundedMask d where
  symbol η := 1 - m.symbol η
  measurable := stronglyMeasurable_const.sub m.measurable
  bound := 1 + m.bound
  bound_nonneg := by linarith [m.bound_nonneg]
  norm_le η := (norm_sub_le _ _).trans (by simpa using add_le_add_left (m.norm_le η) 1)

/-- Exact complementary multiplier identity on the original L² source in
`app:ch_response:thm:response-literal-transfer`. -/
theorem complement_fourierMultiplier (m : BoundedMask d) (f : H) :
    m.complement.fourierMultiplier f = f - m.fourierMultiplier f := by
  apply (fourierEquiv ℂ H).injective
  change (𝓕 (m.complement.fourierMultiplier f) : H) = 𝓕 (f - m.fourierMultiplier f)
  have he : (𝓕 (f - m.fourierMultiplier f) : H) = 𝓕 f - 𝓕 (m.fourierMultiplier f) :=
    map_sub (fourierCLM ℂ H) _ _
  rw [he]
  apply Lp.ext
  filter_upwards [m.complement.fourierMultiplier_fourier_ae f,
    m.fourierMultiplier_fourier_ae f,
    Lp.coeFn_sub (𝓕 f) (𝓕 (m.fourierMultiplier f))] with ξ h₁ h₂ h₃
  rw [h₁, h₃]
  change (1 - m.symbol _) • (𝓕 f : H) ξ = (𝓕 f : H) ξ - (𝓕 (m.fourierMultiplier f) : H) ξ
  rw [h₂, sub_smul, one_smul]

omit [CompleteSpace F] in
/-- A physical cutoff equal to one on the actual source support is exactly
the identity, as used in `app:ch_response:thm:response-literal-transfer`. -/
theorem multiply_eq_of_one_on_support (χ : BoundedMask d) (f : H)
    (hχ : ∀ᵐ x ∂volume, f x ≠ 0 → χ.symbol x = 1) : χ.multiply f = f := by
  apply Lp.ext
  filter_upwards [χ.multiply_ae f, hχ] with x hx hplateau
  by_cases hf : f x = 0
  · simp [hx, hf]
  · simp [hx, hplateau hf]

/-- The full ordered source factor in
`app:ch_response:thm:response-literal-transfer`: target cutoff, Fourier mask,
then source cutoff. -/
def localized (m χout χin : BoundedMask d) (f : H) : H :=
  χout.multiply (m.fourierMultiplier (χin.multiply f))

/-- Inactive factors act on the original source when its source cutoff is
one (`app:ch_response:thm:response-literal-transfer`). The target cutoff
remains on the left of the Fourier multiplier. -/
theorem localized_eq_on_supported_source (m χout χin : BoundedMask d) (f : H)
    (hin : ∀ᵐ x ∂volume, f x ≠ 0 → χin.symbol x = 1) :
    m.localized χout χin f = χout.multiply (m.fourierMultiplier f) := by
  rw [localized, χin.multiply_eq_of_one_on_support f hin]

/-- The literal `A₊ - I` identity on an original supported carrier source,
including the sign and cutoff order
(`app:ch_response:thm:response-literal-transfer`). -/
theorem localized_sub_identity (m χout χin : BoundedMask d) (f : H)
    (hin : ∀ᵐ x ∂volume, f x ≠ 0 → χin.symbol x = 1)
    (hout : ∀ᵐ x ∂volume, f x ≠ 0 → χout.symbol x = 1) :
    m.localized χout χin f - f =
      -χout.multiply (m.complement.fourierMultiplier f) := by
  rw [m.localized_eq_on_supported_source χout χin f hin,
    m.complement_fourierMultiplier f, χout.multiply_sub,
    χout.multiply_eq_of_one_on_support f hout, neg_sub]

omit [CompleteSpace F] in
/-- Support plateaus can be checked on the original envelope before carrier
modulation (`app:ch_response:thm:response-literal-transfer`). -/
theorem carrier_plateau (χ : BoundedMask d) (f : E → F) (ρ : ℝ) (φ : E → ℝ)
    (hχ : ∀ x ∈ Function.support f, χ.symbol x = 1) (x : E)
    (hx : carrier ρ φ x • f x ≠ 0) : χ.symbol x = 1 := by
  apply hχ x
  intro hf
  exact hx (by rw [hf, smul_zero])

end BoundedMask
end JanetCartan.ResponseTransfer.Complement.InactiveSource
