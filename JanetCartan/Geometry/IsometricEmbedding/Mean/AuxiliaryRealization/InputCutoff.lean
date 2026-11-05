module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff

/-!
# Ordered cutoff of raw auxiliary data

The raw squared Fourier multiplier in `app:ch_background:defn:bg-mixed` and
`app:ch_background:eq:bg-Vaux`. This module uses the actual unit-torus cutoff
and applies the physical source cutoff after both Fourier cuts. It stops before
the Bessel potential and does not identify a continuous input with the image
component of the as-yet unconstructed continuum adjoint.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.AuxiliaryRealization

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The raw auxiliary input multiplier `π_K²` in `app:ch_background:defn:bg-mixed`.
Both copies of the Fourier cutoff precede multiplication by the source cutoff. -/
def squaredCutoff (K : ℝ) (h : Torus n → F) : Torus n → F :=
  periodicCutoff K (periodicCutoff K h)

/-- The raw cut data are smooth periodic (`app:ch_background:eq:bg-Vaux`). -/
theorem isSmoothPeriodic_squaredCutoff (K : ℝ) (h : Torus n → F) :
    IsSmoothPeriodic (squaredCutoff K h) :=
  isSmoothPeriodic_periodicCutoff K (periodicCutoff K h)

/-- The literal squared multiplier identity from `app:ch_background:defn:bg-mixed`.
This uses physical frequencies `2π k` from the shared unit-torus convention. -/
theorem periodicFourierCoeff_squaredCutoff [CompleteSpace F]
    {h : Torus n → F} (hh : Continuous h) {K : ℝ} (hK : 0 < K) (k : Fin n → ℤ) :
    periodicFourierCoeff (squaredCutoff K h) k =
      (periodicCutoffSymbol K k) ^ 2 • periodicFourierCoeff h k := by
  rw [squaredCutoff,
    periodicFourierCoeff_periodicCutoff (isSmoothPeriodic_periodicCutoff K h).1 hK,
    periodicFourierCoeff_periodicCutoff hh hK, smul_smul, pow_two]

/-- The exact raw support bound in `app:ch_background:defn:bg-mixed` applies before
the physical source cutoff. No Fourier support assertion is made after that cutoff. -/
theorem hasFourierSupport_squaredCutoff [CompleteSpace F]
    (h : Torus n → F) {K : ℝ} (hK : 0 < K) :
    HasFourierSupport (2 * K) (squaredCutoff K h) :=
  hasFourierSupport_periodicCutoff (isSmoothPeriodic_periodicCutoff K h).1 hK

/-- The raw multiplier is exactly one on the inner band
(`app:ch_background:defn:bg-mixed`). -/
theorem periodicFourierCoeff_squaredCutoff_of_le [CompleteSpace F]
    {h : Torus n → F} (hh : Continuous h) {K : ℝ} (hK : 0 < K)
    {k : Fin n → ℤ} (hk : frequencyNorm k ≤ K) :
    periodicFourierCoeff (squaredCutoff K h) k = periodicFourierCoeff h k := by
  rw [periodicFourierCoeff_squaredCutoff hh hK, periodicCutoffSymbol_eq_one hK hk]
  simp

/-- The input `χ_src π_K² h_im` to the Bessel potential in
`app:ch_background:eq:bg-Vaux`, expressed in physical coordinates. -/
def sourceCutInput (χ : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ) (h : Torus n → F) :
    EuclideanSpace ℝ (Fin n) → F :=
  fun x ↦ χ x • periodicLift (squaredCutoff K h) x

/-- Smoothness of the ordered physical source in `app:ch_background:eq:bg-Vaux`. -/
theorem contDiff_sourceCutInput {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (K : ℝ) (h : Torus n → F) :
    ContDiff ℝ ∞ (sourceCutInput χ K h) :=
  hχ.smul (isSmoothPeriodic_squaredCutoff K h).2

/-- The source cutoff controls physical support after the raw Fourier cut
(`app:ch_background:eq:bg-Vaux`). This is a statement before the nonlocal
Bessel potential, not a support assertion for the realized covector. -/
theorem support_sourceCutInput_subset (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : ℝ) (h : Torus n → F) :
    Function.support (sourceCutInput χ K h) ⊆ Function.support χ := by
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp [sourceCutInput, hx]

end JanetCartan.AuxiliaryRealization
