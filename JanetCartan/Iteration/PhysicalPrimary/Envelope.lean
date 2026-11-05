module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.CompletionAssembly.PrimaryProfiles

/-!
# Retaining the inverse carrier in the physical primary jets

Paper-v2 `main:eq:lag-full-envelope`: the displacement envelope has a factor
`τ`, unlike the full derivative amplitude.  The existing graded physical
calculus is homogeneous in this envelope.  Retain that factor through
remodulation to obtain the sharp `λ^(r-1)` input for the real physical primary.

The original envelope is produced by
`CorrectedAtoms.fullCorrectedDisplacementAmplitude_joint_bounds`, with the
SAME response's displacement estimates.  This file does not construct that
response or assert a successful original-data wave family.  It closes only
the sharp remodulation deduction consumed by the physical sampled profiles.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.PhysicalPrimary

private theorem atomJetConstant_mul (τ : ℝ) (a s : ℕ → ℝ) (q : ℕ) :
    RawPrimary.atomJetConstant (fun j ↦ τ * a j) s q =
      τ * RawPrimary.atomJetConstant a s q := by
  simp only [RawPrimary.atomJetConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Remodulation preserves the original `τ` displacement factor.  The
phase and displacement profiles come from the SAME retained corrected atom;
no derivative profile of the final physical wave is assumed
(`main:eq:lag-full-envelope`, `main:eq:primary-fixed-scales`). -/
theorem physical_jets_le_of_displacement_envelope {n N : ℕ}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (φ : Euclidean n → ℝ) (A : Euclidean n → EuclideanSpace ℂ (Fin N))
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    (hmod : EqOn Z (fun x ↦ Complex.exp (Complex.I * (φ x : ℂ)) • A x) U)
    (a s : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 ≤ s j)
    {τ lam L : ℝ} (hτ : 0 ≤ τ) (hlam : 1 ≤ lam) (hL : 0 ≤ L) (hLlam : L ≤ lam)
    (hAj : ∀ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ j A x‖ ≤ τ * a j * L ^ j)
    (hφj : ∀ j, 1 ≤ j → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ s j * lam * L ^ (j - 1)) :
    ContDiffOn ℝ ∞ Z U ∧ ∀ q, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ q Z x‖ ≤
        ((2 : ℝ) ^ q * RawPrimary.atomJetConstant a s q) * τ * lam ^ q := by
  obtain ⟨hZ, hjet⟩ := UniformStep.primary_physical_jets_of_displacement_envelope
    hU Z φ A hφ hA hmod (fun j ↦ τ * a j) s
    (fun j ↦ mul_nonneg hτ (ha j)) hs hlam hL hLlam hAj hφj
  refine ⟨hZ, fun q x hx ↦ (hjet q x hx).trans_eq ?_⟩
  rw [atomJetConstant_mul]
  ring

/-- The radial comparison turns the same `τ` envelope into the sharp
`λ^(r-1)` physical jets, also at `r=0`.  This is the exact primary Sobolev
input in paper-v2 §15; the inverse carrier is NOT discarded. -/
theorem physical_jets_le_inverse_carrier {n N : ℕ}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (φ : Euclidean n → ℝ) (A : Euclidean n → EuclideanSpace ℂ (Fin N))
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    (hmod : EqOn Z (fun x ↦ Complex.exp (Complex.I * (φ x : ℂ)) • A x) U)
    (a s : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 ≤ s j)
    {τ lam L Cτ : ℝ} (hτ : 0 ≤ τ) (hlam : 1 ≤ lam) (hL : 0 ≤ L) (hLlam : L ≤ lam)
    (hτlam : τ ≤ Cτ * lam⁻¹)
    (hAj : ∀ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ j A x‖ ≤ τ * a j * L ^ j)
    (hφj : ∀ j, 1 ≤ j → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ s j * lam * L ^ (j - 1)) :
    ContDiffOn ℝ ∞ Z U ∧ ∀ q, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ q Z x‖ ≤
        (Cτ * (2 : ℝ) ^ q * RawPrimary.atomJetConstant a s q) * lam ^ ((q : ℝ) - 1) := by
  obtain ⟨hZ, hjet⟩ := physical_jets_le_of_displacement_envelope hU Z φ A
    hφ hA hmod a s ha hs hτ hlam hL hLlam hAj hφj
  refine ⟨hZ, ?_⟩
  intro q x hx
  have hcoeff : 0 ≤ (2 : ℝ) ^ q * RawPrimary.atomJetConstant a s q :=
    mul_nonneg (by positivity)
      (RawPrimary.atomJetConstant_nonneg (fun j _ ↦ ha j) (fun j _ _ ↦ hs j))
  calc
    _ ≤ ((2 : ℝ) ^ q * RawPrimary.atomJetConstant a s q) * τ * lam ^ q := hjet q x hx
    _ ≤ ((2 : ℝ) ^ q * RawPrimary.atomJetConstant a s q) *
        (Cτ * lam⁻¹) * lam ^ q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτlam hcoeff)
        (pow_nonneg (zero_le_one.trans hlam) q)
    _ = _ := by
      rw [Real.rpow_sub (zero_lt_one.trans_le hlam), Real.rpow_one, Real.rpow_natCast]
      ring

end JanetCartan.PhysicalPrimary
