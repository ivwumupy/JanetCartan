module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Basic

/-!
# All three normal-comparison cross terms

For `app:ch_background:prop:bg-frame`, Step 1, a channel comparison `T = B + D`
gives the mixed products `B D*`, `D B*`, and the product `D D*` of both
remainders. This deduction does not supply the channel comparison. Its actual
producer must differentiate `periodicBesselInverse_localized_eq_add_remainder`.
The Euclidean construction must separately identify `B B*` with the literal
source-square Schwartz normal. These obligations remain with the parent
periodic-comparison construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E

/-- The complete normal error from a one-channel remainder, with all three
cross terms retained (`app:ch_background:prop:bg-frame`, Step 1). -/
def normalCrossTerms (B D : R² →L[ℝ] R²) : R² →L[ℝ] R² :=
  B.comp D.adjoint + D.comp B.adjoint + D.comp D.adjoint

/-- The full error is self-adjoint: the mixed terms exchange and the
two-remainder term is its own adjoint (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normalCrossTerms_adjoint (B D : R² →L[ℝ] R²) :
    (normalCrossTerms B D).adjoint = normalCrossTerms B D := by
  simp only [normalCrossTerms, map_add, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  abel

/-- Expansion of both normal factors, including the product of two comparison
remainders (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normal_add_eq (B D : R² →L[ℝ] R²) :
    (B + D).comp (B + D).adjoint = B.comp B.adjoint + normalCrossTerms B D := by
  simp only [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    normalCrossTerms]
  abel

/-- The normal comparison follows from a proved channel comparison on actual
Lebesgue L². This conditional deduction does not construct either factor
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem pullback_normal_eq_of_channel_eq
    (T : ContinuumRow.OutputL2 d →L[ℝ] ContinuumRow.OutputL2 d)
    (B D : R² →L[ℝ] R²) (hT : pullback T = B + D) :
    pullback (T.comp T.adjoint) = B.comp B.adjoint + normalCrossTerms B D := by
  rw [pullback_normal, hT, normal_add_eq]

/-- If both channel summands retain the measurement support, so does the
entire normal error and its literal adjoint
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem normalCrossTerms_support (B D : R² →L[ℝ] R²) (μ : E → ℝ)
    (hB : ∀ f, ∀ᵐ x ∂volume, x ∉ tsupport μ → B f x = 0)
    (hD : ∀ f, ∀ᵐ x ∂volume, x ∉ tsupport μ → D f x = 0) (f : R²) :
    (∀ᵐ x ∂volume, x ∉ tsupport μ → normalCrossTerms B D f x = 0) ∧
      (∀ᵐ x ∂volume, x ∉ tsupport μ → (normalCrossTerms B D).adjoint f x = 0) := by
  suffices hs : ∀ᵐ x ∂volume, x ∉ tsupport μ → normalCrossTerms B D f x = 0 by
    exact ⟨hs, by rwa [normalCrossTerms_adjoint]⟩
  filter_upwards [hB (D.adjoint f), hD (B.adjoint f), hD (D.adjoint f),
    Lp.coeFn_add (B (D.adjoint f) + D (B.adjoint f)) (D (D.adjoint f)),
    Lp.coeFn_add (B (D.adjoint f)) (D (B.adjoint f))] with x h₁ h₂ h₃ h₄ h₅ hx
  change (B (D.adjoint f) + D (B.adjoint f) + D (D.adjoint f)) x = 0
  simp only [Pi.add_apply] at h₄ h₅
  rw [h₄, h₅, h₁ hx, h₂ hx, h₃ hx, add_zero, add_zero]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
