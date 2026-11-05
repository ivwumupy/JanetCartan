module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev

/-!
# Common physical masks on the constructed sector factors

Apply the proved smooth-multiplier estimate to the actual source and output
cutoffs. The source multiplier stays to the right of the operator. Its literal
adjoint exchanges the two masks. Constants precede the varying coefficients
and operators. The finite construction consumes this deduction for its retained
retarded factors (`energy-complete-residual`, `measured-adjoint`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open FourierIntegral LowBounds Pseudodifferential
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

/-- Fixed common masks preserve the same additive high coefficient quantity.
Both orientations use the SAME localized operator and constants. The only
operator premise is supplied by the actual retarded/PDO producer; all mask
estimates are constructed here (`sector-theorem-residual`, `measured-adjoint`). -/
theorem exists_commonMask_sobolev_constants
    (χout χsource : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hob : ∀ x, ‖χout x‖ ≤ 1) (hsb : ∀ x, ‖χsource x‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧
    ∀ (T : H →L[ℂ] H) (s t : ℕ) (A high : ℝ), 0 ≤ A → 0 ≤ high →
      (∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (t : ℝ) (V u) ∧
        vectorFourierSobolevNorm (t : ℝ) (V u) ≤
          A * (vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖)) →
      let S := (sourceCutMultiplier χout ho.continuous hob).comp
        (T.comp (sourceCutMultiplier χsource hs.continuous hsb))
      ∀ V : H →L[ℂ] H, (V = S ∨ V = S.adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (t : ℝ) (V u) ∧
        vectorFourierSobolevNorm (t : ℝ) (V u) ≤
          (D t * A * D s) * (vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖) := by
  have hmo m := exists_sourceCutMultiplier_fourierSobolev_bound (r := q) χout ho hoc hob m
  have hms m := exists_sourceCutMultiplier_fourierSobolev_bound (r := q) χsource hs hsc hsb m
  choose Co hCo hco using hmo
  choose Cs hCs hcs using hms
  let D m := 1 + Co m + Cs m
  have hD m : 1 ≤ D m := by dsimp [D]; linarith [hCo m, hCs m]
  let Mo : H →L[ℂ] H := sourceCutMultiplier χout ho.continuous hob
  let Ms : H →L[ℂ] H := sourceCutMultiplier χsource hs.continuous hsb
  have hmask (m : ℕ) (V : H →L[ℂ] H) (hV : V = Mo ∨ V = Ms) (u : H)
      (hu : MemVectorFourierSobolev (m : ℝ) u) :
      MemVectorFourierSobolev (m : ℝ) (V u) ∧
        vectorFourierSobolevNorm (m : ℝ) (V u) ≤ D m * vectorFourierSobolevNorm (m : ℝ) u := by
    rcases hV with rfl | rfl
    · refine ⟨(hco m u hu).1, (hco m u hu).2.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [D]; linarith [hCs m]
    · refine ⟨(hcs m u hu).1, (hcs m u hu).2.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [D]; linarith [hCo m]
  have hnorm (V : H →L[ℂ] H) (hV : V = Mo ∨ V = Ms) (u : H) : ‖V u‖ ≤ ‖u‖ := by
    apply (V.le_opNorm u).trans
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg u)).trans_eq (one_mul _)
    rcases hV with rfl | rfl
    · exact norm_sourceCutMultiplier_le _ _ _
    · exact norm_sourceCutMultiplier_le _ _ _
  refine ⟨D, hD, ?_⟩
  intro T s t A high hA hhigh hT S V hV u hu
  have hbound (O I W : H →L[ℂ] H) (hO : O = Mo ∨ O = Ms)
      (hI : I = Mo ∨ I = Ms) (hW : W = T ∨ W = T.adjoint) :
      MemVectorFourierSobolev (t : ℝ) (O (W (I u))) ∧
      vectorFourierSobolevNorm (t : ℝ) (O (W (I u))) ≤
        (D t * A * D s) * (vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖) := by
    obtain ⟨hi, hni⟩ := hmask s I hI u hu
    obtain ⟨hw, hnw⟩ := hT W hW (I u) hi
    obtain ⟨hout, hnout⟩ := hmask t O hO (W (I u)) hw
    refine ⟨hout, hnout.trans ((mul_le_mul_of_nonneg_left hnw
      (zero_le_one.trans (hD t))).trans ?_)⟩
    have hiNorm := hnorm I hI u
    have hhighNorm : high * ‖I u‖ ≤ D s * (high * ‖u‖) :=
      (mul_le_mul_of_nonneg_left hiNorm hhigh).trans
        (le_mul_of_one_le_left (mul_nonneg hhigh (norm_nonneg u)) (hD s))
    calc
      D t * (A * (vectorFourierSobolevNorm (s : ℝ) (I u) + high * ‖I u‖))
          ≤ D t * (A * (D s * vectorFourierSobolevNorm (s : ℝ) u +
              D s * (high * ‖u‖))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (add_le_add hni hhighNorm) hA)
              (zero_le_one.trans (hD t))
      _ = _ := by ring
  rcases hV with rfl | rfl
  · exact hbound Mo Ms T (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  · have he : S.adjoint = Ms.comp (T.adjoint.comp Mo) := by
      dsimp [S, Mo, Ms]
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
        sourceCutMultiplier_adjoint, sourceCutMultiplier_adjoint,
        ContinuousLinearMap.comp_assoc]
    rw [he]
    exact hbound Ms Mo T.adjoint (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)

end JanetCartan.RegularSector.FiniteAssembly
