module

public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Scalar
public import JanetCartan.Analysis.Fourier.Periodic.Coefficient
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Real vector-valued cutoff identities

The exact multiplier identity, support, and reproduction in `main:lem:smoothing`
and Appendix B of paper.tex. These apply in particular to Euclidean vector spaces
and the fixed Frobenius matrix norm. Completeness is used for Bochner integration.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The actual smoothing operator commutes with real continuous linear maps
(`main:lem:smoothing`). -/
theorem periodicCutoff_comp_clm (A : F →L[ℝ] G) {f : Torus n → F}
    (hf : Continuous f) (R : ℝ) :
    periodicCutoff R (A ∘ f) = A ∘ periodicCutoff R f := by
  funext x
  simp [periodicCutoff, periodicFourierMode, periodicFourierCoeff_comp_clm A hf]

/-- Additivity of the real smoothing operator (`main:lem:smoothing`). -/
theorem periodicCutoff_add {f g : Torus n → F} (hf : Continuous f) (hg : Continuous g)
    (R : ℝ) : periodicCutoff R (f + g) = periodicCutoff R f + periodicCutoff R g := by
  let p : Torus n → F × F := fun x ↦ (f x, g x)
  have hp : Continuous p := hf.prodMk hg
  have ha := periodicCutoff_comp_clm
    (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F) hp R
  have h₁ := periodicCutoff_comp_clm (ContinuousLinearMap.fst ℝ F F) hp R
  have h₂ := periodicCutoff_comp_clm (ContinuousLinearMap.snd ℝ F F) hp R
  funext x
  have ha' := congrFun ha x
  have h₁' := congrFun h₁ x
  have h₂' := congrFun h₂ x
  change periodicCutoff R (f + g) x = (periodicCutoff R p x).1 +
    (periodicCutoff R p x).2 at ha'
  change periodicCutoff R f x = (periodicCutoff R p x).1 at h₁'
  change periodicCutoff R g x = (periodicCutoff R p x).2 at h₂'
  simpa only [← h₁', ← h₂', Pi.add_apply] using ha'

/-- Real homogeneity of the smoothing operator (`main:lem:smoothing`). -/
theorem periodicCutoff_smul {f : Torus n → F} (hf : Continuous f) (R a : ℝ) :
    periodicCutoff R (a • f) = a • periodicCutoff R f := by
  exact periodicCutoff_comp_clm (a • ContinuousLinearMap.id ℝ F) hf R

/-- The actual smoothing operator as a real linear map on continuous periodic fields
(`main:lem:smoothing`). Its image consists of smooth periodic fields. -/
def periodicCutoffLinearMap (R : ℝ) : C(Torus n, F) →ₗ[ℝ] C(Torus n, F) where
  toFun f := ⟨periodicCutoff R f, (isSmoothPeriodic_periodicCutoff R f).1⟩
  map_add' f g := by
    apply ContinuousMap.coe_injective
    exact periodicCutoff_add f.continuous g.continuous R
  map_smul' a f := by
    apply ContinuousMap.coe_injective
    exact periodicCutoff_smul f.continuous R a

/-- Exact Fourier coefficients of the real vector-valued multiplier
(`main:lem:smoothing`). -/
theorem periodicFourierCoeff_periodicCutoff {f : Torus n → F} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicCutoff R f) k =
      periodicCutoffSymbol R k • periodicFourierCoeff f k := by
  have h (A : F →L[ℝ] ℝ) :=
    periodicFourierCoeff_periodicCutoff_scalar (A.continuous.comp hf) hR k
  simp only [periodicCutoff_comp_clm _ hf,
    periodicFourierCoeff_comp_clm _ (isSmoothPeriodic_periodicCutoff R f).1,
    periodicFourierCoeff_comp_clm _ hf] at h
  apply Prod.ext
  · apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
    intro A
    simpa using congrArg Prod.fst (h A)
  · apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
    intro A
    simpa using congrArg Prod.snd (h A)

/-- The output has exact Fourier support below `2R` (`main:lem:smoothing`). -/
theorem hasFourierSupport_periodicCutoff {f : Torus n → F} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) : HasFourierSupport (2 * R) (periodicCutoff R f) := by
  intro k hk
  rw [periodicFourierCoeff_periodicCutoff hf hR,
    periodicCutoffSymbol_eq_zero hR hk.le, zero_smul]

/-- Coefficients on the inner plateau are reproduced exactly (`main:lem:smoothing`). -/
theorem periodicFourierCoeff_periodicCutoff_of_le {f : Torus n → F} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) {k : Fin n → ℤ} (hk : frequencyNorm k ≤ R) :
    periodicFourierCoeff (periodicCutoff R f) k = periodicFourierCoeff f k := by
  rw [periodicFourierCoeff_periodicCutoff hf hR, periodicCutoffSymbol_eq_one hR hk, one_smul]

/-- A real vector-valued field already supported below `R` is fixed by the cutoff
(`main:lem:smoothing`). -/
theorem periodicCutoff_eq_self {f : Torus n → F} (hf : Continuous f)
    {R : ℝ} (hR : 0 < R) (hs : HasFourierSupport R f) : periodicCutoff R f = f := by
  funext x
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro A
  have hsA : HasFourierSupport R (A ∘ f) := by
    intro k hk
    rw [periodicFourierCoeff_comp_clm A hf, hs k hk]
    simp
  have h := congrFun (periodicCutoff_eq_self_scalar (A.continuous.comp hf) hR hsA) x
  rw [periodicCutoff_comp_clm A hf] at h
  exact h

end JanetCartan
