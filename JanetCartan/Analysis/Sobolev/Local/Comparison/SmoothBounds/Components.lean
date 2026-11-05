module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.Integrability

/-!
# Orthonormal components of smooth Cartesian energies

The componentwise convention in `app:not:fourier` and the fixed extension in
`app:ch_regular_base:lem:ball-extension` use each Cartesian multiindex once.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Cartesian energy of smooth within-jets is the sum of the scalar
Cartesian energies in fixed orthonormal output coordinates (`app:not:fourier`). -/
theorem cartesianJetEnergy_iteratedFDerivWithin_eq_sum_components
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (m : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f U)
    (hJ : ∀ j ≤ m, MemLp (iteratedFDerivWithin ℝ j f U) 2 (volume.restrict U)) :
    cartesianJetEnergy U m (fun j ↦ iteratedFDerivWithin ℝ j f U) =
      ∑ i, BallExtension.cartesianSobolevEnergy U m (fun x ↦ inner ℝ (b i) (f x)) := by
  rw [cartesianJetEnergy_eq_sum_components b U m _ hJ, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro α _
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  unfold BallExtension.cartesianDerivativeWithin cartesianJetDerivative
  dsimp only
  have he := (innerSL ℝ (b i)).iteratedFDerivWithin_comp_left
    (hf x hx) hU.uniqueDiffOn hx (i := (sobolevDerivativeList (fun k ↦ α (some k))).length)
    (by simp)
  rw [show (fun x ↦ inner ℝ (b i) (f x)) = (innerSL ℝ (b i)) ∘ f from rfl, he]
  rfl

end JanetCartan.LocalSobolev
