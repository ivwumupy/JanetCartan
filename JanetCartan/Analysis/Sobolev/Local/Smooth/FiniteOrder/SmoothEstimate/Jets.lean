module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Lifting scalar Sobolev estimates to smooth jets

The smoothness argument of `app:ch_regular:thm:exact-correction` needs a uniform
bound on all jets of a smooth function. A scalar pointwise bound suffices: a
norming functional reduces a jet value to a scalar, and currying identifies
its higher derivative norms with the original higher jets. No Hilbert norm
on the space of multilinear maps, and no compact-support assumption, is needed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev.FiniteOrder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Currying preserves the operator norms when differentiating an existing jet.
This identifies the derivative orders in the Sobolev norms of `app:not:fourier`. -/
theorem norm_iteratedFDeriv_iteratedFDeriv (v : E → F) (l j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ l (iteratedFDeriv ℝ j v) x‖ =
      ‖iteratedFDeriv ℝ (j + l) v x‖ := by
  induction j generalizing l with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.zero_add]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    change ‖iteratedFDeriv ℝ l
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E) F).symm ∘
        fderiv ℝ (iteratedFDeriv ℝ j v)) x‖ = _
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (E := E) (F := E →L[ℝ] E [×j]→L[ℝ] F)
      (G := E [×(j + 1)]→L[ℝ] F)]
    rw [norm_iteratedFDeriv_fderiv, ih]
    exact congrArg (fun q ↦ ‖iteratedFDeriv ℝ q v x‖) (by omega : j + (l + 1) = j + 1 + l)

/-- A scalar pointwise Sobolev estimate with loss `r` bounds every vector-valued
jet through order `k`, using derivatives through order `k + r`. The constant
is unchanged. This is the jet-lifting step for the smoothness argument in
`app:ch_regular:thm:exact-correction`, with the norms of `app:not:fourier`.

The scalar estimate is an explicit prerequisite, not proved by this reduction. -/
theorem smooth_jet_estimate_of_scalar [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {r k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hscalar : ∀ u : E → ℝ, ContDiff ℝ ∞ u →
      (∀ l ≤ r, MemLp (iteratedFDeriv ℝ l u) 2 μ) →
      ∀ x, ‖u x‖ ≤ C * ∑ l ∈ Finset.range (r + 1),
        (eLpNorm (iteratedFDeriv ℝ l u) 2 μ).toReal)
    {v : E → F} (hv : ContDiff ℝ ∞ v)
    (hmem : ∀ l ≤ k + r, MemLp (iteratedFDeriv ℝ l v) 2 μ)
    {j : ℕ} (hj : j ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ j v x‖ ≤ C * ∑ l ∈ Finset.range (k + r + 1),
      (eLpNorm (iteratedFDeriv ℝ l v) 2 μ).toReal := by
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ (iteratedFDeriv ℝ j v x)
  let u : E → ℝ := φ ∘ iteratedFDeriv ℝ j v
  have hvj : ContDiff ℝ ∞ (iteratedFDeriv ℝ j v) :=
    hv.iteratedFDeriv_right (by simp)
  have hu : ContDiff ℝ ∞ u := φ.contDiff.comp hvj
  have hnorm (l : ℕ) (y : E) :
      ‖iteratedFDeriv ℝ l u y‖ ≤ ‖iteratedFDeriv ℝ (j + l) v y‖ := by
    calc
      _ ≤ ‖φ‖ * ‖iteratedFDeriv ℝ l (iteratedFDeriv ℝ j v) y‖ :=
        φ.norm_iteratedFDeriv_comp_left hvj.contDiffAt (by simp)
      _ ≤ 1 * ‖iteratedFDeriv ℝ l (iteratedFDeriv ℝ j v) y‖ :=
        mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
      _ = _ := by rw [one_mul, norm_iteratedFDeriv_iteratedFDeriv]
  have humeas (l : ℕ) : AEStronglyMeasurable (iteratedFDeriv ℝ l u) μ :=
    (hu.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
  have humem (l : ℕ) (hl : l ≤ r) : MemLp (iteratedFDeriv ℝ l u) 2 μ :=
    (hmem (j + l) (by omega)).of_le (humeas l) (Filter.Eventually.of_forall (hnorm l))
  have h := hscalar u hu humem x
  have hux : ‖u x‖ = ‖iteratedFDeriv ℝ j v x‖ := by
    dsimp [u]
    simpa using congrArg norm hφx
  rw [hux] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
  apply Finset.sum_le_sum_of_injOn (fun l ↦ j + l)
  · intro a _ b _ hab
    exact Nat.add_left_cancel hab
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_range] at hb ⊢
    omega
  · intro l hl
    apply ENNReal.toReal_mono (hmem (j + l) (by simp only [Finset.mem_range] at hl; omega)).ne_top
    exact eLpNorm_mono (humeas l) (hnorm l)
  · intro a _ _
    exact ENNReal.toReal_nonneg

end JanetCartan.LocalSobolev.FiniteOrder
