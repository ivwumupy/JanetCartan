module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ChartComparison
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.MixedHessian
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Finite-order comparison of the explicit phase

The last step in the continuity assertion of `app:lem:common-hamilton-phase`
is linear in the inverse coordinates: `S = e t + u' · η'`. On a fixed compact
target its `C^m` difference is bounded by a fixed multiple of the inverse
coordinate difference at the same order. This module proves that deduction,
not the symbol-to-inverse continuity needed to instantiate it.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

private theorem cNorm_bilinear_le_on_open
    {X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : Y →L[ℝ] Z →L[ℝ] W) {K V : Set X} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) {m : ℕ} {f : X → Y} {g : X → Z}
    (hf : ContDiffOn ℝ m f V) (hg : ContDiffOn ℝ m g V) :
    cNorm K m (fun x ↦ B (f x) (g x)) ≤
      (∑ j ∈ Finset.range (m + 1), ‖B‖ *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * cNorm K m f * cNorm K m g := by
  have hbound : ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y ↦ B (f y) (g y)) x‖ ≤
        (‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
          cNorm K m f * cNorm K m g := by
    intro j hj x hx
    have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg
      hV.uniqueDiffOn (hKV hx) (by exact_mod_cast hj : (j : ℕ∞ω) ≤ m)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hV (hKV hx)] at hb
    apply hb.trans
    calc
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * cNorm K m f * cNorm K m g := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
        have hji : j - i ≤ m := (Nat.sub_le j i).trans hj
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
              (fun _ hy ↦ hf.contDiffAt (hV.mem_nhds (hKV hy))) hx hi') (by positivity))
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
            (fun _ hy ↦ hg.contDiffAt (hV.mem_nhds (hKV hy))) hx hji)
          (norm_nonneg _) (mul_nonneg (by positivity) (cNorm_nonneg _ _ _))
      _ = _ := by simp only [← Finset.sum_mul, mul_assoc]
  apply (cNorm_le_sum_of_bounds (C := fun j ↦
    (‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
      cNorm K m f * cNorm K m g) (fun _ _ ↦ by
        exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg B)
          (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)))
          (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)) hbound).trans_eq
  simp only [Finset.sum_mul]

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

local instance phaseContinuityNormedSpaceU : NormedSpace ℝ U :=
  InnerProductSpace.toNormedSpace

/-- The explicit Hamilton phase is locally Lipschitz in `C^m` as a function of
its inverse coordinates, with no derivative loss (`app:lem:common-hamilton-phase`).
The constant is chosen before either chart. Smoothness is needed only on the
open target containing the fixed compact inner domain. The final construction
must produce the inverse-coordinate comparison separately. -/
theorem exists_phase_finiteOrder_bound {K : Set (E × (ℝ × U))}
    (hK : IsCompact K) (m : ℕ) :
    ∃ B > (0 : ℝ), ∀ (V : Set (E × (ℝ × U)))
      (C C₀ : E × (ℝ × U) → ℝ × U),
      IsOpen V → K ⊆ V → ContDiffOn ℝ m C V → ContDiffOn ℝ m C₀ V →
      cNorm K m (fun z ↦ phase C z - phase C₀ z) ≤
        B * cNorm K m (fun z ↦ C z - C₀ z) := by
  let B : ℝ := (∑ j ∈ Finset.range (m + 1),
    ‖(canonicalCovectorLinear : (ℝ × U) →L[ℝ] (ℝ × U) →L[ℝ] ℝ)‖ *
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
      cNorm K m (Prod.snd : E × (ℝ × U) → ℝ × U)
  refine ⟨1 + |B|, by positivity, ?_⟩
  intro V C C₀ hV hKV hC hC₀
  have he : (fun z ↦ phase C z - phase C₀ z) =
      (fun z ↦ canonicalCovectorLinear (C z - C₀ z) z.2) := by
    funext z
    simp only [phase, canonicalCovectorLinear_apply, canonicalCovector_apply,
      Prod.fst_sub, Prod.snd_sub, inner_sub_left]
    ring
  rw [he]
  have hb := cNorm_bilinear_le_on_open canonicalCovectorLinear hK hV hKV
    (hC.sub hC₀) (contDiff_snd.contDiffOn : ContDiffOn ℝ m Prod.snd V)
  calc
    _ ≤ B * cNorm K m (fun z ↦ C z - C₀ z) := by
      convert hb using 1
      dsimp [B]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [le_abs_self B]) (cNorm_nonneg _ _ _)

namespace ProjectionChart

variable {H H₀ : HomogeneousSymbol E} {Φ : HamiltonFlow H U} {Φ₀ : HamiltonFlow H₀ U}

/-- Equality of forward projections and the common derivative gap identify
inverse coordinates even when they came from different construction choices
(`app:lem:common-hamilton-phase`). This resolves reference-chart choices in
finite-order comparisons once ODE uniqueness identifies the forward maps. -/
theorem coordinates_eq_of_projection_eq (C : ProjectionChart Φ) (C₀ : ProjectionChart Φ₀)
    {D : Set (ℝ × InitialData U)} (hD : Convex ℝ D)
    (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U)))
    (hadm : D ⊆ Φ.time ×ˢ Φ.parameters)
    (hgap : ∀ q ∈ D,
      ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
        (fderiv ℝ Φ.augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖
        ≤ 1 / 2)
    (heq : EqOn Φ.augmentedProjection Φ₀.augmentedProjection D)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) (hz₀ : z ∈ C₀.target)
    (hlift : chartLift C.coordinates z ∈ D) (hlift₀ : chartLift C₀.coordinates z ∈ D) :
    C.coordinates z = C₀.coordinates z := by
  have hb := C.norm_coordinates_sub_le_of_projection_close C₀ hD A hadm hgap
    (ε := 0) (fun q hq ↦ by simp only [heq hq, sub_self, norm_zero, le_refl])
    hz hz₀ hlift hlift₀
  rw [mul_zero] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

end ProjectionChart
end JanetCartan.HamiltonPhase
