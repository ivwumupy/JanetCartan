module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.InverseJetBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition

/-!
# Value and coefficient comparison for buffered inverses

The inverse induction for `app:lem:common-hamilton-phase` uses the segment
estimate of `app:lem:buffered-inverse-stability`. Only the fixed reference map
uses an additional derivative in the coefficient comparison.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.HamiltonPhase.InverseContinuity
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `app:lem:buffered-inverse-stability`: the value comparison consumed by the
finite-order inverse induction, in coordinates normalized by the central matrix. -/
theorem norm_inverse_sub_le {f f₀ : X → X} {g g₀ : Y → X}
    {K D : Set X} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    (hgap : ∀ x ∈ K, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2)
    {y : Y} (hy : g y ∈ K) (hy₀ : g₀ y ∈ K) (heq : f (g y) = f₀ (g₀ y))
    (m : ℕ) : ‖g y - g₀ y‖ ≤ 2 * cNorm K m (f - f₀) := by
  have h := normalized_lower_lipschitz_of_derivative_gap hconv
    (ContinuousLinearEquiv.refl ℝ X)
    (fun x hx ↦ (hf.contDiffAt (hD.mem_nhds (hKD hx))).differentiableAt (by simp))
    (by simpa using hgap) hy hy₀
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply, heq,
    norm_sub_rev (f₀ (g₀ y))] at h
  have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (f := f - f₀) hK
    (fun x hx ↦ ((hf.sub hf₀).contDiffAt (hD.mem_nhds (hKD hx))).of_le (by simp))
    hy₀ (Nat.zero_le m)
  simp only [norm_iteratedFDeriv_zero, Pi.sub_apply] at hb
  linarith

/-- `app:lem:common-hamilton-phase`: forward jets at the two inverse images
are close at exactly the perturbation order. Consumed by the top-jet step. -/
theorem norm_forward_jet_at_inverse_sub_le {f f₀ : X → X} {g g₀ : Y → X}
    {K D : Set X} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hD : IsOpen D) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hf₀ : ContDiffOn ℝ ∞ f₀ D)
    (hgap : ∀ x ∈ K, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ X‖ ≤ 1 / 2)
    {y : Y} (hy : g y ∈ K) (hy₀ : g₀ y ∈ K) (heq : f (g y) = f₀ (g₀ y))
    {m n : ℕ} (hn : n ≤ m) :
    ‖iteratedFDeriv ℝ n f (g y) - iteratedFDeriv ℝ n f₀ (g₀ y)‖ ≤
      (1 + 2 * cNorm K (m + 1) f₀) * cNorm K m (f - f₀) := by
  have hs (x : X) (hx : x ∈ K) : ContDiffAt ℝ ∞ f₀ x :=
    hf₀.contDiffAt (hD.mem_nhds (hKD hx))
  have hshift : ‖iteratedFDeriv ℝ n f₀ (g y) - iteratedFDeriv ℝ n f₀ (g₀ y)‖ ≤
      cNorm K (m + 1) f₀ * ‖g y - g₀ y‖ := by
    apply hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun x hx ↦ ((hs x hx).iteratedFDeriv_right (m := 1) (by simp)).differentiableAt
        (by simp)) _ hy₀ hy
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun x hx ↦ (hs x hx).of_le (by simp)) hx (Nat.add_le_add_right hn 1)
  have hsame := CompositionContinuity.norm_iteratedFDeriv_sub_le_cNorm hK
    (fun x hx ↦ (hf.contDiffAt (hD.mem_nhds (hKD hx))).of_le (by simp))
    (fun x hx ↦ (hs x hx).of_le (by simp)) hn hy
  have hv := norm_inverse_sub_le hK hconv hD hKD hf hf₀ hgap hy hy₀ heq m
  have hshift' := hshift.trans (mul_le_mul_of_nonneg_left hv (cNorm_nonneg _ _ _))
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (g y) - iteratedFDeriv ℝ n f₀ (g y)‖ +
        ‖iteratedFDeriv ℝ n f₀ (g y) - iteratedFDeriv ℝ n f₀ (g₀ y)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ cNorm K m (f - f₀) + cNorm K (m + 1) f₀ * (2 * cNorm K m (f - f₀)) :=
      add_le_add hsame hshift'
    _ = _ := by ring

end JanetCartan.HamiltonPhase.InverseContinuity
