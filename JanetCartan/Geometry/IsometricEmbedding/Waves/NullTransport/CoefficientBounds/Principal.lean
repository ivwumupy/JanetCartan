module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.Inputs

/-!
# Joint estimates for the five principal coefficient formulas

The compact range is obtained from a fixed low input budget and the adapted
denominator gap. Composition preserves a single high input norm. The final
producer instantiates both inputs using the literal carrier family, as required
by `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.CoefficientBounds

variable {n : ℕ}

/-- All principal formulas, including the reciprocal denominator, have one
high joint norm. The direction also has a fixed `C¹` budget. The final actual
producer supplies the low input bound and the denominator gap from primitive
frame closeness (`app:ch_waves:eq:joint-tame`). -/
theorem exists_principal_formula_bounds
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (ν : Euclidean n) (r c : Fin n) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ B : ℝ, ∃ A : ℕ → ℝ, 0 < B ∧ (∀ m, 0 < A m) ∧
      ∀ (Ω : Set (Euclidean n × Euclidean 3)), IsOpen Ω → closedBall a ρ ⊆ Ω →
      ∀ f : Euclidean n × Euclidean 3 → Input n, ContDiffOn ℝ ∞ f Ω →
      cNorm (closedBall a ρ) 1 f ≤ L →
      (∀ w ∈ closedBall a ρ, ε ≤ |denominator ν r c (f w)|) →
      cNorm (closedBall a ρ) 1 (direction ν r c ∘ f) ≤ B ∧
      ∀ m,
        cNorm (closedBall a ρ) m (right c ∘ f) +
        cNorm (closedBall a ρ) m (left r ∘ f) +
        cNorm (closedBall a ρ) m (denominator ν r c ∘ f) +
        cNorm (closedBall a ρ) m (fun w ↦ (denominator ν r c (f w))⁻¹) +
        cNorm (closedBall a ρ) m (direction ν r c ∘ f) ≤
          A m * (1 + cNorm (closedBall a ρ) m f) := by
  have hcompact := compact_admissibleInputs ν r c L ε
  choose A₁ hA₁ hb₁ using fun m : ℕ ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ hcompact (r := m) (k := m) le_rfl
      (g := right c) (fun _ _ ↦ (smooth_right c).contDiffAt.of_le (by simp))
  choose A₂ hA₂ hb₂ using fun m : ℕ ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ hcompact (r := m) (k := m) le_rfl
      (g := left r) (fun _ _ ↦ (smooth_left r).contDiffAt.of_le (by simp))
  choose A₃ hA₃ hb₃ using fun m : ℕ ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ hcompact (r := m) (k := m) le_rfl
      (g := denominator ν r c)
      (fun _ _ ↦ (smooth_denominator ν r c).contDiffAt.of_le (by simp))
  choose A₄ hA₄ hb₄ using fun m : ℕ ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ hcompact (r := m) (k := m) le_rfl
      (g := fun p ↦ (denominator ν r c p)⁻¹)
      (fun _ hp ↦ (smoothAt_inverse hε hp).of_le (by simp))
  choose A₅ hA₅ hb₅ using fun m : ℕ ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      a hρ hcompact (r := m) (k := m) le_rfl
      (g := direction ν r c) (fun _ hp ↦ (smoothAt_direction hε hp).of_le (by simp))
  refine ⟨A₅ 1 * (1 + L), fun m ↦ A₁ m + A₂ m + A₃ m + A₄ m + A₅ m,
    mul_pos (hA₅ 1) (by linarith), fun m ↦ by
      have := hA₁ m; have := hA₂ m; have := hA₃ m; have := hA₄ m; have := hA₅ m
      positivity, ?_⟩
  intro Ω hΩ hball f hf hlow hgap
  have hmap : MapsTo f (closedBall a ρ) (admissibleInputs ν r c L ε) := by
    intro w hw
    refine ⟨?_, hgap w hw⟩
    have hn := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
      (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hball hy))).of_le
        (by simp : (1 : ℕ∞ω) ≤ ∞)) hw (Nat.zero_le 1)
    rw [mem_closedBall_zero_iff]
    have hv : ‖f w‖ ≤ cNorm (closedBall a ρ) 1 f := by
      simpa only [norm_iteratedFDeriv_zero] using hn
    exact hv.trans hlow
  refine ⟨(hb₅ 1 Ω hΩ hball f hf hmap).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hlow) (hA₅ 1).le), fun m ↦ ?_⟩
  have h₁ := hb₁ m Ω hΩ hball f hf hmap
  have h₂ := hb₂ m Ω hΩ hball f hf hmap
  have h₃ := hb₃ m Ω hΩ hball f hf hmap
  have h₄ := hb₄ m Ω hΩ hball f hf hmap
  have h₅ := hb₅ m Ω hΩ hball f hf hmap
  exact (add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅).trans_eq
    (by ring)

end JanetCartan.NullTransport.CoefficientBounds
