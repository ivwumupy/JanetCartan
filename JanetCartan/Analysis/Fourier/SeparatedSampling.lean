module

public import JanetCartan.Analysis.Fourier.SeparatedSampling.Counting

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic separated sampling

The counting, spacing, and mass assertions of `app:ch_waves:thm:sampling`
(paper.tex, lines 5780–5810), on one bounded three-parameter patch.

The hypotheses `WindowBounds` and `PatchBounds` state the elementary nonnegativity,
size, and support inputs for the manuscript's window and patch weight. The window
construction and its quadrature identities are separate analytic inputs; no
probabilistic or operator conclusion of the sampling theorem is asserted here.
The shifts are arbitrary points in `[0,h)^3`. All constants and the `(p+1)^3`
colors are fixed before the mesh, shifts, frequency, or accuracy are chosen.
-/

@[expose] public noncomputable section

namespace JanetCartan.SeparatedSampling

/-- `N_s = h⁻³` in `app:ch_waves:thm:sampling`. -/
def samplingScale (h : ℝ) : ℝ := (h ^ 3)⁻¹

/-- The mass of all literal nonzero samples (`app:ch_waves:thm:sampling`). -/
def totalMass (p : ℕ) (B : ℝ) (ψ : Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : Lattice → Point) : ℝ :=
  ∑ a ∈ samples p B ψ w h U, weight ψ w h U a

variable {p : ℕ} {w : ℝ → ℝ} {W : ℝ} {ψ : Point → ℝ} {B P : ℝ}
  {h : ℝ} {U : Lattice → Point}

/-- Total sampled mass is nonnegative (`app:ch_waves:thm:sampling`). -/
theorem totalMass_nonneg (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) : 0 ≤ totalMass p B ψ w h U :=
  Finset.sum_nonneg fun a _ ↦ weight_nonneg hw hψ hh a

/-- Total mass is bounded independently of mesh, shifts, and accuracy,
as asserted in `app:ch_waves:thm:sampling`. -/
theorem totalMass_le (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 < h) (hh₁ : h ≤ 1) :
    totalMass p B ψ w h U ≤ countConstant p B * (P * W ^ 3) := by
  have hP : 0 ≤ P := (hψ.nonneg 0).trans (hψ.le_bound 0)
  have hW : 0 ≤ W := (hw.nonneg 0).trans (hw.le_bound 0)
  calc
    _ ≤ ∑ _a ∈ samples p B ψ w h U, h ^ 3 * (P * W ^ 3) :=
      Finset.sum_le_sum fun a _ ↦ weight_le hw hψ hh.le a
    _ = ((samples p B ψ w h U).card : ℝ) * h ^ 3 * (P * W ^ 3) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ countConstant p B * (P * W ^ 3) := mul_le_mul_of_nonneg_right
      (card_samples_mul_cube_le hψ.radius_nonneg hh hh₁) (by positivity)

/-- Each individual block has sampled mass `O(h³)`, as used in the background
quadrature proof of `app:ch_waves:thm:sampling`. -/
theorem block_mass_le (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hh : 0 ≤ h) (q : Lattice) :
    ∑ m ∈ blockSamples p ψ w h U q, weight ψ w h U (q, m) ≤
      (nodesPerBlock p : ℝ) * h ^ 3 * (P * W ^ 3) := by
  have hP : 0 ≤ P := (hψ.nonneg 0).trans (hψ.le_bound 0)
  have hW : 0 ≤ W := (hw.nonneg 0).trans (hw.le_bound 0)
  calc
    _ ≤ ∑ _m ∈ blockSamples p ψ w h U q, h ^ 3 * (P * W ^ 3) :=
      Finset.sum_le_sum fun m _ ↦ weight_le hw hψ hh (q, m)
    _ = ((blockSamples p ψ w h U q).card : ℝ) * (h ^ 3 * (P * W ^ 3)) := by simp
    _ ≤ (nodesPerBlock p : ℝ) * (h ^ 3 * (P * W ^ 3)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_blockSamples_le p ψ w h U q)
        (by positivity)
    _ = _ := by ring

/-- Fixed coefficient large enough for all three deterministic estimates in
`app:ch_waves:thm:sampling`. -/
def samplingConstant (p : ℕ) (B P W : ℝ) : ℝ :=
  (countConstant p B + 1) * (P * W ^ 3 + 1)

/-- Simultaneous deterministic conclusions of `app:ch_waves:thm:sampling` on a
bounded patch. The elementary window and patch bounds are the only analytic
inputs. In particular all shifts in `[0,h)^3` satisfy the estimates, and the
constant is chosen before `h` and `U`. -/
theorem deterministic_sampling (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (U : Lattice → Point), 0 < h → h ≤ 1 →
        (∀ q i, 0 ≤ U q i ∧ U q i < h) →
        Fintype.card (Fin 3 → Fin (p + 1)) = (p + 1) ^ 3 ∧
        (∀ q, (blockSamples p ψ w h U q).card ≤ nodesPerBlock p) ∧
        ((samples p B ψ w h U).card : ℝ) ≤ C * samplingScale h ∧
        (∀ a ∈ samples p B ψ w h U,
          0 < weight ψ w h U a ∧ weight ψ w h U a ≤ C / samplingScale h) ∧
        (∀ a ∈ samples p B ψ w h U, ∀ b ∈ samples p B ψ w h U,
          a ≠ b → color p a.1 = color p b.1 →
            h / 2 ≤ ‖(WithLp.toLp 2 (node h U a) : EuclideanSpace ℝ (Fin 3)) -
              WithLp.toLp 2 (node h U b)‖) ∧
        totalMass p B ψ w h U ≤ C := by
  have hP : 0 ≤ P := (hψ.nonneg 0).trans (hψ.le_bound 0)
  have hW : 0 ≤ W := (hw.nonneg 0).trans (hw.le_bound 0)
  have hD : 0 ≤ P * W ^ 3 := by positivity
  have hK : 0 ≤ countConstant p B := by
    dsimp [countConstant, blockCountConstant]
    have := hψ.radius_nonneg
    positivity
  have hC : 0 < samplingConstant p B P W := by
    dsimp [samplingConstant]
    positivity
  have hKC : countConstant p B ≤ samplingConstant p B P W := by
    dsimp [samplingConstant]
    nlinarith
  have hDC : P * W ^ 3 ≤ samplingConstant p B P W := by
    dsimp [samplingConstant]
    nlinarith
  have hKDC : countConstant p B * (P * W ^ 3) ≤ samplingConstant p B P W := by
    dsimp [samplingConstant]
    nlinarith
  refine ⟨samplingConstant p B P W, hC, ?_⟩
  intro h U hh hh₁ hU
  refine ⟨card_colors p, card_blockSamples_le p ψ w h U, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ countConstant p B / h ^ 3 := card_samples_le hψ.radius_nonneg hh hh₁
      _ ≤ samplingConstant p B P W * samplingScale h := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hKC (by positivity)
  · intro a ha
    have ha' := (mem_samples_iff hw hψ hh hh₁ hU).mp ha
    refine ⟨lt_of_le_of_ne (weight_nonneg hw hψ hh.le a) (Ne.symm ha'), ?_⟩
    calc
      _ ≤ h ^ 3 * (P * W ^ 3) := weight_le hw hψ hh.le a
      _ ≤ h ^ 3 * samplingConstant p B P W :=
        mul_le_mul_of_nonneg_left hDC (by positivity)
      _ = _ := by simp [samplingScale, div_eq_mul_inv, mul_comm]
  · intro a ha b hb hab hc
    exact euclidean_nonzero_samples_separated hw hh
      ((mem_samples_iff hw hψ hh hh₁ hU).mp ha)
      ((mem_samples_iff hw hψ hh hh₁ hU).mp hb) hab hc
  · exact (totalMass_le hw hψ hh hh₁).trans hKDC

end JanetCartan.SeparatedSampling
