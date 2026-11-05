module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry.Frequencies
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Noncomparable graph base geometry

This supplies the larger-frequency squared gap and open integration regions
for the noncomparable assembly of `app:ch_regular:eq:chain-tail`. The phase is
literally `jointPhase` with all three physical covectors frozen. The actual
parent phase chart must supply its base differentiability, Riesz covector, and
primitive comparison `c * ‖ξ‖ ≤ ‖φ_u‖ ≤ C * ‖ξ‖` on the carrier. No kernel
bound or desired gradient gap is an input. The open-neighborhood theorem uses
only C¹ regularity near that carrier, not comparability on the neighborhood.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

/-- The primitive comparison produces the squared gap for the literal physical
base phase, uniformly in both orientations and all three frequencies
(`app:ch_regular:eq:chain-tail`). -/
theorem basePhase_gradient_gap
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    (backward : Bool) (φ : E → E → ℝ) (x y ξ η ζ g : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1)
    (hg : fderiv ℝ (fun u => φ u ξ) b.1 = innerSL ℝ g)
    {c C : ℝ} (hc : 0 < c) (hlow : c * ‖ξ‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ξ‖)
    (hsep : OutsideInputAnnuli c C ξ η ζ) :
    gapCoefficient c C * largestFrequency ξ η ζ ^ 2 ≤
      Localization.phaseGradientSquare (baseDirections eu ez)
        (basePhase backward φ x y ξ η ζ) b := by
  cases backward
  · rw [basePhase_forward_gradientSquare eu ez φ x y ξ η ζ g b hφ hg]
    exact forward_covector_squared_gap hc g ξ η ζ hlow hhigh hsep
  · rw [basePhase_reverse_gradientSquare eu ez φ x y ξ η ζ g b hφ hg]
    exact reverse_covector_squared_gap hc g ξ η ζ hlow hhigh hsep

/-- A lower bound on the largest physical frequency yields the shell-scaled
squared gap. There is no lower bound on either smaller frequency
(`app:ch_regular:eq:chain-tail`). -/
theorem basePhase_scaled_gradient_gap
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    (backward : Bool) (φ : E → E → ℝ) (x y ξ η ζ g : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1)
    (hg : fderiv ℝ (fun u => φ u ξ) b.1 = innerSL ℝ g)
    {c C R : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hlow : c * ‖ξ‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ξ‖)
    (hsep : OutsideInputAnnuli c C ξ η ζ) (hlarge : R ≤ largestFrequency ξ η ζ) :
    gapCoefficient c C * R ^ 2 ≤
      Localization.phaseGradientSquare (baseDirections eu ez)
        (basePhase backward φ x y ξ η ζ) b :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hlarge 2)
    (gapCoefficient_pos c C).le).trans
      (basePhase_gradient_gap eu ez backward φ x y ξ η ζ g b hφ hg hc hlow hhigh hsep)

/-- Dividing the literal physical phase by the shell radius produces a uniform
normalized gap, without needing homogeneity away from the actual covectors
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem basePhase_normalized_gradient_gap
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    (backward : Bool) (φ : E → E → ℝ) (x y ξ η ζ g : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1)
    (hg : fderiv ℝ (fun u => φ u ξ) b.1 = innerSL ℝ g)
    {c C R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlow : c * ‖ξ‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ξ‖)
    (hsep : OutsideInputAnnuli c C ξ η ζ) (hlarge : R ≤ largestFrequency ξ η ζ) :
    gapCoefficient c C ≤
      Localization.phaseGradientSquare (baseDirections eu ez)
        (R⁻¹ • basePhase backward φ x y ξ η ζ) b := by
  have hd := differentiableAt_basePhase backward φ x y ξ η ζ b hφ
  have he : Localization.phaseGradientSquare (baseDirections eu ez)
      (R⁻¹ • basePhase backward φ x y ξ η ζ) b = R⁻¹ ^ 2 *
        Localization.phaseGradientSquare (baseDirections eu ez)
          (basePhase backward φ x y ξ η ζ) b := by
    simp only [Localization.phaseGradientSquare, fderiv_const_smul hd, smul_apply,
      smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [he]
  have h := mul_le_mul_of_nonneg_left
    (basePhase_scaled_gradient_gap eu ez backward φ x y ξ η ζ g b hφ hg hc hR.le
      hlow hhigh hsep hlarge) (sq_nonneg R⁻¹)
  have hh : R⁻¹ ^ 2 * (gapCoefficient c C * R ^ 2) = gapCoefficient c C := by
    field_simp
  rwa [hh] at h

/-- C¹ phase regularity constructs an open carrier neighborhood with half the
physical squared gap. Comparison is needed only on the carrier; the constant
is uniform in the shell radius and integration order. This is the geometric
input to base integration by parts for `app:ch_regular:eq:chain-tail`. -/
theorem exists_open_basePhase_gradient_gap
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    (backward : Bool) (φ : E → E → ℝ) (x y ξ η ζ : E)
    {S V : Set (E × E)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hregular : ContDiffOn ℝ 1 (basePhase backward φ x y ξ η ζ) V)
    (g : E × E → E)
    (hφ : ∀ b ∈ S, DifferentiableAt ℝ (fun u => φ u ξ) b.1)
    (hg : ∀ b ∈ S, fderiv ℝ (fun u => φ u ξ) b.1 = innerSL ℝ (g b))
    {c C R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlow : ∀ b ∈ S, c * ‖ξ‖ ≤ ‖g b‖)
    (hhigh : ∀ b ∈ S, ‖g b‖ ≤ C * ‖ξ‖)
    (hsep : OutsideInputAnnuli c C ξ η ζ) (hlarge : R ≤ largestFrequency ξ η ζ) :
    ∃ U : Set (E × E), IsOpen U ∧ S ⊆ U ∧ U ⊆ V ∧
      ∀ b ∈ U, (gapCoefficient c C / 2) * R ^ 2 ≤
        Localization.phaseGradientSquare (baseDirections eu ez)
          (basePhase backward φ x y ξ η ζ) b := by
  let G := Localization.phaseGradientSquare (baseDirections eu ez)
    (basePhase backward φ x y ξ η ζ)
  have hG : ContinuousOn G V := by
    apply continuousOn_finsetSum
    intro i _
    exact ((hregular.continuousOn_fderiv_of_isOpen hV (by rfl)).clm_apply
      continuousOn_const).pow 2
  refine ⟨V ∩ G ⁻¹' Ioi ((gapCoefficient c C / 2) * R ^ 2),
    hG.isOpen_inter_preimage hV isOpen_Ioi, ?_, inter_subset_left, fun b hb => hb.2.le⟩
  intro b hb
  refine ⟨hSV hb, ?_⟩
  have h := basePhase_scaled_gradient_gap eu ez backward φ x y ξ η ζ (g b) b
    (hφ b hb) (hg b hb) hc hR.le (hlow b hb) (hhigh b hb) hsep hlarge
  have hp : 0 < gapCoefficient c C * R ^ 2 := mul_pos (gapCoefficient_pos c C) (sq_pos_of_pos hR)
  change (gapCoefficient c C / 2) * R ^ 2 < G b
  dsimp [G]
  nlinarith

end JanetCartan.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
