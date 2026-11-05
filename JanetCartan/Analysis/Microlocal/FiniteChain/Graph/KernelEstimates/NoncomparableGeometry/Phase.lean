module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Analysis.Microlocal.Localization.Phase
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp

/-!
# Base derivatives with all three physical frequencies frozen

These identities supply the base integration by parts in
`app:ch_regular:eq:chain-tail`, for the literal phase
`app:ch_regular:eq:joint-kernel-phase` and its inverse orientation.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Freeze physical frequencies, without changing either amplitude position
(`app:ch_regular:eq:joint-kernel-phase`). -/
def basePhase (backward : Bool) (φ : E → E → ℝ) (x y ξ η ζ : E) (b : E × E) : ℝ :=
  jointPhase backward φ x y (b, ξ, η, ζ)

/-- Independent orthonormal directions in the two base variables
(`app:ch_regular:eq:joint-stationary`). -/
def baseDirections [Fintype ι] [Fintype κ] (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E) :
    ι ⊕ κ → E × E
  | .inl i => (eu i, 0)
  | .inr i => (0, ez i)

attribute [local fun_prop] DifferentiableAt.inner

/-- The frozen forward phase has exactly the two physical base covectors
`φ_u - ζ` and `η - ξ` (`app:ch_regular:eq:joint-stationary`). -/
theorem fderiv_basePhase_forward (φ : E → E → ℝ) (x y ξ η ζ : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1) :
    fderiv ℝ (basePhase false φ x y ξ η ζ) b =
      (fderiv ℝ (fun u => φ u ξ) b.1 - innerSL ℝ ζ).coprod (innerSL ℝ (η - ξ)) := by
  have he : basePhase false φ x y ξ η ζ = fun p : E × E =>
      forwardPhase φ x y p.1 b.2 ξ η ζ +
        forwardPhase φ x y b.1 p.2 ξ η ζ - forwardPhase φ x y b.1 b.2 ξ η ζ := by
    funext p
    simp only [basePhase, jointPhase, Bool.false_eq_true, ↓reduceIte, forwardPhase]
    ring
  have hu : DifferentiableAt ℝ (fun u => forwardPhase φ x y u b.2 ξ η ζ) b.1 := by
    unfold forwardPhase
    fun_prop
  have hz : DifferentiableAt ℝ (fun z => forwardPhase φ x y b.1 z ξ η ζ) b.2 := by
    unfold forwardPhase
    fun_prop
  have h := ((hu.hasFDerivAt.comp b hasFDerivAt_fst).add
    (hz.hasFDerivAt.comp b hasFDerivAt_snd)).sub_const (forwardPhase φ x y b.1 b.2 ξ η ζ)
  simp only [Function.comp_def, Pi.add_apply] at h
  rw [he, h.fderiv]
  rw [fderiv_forwardPhase_u φ x y b.1 b.2 ξ η ζ hφ, fderiv_forwardPhase_z]
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- The reverse base covectors are `η - φ_u` and `ξ - ζ`; reversal exchanges
physical input and output (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem fderiv_basePhase_reverse (φ : E → E → ℝ) (x y ξ η ζ : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1) :
    fderiv ℝ (basePhase true φ x y ξ η ζ) b =
      (innerSL ℝ η - fderiv ℝ (fun u => φ u ξ) b.1).coprod (innerSL ℝ (ξ - ζ)) := by
  have he : basePhase true φ x y ξ η ζ = -basePhase false φ y x ξ ζ η := by
    funext p
    exact reversePhase_eq_neg_swap φ x y p.1 p.2 ξ η ζ
  rw [he, fderiv_neg, fderiv_basePhase_forward φ y x ξ ζ η b hφ]
  apply ContinuousLinearMap.ext
  intro v
  simp only [neg_apply, ContinuousLinearMap.coprod_apply,
    sub_apply, innerSL_apply_apply, inner_sub_left]
  ring

/-- Parseval in each base identifies the actual squared gradient with the
squared norms of the two forward physical covectors. The primitive derivative
representation is supplied by the parent's phase chart
(`app:ch_regular:eq:joint-stationary`). -/
theorem basePhase_forward_gradientSquare [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    (φ : E → E → ℝ) (x y ξ η ζ g : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1)
    (hg : fderiv ℝ (fun u => φ u ξ) b.1 = innerSL ℝ g) :
    Localization.phaseGradientSquare (baseDirections eu ez) (basePhase false φ x y ξ η ζ) b =
      ‖g - ζ‖ ^ 2 + ‖η - ξ‖ ^ 2 := by
  simp only [Localization.phaseGradientSquare, fderiv_basePhase_forward _ _ _ _ _ _ _ hφ,
    hg, ← map_sub, Fintype.sum_sum_type, baseDirections, ContinuousLinearMap.coprod_apply,
    innerSL_apply_apply, inner_zero_right, add_zero, zero_add]
  rw [eu.sum_sq_inner_left, ez.sum_sq_inner_left]

/-- The same Parseval identity for the literal inverse phase
(`app:ch_regular:eq:joint-stationary`). -/
theorem basePhase_reverse_gradientSquare [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ E) (ez : OrthonormalBasis κ ℝ E)
    (φ : E → E → ℝ) (x y ξ η ζ g : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1)
    (hg : fderiv ℝ (fun u => φ u ξ) b.1 = innerSL ℝ g) :
    Localization.phaseGradientSquare (baseDirections eu ez) (basePhase true φ x y ξ η ζ) b =
      ‖η - g‖ ^ 2 + ‖ξ - ζ‖ ^ 2 := by
  simp only [Localization.phaseGradientSquare, fderiv_basePhase_reverse _ _ _ _ _ _ _ hφ,
    hg, ← map_sub, Fintype.sum_sum_type, baseDirections, ContinuousLinearMap.coprod_apply,
    innerSL_apply_apply, inner_zero_right, add_zero, zero_add]
  rw [eu.sum_sq_inner_left, ez.sum_sq_inner_left]

/-- Differentiability requires only the frozen graph covector's base slice
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem differentiableAt_basePhase (backward : Bool) (φ : E → E → ℝ)
    (x y ξ η ζ : E) (b : E × E)
    (hφ : DifferentiableAt ℝ (fun u => φ u ξ) b.1) :
    DifferentiableAt ℝ (basePhase backward φ x y ξ η ζ) b := by
  have hu : DifferentiableAt ℝ (fun p : E × E => φ p.1 ξ) b :=
    hφ.comp b differentiableAt_fst
  cases backward <;> unfold basePhase jointPhase forwardPhase reversePhase <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

end JanetCartan.FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
