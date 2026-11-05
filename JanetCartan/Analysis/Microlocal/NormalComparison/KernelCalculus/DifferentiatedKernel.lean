module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.FullKernel
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The full kernel of the operator derivative

The operator norm derivative in `app:ch_osc:prop:osc-normal` has the literal
two-position kernel obtained by differentiating both factors. All exchanges
of integrals and finite sums follow from the compact cross-kernel estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

set_option maxHeartbeats 800000

namespace JanetCartan.NormalComparison

open AmplitudeBound

variable {d m r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The sum of the two genuine cross compositions has the product-rule kernel
in `app:ch_osc:prop:osc-normal`. This applies to an original kernel `t` and its
parameter derivative `v`, without any assumed normal-kernel identity. -/
theorem compactVectorKernelOperator_cross_add_ae_integral
    (D : Set U) {t v : Fin r → E → U → ℂ}
    (ht : ∀ i, Continuous (Function.uncurry (t i)))
    (hst : ∀ i, HasCompactSupport (Function.uncurry (t i)))
    (hv : ∀ i, Continuous (Function.uncurry (v i)))
    (hsv : ∀ i, HasCompactSupport (Function.uncurry (v i)))
    (g : Lp ℂ ∞ (volume.restrict D)) (f : NormalOutputL2 d r) (i : Fin r) :
    let T := compactVectorKernelOperator D ht hst
    let V := compactVectorKernelOperator D hv hsv
    let M := multiplicationOperator g
    ((V.comp (M.comp T.adjoint) + T.comp (M.comp V.adjoint)) f) i =ᵐ[volume]
      fun x ↦ ∑ j, ∫ y, (∫ u in D,
        (v i x u * star (t j y u) + t i x u * star (v j y u)) * g u) * f j y := by
  dsimp only
  have h₁ := compactVectorKernelOperator_cross_ae_integral D hv hsv ht hst g f i
  have h₂ := compactVectorKernelOperator_cross_ae_integral D ht hst hv hsv g f i
  have hsum := Lp.coeFn_add
    (((compactVectorKernelOperator D hv hsv).comp
      ((multiplicationOperator g).comp (compactVectorKernelOperator D ht hst).adjoint) f) i)
    (((compactVectorKernelOperator D ht hst).comp
      ((multiplicationOperator g).comp (compactVectorKernelOperator D hv hsv).adjoint) f) i)
  filter_upwards [h₁, h₂, hsum] with x hx₁ hx₂ hxsum
  refine (hxsum.trans (congrArg₂ (· + ·) hx₁ hx₂)).trans ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_add
    (integrable_compactCrossKernel_action D (hv i) (hsv i) (ht j) (hst j) g (f j) x)
    (integrable_compactCrossKernel_action D (ht i) (hst i) (hv j) (hsv j) g (f j) x)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [← add_mul, ← integral_add
    (integrable_compactCrossKernel_section D (hv i) (hsv i) (ht j) (hst j) g x y)
    (integrable_compactCrossKernel_section D (ht i) (hst i) (hv j) (hsv j) g x y)]
  simp only [add_mul]

/-- Joint C¹ regularity and common compact support give an actual operator
norm derivative and its full integral formula (`app:ch_osc:prop:osc-normal`).
Neither differentiability nor the kernel formula is a hypothesis. -/
theorem exists_compactVectorKernel_normalDerivative (D : Set U)
    {t : Fin r → ℝ → E × U → ℂ}
    (ht : ∀ i, ContDiff ℝ 1 (Function.uncurry (t i)))
    {S : Set (E × U)} (hS : IsCompact S)
    (hs : ∀ i s z, z ∉ S → t i s z = 0)
    (g : Lp ℂ ∞ (volume.restrict D)) (s₀ : ℝ) :
    let T := fun s ↦ compactVectorKernelOperator D (t := fun i x u ↦ t i s (x, u))
      (fun i ↦ continuous_kernelSlice (ht i) s)
      (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s)
    ∃ E' : NormalOutputL2 d r →L[ℂ] NormalOutputL2 d r,
      HasDerivAt (fun s ↦ (T s).comp ((multiplicationOperator g).comp (T s).adjoint))
        E' s₀ ∧
      ∀ f i, (E' f) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y,
        (∫ u in D, deriv (fun s ↦ t i s (x, u) * star (t j s (y, u))) s₀ * g u) * f j y := by
  dsimp only
  refine ⟨_, hasDerivAt_compactVectorKernel_maskedNormal D ht hS hs g s₀, ?_⟩
  intro f i
  have h := compactVectorKernelOperator_cross_add_ae_integral D
    (t := fun i x u ↦ t i s₀ (x, u))
    (v := fun i x u ↦ kernelParameterDeriv (t i) s₀ (x, u))
    (fun i ↦ continuous_kernelSlice (ht i) s₀)
    (fun i ↦ hasCompactSupport_kernelSlice hS (hs i) s₀)
    (fun i ↦ continuous_kernelParameterDeriv_slice (ht i) s₀)
    (fun i ↦ hasCompactSupport_kernelParameterDeriv (ht i) hS (hs i) s₀) g f i
  convert h using 1
  funext x
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext y
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  dsimp only
  rw [((hasDerivAt_kernelParameterDeriv (ht i) s₀ (x, u)).fun_mul
    (hasDerivAt_kernelParameterDeriv (ht j) s₀ (y, u)).star).deriv]

end JanetCartan.NormalComparison
