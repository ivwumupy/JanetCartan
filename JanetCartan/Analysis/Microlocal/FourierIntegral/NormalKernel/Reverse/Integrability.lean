module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Compact
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Absolute convergence of the reverse graph

The integrability obligations for the literal adjoint in
`app:ch_regular_base:eq:actual-normal-kernel`, consumed by
`compactGraph_adjoint_ae_reverseIntegral`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison AmplitudeBound

variable {n : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {a : Euclidean n → Euclidean n → ℂ}

private theorem continuous_reverseEntry
    (hS : Continuous (Function.uncurry S)) (ha : Continuous (Function.uncurry a))
    (y : Euclidean n) :
    Continuous (fun p : Euclidean n × Euclidean n ↦
      star (graphOscillation S p.2 y p.1) * star (a p.2 p.1)) := by
  have hS' := hS.comp continuous_swap
  have ha' := ha.comp continuous_swap
  unfold graphOscillation
  fun_prop

private theorem hasCompactSupport_reverseEntry
    (hs : HasCompactSupport (Function.uncurry a)) (y : Euclidean n) :
    HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      star (graphOscillation S p.2 y p.1) * star (a p.2 p.1)) := by
  exact HasCompactSupport.mul_left
    ((hs.comp_homeomorph (Homeomorph.prodComm _ _)).comp_left (star_zero ℂ))

/-- Each physical position integral in the reverse graph is absolutely
convergent on L² inputs (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem integrable_reverseEntry_mul_L2
    (hS : Continuous (Function.uncurry S)) (ha : Continuous (Function.uncurry a))
    (hs : HasCompactSupport (Function.uncurry a))
    (f : Lp (α := Euclidean n) ℂ 2) (y η : Euclidean n) :
    Integrable (fun x ↦ star (graphOscillation S x y η) * star (a x η) * f x) :=
  integrable_compactKernel_mul_L2
    (t := fun η x ↦ star (graphOscillation S x y η) * star (a x η))
    (continuous_reverseEntry hS ha y) (hasCompactSupport_reverseEntry hs y) f η

/-- The outer covector integral of each reverse channel is absolutely convergent;
this justifies finite channel summation in the literal adjoint
(`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem integrable_reverseEntry_integral_L2
    (hS : Continuous (Function.uncurry S)) (ha : Continuous (Function.uncurry a))
    (hs : HasCompactSupport (Function.uncurry a))
    (f : Lp (α := Euclidean n) ℂ 2) (y : Euclidean n) :
    Integrable (fun η ↦ ∫ x,
      star (graphOscillation S x y η) * star (a x η) * f x) := by
  exact (continuous_compactKernel_integral_L2
    (t := fun η x ↦ star (graphOscillation S x y η) * star (a x η))
    (continuous_reverseEntry hS ha y) (hasCompactSupport_reverseEntry hs y) f).integrable_of_hasCompactSupport
        (hasCompactSupport_compactKernel_integral_L2
          (hasCompactSupport_reverseEntry hs y) f)

end JanetCartan.FourierIntegral.NormalKernel
