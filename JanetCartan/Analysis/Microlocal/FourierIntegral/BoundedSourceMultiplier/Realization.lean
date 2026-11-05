module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.BoundedSourceMultiplier.Multipliers

/-!
# Bounded realization of the exact source symbol

The source-independent low graph constructor supplies `T` and its Schwartz
realization. Multiplication by the fixed source mask then constructs a bounded
operator for the SAME literal `sourceSymbol`. No source-symbol operator bound
or source-multiplication identity is assumed. The principal graph and the
order-minus-one remainder budget are separate construction obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius ENNReal
namespace JanetCartan.FourierIntegral.BoundedSourceMultiplier
open LowBounds LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual bounded source composition, before any principal/remainder
split. Its literal symbol is proved in `sourceSymbolOperator_realizes`.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
def sourceSymbolOperator (T : H →L[ℂ] H) (m : SchwartzMap E ℂ) : H →L[ℂ] H :=
  T ∘L physicalMultiplier (m.toLp ∞)

/-- A proved operator budget for the complete shifted source symbol; it does
not assert a remainder order. Source: the fixed-source formula. -/
theorem norm_sourceSymbolOperator_le (T : H →L[ℂ] H) (m : SchwartzMap E ℂ) :
    ‖sourceSymbolOperator T m‖ ≤ ‖T‖ * ‖m.toLp ∞‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_physicalMultiplier_le _) (norm_nonneg T))

/-- Composition of the actual low graph with a fixed Schwartz source mask
realizes the original absolutely convergent `sourceSymbol`, including all
shifted-frequency pieces. The input realization is exactly the output of
`LowBounds.exists_graphL2_of_primitive_inputs`; the source identity is deduced
by Fourier inversion, Fubini and the regularized limit already proved in
`graphOperator_sourceSymbol`. Source:
`app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbolOperator_realizes
    (S : E → E → ℝ) (A : E → E → Matrix (Fin r) (Fin r) ℂ)
    (T : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x))
    (m : SchwartzMap E ℂ) (hS : ∀ x, Continuous (S x))
    (hA : ∀ x, Continuous (A x)) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (u : SchwartzMap E (Fin r → ℂ)) :
    sourceSymbolOperator T m (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ sourceSymbol S A m z η) u x) := by
  simp only [sourceSymbolOperator, ContinuousLinearMap.comp_apply]
  rw [physicalMultiplier_schwartzVectorToLp _ m m.hasTemperateGrowth (m.coeFn_toLp ∞)]
  refine (hT _).trans (Eventually.of_forall ?_)
  intro x
  apply congrArg (WithLp.toLp 2)
  rw [SchwartzMap.smulLeftCLM_apply m.hasTemperateGrowth]
  exact graphOperator_sourceSymbol S A m u x (hS x) (hA x) C hC k (hb x)

/-- The same source-symbol operator with the actual input cutoff realizes
`T_b Πin` on Schwartz inputs. All cutoff shoulders remain in `q`; no plateau
is used. Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbolOperator_inputCutoff_realizes
    (S : E → E → ℝ) (A : E → E → Matrix (Fin r) (Fin r) ℂ)
    (T : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x))
    (m : SchwartzMap E ℂ) (hS : ∀ x, Continuous (S x))
    (hA : ∀ x, Continuous (A x)) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (a : Lp ℂ ∞ (volume : Measure E)) (q : E → ℂ) (hq : q.HasTemperateGrowth)
    (ha : a =ᵐ[volume] fun ξ ↦ q ((2 * Real.pi) • ξ))
    (u : SchwartzMap E (Fin r → ℂ)) :
    (sourceSymbolOperator T m ∘L inputFrequencyCutoff a) (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ sourceSymbol S A m z η)
        (sourceInputFrequencyCutoff q hq u) x) := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [inputFrequencyCutoff_schwartzVectorToLp a q hq ha]
  exact sourceSymbolOperator_realizes S A T hT m hS hA C hC k hb _

/-- The bounded source symbol is unique because compact smooth tests are
dense in the original Euclidean L². Source: the fixed-source formula. -/
theorem sourceSymbolOperator_unique
    (S : E → E → ℝ) (A : E → E → Matrix (Fin r) (Fin r) ℂ)
    (T : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x))
    (m : SchwartzMap E ℂ) (hS : ∀ x, Continuous (S x))
    (hA : ∀ x, Continuous (A x)) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (B : H →L[ℂ] H)
    (hB : ∀ u : graphTestSpace n r, B (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ sourceSymbol S A m z η)
        (graphTestToSchwartz u) x)) :
    T ∘L physicalMultiplier (m.toLp ∞) = B := by
  apply DFunLike.coe_injective
  apply denseRange_graphTestToLp.equalizer (map_continuous _) (map_continuous _)
  funext u
  apply Lp.ext
  have hs := sourceSymbolOperator_realizes S A T hT m hS hA C hC k hb
    (graphTestToSchwartz u)
  rw [schwartzVectorToLp_graphTestToSchwartz] at hs
  exact hs.trans (hB u).symm

end JanetCartan.FourierIntegral.BoundedSourceMultiplier
