module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.BoundedSourceMultiplier.Realization

/-!
# The literal source remainder as a difference of bounded graphs

The integral subtraction is justified from the original polynomial amplitude
bound and Schwartz moments. Once the principal graph has been constructed,
its difference from the complete source symbol realizes the SAME remainder
defined in `SourceMultiplier`. The principal graph construction and the
order-minus-one jet budget are not established by this conditional deduction.
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
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace

/-- The literal principal source amplitude in
`app:ch_regular_base:eq:fixed-source-multiplication`. Consumer: the principal
low-graph construction and the exact bounded remainder split. -/
def sourcePrincipalSymbol (S : E → E → ℝ) (A : E → E → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap E ℂ) (x η : E) : Matrix (Fin r) (Fin r) ℂ :=
  m (gradient (S x) η) • A x η

/-- Subtraction commutes with the literal source-first integral. All needed
frequency integrability is proved from the original amplitude bound and the
fixed source Schwartz moments, with no remainder bound as a premise.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem graphOperator_sourceRemainder_eq_sub
    (S : E → E → ℝ) (A : E → E → Matrix (Fin r) (Fin r) ℂ)
    (m : SchwartzMap E ℂ) (u : SchwartzMap E (Fin r → ℂ)) (x : E)
    (hS : ContDiff ℝ 1 (S x)) (hA : Continuous (A x))
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k)) :
    graphOperator S (fun z _ η ↦ sourceRemainder S A m z η) u x =
      graphOperator S (fun z _ η ↦ sourceSymbol S A m z η) u x -
        graphOperator S (fun z _ η ↦ sourcePrincipalSymbol S A m z η) u x := by
  have hgrad : Continuous (gradient (S x)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hS.continuous_fderiv (by simp))
  have hp : Continuous (sourcePrincipalSymbol S A m x) :=
    (m.continuous.comp hgrad).smul hA
  have hib := sourceFourierIntegral_integrable S (sourceSymbol S A m) u x hS.continuous
    (sourceSymbol_stronglyMeasurable S A m x hS.continuous hA).aestronglyMeasurable
    (C * (1 + 2 ^ (k - 1)) *
      ∫ v, ‖sourceFourierTransform m v‖ + ‖v‖ ^ k * ‖sourceFourierTransform m v‖) k
    (fun η ↦ sourceSymbol_polynomial_majorant S A m x η C hC k hb)
  have hip := sourceFourierIntegral_integrable S (sourcePrincipalSymbol S A m) u x
    hS.continuous hp.aestronglyMeasurable (SchwartzMap.seminorm ℝ 0 0 m * C) k
    (fun η ↦ by
      change ‖m (gradient (S x) η) • A x η‖ ≤ _
      rw [norm_smul]
      exact (mul_le_mul (m.norm_le_seminorm ℝ _) (hb η) (norm_nonneg _)
        (apply_nonneg _ _)).trans_eq (mul_assoc _ _ _).symm)
  simp only [sourcePrincipalSymbol] at hip
  simp only [graphOperator_eq_sourceFourierIntegral, sourceRemainder,
    sourcePrincipalSymbol, Matrix.sub_mulVec, smul_sub]
  rw [integral_sub hib hip, smul_sub]

/-- A bounded operator for the exact remainder, once the separately constructed
principal graph is supplied. Source: the fixed-source formula. -/
def sourceRemainderOperator (T P : H →L[ℂ] H) (m : SchwartzMap E ℂ) : H →L[ℂ] H :=
  sourceSymbolOperator T m - P

/-- The difference operator realizes the literal `sourceRemainder`, including
all angular and low-frequency pieces. `P` must be produced by applying the
low graph constructor to `sourcePrincipalSymbol`; this theorem does not
replace that construction. Source: the fixed-source formula. -/
theorem sourceRemainderOperator_realizes
    (S : E → E → ℝ) (A : E → E → Matrix (Fin r) (Fin r) ℂ)
    (T P : H →L[ℂ] H)
    (hT : ∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x))
    (m : SchwartzMap E ℂ)
    (hP : ∀ u : SchwartzMap E (Fin r → ℂ), P (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (graphOperator S (fun z _ η ↦ sourcePrincipalSymbol S A m z η) u x))
    (hS : ∀ x, ContDiff ℝ 1 (S x)) (hA : ∀ x, Continuous (A x))
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hb : ∀ x η, ‖A x η‖ ≤ C * (1 + ‖η‖ ^ k))
    (u : SchwartzMap E (Fin r → ℂ)) :
    sourceRemainderOperator T P m (schwartzVectorToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2
        (graphOperator S (fun z _ η ↦ sourceRemainder S A m z η) u x) := by
  simp only [sourceRemainderOperator, sub_apply]
  filter_upwards [Lp.coeFn_sub (sourceSymbolOperator T m (schwartzVectorToLp u))
      (P (schwartzVectorToLp u)),
    sourceSymbolOperator_realizes S A T hT m (fun x ↦ (hS x).continuous) hA C hC k hb u,
    hP u] with x hsub hsource hprincipal
  rw [hsub, Pi.sub_apply, hsource, hprincipal, graphOperator_sourceRemainder_eq_sub S A m u x
    (hS x) (hA x) C hC k (hb x)]
  rfl

/-- The exact bounded split retains the input cutoff. Its principal graph
realization and its remainder realization are separate proved statements;
the order-minus-one budget is still required for a gain estimate.
Source: `app:ch_regular_base:eq:fixed-source-multiplication`. -/
theorem sourceSymbolOperator_eq_principal_add_remainder
    (T P : H →L[ℂ] H) (m : SchwartzMap E ℂ) (qin : Lp ℂ ∞ (volume : Measure E)) :
    T ∘L physicalMultiplier (m.toLp ∞) ∘L inputFrequencyCutoff qin =
      P ∘L inputFrequencyCutoff qin + sourceRemainderOperator T P m ∘L
        inputFrequencyCutoff qin := by
  ext f : 1
  simp [sourceRemainderOperator, sourceSymbolOperator]

/-- The source-cut mismatch is identity minus multiplication by the compact
square; its remainder has the required negative sign. This is an operator
identity, with `Πin` still present on every term. No assertion that
`1-χs²` is compactly supported is made.
Source: `app:ch_regular_base:eq:source-cut-normal`. -/
theorem sourceCutMismatch_eq_principal_add_remainder
    (T P : H →L[ℂ] H) (χ : E → ℝ) (hχ : Continuous χ) (hb : ∀ x, ‖χ x‖ ≤ 1)
    (m : SchwartzMap E ℂ) (hm : ∀ x, m x = (χ x : ℂ) ^ 2)
    (qin : Lp ℂ ∞ (volume : Measure E)) :
    T ∘L (ContinuousLinearMap.id ℂ H -
        sourceCutMultiplier χ hχ hb ∘L sourceCutMultiplier χ hχ hb) ∘L
      inputFrequencyCutoff qin =
      (T - P) ∘L inputFrequencyCutoff qin +
        (-sourceRemainderOperator T P m) ∘L inputFrequencyCutoff qin := by
  rw [sourceCutMultiplier_sq χ hχ hb m hm]
  ext f : 1
  simp [sourceRemainderOperator, sourceSymbolOperator]

end JanetCartan.FourierIntegral.BoundedSourceMultiplier
