module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.VectorGraph
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactPDO.Fubini

/-!
# The constructed compact graph normal is the existing vector PDO

For `app:ch_regular_base:eq:actual-normal-kernel` and
`app:ch_regular_base:eq:actual-normal-amplitude`, the actual compact graph cross
normal agrees with the existing vector two-position PDO. The proof identifies
its literal matrix integral on compact smooth tests and uses their L² density.

The normal-symbol budget and joint compact support are explicit conditional
inputs, to be produced by `jc-fio-low-primitive-normal-budget` and instantiated
by the parent `jc-fio-source-independent-l2` construction. These results do not supply primitive estimates
or the unregularized graph.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.LowBounds

open AmplitudeBound Pseudodifferential

variable {n r : ℕ}
local notation "E" => Euclidean n

/-- The actual compact cross normal acts by the literal matrix full-amplitude
operator on smooth compact tests (`app:ch_regular_base:eq:actual-normal-amplitude`).
The only extra inputs describe the exact symbol, not an operator identity. -/
theorem compactVectorGraph_cross_graphTest_ae_matrixFullAmplitudeOperator
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    {A B : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : E × E ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : E × E ↦ B p.1 p.2 j k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hcarrierB : ∀ y u, y ∉ K → B y u = 0)
    (hb : Continuous (Function.uncurry (cycleCrossNormalSymbol D S A B η J)))
    (hs : HasCompactSupport (Function.uncurry (cycleCrossNormalSymbol D S A B η J)))
    (u : graphTestSpace n r) :
    compactVectorGraph hS hA hsA ((compactVectorGraph hS hB hsB).adjoint
      (graphTestToLp u)) =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (matrixFullAmplitudeOperator
          (fun x y ξ ↦ cycleCrossNormalSymbol D S A B η J ξ (pairedPosition x y))
          (fun y j ↦ u.val y j) x) := by
  refine (compactVectorGraph_cross_ae_cycleIntegral G hS hA hsA hB hsB
    hcarrierA hcarrierB (graphTestToLp u)).trans ?_
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [compactSymbol_matrixFullAmplitudeOperator_eq_cycleIntegral _ hb hs
    u.val u.property.1.continuous u.property.2 x]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
  simp only [cycleCrossNormalSymbol_pairedPosition]
  change _ * ((graphTest_memLp u).toLp u.val) y j = _ * u.val y j
  rw [hy]

/-- The constructed compact cross normal is the existing vector two-position PDO
on all of Euclidean L². Testwise Fubini and density prove the equality; the
normal symbol is the literal cycle-rescaled symbol with both positions.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem compactVectorGraph_cross_eq_vectorTwoPositionL2Operator
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    {A B : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : E × E ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : E × E ↦ B p.1 p.2 j k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hcarrierB : ∀ y u, y ∉ K → B y u = 0)
    (hn : 0 < n) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A B η J) R M)
    (hs : HasCompactSupport (Function.uncurry (cycleCrossNormalSymbol D S A B η J))) :
    (compactVectorGraph hS hA hsA).comp (compactVectorGraph hS hB hsB).adjoint =
      vectorTwoPositionL2Operator hn R (cycleCrossNormalSymbol D S A B η J)
        hb.smooth hb.support M hb.entry_bound := by
  apply DFunLike.coe_injective
  refine denseRange_graphTestToLp.equalizer
    ((compactVectorGraph hS hA hsA).comp (compactVectorGraph hS hB hsB).adjoint).continuous
    (vectorTwoPositionL2Operator hn R (cycleCrossNormalSymbol D S A B η J)
      hb.smooth hb.support M hb.entry_bound).continuous ?_
  funext u
  apply Lp.ext
  refine (compactVectorGraph_cross_graphTest_ae_matrixFullAmplitudeOperator G hS hA hsA
    hB hsB hcarrierA hcarrierB hb.smooth.continuous hs u).trans ?_
  symm
  refine vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R _
    hb.smooth hb.support M hb.entry_bound u.val (graphTest_memLp u) ?_ ?_
  · intro j
    exact (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).restrictScalars ℝ).contDiff.comp
      u.property.1).of_le (by simp)
  · intro j
    exact u.property.2.comp_left (g := fun v : EuclideanSpace ℂ (Fin r) ↦ v j) rfl

/-- The compact graph cross normal equals the existing graph normal producer,
by its already checked equality with the vector PDO. This is the identity
consumed by the low graph estimate in `app:ch_regular_base:eq:actual-normal-kernel`. -/
theorem compactVectorGraph_cross_eq_graphNormalL2Operator
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    {A B : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hB : ∀ j k, Continuous (fun p : E × E ↦ B p.1 p.2 j k))
    (hsB : ∀ j k, HasCompactSupport (fun p : E × E ↦ B p.1 p.2 j k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hcarrierB : ∀ y u, y ∉ K → B y u = 0)
    (hn : 0 < n) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A B η J) R M)
    (hs : HasCompactSupport (Function.uncurry (cycleCrossNormalSymbol D S A B η J))) :
    (compactVectorGraph hS hA hsA).comp (compactVectorGraph hS hB hsB).adjoint =
      graphNormalL2Operator hn R (cycleCrossNormalSymbol D S A B η J) M hb := by
  rw [compactVectorGraph_cross_eq_vectorTwoPositionL2Operator G hS hA hsA hB hsB
    hcarrierA hcarrierB hn R M hb hs,
    vectorTwoPositionL2Operator_eq_graphNormalL2Operator]

/-- Conditional low L² bound for the actual compact graph, obtained from its
proved normal identity and the finite symbol budget. The parent construction
must supply this budget (`app:ch_regular_base:eq:fio-input`, Step 1). -/
theorem norm_compactVectorGraph_le_of_normalSymbol
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    {A : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hn : 0 < n) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A A η J) R M)
    (hs : HasCompactSupport (Function.uncurry (cycleCrossNormalSymbol D S A A η J))) :
    ‖compactVectorGraph hS hA hsA‖ ≤
      Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb.derivative 0 [] (by simp) 0)
  exact norm_graphRegularization_le hn R _ hM hb _
    (compactVectorGraph_cross_eq_graphNormalL2Operator G hS hA hsA hA hsA
      hcarrierA (fun y u hy ↦ hcarrierA y u (Or.inl hy)) hn R M hb hs)

/-- The literal Hilbert adjoint has the same conditional low bound, as required
in `app:ch_regular_base:eq:fio-input`. No weighted inverse or unregularized
graph is identified here. -/
theorem norm_compactVectorGraph_adjoint_le_of_normalSymbol
    {S : E → E → ℝ} {K D : Set E}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {δ : ℝ}
    (G : AveragedGradientChart S K D η J δ)
    {A : E → E → Matrix (Fin r) (Fin r) ℂ}
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ i k, Continuous (fun p : E × E ↦ A p.1 p.2 i k))
    (hsA : ∀ i k, HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i k))
    (hcarrierA : ∀ x u, x ∉ K ∨ u ∉ D → A x u = 0)
    (hn : 0 < n) (R M : ℝ)
    (hb : GraphNormalAmplitudeBounds (cycleCrossNormalSymbol D S A A η J) R M)
    (hs : HasCompactSupport (Function.uncurry (cycleCrossNormalSymbol D S A A η J))) :
    ‖(compactVectorGraph hS hA hsA).adjoint‖ ≤
      Real.sqrt ((r : ℝ) * r * (fixedBoxAmplitudeConstant n R * M)) := by
  simpa only [LinearIsometryEquiv.norm_map] using
    norm_compactVectorGraph_le_of_normalSymbol G hS hA hsA hcarrierA hn R M hb hs

end JanetCartan.FourierIntegral.LowBounds
