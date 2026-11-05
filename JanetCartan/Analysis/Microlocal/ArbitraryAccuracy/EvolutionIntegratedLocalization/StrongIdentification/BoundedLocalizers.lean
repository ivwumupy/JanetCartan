module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.VectorGraph
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic

/-!
# Bounded realizations of the physical proof localizers

The compact real symbols in `app:ch_regular:eq:chain-tail` give bounded left
quantizations by the existing compact vector graph construction. Their literal
Hilbert adjoints are the right quantizations. These maps are constructed before
any elapsed shell estimate; no localization estimate is a premise.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

/-- Both quantizations of a compact physical proof symbol have bounded L²
realizations. The right map is exactly the adjoint of the left map. In
particular its formula holds on every L² datum, so applying the input
localizer does not require an assumed uncut graph action. Consumer: the
finite elapsed-kernel realization for `app:ch_regular:eq:chain-tail`. -/
theorem exists_bounded_physicalLocalizers {ρ : ℝ} (hρ : ρ ≠ 0)
    (m : LocalizerSymbol n) (hm : Continuous m) (hms : HasCompactSupport m) :
    ∃ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) →
        M u =ᵐ[volume] fun x ↦ WithLp.toLp 2 (leftLocalizer ρ m (fun y ↦ (u y).ofLp) x)) ∧
      (∀ u : H, M.adjoint u =ᵐ[volume] fun x ↦
        WithLp.toLp 2 (rightLocalizer ρ m (fun y ↦ (u y).ofLp) x)) := by
  let A : E → E → Matrix (Fin q) (Fin q) ℂ :=
    fun x ξ ↦ (m (x, ρ⁻¹ • ξ) : ℂ) • 1
  have hc (i j : Fin q) : Continuous (fun p : E × E ↦ A p.1 p.2 i j) := by
    dsimp [A]
    exact (Complex.continuous_ofReal.comp
      (hm.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))).mul continuous_const
  have hs (i j : Fin q) : HasCompactSupport (fun p : E × E ↦ A p.1 p.2 i j) := by
    apply HasCompactSupport.intro
      (hms.image (continuous_fst.prodMk (continuous_snd.const_smul ρ)))
    intro p hp
    have hz : m (p.1, ρ⁻¹ • p.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hp ⟨(p.1, ρ⁻¹ • p.2), h, by simp [smul_smul, hρ]⟩
    simp [A, hz]
  have hS : Continuous (Function.uncurry (fun x ξ : E ↦ inner ℝ x ξ)) := by
    exact continuous_fst.inner continuous_snd
  refine ⟨LowBounds.compactVectorGraph hS hc hs, ?_, ?_⟩
  · intro u hu
    exact LowBounds.compactVectorGraph_ae_graphOperator hS hc hs u hu
  · intro u
    refine (LowBounds.compactVectorGraph_adjoint_ae_reverseIntegral hS hc hs u).trans ?_
    apply Eventually.of_forall
    intro x
    apply congrArg (WithLp.toLp 2)
    unfold rightLocalizer graphOperator
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [] with y
    have hp : star (graphOscillation (fun a b : E ↦ inner ℝ a b) y x ξ) =
        graphOscillation (fun a b : E ↦ inner ℝ a b) x y ξ := by
      simp only [graphOscillation, Complex.star_def, ← Complex.exp_conj,
        map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1
      push_cast
      ring
    simp only [A, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal, hp]

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
