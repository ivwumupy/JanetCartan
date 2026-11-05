module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.Fubini

/-!
# Integrated compact full kernels and their adjoints

A compact full integrand produces the literal forward and reverse operators
in `app:ch_regular_base:eq:actual-adjoint-trade`. No geometric nondegeneracy
or symbol estimate is needed at this finite-cutoff stage.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
namespace JanetCartan.FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Construct both literal iterated integral identities from the continuous
compact full integrand. Consumer: `compactFullGraph_adjoint_ae`, for
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem exists_compactFullEntryOperator
    (F : Fin r → Fin r → (E × E) × E → ℂ)
    (hc : ∀ i j, Continuous (F i j)) (hs : ∀ i j, HasCompactSupport (F i j)) :
    ∃ T : H →L[ℂ] H,
      (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (∫ η, ∫ y, fun i ↦ ∑ j, F i j ((x, y), η) * u.val y j)) ∧
      (∀ u : graphTestSpace n r, T.adjoint (graphTestToLp u) =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (∫ η, ∫ x, fun j ↦ ∑ i, star (F i j ((x, y), η)) * u.val x i)) := by
  have hreg i j := compactEntry_integral_regular (hc i j) (hs i j)
  let k : Fin r → Fin r → E → E → ℂ := fun i j x y ↦ ∫ η, F i j ((x, y), η)
  let T := compactFullKernelOperator (k := k) (fun i j ↦ (hreg i j).1)
    (fun i j ↦ (hreg i j).2)
  refine ⟨T, ?_, ?_⟩
  · intro u
    refine (compactFullKernelOperator_test_ae (fun i j ↦ (hreg i j).1)
      (fun i j ↦ (hreg i j).2) u).trans (Eventually.of_forall fun x ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    funext i
    exact (compactEntry_integral_sum (fun i j p ↦ F i j ((x, p.2), p.1))
      (fun i j ↦ (hc i j).comp ((continuous_const.prodMk continuous_snd).prodMk continuous_fst))
      (fun i j ↦ compactEntry_forward_section (hs i j) x)
      (fun y ↦ (u.val y).ofLp) ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).continuous.comp
        u.property.1.continuous) i).symm
  · intro u
    refine (compactFullKernelOperator_adjoint_test_ae (fun i j ↦ (hreg i j).1)
      (fun i j ↦ (hreg i j).2) u).trans (Eventually.of_forall fun y ↦ ?_)
    apply congrArg (WithLp.toLp 2)
    funext j
    have he := compactEntry_integral_sum (fun j i p ↦ star (F i j ((p.2, y), p.1)))
      (fun j i ↦ ((hc i j).comp ((continuous_snd.prodMk continuous_const).prodMk
        continuous_fst)).star)
      (fun j i ↦ compactEntry_reverse_section (hs i j) y)
      (fun x ↦ (u.val x).ofLp) ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).continuous.comp
        u.property.1.continuous) j
    simpa only [k, Complex.star_def, integral_conj] using he.symm

end JanetCartan.FourierIntegral.FullLowBounds
