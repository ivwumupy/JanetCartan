module

public import JanetCartan.Analysis.Operator.MeasureEnvelopes.Derivatives
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Analytic adapters for the literal kernel jets

The measurability and multilinear-norm steps of
`app:ch_response:lem:energy-carrier-jets`. These close the input interface for
full-frequency integration from ordinary measurable kernels and bounds on
unit external direction tuples, without extra assumptions on derivative
measurability or on any integrated remainder.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement

variable {Z X F : Type} [MeasurableSpace Z] {μ : Measure Z}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem measurable_directional_derivative {f : Z → X → F} {U : Set X} (hU : IsOpen U)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (fun z ↦ f z x) μ)
    {x : X} (hx : x ∈ U) (hd : ∀ z, DifferentiableAt ℝ (f z) x) (v : X) :
    AEStronglyMeasurable (fun z ↦ fderiv ℝ (f z) x v) μ := by
  classical
  let q : ℝ → Z → F := fun t z ↦ t⁻¹ •
    ((if x + t • v ∈ U then f z (x + t • v) else f z x) - f z x)
  have hq (t : ℝ) : AEStronglyMeasurable (q t) μ := by
    dsimp [q]
    split_ifs with ht
    · exact ((hm _ ht).sub (hm x hx)).const_smul _
    · exact ((hm x hx).sub (hm x hx)).const_smul _
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) hq
  apply ae_of_all
  intro z
  have hv : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf : HasDerivAt (fun t : ℝ ↦ f z (x + t • v)) (fderiv ℝ (f z) x v) 0 := by
    have hz : HasFDerivAt (f z) (fderiv ℝ (f z) x) (x + (0 : ℝ) • v) := by
      simpa using (hd z).hasFDerivAt
    exact hz.comp_hasDerivAt 0 hv
  have he : (fun t ↦ q t z) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t ↦ t⁻¹ • (f z (x + t • v) - f z x)) := by
    have hn : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x + t • v ∈ U := by
      exact (by simpa using hv.continuousAt : ContinuousAt (fun t : ℝ ↦ x + t • v) 0)
        (by simpa using hU.mem_nhds hx)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with t ht
    simp [q, ht]
  apply Tendsto.congr' he.symm
  simpa using hf.tendsto_slope_zero

private theorem measurable_total_derivative [FiniteDimensional ℝ X] {f : Z → X → F} {U : Set X} (hU : IsOpen U)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (fun z ↦ f z x) μ)
    {x : X} (hx : x ∈ U) (hd : ∀ z, DifferentiableAt ℝ (f z) x) :
    AEStronglyMeasurable (fun z ↦ fderiv ℝ (f z) x) μ := by
  let b := Module.finBasis ℝ X
  let c := fun a ↦ (b.coord a).toContinuousLinearMap
  have he (z : Z) : fderiv ℝ (f z) x =
      ∑ a, (c a).smulRight (fderiv ℝ (f z) x (b a)) := by
    ext v
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
    change (fderiv ℝ (f z) x) v = ∑ a, b.repr v a • (fderiv ℝ (f z) x) (b a)
    calc
      _ = (fderiv ℝ (f z) x) (∑ a, b.repr v a • b a) :=
        congrArg (fderiv ℝ (f z) x) (b.sum_repr v).symm
      _ = _ := by rw [map_sum]; congr 1; ext a; exact map_smul _ _ _
  have hh : AEStronglyMeasurable (fun z ↦
      ∑ a, (c a).smulRight (fderiv ℝ (f z) x (b a))) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro a _
    exact (ContinuousLinearMap.smulRightL ℝ X F (c a)).continuous.comp_aestronglyMeasurable
      (measurable_directional_derivative hU hm hx hd (b a))
  exact hh.congr (ae_of_all _ (fun z ↦ (he z).symm))

/-- Frequency measurability of all actual external jets follows from
frequency measurability of the kernel and smoothness in the finite-dimensional
external variables. Consumer: dominated annular frequency differentiation in
`app:ch_response:lem:energy-carrier-jets`. No frequency smoothness is required. -/
theorem aestronglyMeasurable_annularKernel_jet [FiniteDimensional ℝ X] {f : Z → X → F} {U : Set X} (hU : IsOpen U)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (fun z ↦ f z x) μ)
    (hf : ∀ z, ContDiffOn ℝ ∞ (f z) U) (j : ℕ) {x : X} (hx : x ∈ U) :
    AEStronglyMeasurable (fun z ↦ iteratedFDeriv ℝ j (f z) x) μ := by
  induction j generalizing x with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ X F).symm.continuous.comp_aestronglyMeasurable (hm x hx)
  | succ j ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) F).symm.continuous.comp_aestronglyMeasurable
      (measurable_total_derivative hU (fun y hy ↦ ih hy) hx (fun z ↦
        ((hf z).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast ENat.natCast_lt_top j : (j : ℕ∞ω) < ∞)))

/-- Bounds on unit direction tuples give the full multilinear operator norm.
This converts the literal source-kernel jet interface of
`app:ch_response:lem:energy-carrier-jets` to an integrable norm majorant. -/
theorem annularJet_norm_le_of_unit_directions {k : ℕ} (T : X [×k]→L[ℝ] F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ v : Fin k → X, (∀ a, ‖v a‖ ≤ 1) → ‖T v‖ ≤ B) : ‖T‖ ≤ B := by
  apply ContinuousMultilinearMap.opNorm_le_bound hB
  intro v
  let w : Fin k → X := fun a ↦ ‖v a‖⁻¹ • v a
  have hw (a : Fin k) : ‖w a‖ ≤ 1 := by
    by_cases h : v a = 0
    · simp [w, h]
    · exact (norm_smul_inv_norm (𝕜 := ℝ) h).le
  have he : v = fun a ↦ ‖v a‖ • w a := by
    funext a
    by_cases h : v a = 0
    · simp [w, h]
    · simp [w, smul_smul, norm_ne_zero_iff.mpr h]
  calc
    ‖T v‖ = ‖T (fun a ↦ ‖v a‖ • w a)‖ := congrArg (fun q ↦ ‖T q‖) he
    _ = (∏ a, ‖v a‖) * ‖T w‖ := by
      rw [T.map_smul_univ, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg (fun a _ ↦ norm_nonneg _))]
    _ ≤ (∏ a, ‖v a‖) * B := mul_le_mul_of_nonneg_left (hb w hw) (Finset.prod_nonneg (fun a _ ↦ norm_nonneg _))
    _ = _ := mul_comm _ _

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
