module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.Differentiation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.KernelJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.ParameterJets

/-!
# Parameter differentiation through the physical frequency integral

The pointwise representative needed for the actual L² derivatives in
`app:ch_response:lem:energy-carrier-jets`. The joint kernel majorants supplied
by radial integration also dominate its parameter slices; freezing the physical
output costs no order or scale loss.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open Complement.ParameterDerivatives.MixedGrades

variable {n : ℕ} {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => Euclidean n

/-- Every parameter derivative passes through the full physical frequency
integral, as a genuine Bochner-integrable multilinear map and after evaluation
on arbitrary directions. Consumer: the L² derivative representative in
`app:ch_response:lem:energy-carrier-jets`. -/
theorem annularIntegral_parameter_derivative
    {κ : E → P × E → F} {U : Set P} (hU : IsOpen U)
    (hκ : ∀ ξ, ContDiffOn ℝ ∞ (κ ξ) (U ×ˢ univ))
    (hm : ∀ z, z ∈ U ×ˢ univ → AEStronglyMeasurable (fun ξ ↦ κ ξ z) volume)
    (B : ℕ → E → ℝ) (hi : ∀ j, Integrable (B j))
    (hb : ∀ j ξ z, z ∈ U ×ˢ univ → ‖iteratedFDeriv ℝ j (κ ξ) z‖ ≤ B j ξ)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ U) (x : E) :
    Integrable (fun ξ ↦ iteratedFDeriv ℝ k (fun a ↦ κ ξ (a, x)) c) ∧
    iteratedFDeriv ℝ k (fun a ↦ ∫ ξ, κ ξ (a, x)) c v =
      ∫ ξ, iteratedFDeriv ℝ k (fun a ↦ κ ξ (a, x)) c v := by
  have hs (ξ : E) : ContDiffOn ℝ ∞ (fun a ↦ κ ξ (a, x)) U :=
    (hκ ξ).comp (contDiffOn_id.prodMk contDiffOn_const) (fun a ha ↦ ⟨ha, mem_univ x⟩)
  have hms (j : ℕ) (a : P) (ha : a ∈ U) :
      AEStronglyMeasurable (fun ξ ↦ iteratedFDeriv ℝ j (fun a ↦ κ ξ (a, x)) a) volume :=
    aestronglyMeasurable_annularKernel_jet hU (fun a ha ↦ hm (a, x) ⟨ha, mem_univ x⟩) hs j ha
  have hbs (j : ℕ) (ξ : E) (a : P) (ha : a ∈ U) :
      ‖iteratedFDeriv ℝ j (fun a ↦ κ ξ (a, x)) a‖ ≤ B j ξ := by
    let T : P →L[ℝ] P × E := (ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] E)
    have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (fun y ↦ by simp [T, Prod.norm_def])
    have hn := norm_iteratedFDeriv_affine_contraction_le T hT ((0 : P), x)
      (hU.prod isOpen_univ) (hκ ξ) j (x := a) (by simpa [T] using ha)
    apply le_trans ?_ (hb j ξ (a, x) ⟨ha, mem_univ x⟩)
    simpa [T] using hn
  have hint : Integrable (fun ξ ↦ iteratedFDeriv ℝ k (fun a ↦ κ ξ (a, x)) c) :=
    (hi k).mono' (hms k c hc) (ae_of_all _ (fun ξ ↦ hbs k ξ c hc))
  refine ⟨hint, ?_⟩
  rw [iteratedFDeriv_annularIntegral_of_jet_majorants hU hs hms B hi hbs k hc,
    ContinuousMultilinearMap.integral_apply hint]

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
