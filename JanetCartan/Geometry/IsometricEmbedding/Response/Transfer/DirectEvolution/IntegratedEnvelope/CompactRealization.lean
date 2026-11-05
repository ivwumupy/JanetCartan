module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Operators
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.Measurability

/-!
# Realization of the compact annular elapsed kernels

The annular localization has compact physical and frequency support. The
existing compact entry-kernel constructor therefore identifies the SAME
`fullGraphOperator` and its literal adjoint, without any operator hypothesis.
This supplies the test realization needed for elapsed-time measurability in
`app:ch_response:eq:direct-envelope-profile`. Quantitative bounds still come
from the primitive annular Sobolev theorems, not from this compact construction.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope
open FourierIntegral FourierIntegral.FullLowBounds
open RegularSector.Characteristic.EvolutionIntegral
open AnnularSobolev
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Continuous compact full amplitudes realize the canonical graph and its
literal adjoint on tests. This discharges, rather than assumes, the finite
kernel realization used in `app:ch_response:eq:direct-envelope-profile`.
The only construction invoked is `exists_compactFullEntryOperator`. -/
theorem compact_fullGraphOperator_realizations
    (S : E → E → ℝ) (hS : Continuous (Function.uncurry S))
    (A : FullAmplitude n r)
    (hA : Continuous (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2))
    {X Y K : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K)
    (hs : ∀ x y ξ, x ∉ X ∨ y ∉ Y ∨ ξ ∉ K → A x y ξ = 0) :
    (∀ u : graphTestSpace n r,
      fullGraphOperator S A (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
    (∀ u : graphTestSpace n r,
      (fullGraphOperator S A).adjoint (graphTestToLp u) =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (reverseGraphOperator S
          (fun x y ξ ↦ (A x y ξ).conjTranspose) (fun x ↦ (u.val x).ofLp) y)) := by
  let c : ℂ := ((2 * Real.pi) ^ n : ℂ)⁻¹
  let F : Fin r → Fin r → (E × E) × E → ℂ := fun i j p ↦
    c * graphOscillation S p.1.1 p.1.2 p.2 * A p.1.1 p.1.2 p.2 i j
  have hc (i j : Fin r) : Continuous (F i j) := by
    have ha := (AmplitudeBound.matrixEntryEvaluation i j).continuous.comp hA
    have hp : Continuous (fun p : (E × E) × E ↦ S p.1.1 p.2) :=
      hS.comp (continuous_fst.fst.prodMk continuous_snd)
    have hg : Continuous (fun p : (E × E) × E ↦ graphOscillation S p.1.1 p.1.2 p.2) := by
      unfold graphOscillation
      fun_prop
    exact (continuous_const.mul hg).mul ha
  have hfs (i j : Fin r) : HasCompactSupport (F i j) := by
    apply HasCompactSupport.intro ((hX.prod hY).prod hK)
    rintro ⟨⟨x, y⟩, ξ⟩ hp
    have hz : A x y ξ = 0 := hs x y ξ (by simpa only [mem_prod, not_and_or, or_assoc] using hp)
    simp [F, hz]
  obtain ⟨T, hT, hTa⟩ := exists_compactFullEntryOperator F hc hfs
  have hf (u : graphTestSpace n r) (x : E) :
      WithLp.toLp 2 (∫ ξ, ∫ y, fun i ↦ ∑ j, F i j ((x, y), ξ) * u.val y j) =
        graphTestOutput S A u x := by
    change WithLp.toLp 2 _ = WithLp.toLp 2 (c • _)
    apply congrArg (WithLp.toLp 2)
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ξ
    dsimp only
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    funext i
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hreal (u : graphTestSpace n r) :
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u :=
    (hT u).trans (Eventually.of_forall (hf u))
  rw [fullGraphOperator_eq_of_realizes S A T hreal]
  refine ⟨hreal, fun u ↦ (hTa u).trans (Eventually.of_forall fun y ↦ ?_)⟩
  change WithLp.toLp 2 _ = WithLp.toLp 2 (c • _)
  apply congrArg (WithLp.toLp 2)
  rw [← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  dsimp only
  rw [← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  funext j
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    smul_eq_mul, Finset.mul_sum, F]
  apply Finset.sum_congr rfl
  intro i _
  have hcstar : star c = c := by simp [c]
  simp only [star_mul, hcstar]
  ring

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope
