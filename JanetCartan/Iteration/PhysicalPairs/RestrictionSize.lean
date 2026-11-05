module

public import JanetCartan.Iteration.PhysicalPairs.Reconstruction
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedReconstructionSize

/-!
# Original reduced/source profiles produce actual physical reconstruction size

For `main:prop:pairs`, construct the actual coordinate families from the
normalized inverse's real restriction profile and complete tensor source jets.
The SAME real Schwartz output of the literal ambient formula then has physical
radian size, at every order, with exactly one carrier power. No physical output
estimate or torus identification is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs
open LocalSobolev ArbitraryAccuracy Pseudodifferential AmplitudeBound
open ResponseTransfer ResponseTransfer.LowEnvelope SignedProductEstimates
open IsometricEmbedding.Reconstruction
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

private theorem tensor_coordinate_size_constants
    {S : Set E} (hS : IsCompact S) (A : ℕ → ℝ) (hA : ∀ r, 0 ≤ A r) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (lam : ℝ), 1 ≤ lam → ∀ a : E → Matrix (Fin n) (Fin n) ℂ,
      ContDiff ℝ ∞ a → tsupport a ⊆ S →
      (∀ x r, ‖iteratedFDeriv ℝ r a x‖ ≤ A r * lam^r) →
      ∃ ua : PiLp 2 (fun _ : Fin n × Fin n ↦ L2),
        (∀ ij, ua ij =ᵐ[volume] fun x ↦ a x ij.1 ij.2) ∧
        ∀ r : ℕ, MemMatrixFourierSobolev (r : ℝ) ua ∧
          matrixFourierSobolevNorm (r : ℝ) ua ≤ D r * lam^r := by
  let C := fun r ↦ compactCoordinateSobolevConstant n r * Real.sqrt (volume.real S) *
    ∑ j ∈ Finset.range (r+1), A j
  have hC r : 0 ≤ C r := mul_nonneg
    (mul_nonneg (compactCoordinateSobolevConstant_pos n r).le (Real.sqrt_nonneg _))
    (Finset.sum_nonneg (fun j _ ↦ hA j))
  refine ⟨fun r ↦ (n : ℝ)*(n : ℝ)*C r,
    fun r ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hC r), ?_⟩
  intro lam hlam a ha hs haj
  let π (ij : Fin n × Fin n) := matrixEntryEvaluation ij.1 ij.2
  have hπ ij : ‖π ij‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    simpa [π, matrixEntryEvaluation] using norm_matrixEntry_le_frobenius T ij.1 ij.2
  have has : HasCompactSupport a := hS.of_isClosed_subset (isClosed_tsupport _) hs
  have hmem (ij : Fin n × Fin n) : MemLp (fun x ↦ a x ij.1 ij.2) 2 volume :=
    ((π ij).contDiff.comp ha).continuous.memLp_of_hasCompactSupport
      (has.comp_left (π ij).map_zero)
  let ua : PiLp 2 (fun _ : Fin n × Fin n ↦ L2) :=
    WithLp.toLp 2 (fun ij ↦ (hmem ij).toLp (fun x ↦ a x ij.1 ij.2))
  refine ⟨ua, fun ij ↦ (hmem ij).coeFn_toLp, fun r ↦ ?_⟩
  have hcoord ij : MemFourierSobolev (r : ℝ) (ua ij) ∧
      fourierSobolevNorm (r : ℝ) (ua ij) ≤ C r * lam^r := by
    obtain ⟨hm, hsob, hb⟩ := exists_compactCoordinateSobolev r
      (fun x ↦ a x ij.1 ij.2) ((π ij).contDiff.comp ha) hS
      ((subset_tsupport _).trans ((tsupport_comp_subset (π ij).map_zero a).trans hs))
      (B := (∑ j ∈ Finset.range (r+1), A j) * lam^r)
      (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hA j)) (pow_nonneg (zero_le_one.trans hlam) _))
      (fun w hw x ↦ (norm_euclideanCoordinateDerivList_le_iteratedFDeriv
        ((π ij).contDiff.comp ha) w x).trans
        (((π ij).norm_iteratedFDeriv_comp_left ha.contDiffAt (by simp)).trans
          ((mul_le_of_le_one_left (norm_nonneg _) (hπ ij)).trans
            ((haj x w.length).trans (mul_le_mul
              (Finset.single_le_sum (fun j _ ↦ hA j) (Finset.mem_range_succ_iff.mpr hw))
              (pow_le_pow_right₀ hlam hw) (pow_nonneg (zero_le_one.trans hlam) _)
              (Finset.sum_nonneg (fun j _ ↦ hA j)))))))
    exact ⟨hsob, hb.trans_eq (by dsimp only [C]; ring)⟩
  refine ⟨fun ij ↦ (hcoord ij).1, (matrixFourierSobolevNorm_le_sum _ _).trans ?_⟩
  calc
    _ ≤ ∑ _ij : Fin n × Fin n, C r * lam^r := Finset.sum_le_sum fun ij _ ↦ (hcoord ij).2
    _ = _ := by simp; ring

/-- The actual normalized reduced restriction profile and full source jets
produce the SAME real Schwartz ambient field's physical norm, without an order
loss (`main:prop:pairs`). The root input is the proved normalized inverse size
producer; the source input is the proved complete signed carrier jet producer. -/
theorem exists_completedVariation_physicalWeighted_size_of_restriction
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {S : Set E} (hS : IsCompact S)
    (C A B : ℕ → ℝ) (hC : ∀ r, 1 ≤ C r) (hA : ∀ r, 0 ≤ A r) (hB : ∀ r, 0 ≤ B r) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (F : E → Euclidean N) (Ω : Set E), IsOpen Ω → tsupport ψ ⊆ Ω →
      ∀ (g : E → Euclidean n) (a : E → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ g → ContDiff ℝ ∞ a → tsupport a ⊆ S →
      (∀ l j, ContDiffOn ℝ ∞ (reconstructionValueEntry F l j) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionDerivativeEntry F l ij) Ω) →
      (∀ l ij, ContDiffOn ℝ ∞ (reconstructionSourceEntry F l ij) Ω) →
      ∀ (L lam : ℝ), 1 ≤ L → L ≤ lam →
      (∀ l j r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionValueEntry F l j) x‖ ≤ C r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionDerivativeEntry F l ij) x‖ ≤ C r * L^r) →
      (∀ l ij r, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ r (reconstructionSourceEntry F l ij) x‖ ≤ C r * L^r) →
      (∀ x r, ‖iteratedFDeriv ℝ r a x‖ ≤ A r * lam^r) →
      ∀ hg : MemLp g 2 volume,
      (∀ r : ℕ, MemRestrictionSobolev univ r ((hg.restrict univ).toLp g) ∧
        restrictionSobolevNorm univ r ((hg.restrict univ).toLp g) ≤ B r * lam^r) →
      ∀ u : 𝓢(E, Euclidean N),
      (∀ x, u x = ψ x • AmbientResponse.completedVariation F g
        (ResponseSourceExtension.tensorFieldRealPart a) x) →
      ∀ r : ℕ,
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight r ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤ D r * lam^(r+1) := by
  obtain ⟨Dg, hDg, hroot⟩ := exists_reduced_solution_coordinate_size_constants (n := n) B hB
  obtain ⟨Da, hDa, hsource⟩ := tensor_coordinate_size_constants hS A hA
  obtain ⟨D, hD, hphysical⟩ := exists_completedVariation_physicalWeighted_size_constants
    (N := N) ψ hψ hψc C (fun r ↦ Dg r + Da r) hC
    (fun r ↦ add_nonneg (hDg r) (hDa r))
  refine ⟨D, hD, ?_⟩
  intro F Ω hΩ hψΩ g a hgsm hasm hs hV hDer hSrc L lam hL hLlam
    hVB hDB hSB haj hg hraw u hu r
  have hlam : 1 ≤ lam := hL.trans hLlam
  obtain ⟨ug, hgrep, hgb⟩ := hroot lam g hg hraw
  obtain ⟨ua, harep, hab⟩ := hsource lam hlam a hasm hs haj
  have hreal : (fun x ↦ euclideanRealPart (euclideanComplexInclusion (g x))) = g := by
    funext x
    apply PiLp.ext
    intro j
    simp
  apply hphysical F Ω hΩ hψΩ
    (fun x ↦ euclideanComplexInclusion (g x)) a
    ((euclideanComplexInclusion (ι := Fin n)).contDiff.comp hgsm) hasm hV hDer hSrc
    L lam hL hLlam hVB hDB hSB ug ua hgrep harep
    (fun p ↦ ⟨(hgb p).1, (hgb p).2.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hDa p)) (pow_nonneg (zero_le_one.trans hlam) _))⟩)
    (fun p ↦ ⟨(hab p).1, (hab p).2.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hDg p)) (pow_nonneg (zero_le_one.trans hlam) _))⟩) u _ r
  simpa only [hreal] using hu

end JanetCartan.PhysicalPairs
