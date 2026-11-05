module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReconstructionSize
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.SourceSize
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier

/-!
# The actual reduced restriction profile supplies reconstruction coordinates

The normalized solver gives a smooth real solution with a whole-space
restriction bound. Its actual L² class determines the complexified coordinate
family used by the existing ambient reconstruction. Genuine weak extensions
prove the Fourier bounds at the same order. Compact full-tensor source jets
supply the other input family. Neither family is independently reselected at
different Sobolev orders (`app:ch_pairs:eq:pairs-lag-sum-size`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open LocalSobolev ArbitraryAccuracy Pseudodifferential AmplitudeBound
open ResponseTransfer ResponseTransfer.LowEnvelope
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The same real reduced solution supplies one complex coordinate family
before all orders. Its restriction profile, proved for the normalized product
response, gives the Fourier reconstruction input without a derivative loss
(`app:ch_pairs:eq:pairs-lag-sum-size`). -/
theorem exists_reduced_solution_coordinate_size_constants
    (B : ℕ → ℝ) (hB : ∀ r, 0 ≤ B r) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (lam : ℝ) (g : E → Euclidean n) (hg : MemLp g 2 volume),
      (∀ r : ℕ, MemRestrictionSobolev univ r ((hg.restrict univ).toLp g) ∧
        restrictionSobolevNorm univ r ((hg.restrict univ).toLp g) ≤ B r * lam^r) →
      ∃ ug : PiLp 2 (fun _ : Fin n ↦ L2),
        (∀ j, ug j =ᵐ[volume] fun x ↦ (g x j : ℂ)) ∧
        ∀ r : ℕ, MemMatrixFourierSobolev (r : ℝ) ug ∧
          matrixFourierSobolevNorm (r : ℝ) ug ≤ D r * lam^r := by
  let basis := EuclideanSpace.basisFun (Fin n) ℝ
  choose C hC hbound using fun r ↦ componentFourierSobolev_extension_bounds n r basis
  refine ⟨fun r ↦ C r * B r, fun r ↦ mul_nonneg (hC r).le (hB r), ?_⟩
  intro lam g hg hraw
  let z := hg.toLp g
  let ug : PiLp 2 (fun _ : Fin n ↦ L2) := WithLp.toLp 2 (fun j ↦ realComponentL2 basis j z)
  have hrep j : ug j =ᵐ[volume] fun x ↦ (g x j : ℂ) := by
    filter_upwards [realComponentL2_coeFn basis j z, hg.coeFn_toLp] with x hx hz
    change (realComponentL2 basis j z) x = _
    change z x = g x at hz
    simpa only [basis, EuclideanSpace.basisFun_inner, hz] using hx
  refine ⟨ug, hrep, fun r ↦ ?_⟩
  let v : LocalL2 univ (Euclidean n) := (hg.restrict univ).toLp g
  have heq (e : SobolevExtension univ r v) : e.toL2 = z := by
    apply Lp.ext
    have he : e.toFun =ᵐ[volume] g := by
      simpa only [Measure.restrict_univ] using
        e.restrict_eq.trans (hg.restrict univ).coeFn_toLp
    exact e.toL2_coeFn.trans (he.trans hg.coeFn_toLp.symm)
  have hfor (e : SobolevExtension univ r v) :
      MemMatrixFourierSobolev (r : ℝ) ug ∧
        matrixFourierSobolevNorm (r : ℝ) ug ≤ C r * e.jetNorm := by
    obtain ⟨hm, hb⟩ := hbound r univ v e
    rw [heq e] at hm hb
    have hnorm : matrixFourierSobolevNorm (r : ℝ) ug =
        componentFourierSobolevNorm basis (r : ℝ) z := by
      simp only [matrixFourierSobolevNorm, componentFourierSobolevNorm, ug,
        PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
    exact ⟨hm, hnorm ▸ hb⟩
  refine ⟨(hfor (hraw r).1.some).1, ?_⟩
  calc
    _ ≤ C r * restrictionSobolevNorm univ r v :=
      le_mul_restrictionSobolevNorm_of_extensions (hraw r).1 (hC r).le (fun e ↦ (hfor e).2)
    _ ≤ C r * (B r * lam^r) := mul_le_mul_of_nonneg_left (hraw r).2 (hC r).le
    _ = _ := by ring

/-- Complete compact tensor jets supply one pair-indexed Fourier family,
retaining every Frobenius entry and the original cutoff
(`app:ch_pairs:eq:pairs-lag-sum-size`). -/
private theorem exists_tensor_coordinate_size_constants
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

/-- The normalized reduced solution's restriction profile and the complete
tensor source jets imply the physical ambient size, with exactly the original
one-derivative carrier cost (`app:ch_pairs:eq:pairs-lag-sum-size`). The root
profile is the conclusion of `exists_normalized_product_reduced_solver_size_constants`;
the source jets come from `exists_signed_modulated_source_jet_constants`.
Every Fourier family and every norm conversion is constructed here. No
individual ambient size estimate is an input. -/
theorem exists_completedVariation_physical_size_of_restriction
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {b : ℝ} (hb : b < 1/2) (hψbox : tsupport ψ ⊆ {x | ∀ i, |x i| ≤ b})
    {S : Set E} (hS : IsCompact S)
    (C A B : ℕ → ℝ) (hC : ∀ r, 1 ≤ C r) (hA : ∀ r, 0 ≤ A r) (hB : ∀ r, 0 ≤ B r) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (F : E → Euclidean N) (Ω : Set E), IsOpen Ω → tsupport ψ ⊆ Ω →
      ContDiffOn ℝ ∞ F Ω → IsImmersionOn F Ω → HasFullNormalRankOn F Ω →
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
      ∀ r : ℕ, periodicSobolevNorm r
        (UniformStep.Periodization.cutToTorus ψ
          (AmbientResponse.completedVariation F g (ResponseSourceExtension.tensorFieldRealPart a))) ≤
            D r * lam^(r+1) := by
  obtain ⟨Dg, hDg, hroot⟩ := exists_reduced_solution_coordinate_size_constants (n := n) B hB
  obtain ⟨Da, hDa, hsource⟩ := exists_tensor_coordinate_size_constants hS A hA
  obtain ⟨D, hD, hphysical⟩ := exists_completedVariation_physical_size_constants
    (N := N) ψ hψ hψc hb hψbox C (fun r ↦ Dg r + Da r) hC
    (fun r ↦ add_nonneg (hDg r) (hDa r))
  refine ⟨D, hD, ?_⟩
  intro F Ω hΩ hψΩ hF himm hrank g a hgsm hasm hs hV hDer hSrc L lam hL hLlam
    hVB hDB hSB haj hg hraw r
  have hlam : 1 ≤ lam := hL.trans hLlam
  obtain ⟨ug, hgrep, hgb⟩ := hroot lam g hg hraw
  obtain ⟨ua, harep, hab⟩ := hsource lam hlam a hasm hs haj
  have hreal : (fun x ↦ euclideanRealPart (euclideanComplexInclusion (g x))) = g := by
    funext x
    apply PiLp.ext
    intro j
    simp
  have hbound := hphysical F Ω hΩ hψΩ hF himm hrank
    (fun x ↦ euclideanComplexInclusion (g x)) a
    ((euclideanComplexInclusion (ι := Fin n)).contDiff.comp hgsm) hasm hV hDer hSrc
    L lam hL hLlam hVB hDB hSB ug ua hgrep harep
    (fun p ↦ ⟨(hgb p).1, (hgb p).2.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hDa p)) (pow_nonneg (zero_le_one.trans hlam) _))⟩)
    (fun p ↦ ⟨(hab p).1, (hab p).2.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hDg p)) (pow_nonneg (zero_le_one.trans hlam) _))⟩) r
  simpa only [hreal] using hbound

end JanetCartan.SignedProductEstimates
