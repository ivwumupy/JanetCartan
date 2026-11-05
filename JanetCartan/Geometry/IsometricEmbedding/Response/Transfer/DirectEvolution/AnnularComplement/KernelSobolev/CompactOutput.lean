module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.CompactSobolev
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.KernelSobolev.ParameterJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Hilbert.CompactFamily

/-!
# Compact vector Sobolev reconstruction of annular outputs

The final compact-output deduction in `app:ch_response:lem:energy-carrier-jets`.
The shared scalar compact Sobolev conversion and exact vector L² coordinate
isometry give membership and norms in the existing vector Fourier spaces.
The physical output support is fixed before the family member and accuracy.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open LowEnvelope Pseudodifferential AmplitudeBound

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Compact-output conversion into the existing vector Fourier Sobolev space,
including arbitrary real orders. Consumer: the actual parameter derivatives
of the annular frequency integral in `app:ch_response:lem:energy-carrier-jets`.
The hypotheses are pointwise classical derivative bounds, not Sobolev bounds. -/
theorem exists_annular_compact_vectorSobolev (s : ℝ) (m : ℕ) (hsm : s ≤ m)
    (u : E → F) (hu : ContDiff ℝ ∞ u) {S : Set E} (hS : IsCompact S)
    (hs : Function.support u ⊆ S) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ B) :
    ∃ hmem : MemLp u 2 volume, MemVectorFourierSobolev s (hmem.toLp u) ∧
      vectorFourierSobolevNorm s (hmem.toLp u) ≤
        (r : ℝ) * compactCoordinateSobolevConstant n m * Real.sqrt (volume.real S) * B := by
  have hcoord (a : Fin r) (α : List (Fin n)) (hα : α.length ≤ m) (x : E) :
      ‖euclideanCoordinateDerivList α (fun y ↦ u y a) x‖ ≤ B := by
    let T := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a).restrictScalars ℝ
    have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one
      (fun z ↦ by simpa [T] using PiLp.norm_apply_le z a)
    have hc : ContDiff ℝ ∞ (fun y ↦ u y a) := T.contDiff.comp hu
    apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hc α x).trans
    exact ((T.norm_iteratedFDeriv_comp_left hu.contDiffAt (by simp)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hT)).trans (hb α.length hα x)
  obtain ⟨hmem, hc, hmc, hnc, _⟩ :=
    exists_compactCoordinateSobolev_components m u hu hS hs hB hcoord
  have he (a : Fin r) : finiteL2CoordinateIsometry volume (hmem.toLp u) a =
      (hc a).toLp (fun x ↦ u x a) := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume (hmem.toLp u) a,
      hmem.coeFn_toLp, (hc a).coeFn_toLp] with x hx hy hz
    exact hx.trans ((congrArg (fun z : F ↦ z a) hy).trans hz.symm)
  refine ⟨hmem, ?_, ?_⟩
  · intro a
    rw [he a]
    exact (hmc a).mono hsm
  · calc
      _ ≤ ∑ a, fourierSobolevNorm s
          (finiteL2CoordinateIsometry volume (hmem.toLp u) a) :=
        matrixFourierSobolevNorm_le_sum _ _
      _ ≤ ∑ _a : Fin r,
          compactCoordinateSobolevConstant n m * Real.sqrt (volume.real S) * B := by
        apply Finset.sum_le_sum
        intro a _
        rw [he a]
        exact (fourierSobolevNorm_mono (hmc a) hsm).trans (hnc a)
      _ = _ := by simp [mul_assoc]

open Complement.ParameterDerivatives.Hilbert

/-- The compact-family realization transfers joint pointwise precision to
actual parameter derivatives in vector L² and in every real Fourier Sobolev
space. The consumer supplies joint precision by frequency integration, not
by a hypothesis on these L² derivatives. Source:
`app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_annularL2Family_sobolev_precision
    {P I : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} (hU : IsOpen U) {S : Set E} (hS : IsCompact S) [CompactSpace S]
    (g : I → P × E → F) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U ×ˢ univ))
    (hs : ∀ i c, c ∈ U → ∀ x ∉ S, g i (c, x) = 0)
    (lam A : I → ℝ) (hlam : ∀ i, 1 ≤ lam i) (hA : ∀ i, 0 ≤ A i)
    (hprec : ∀ j (Q : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ i z, z ∈ U ×ˢ univ →
      ‖iteratedFDeriv ℝ j (g i) z‖ ≤ D * A i * lam i ^ (-Q)) :
    (∀ i, ContDiffOn ℝ ∞
      (compactVectorL2Family hS (fun c x ↦ g i (c, x))) U) ∧
    ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ D : ℝ, 0 ≤ D ∧
      ∀ i c, c ∈ U → ∀ v : Fin k → P, (∀ a, ‖v a‖ ≤ 1) →
      MemVectorFourierSobolev s (iteratedFDeriv ℝ k
        (compactVectorL2Family hS (fun a x ↦ g i (a, x))) c v) ∧
      vectorFourierSobolevNorm s (iteratedFDeriv ℝ k
        (compactVectorL2Family hS (fun a x ↦ g i (a, x))) c v) ≤
        D * A i * lam i ^ (-Q) := by
  refine ⟨fun i ↦ contDiffOn_compactVectorL2Family hS hU (hg i), ?_⟩
  intro s k Q
  obtain ⟨m, hsm⟩ := exists_nat_ge s
  choose D hD hb using fun j ↦ hprec (j + k) Q
  let T := ∑ j ∈ Finset.range (m + 1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ ↦ hD j)
  let C := (r : ℝ) * compactCoordinateSobolevConstant n m * Real.sqrt (volume.real S)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (compactCoordinateSobolevConstant_pos n m).le) (Real.sqrt_nonneg _)
  refine ⟨C * T, mul_nonneg hC hT, ?_⟩
  intro i c hc v hv
  let u : E → F := fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g i (a, x)) c v
  have hu : ContDiff ℝ ∞ u := by
    apply contDiffOn_univ.mp
    exact (contDiffOn_annularParameterJet hU (hg i) k v).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun x _ ↦ ⟨hc, mem_univ x⟩)
  have hus : Function.support u ⊆ S := by
    intro x hx
    by_contra hn
    exact hx (annularParameterJet_eq_zero_off_support hU (hs i) k v hc hn)
  have hB : 0 ≤ T * A i * lam i ^ (-Q) :=
    mul_nonneg (mul_nonneg hT (hA i)) (Real.rpow_nonneg (zero_le_one.trans (hlam i)) _)
  have hub (j : ℕ) (hj : j ≤ m) (x : E) :
      ‖iteratedFDeriv ℝ j u x‖ ≤ T * A i * lam i ^ (-Q) := by
    apply (norm_annularParameterJet_spatial_le hU (hg i) k v hv j hc x).trans
    apply (hb j i (c, x) ⟨hc, mem_univ x⟩).trans
    have hjT : D j ≤ T :=
      Finset.single_le_sum (fun a _ ↦ hD a) (Finset.mem_range_succ_iff.mpr hj)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjT (hA i))
      (Real.rpow_nonneg (zero_le_one.trans (hlam i)) _)
  obtain ⟨hmem, hsob, hnorm⟩ :=
    exists_annular_compact_vectorSobolev s m hsm u hu hS hus hB hub
  have he : iteratedFDeriv ℝ k
      (compactVectorL2Family hS (fun a x ↦ g i (a, x))) c v = hmem.toLp u := by
    apply Lp.ext
    exact (iteratedFDeriv_compactVectorL2Family_ae hS
      (g := fun a x ↦ g i (a, x)) hU (hg i) (hs i) k v hc).trans
      hmem.coeFn_toLp.symm
  rw [he]
  refine ⟨hsob, hnorm.trans_eq ?_⟩
  dsimp [C]
  ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
