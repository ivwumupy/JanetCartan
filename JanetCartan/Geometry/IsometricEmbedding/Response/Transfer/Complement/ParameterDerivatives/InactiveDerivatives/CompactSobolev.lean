module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.SobolevMembership
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Bounds

/-!
# Quantitative Sobolev reconstruction for the inactive source jets

The finite spatial jet profile of the expanded original source is converted to
its actual vector Fourier Sobolev profile. Consumer: the differentiated inactive
source in `app:ch_response:thm:response-literal-transfer`. The reconstruction
uses the existing coordinate derivative calculus and the literal Euclidean L²
measure, without a multiplication or differentiated-envelope estimate as input.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open Pseudodifferential FourierIntegral AmplitudeBound
variable {d r : ℕ}
local notation "E" => Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

private theorem coordinateDerivList_append (is js : List (Fin d)) (f : E → ℂ) :
    euclideanCoordinateDerivList (is ++ js) f =
      euclideanCoordinateDerivList is (euclideanCoordinateDerivList js f) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, euclideanCoordinateDerivList, ih]

private theorem scalarSobolev_le_coordinateNorms (s : ℕ) (g : E → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) {B : ℝ}
    (hb : ∀ is : List (Fin d), is.length ≤ s →
      ‖((contDiff_euclideanCoordinateDerivList hg is).continuous.memLp_of_hasCompactSupport
        (p := 2) (μ := volume) (hasCompactSupport_euclideanCoordinateDerivList hgs is)).toLp
        (euclideanCoordinateDerivList is g)‖ ≤ B) :
    fourierSobolevNorm (s : ℝ)
      ((hg.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgs).toLp g) ≤
        (1 + (d : ℝ)) ^ s * B := by
  induction s generalizing g with
  | zero => simpa [fourierSobolevNorm_zero, euclideanCoordinateDerivList] using hb [] (by simp)
  | succ s ih =>
    have hbase := ih g hg hgs (fun is hi ↦ hb is (hi.trans (Nat.le_succ _)))
    have hder (i : Fin d) := ih _ (contDiff_euclideanCoordinateDerivList hg [i])
      (hasCompactSupport_euclideanCoordinateDerivList hgs [i])
      (fun is hi ↦ by
        simpa only [coordinateDerivList_append] using hb (is ++ [i]) (by simp; omega))
    rw [Nat.cast_add, Nat.cast_one]
    apply (fourierSobolevNorm_le_coordinateDerivatives (by positivity)
      (memFourierSobolev_nat_toLp s g hg hgs)
      (fun i ↦ memFourierSobolev_nat_toLp s _ (contDiff_euclideanCoordinateDerivList hg [i])
        (hasCompactSupport_euclideanCoordinateDerivList hgs [i]))
      (hasEuclideanL2CoordinateDerivative_toLp g hg hgs)).trans
    calc
      _ ≤ (1 + (d : ℝ)) ^ s * B + ∑ i : Fin d, (1 + (d : ℝ)) ^ s * B :=
        add_le_add hbase (Finset.sum_le_sum (fun i _ ↦ hder i))
      _ = _ := by simp [pow_succ]; ring

private theorem scalarSobolev_le_compactJets {S : Set E} (hS : IsCompact S)
    (s : ℕ) (g : E → ℂ) (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ S)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ s, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    fourierSobolevNorm (s : ℝ) ((hg.continuous.memLp_of_hasCompactSupport
      (hS.of_isClosed_subset (isClosed_tsupport _) hs)).toLp g) ≤
        (1 + (d : ℝ)) ^ s * (B * Real.sqrt (volume.real S)) := by
  apply scalarSobolev_le_coordinateNorms s g hg
    (hS.of_isClosed_subset (isClosed_tsupport _) hs)
  intro is hi
  apply FiniteChain.Retarded.KernelSobolev.norm_toLp_le_of_support_bound _
    hS.measurableSet hS.measure_ne_top hB
    (fun x ↦ (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hg is x).trans
      (hb is.length hi x))
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  have hsupport : tsupport (euclideanCoordinateDerivList is g) ⊆ tsupport g := by
    clear hi
    induction is with
    | nil => exact Subset.rfl
    | cons i is ih => exact (tsupport_fderiv_apply_subset ℝ _).trans ih
  exact fun h ↦ hx (hs (hsupport h))

/-- A compactly supported vector source with bounded spatial jets has its
actual integer Fourier Sobolev bound on the same L² space. This is the finite
calculus producer used for the normalized carrier jet profile in
`app:ch_response:thm:response-literal-transfer`. -/
theorem vectorSobolev_le_compactJets {S : Set E} (hS : IsCompact S)
    (s : ℕ) (g : E → F) (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ S)
    (hmem : MemLp g 2 volume) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ s, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    vectorFourierSobolevNorm (s : ℝ) (hmem.toLp g) ≤
      ((r : ℝ) * (1 + (d : ℝ)) ^ s * Real.sqrt (volume.real S)) * B := by
  have hcoord (a : Fin r) : fourierSobolevNorm (s : ℝ)
      (finiteL2CoordinateIsometry volume (hmem.toLp g) a) ≤
        (1 + (d : ℝ)) ^ s * (B * Real.sqrt (volume.real S)) := by
    let L := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) a).restrictScalars ℝ
    have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun z ↦ by
      simpa [L] using PiLp.norm_apply_le z a)
    have hgc : ContDiff ℝ ∞ (fun x ↦ (g x) a) := L.contDiff.comp hg
    have hsc : tsupport (fun x ↦ (g x) a) ⊆ S :=
      (tsupport_comp_subset L.map_zero g).trans hs
    have he : finiteL2CoordinateIsometry volume (hmem.toLp g) a =
        (hgc.continuous.memLp_of_hasCompactSupport
          (hS.of_isClosed_subset (isClosed_tsupport _) hsc)).toLp (fun x ↦ (g x) a) := by
      apply Lp.ext
      filter_upwards [finiteL2Coordinates_apply_ae volume (hmem.toLp g) a,
        hmem.coeFn_toLp, (hgc.continuous.memLp_of_hasCompactSupport
          (hS.of_isClosed_subset (isClosed_tsupport _) hsc)).coeFn_toLp] with x hx hy hz
      exact hx.trans ((congrArg (fun z : F ↦ z a) hy).trans hz.symm)
    rw [he]
    apply scalarSobolev_le_compactJets hS s _ hgc hsc hB
    intro j hj x
    exact ((L.norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp : (j : ℕ∞ω) ≤ ∞)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hL)).trans (hb j hj x)
  calc
    _ ≤ ∑ a, fourierSobolevNorm (s : ℝ)
        (finiteL2CoordinateIsometry volume (hmem.toLp g) a) :=
      matrixFourierSobolevNorm_le_sum _ _
    _ ≤ ∑ _a : Fin r, (1 + (d : ℝ)) ^ s * (B * Real.sqrt (volume.real S)) :=
      Finset.sum_le_sum (fun a _ ↦ hcoord a)
    _ = _ := by simp; ring

/-- A spatial jet profile loses no scale power in passage to Sobolev norms:
only finitely many profile constants are used at each order. Consumer: the
original-source polynomial profile in
`app:ch_response:thm:response-literal-transfer`. -/
theorem vectorSobolev_le_compactJetProfile {S : Set E} (hS : IsCompact S)
    (s : ℕ) (g : E → F) (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ S)
    (hmem : MemLp g 2 volume) (J : ℕ → ℝ) (hJ : ∀ j, 0 ≤ J j)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 1 ≤ K)
    (hb : ∀ j x, ‖iteratedFDeriv ℝ j g x‖ ≤ J j * A * K ^ j) :
    vectorFourierSobolevNorm (s : ℝ) (hmem.toLp g) ≤
      (((r : ℝ) * (1 + (d : ℝ)) ^ s * Real.sqrt (volume.real S)) *
        ∑ j ∈ Finset.range (s + 1), J j) * A * K ^ s := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range (s + 1), J j :=
    Finset.sum_nonneg (fun j _ ↦ hJ j)
  apply (vectorSobolev_le_compactJets hS s g hg hs hmem
    (mul_nonneg (mul_nonneg hsum hA) (pow_nonneg (zero_le_one.trans hK) s)) ?_).trans_eq
      (by ring)
  intro j hj x
  apply (hb j x).trans
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ ↦ hJ i) (Finset.mem_range_succ_iff.mpr hj)) hA)
    (pow_le_pow_right₀ hK hj) (pow_nonneg (zero_le_one.trans hK) j)
    (mul_nonneg hsum hA)

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
