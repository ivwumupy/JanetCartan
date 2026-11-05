module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Bounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates

/-!
# Local physical differentiation profiles for the original forward mean row

Step 3 of `app:ch_mean_pairs:eq:block-normal` differentiates the SAME full
oscillatory coefficient. The existing exact binary branches retain their
frequency factor count. Only physical primitive jets on the amplitude support
are used; no initial-frequency or sample-index derivatives occur. Off that
support every branch jet vanishes. The resulting constants precede arbitrary
sample types and feed the native on-mask scalar row tester, not a row-by-row
sample sum. The complete corrected coefficient is supplied by primary13 and
the normalized original phase by PhysicalAdjointGeometry28.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open RawPrimary.SliceBounds Pseudodifferential AmplitudeBound

/-- Sum of the finitely many physical test-jet constants for one exact binary
branch. It contains no sample, frequency, shell count or cutoff parameter
(`app:ch_mean_pairs:eq:block-normal`, `new:eq:amplitude-test`). -/
def forwardBranchConstant (ell : ℕ) (a p : ℕ → ℝ) {s : ℕ}
    (b : SliceDerivativeBranch s) : ℝ :=
  ∑ k ∈ Finset.range (ell + 1), sliceDerivativeJetConstant a p b k

/-- The fixed branch constant is nonnegative for the actual positive primitive
profiles (`app:ch_mean_pairs:eq:block-normal`). -/
theorem forwardBranchConstant_nonneg {ell s : ℕ} {a p : ℕ → ℝ}
    (b : SliceDerivativeBranch s) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ forwardBranchConstant ell a p b := by
  apply Finset.sum_nonneg
  intro k _
  exact sliceDerivativeJetConstant_nonneg b k (fun j _ ↦ ha j) (fun j _ _ ↦ hp j)

/-- One physical test order is bounded by the same fixed finite constant
(`new:eq:amplitude-test`). -/
theorem sliceDerivativeJetConstant_le_forwardBranchConstant {ell s k : ℕ} {a p : ℕ → ℝ}
    (b : SliceDerivativeBranch s) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hk : k ≤ ell) :
    sliceDerivativeJetConstant a p b k ≤ forwardBranchConstant ell a p b := by
  exact Finset.single_le_sum
    (fun j _ ↦ sliceDerivativeJetConstant_nonneg b j (fun i _ ↦ ha i) (fun i _ _ ↦ hp i))
    (Finset.mem_range.mpr (by omega))

/-- Primitive physical jets ONLY on the original amplitude support give the
forward coefficient cost `T^(s-k-s0)`. The fixed scalar-test reserve `ell` is
paid once, not once for every phase factor. Applied for each original source
parameter satisfying `m u ≠ 0`; no off-mask bounds are requested
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-fields`). -/
theorem coordinateJet_branch_le_of_localPrimitiveJets {n s ell s0 : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {φ : EuclideanSpace ℝ (Fin n) → ℝ} {A : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hA : ContDiff ℝ ∞ A) (hAK : tsupport A ⊆ K)
    {T : ℝ} (hT : 1 ≤ T) {a p : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hAj : ∀ x ∈ K, ∀ j ≤ s + ell,
      ‖iteratedFDeriv ℝ j A x‖ ≤ a j * T ^ (j - (s0 + ell)))
    (hφj : ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ s + ell →
      ‖iteratedFDeriv ℝ j φ x‖ ≤ p j * T ^ (j - 1 - (s0 + ell)))
    (v : Fin s → EuclideanSpace ℝ (Fin n)) (hv : ∀ i, ‖v i‖ ≤ 1) (b : SliceDerivativeBranch s)
    (ds : List (Fin n)) (hds : ds.length ≤ ell) (x : EuclideanSpace ℝ (Fin n)) :
    ‖euclideanCoordinateDerivList ds (sliceDerivativeAmplitude φ A v b) x‖ ≤
      forwardBranchConstant ell a p b * T ^ (s - b.phaseCount - s0) := by
  have hbranch : ContDiff ℝ ∞ (sliceDerivativeAmplitude φ A v b) :=
    contDiffOn_univ.mp (contDiffOn_sliceDerivativeAmplitude isOpen_univ hφ.contDiffOn hA.contDiffOn v b)
  apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hbranch ds x).trans
  by_cases hx : x ∈ K
  · have hb := norm_iteratedFDeriv_sliceDerivativeAmplitude_le isOpen_univ
      hφ.contDiffOn hA.contDiffOn (k := ds.length) (R := s0 + ell) v b hv hT
      (fun j _ ↦ ha j) (fun j _ _ ↦ hp j) (mem_univ x)
      (fun j hj ↦ hAj x hx j (by omega)) (fun j hj hj' ↦ hφj x hx j hj (by omega))
    apply hb.trans
    apply mul_le_mul
    · exact sliceDerivativeJetConstant_le_forwardBranchConstant b ha hp hds
    · exact pow_le_pow_right₀ hT (by omega)
    · positivity
    · exact forwardBranchConstant_nonneg b ha hp
  · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx
      (hAK (tsupport_sliceDerivativeAmplitude_subset φ A v b
        (tsupport_iteratedFDeriv_subset ds.length ht)))), norm_zero]
    exact mul_nonneg (forwardBranchConstant_nonneg b ha hp) (pow_nonneg (by linarith) _)

end JanetCartan.PhysicalForwardMean
