module

public import JanetCartan.Iteration.PhysicalMean.CrossBranches

/-!
# Full original samples grouped before quadratic pairing

The individual field of one ORIGINAL sample is the sum over all its refined
shells. Hermitian pairing is performed only AFTER that sum. This file retains
every cross-shell term and moves only the higher differentiated shell sum
inside the SAME native row. The lower amplitude is the full original sample
field, never a single-shell diagonal (`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open BallExtension PhysicalForwardMean RawPrimary.SliceBounds PhysicalSamplingShells RawInputRealization CurrentMean

variable {n N : ℕ} {ν β : Type*} [Fintype ν] [Fintype β]
    [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β]
    (radius : ν × β → ℝ)
    (φ θ : ((ν × β) × Euclidean (n-1)) → Euclidean n → ℝ)
    (m : ((ν × β) × Euclidean (n-1)) → ℝ)
    (A : Fin N → Fin n → ((ν × β) × Euclidean (n-1)) → Euclidean n → ℂ)

local notation "Mat" => Matrix (Fin N) (Fin n) ℂ

/-- The FULL field of an original sample: all refined shells are summed before
any Hermitian product or lower-field norm is taken. -/
def groupedAnnularForwardField (f : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) (i : ν) (x : Euclidean n) : Mat :=
  ∑ j : β, annularForwardField radius φ m A f (i,j) x

/-- Literal original weighted quadratic source, retaining all cross-shell
terms `HB(Σβ Fνβ, Σβ Gνβ)` for each original sample ν. -/
def groupedAnnularWeightedQuadratic (weight : ν → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) (x : Euclidean n) : Euclidean n :=
  C x (∑ i, weight i • hermitianContinuousBilinear
    (groupedAnnularForwardField radius φ m A f i x) (groupedAnnularForwardField radius φ m A g i x))

/-- Actual full-sample lower field in every aggregate higher shell row.
The original weight is replicated, not divided or renormalized by shell count. -/
def groupedAnnularCrossWordBranch (weight : ν → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) (dc dt dr : List (Fin n)) : Euclidean n → Euclidean n :=
  annularCrossWordBranch radius φ θ m A (fun i ↦ weight i.1) C
    (fun i ↦ groupedAnnularForwardField radius φ m A f i.1) g dc dt dr

/-- Original full-sample factors are balanced by derivative order, with the
full lower sample field retained in the modified amplitude. -/
def groupedAnnularBalancedBranch (weight : ν → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) (q : List (Fin n) × List (Fin n) × List (Fin n)) : Euclidean n → Euclidean n :=
  if q.2.1.length ≤ q.2.2.length then
    groupedAnnularCrossWordBranch radius φ θ m A weight C f g q.1 q.2.1 q.2.2
  else groupedAnnularCrossWordBranch radius φ θ m A weight C g f q.1 q.2.2 q.2.1

omit [Fintype ν] [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β] in
/-- Exact derivative of the full individual sample field, before its aggregate
higher shell sum is inserted into the native row. -/
theorem groupedAnnularForwardField_coordinate (f : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i)))
    (hf : ∀ i, ContDiff ℝ ∞ (annularForwardField radius φ m A f i))
    (ds : List (Fin n)) (i : ν) :
    cartesianCoordinateDerivList ds (groupedAnnularForwardField radius φ m A f i) =
      fun x ↦ ∑ j : β, cartesianCoordinateDerivList ds (annularForwardField radius φ m A f (i,j)) x :=
  cartesianWord_finsetSum _ (fun j ↦ hf (i,j)) ds

omit [Fintype ν] [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β] in
/-- Full sample smoothness and support come from the actual finite field sum;
no quantitative estimate is performed before the full sum. -/
theorem groupedAnnularForwardField_smooth_supported (f : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i)))
    {K : Set (Euclidean n)} (hK : IsClosed K)
    (hf : ∀ i, ContDiff ℝ ∞ (annularForwardField radius φ m A f i) ∧
      tsupport (annularForwardField radius φ m A f i) ⊆ K) (i : ν) :
    ContDiff ℝ ∞ (groupedAnnularForwardField radius φ m A f i) ∧
      tsupport (groupedAnnularForwardField radius φ m A f i) ⊆ K := by
  refine ⟨ContDiff.sum (fun j _ ↦ (hf (i,j)).1), ?_⟩
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  apply hx
  apply Finset.sum_eq_zero
  intro j _
  exact image_eq_zero_of_notMem_tsupport (fun ht ↦ hxK ((hf (i,j)).2 ht))

variable
    (hφ : ∀ i, Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ φ (i,z.1) z.2))
    (hm : ∀ i, Continuous (fun η ↦ m (i,η))) (hms : ∀ i, HasCompactSupport (fun η ↦ m (i,η)))
    (hAc : ∀ a c i, Continuous (fun z : Euclidean (n-1) × Euclidean n ↦ A a c (i,z.1) z.2))
    (hθ : ∀ z, ContDiff ℝ ∞ (θ z)) (hA : ∀ a c z, ContDiff ℝ ∞ (A a c z))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c z, tsupport (A a c z) ⊆ K)
    (hphase : ∀ z, m z ≠ 0 → ∀ x ∈ K, φ z x = ‖z.2‖*θ z x)
    (hjets : ∀ a c i j, Continuous (fun z : Euclidean n × Euclidean (n-1) ↦
      iteratedFDeriv ℝ j (fun y ↦ physicalForwardKernel (fun η ↦ φ (i,η)) (fun η ↦ m (i,η))
        (fun η y ↦ A a c (i,η) y) y z.2) z.1))

include hφ hm hms hAc hθ hA hK hAK hphase hjets

/-- Exact grouped high-word reconstruction: every original sample keeps its
FULL lower field, while its higher shell sum is inside the aggregate row.
This identity retains all cross-shell terms with their original weight. -/
theorem groupedWeightedHermitian_highWord_eq_branchSum
    (weight : ν → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) (dc dt dr : List (Fin n))
    (hbc : ∀ a c i (b : SliceDerivativeBranch dr.length),
      Continuous (fun z : Euclidean (n-1) × Euclidean n ↦
        sliceDerivativeAmplitude (θ (i,z.1)) (A a c (i,z.1))
          (fun j ↦ EuclideanSpace.single (dr.get j) 1) b z.2)) (x : Euclidean n) :
    (∑ i : ν, weight i • measuredHermitianDerivativeTerm C
      (groupedAnnularForwardField radius φ m A f i)
      (groupedAnnularForwardField radius φ m A g i) (dc,dt,dr) x) =
      groupedAnnularCrossWordBranch radius φ θ m A weight C f g dc dt dr x := by
  have hg (i : ν × β) := (annularForwardField_smooth_supported radius φ θ m A
    hφ hm hms hAc hθ hA hK hAK hphase hjets g i).1
  have he : (∑ i : ν, weight i • measuredHermitianDerivativeTerm C
      (groupedAnnularForwardField radius φ m A f i)
      (groupedAnnularForwardField radius φ m A g i) (dc,dt,dr) x) =
      ∑ i : ν × β, weight i.1 • measuredHermitianDerivativeTerm C
        (groupedAnnularForwardField radius φ m A f i.1)
        (annularForwardField radius φ m A g i) (dc,dt,dr) x := by
    simp only [measuredHermitianDerivativeTerm, groupedAnnularForwardField_coordinate radius φ m A g hg,
      map_sum, Finset.smul_sum, Fintype.sum_prod_type]
  rw [he]
  exact weightedHermitian_highWord_eq_branchSum radius φ θ m A hφ hm hms hAc hθ hA hK hAK hphase hjets
    (fun i ↦ weight i.1) (fun i ↦ hweight i.1) C
    (fun i ↦ groupedAnnularForwardField radius φ m A f i.1) g dc dt dr hbc x

/-- Exact differentiated ORIGINAL quadratic tensor with shell sums formed
BEFORE Hermitian pairing. The balanced native row expansion loses neither
cross-shell terms nor the common original sampling weights. -/
theorem groupedAnnularWeightedQuadratic_coordinate_eq_balancedBranches
    (weight : ν → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : ContDiff ℝ ∞ C)
    (f g : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i)))
    (hbc : ∀ ds : List (Fin n), ∀ a c i (b : SliceDerivativeBranch ds.length),
      Continuous (fun z : Euclidean (n-1) × Euclidean n ↦
        sliceDerivativeAmplitude (θ (i,z.1)) (A a c (i,z.1))
          (fun j ↦ EuclideanSpace.single (ds.get j) 1) b z.2))
    (ds : List (Fin n)) (x : Euclidean n) :
    cartesianCoordinateDerivList ds (groupedAnnularWeightedQuadratic radius φ m A weight C f g) x =
      ((crossDerivativeBranches ds).map
        (fun q ↦ groupedAnnularBalancedBranch radius φ θ m A weight C f g q x)).sum := by
  let U := groupedAnnularForwardField radius φ m A f
  let V := groupedAnnularForwardField radius φ m A g
  have hfields (w : ∀ i : ν × β, Lp ℂ 2 (annularMeasure n (radius i))) (i : ν) := groupedAnnularForwardField_smooth_supported radius φ m A w hK.isClosed
    (fun j ↦ annularForwardField_smooth_supported radius φ θ m A hφ hm hms hAc hθ hA hK hAK hphase hjets w j) i
  change cartesianCoordinateDerivList ds
    (fun y ↦ C y (∑ i, weight i • hermitianContinuousBilinear (U i y) (V i y))) x = _
  rw [weightedHermitian_coordinate_eq_branchSum weight C U V hC (fun i ↦ (hfields f i).1) (fun i ↦ (hfields g i).1)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  by_cases hrt : q.2.1.length ≤ q.2.2.length
  · simp only [groupedAnnularBalancedBranch, hrt, ↓reduceIte]
    exact groupedWeightedHermitian_highWord_eq_branchSum radius φ θ m A hφ hm hms hAc hθ hA hK hAK hphase hjets
      weight hweight C f g q.1 q.2.1 q.2.2 (hbc q.2.2) x
  · simp only [groupedAnnularBalancedBranch, hrt, ↓reduceIte]
    calc
      _ = ∑ i, weight i • measuredHermitianDerivativeTerm C (V i) (U i) (q.1,q.2.2,q.2.1) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [measuredHermitianDerivativeTerm_swap C (U i) (V i) q.1 q.2.1 q.2.2]
      _ = _ := groupedWeightedHermitian_highWord_eq_branchSum radius φ θ m A hφ hm hms hAc hθ hA hK hAK hphase hjets
        weight hweight C g f q.1 q.2.2 q.2.1 (hbc q.2.1) x

end JanetCartan.PhysicalMean
