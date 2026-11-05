module

public import JanetCartan.Iteration.PhysicalMean.RadialInput
public import JanetCartan.Iteration.PhysicalMean.CrossLeibniz

/-!
# Exact full annular matrix branches of the weighted quadratic source

Apply the actual full matrix derivative formula on each original annulus,
then recombine the labels before any norm estimate. Radial moments remain
inside the same weighted native input and no weight is divided out.
The resulting terms are the literal annular fields already bounded in
`BalancedIntegral` (`new:eq:Q-derivative-term`, `app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open BallExtension PhysicalForwardMean RawPrimary.SliceBounds PhysicalSamplingShells RawInputRealization
open CurrentMean NormalComparison

variable {n N : ℕ} {ι : Type*} [Fintype ι] [MetricSpace ι] [DiscreteTopology ι]
    [MeasurableSpace ι] [BorelSpace ι]
    (radius : ι → ℝ)
    (φ θ : (ι × Euclidean (n-1)) → Euclidean n → ℝ) (m : (ι × Euclidean (n-1)) → ℝ)
    (A : Fin N → Fin n → (ι × Euclidean (n-1)) → Euclidean n → ℂ)

local notation "Mat" => Matrix (Fin N) (Fin n) ℂ

/-- The literal FULL matrix forward integral on each original annulus, before
its original sample weight is applied. -/
def annularForwardField (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ι)
    (x : Euclidean n) : Mat :=
  ∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ (i,η)) (fun η ↦ m (i,η))
    (fun η y ↦ A a c (i,η) y) x η*f i η) : Mat) ∂annularMeasure n (radius i)

variable
    (hφ : ∀ i, Continuous (fun p : Euclidean (n-1) × Euclidean n ↦ φ (i,p.1) p.2))
    (hm : ∀ i, Continuous (fun η ↦ m (i,η))) (hms : ∀ i, HasCompactSupport (fun η ↦ m (i,η)))
    (hAc : ∀ a c i, Continuous (fun p : Euclidean (n-1) × Euclidean n ↦ A a c (i,p.1) p.2))
    (hθ : ∀ z, ContDiff ℝ ∞ (θ z)) (hA : ∀ a c z, ContDiff ℝ ∞ (A a c z))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c z, tsupport (A a c z) ⊆ K)
    (hphase : ∀ z, m z ≠ 0 → ∀ x ∈ K, φ z x = ‖z.2‖*θ z x)
    (hjets : ∀ a c i j, Continuous (fun p : Euclidean n × Euclidean (n-1) ↦
      iteratedFDeriv ℝ j
        (fun y ↦ physicalForwardKernel (fun η ↦ φ (i,η)) (fun η ↦ m (i,η))
          (fun η y ↦ A a c (i,η) y) y p.2) p.1))

include hφ hm hms hAc hθ hA hK hAK hphase hjets

omit [Fintype ι] [MetricSpace ι] [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι] in
/-- Actual smoothness and physical support of the FULL original annular fields
are obtained from the primitive kernels, not supplied as a field premise. -/
theorem annularForwardField_smooth_supported
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (i : ι) :
    ContDiff ℝ ∞ (annularForwardField radius φ m A f i) ∧
      tsupport (annularForwardField radius φ m A f i) ⊆ K :=
  physicalMatrixForwardIntegral_smooth_supported
    (fun η ↦ φ (i,η)) (fun η ↦ θ (i,η)) (fun η ↦ ‖η‖) (fun η ↦ m (i,η))
    (fun a c η y ↦ A a c (i,η) y) (hφ i) (hm i) (hms i) (fun a c ↦ hAc a c i)
    (fun η ↦ hθ (i,η)) (fun a c η ↦ hA a c (i,η)) hK (fun a c η ↦ hAK a c (i,η))
    (fun η ↦ hphase (i,η)) (fun a c j ↦ hjets a c i j) (f i)

/-- Exact high-factor matrix expansion INSIDE the original weighted cross.
The displayed native input is constructed, has genuine radial membership,
and its norm is exactly the original aggregate moment by `RadialInput`.
Only fixed derivative branches are summed outside the native row. -/
theorem weightedHermitian_highWord_eq_branchSum
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : ι → Euclidean n → Mat)
    (f : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (dc dt dr : List (Fin n))
    (hbc : ∀ a c i (b : SliceDerivativeBranch dr.length),
      Continuous (fun p : Euclidean (n-1) × Euclidean n ↦
        sliceDerivativeAmplitude (θ (i,p.1)) (A a c (i,p.1))
          (fun j ↦ EuclideanSpace.single (dr.get j) 1) b p.2))
    (x : Euclidean n) :
    (∑ i, weight i • measuredHermitianDerivativeTerm C (B i)
      (annularForwardField radius φ m A f i) (dc,dt,dr) x) =
    ∑ b : SliceDerivativeBranch dr.length,
      annularMeasuredCross radius φ (fun z ↦ Real.sqrt (weight z.1)*m z)
        (cartesianCoordinateDerivList dc C)
        (fun i ↦ cartesianCoordinateDerivList dt (B i))
        (matrixForwardBranchAmplitude θ A (fun j ↦ EuclideanSpace.single (dr.get j) 1) b)
        (weightedAnnularInput radius weight (annularRadialInput radius f b.phaseCount
          (fun i ↦ annular_radial_memLp (radius i) (f i) b.phaseCount))) x := by
  let dirs := fun j : Fin dr.length ↦ EuclideanSpace.single (dr.get j) (1 : ℝ)
  have hd (i : ι) := physicalMatrixForwardIntegral_coordinate_eq_branchSum
    (fun η ↦ φ (i,η)) (fun η ↦ θ (i,η)) (fun η ↦ ‖η‖) (fun η ↦ m (i,η))
    (fun a c η y ↦ A a c (i,η) y) (hφ i) (hm i) (hms i) (fun a c ↦ hAc a c i)
    (fun η ↦ hθ (i,η)) (fun a c η ↦ hA a c (i,η)) hK (fun a c η ↦ hAK a c (i,η))
    (fun η ↦ hphase (i,η)) (fun a c j ↦ hjets a c i j) dr (fun a c b ↦ hbc a c i b)
    (f i) (fun k _ ↦ annular_radial_memLp (radius i) (f i) k) x
  unfold measuredHermitianDerivativeTerm
  change (∑ i, weight i • cartesianCoordinateDerivList dc C x
    (hermitianContinuousBilinear (cartesianCoordinateDerivList dt (B i) x)
      (cartesianCoordinateDerivList dr (annularForwardField radius φ m A f i) x))) = _
  simp_rw [show ∀ i, cartesianCoordinateDerivList dr (annularForwardField radius φ m A f i) x =
      ∑ b : SliceDerivativeBranch dr.length,
        (∫ η, ((fun a c ↦ physicalForwardKernel (fun η ↦ φ (i,η)) (fun η ↦ m (i,η))
          (fun η y ↦ matrixForwardBranchAmplitude θ A dirs b (i,η) y a c) x η*
            ((‖η‖ : ℂ)^b.phaseCount*f i η)) : Mat) ∂annularMeasure n (radius i) : Mat)
    from fun i ↦ hd i]
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [annularMeasuredCross_weighted_eq radius φ m
    (cartesianCoordinateDerivList dc C) (fun i ↦ cartesianCoordinateDerivList dt (B i))
    (matrixForwardBranchAmplitude θ A dirs b) weight hweight]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  change hermitianContinuousBilinear (cartesianCoordinateDerivList dt (B i) x) _ =
    hermitianContinuousBilinear (cartesianCoordinateDerivList dt (B i) x) _
  congr 1
  apply integral_congr_ae
  filter_upwards [annularRadialInput_ae radius f b.phaseCount
    (fun i ↦ annular_radial_memLp (radius i) (f i) b.phaseCount) i] with η hη
  rw [hη]
  ext a c
  simp only [physicalForwardKernel, sampledMomentKernel, star_star, Matrix.smul_apply, smul_eq_mul]
  ring

omit hφ hm hms hAc hθ hA hK hAK hphase hjets in
/-- The actual original weighted quadratic tensor of two FULL annular fields.
Both fields use the same raw derivative kernel, with distinct original inputs. -/
def annularWeightedQuadratic (weight : ι → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i))) (x : Euclidean n) : Euclidean n :=
  C x (∑ i, weight i • hermitianContinuousBilinear
    (annularForwardField radius φ m A f i x) (annularForwardField radius φ m A g i x))

omit hφ hm hms hAc hθ hA hK hAK hphase hjets in
/-- A full aggregate high-factor word with an arbitrary actual lower field.
In the original sample application this lower field is the SUM over all of
that sample's refined shells, not one diagonal shell contribution. -/
def annularCrossWordBranch (weight : ι → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B : ι → Euclidean n → Mat)
    (g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (dc dt dr : List (Fin n)) (x : Euclidean n) : Euclidean n :=
  ∑ b : SliceDerivativeBranch dr.length,
    annularMeasuredCross radius φ (fun z ↦ Real.sqrt (weight z.1)*m z)
      (cartesianCoordinateDerivList dc C)
      (fun i ↦ cartesianCoordinateDerivList dt (B i))
      (matrixForwardBranchAmplitude θ A (fun j ↦ EuclideanSpace.single (dr.get j) 1) b)
      (weightedAnnularInput radius weight (annularRadialInput radius g b.phaseCount
        (fun i ↦ annular_radial_memLp (radius i) (g i) b.phaseCount))) x

omit hφ hm hms hAc hθ hA hK hAK hphase hjets in
/-- The finite FULL high-factor branch sum for one literal Leibniz term.
Every summand is the same physical annular field bounded by BalancedIntegral. -/
def annularQuadraticWordBranch (weight : ι → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (dc dt dr : List (Fin n)) (x : Euclidean n) : Euclidean n :=
  ∑ b : SliceDerivativeBranch dr.length,
    annularMeasuredCross radius φ (fun z ↦ Real.sqrt (weight z.1)*m z)
      (cartesianCoordinateDerivList dc C)
      (fun i ↦ cartesianCoordinateDerivList dt (annularForwardField radius φ m A f i))
      (matrixForwardBranchAmplitude θ A (fun j ↦ EuclideanSpace.single (dr.get j) 1) b)
      (weightedAnnularInput radius weight (annularRadialInput radius g b.phaseCount
        (fun i ↦ annular_radial_memLp (radius i) (g i) b.phaseCount))) x

omit hφ hm hms hAc hθ hA hK hAK hphase hjets in
/-- Balance the actual two source factors BEFORE estimating them. The lower
word is in the amplitude, while the higher word stays inside the aggregate row. -/
def annularBalancedDerivativeBranch (weight : ι → ℝ)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (f g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (q : List (Fin n) × List (Fin n) × List (Fin n)) (x : Euclidean n) : Euclidean n :=
  if q.2.1.length ≤ q.2.2.length then
    annularQuadraticWordBranch radius φ θ m A weight C f g q.1 q.2.1 q.2.2 x
  else
    annularQuadraticWordBranch radius φ θ m A weight C g f q.1 q.2.2 q.2.1 x

/-- Exact full derivative assembly of the ORIGINAL weighted quadratic source.
It uses the actual three-factor Leibniz formula, exact Hermitian symmetry,
and the full matrix branch identity. No quadratic derivative or norm identity
is assumed, and all original sample sums remain inside the constructed rows. -/
theorem annularWeightedQuadratic_coordinate_eq_balancedBranches
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (hC : ContDiff ℝ ∞ C)
    (f g : ∀ i, Lp ℂ 2 (annularMeasure n (radius i)))
    (hbc : ∀ ds : List (Fin n), ∀ a c i (b : SliceDerivativeBranch ds.length),
      Continuous (fun p : Euclidean (n-1) × Euclidean n ↦
        sliceDerivativeAmplitude (θ (i,p.1)) (A a c (i,p.1))
          (fun j ↦ EuclideanSpace.single (ds.get j) 1) b p.2))
    (ds : List (Fin n)) (x : Euclidean n) :
    cartesianCoordinateDerivList ds (annularWeightedQuadratic radius φ m A weight C f g) x =
      ((crossDerivativeBranches ds).map
        (fun q ↦ annularBalancedDerivativeBranch radius φ θ m A weight C f g q x)).sum := by
  let U := annularForwardField radius φ m A f
  let V := annularForwardField radius φ m A g
  have hU (i : ι) : ContDiff ℝ ∞ (U i) :=
    (annularForwardField_smooth_supported radius φ θ m A hφ hm hms hAc hθ hA hK hAK hphase hjets f i).1
  have hV (i : ι) : ContDiff ℝ ∞ (V i) :=
    (annularForwardField_smooth_supported radius φ θ m A hφ hm hms hAc hθ hA hK hAK hphase hjets g i).1
  change cartesianCoordinateDerivList ds (fun y ↦ C y (∑ i, weight i • hermitianContinuousBilinear (U i y) (V i y))) x = _
  rw [weightedHermitian_coordinate_eq_branchSum weight C U V hC hU hV]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  by_cases hrt : q.2.1.length ≤ q.2.2.length
  · simp only [annularBalancedDerivativeBranch, hrt, ↓reduceIte]
    exact weightedHermitian_highWord_eq_branchSum radius φ θ m A hφ hm hms hAc hθ hA hK hAK
      hphase hjets weight hweight C U g q.1 q.2.1 q.2.2 (hbc q.2.2) x
  · simp only [annularBalancedDerivativeBranch, hrt, ↓reduceIte]
    calc
      _ = ∑ i, weight i • measuredHermitianDerivativeTerm C (V i) (U i) (q.1,q.2.2,q.2.1) x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [measuredHermitianDerivativeTerm_swap C (U i) (V i) q.1 q.2.1 q.2.2]
      _ = _ := weightedHermitian_highWord_eq_branchSum radius φ θ m A hφ hm hms hAc hθ hA hK hAK
        hphase hjets weight hweight C V f q.1 q.2.2 q.2.1 (hbc q.2.1) x

end JanetCartan.PhysicalMean
