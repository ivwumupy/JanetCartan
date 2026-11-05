module

public import JanetCartan.Iteration.PhysicalForwardMean.VectorJets
public import JanetCartan.Iteration.PhysicalForwardMean.IntegralIdentity
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds.NormComparison.Coordinates
public import JanetCartan.Analysis.Fourier.Conventions.NormComparison.Components

/-!
# Exact full-matrix forward branches on the original aggregate input

The higher factor in `app:ch_mean_pairs:eq:block-bilinear` remains the SAME
full matrix Bochner integral. Each physical derivative is expanded before
any operator estimate, leaving its exact frequency moment INSIDE the original
aggregate sampler. Only the fixed physical matrix dimensions enter the
coefficient norm conversion; samples and shells are never counted.

Primitive full-amplitude and normalized-phase profiles are the existing
original-data inputs of task 13. No derivative norm of the output field or
individual raw-operator bound is assumed here.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalForwardMean
open RawPrimary.SliceBounds PhysicalMean Pseudodifferential AmplitudeBound LocalSobolev
open BallExtension FourierConventions
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

variable {n N : ℕ} {X : Type*}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin N) (Fin n) ℂ

/-- The actual binary branch of every entry of the FULL matrix amplitude.
The original phase, input mask, measure and scalar raw input are not changed
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-bilinear`). -/
def matrixForwardBranchAmplitude
    (θ : X → E → ℝ) (A : Fin N → Fin n → X → E → ℂ)
    {s : ℕ} (dirs : Fin s → E) (b : SliceDerivativeBranch s) : X → E → Mat :=
  fun u x a c ↦ sliceDerivativeAmplitude (θ u) (A a c u) dirs b x

/-- Joint continuity of the full branch comes from the SAME finite physical
entry branches, without any sample-coordinate differentiation or norm premise
(`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem continuous_matrixForwardBranchAmplitude [TopologicalSpace X]
    (θ : X → E → ℝ) (A : Fin N → Fin n → X → E → ℂ)
    {s : ℕ} (dirs : Fin s → E) (b : SliceDerivativeBranch s)
    (hbc : ∀ a c, Continuous (fun q : X × E ↦
      sliceDerivativeAmplitude (θ q.1) (A a c q.1) dirs b q.2)) :
    Continuous (fun q : X × E ↦ matrixForwardBranchAmplitude θ A dirs b q.1 q.2) := by
  let e : Mat ≃L[ℂ] (Fin N × Fin n → ℂ) := matrixEntryEquiv
  exact e.symm.continuous.comp (continuous_pi (fun ac ↦ hbc ac.1 ac.2))

/-- The literal matrix branch is smooth and has the SAME compact physical
support, as follows from the original scalar branches, not a matrix-output
regularity premise (`app:ch_mean_pairs:eq:block-normal`). -/
theorem matrixForwardBranch_smooth_supported
    (θ : X → E → ℝ) (A : Fin N → Fin n → X → E → ℂ)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u))
    (hA : ∀ a c u, ContDiff ℝ ∞ (A a c u))
    {K : Set E} (hK : IsClosed K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    {s : ℕ} (dirs : Fin s → E) (b : SliceDerivativeBranch s) (u : X) :
    ContDiff ℝ ∞ (matrixForwardBranchAmplitude θ A dirs b u) ∧
      tsupport (matrixForwardBranchAmplitude θ A dirs b u) ⊆ K := by
  have hs (a : Fin N) (c : Fin n) :
      ContDiff ℝ ∞ (sliceDerivativeAmplitude (θ u) (A a c u) dirs b) :=
    contDiffOn_univ.mp (contDiffOn_sliceDerivativeAmplitude isOpen_univ
      (hθ u).contDiffOn (hA a c u).contDiffOn dirs b)
  have hb (a : Fin N) (c : Fin n) :=
    forwardBranch_smooth_supported θ (A a c) hθ (hA a c) hK (hAK a c) dirs b u
  constructor
  · let e : Mat ≃L[ℂ] (Fin N × Fin n → ℂ) := matrixEntryEquiv
    exact (e.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      (contDiff_pi.mpr (fun ac ↦ hs ac.1 ac.2))
  · apply closure_minimal _ hK
    intro x hx
    by_contra hxK
    apply hx
    ext a c
    have hz := image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ star (sliceDerivativeAmplitude (θ u) (A a c u) dirs b y))
      (fun ht ↦ hxK ((hb a c).2 ht))
    change sliceDerivativeAmplitude (θ u) (A a c u) dirs b x = 0
    simpa only [star_star, star_zero] using congrArg star hz

/-- The generic ordered Cartesian word used in the bilinear Leibniz expansion
has EXACTLY the same scalar entry words. The physical basis conventions agree;
there is no additional derivative or replacement field (`app:not:fourier`). -/
theorem matrix_cartesianCoordinateDerivList_apply
    {B : E → Mat} (hB : ContDiff ℝ ∞ B) (ds : List (Fin n))
    (a : Fin N) (c : Fin n) (x : E) :
    (cartesianCoordinateDerivList ds B x) a c =
      euclideanCoordinateDerivList ds (fun y ↦ B y a c) x := by
  have hword := cartesianCoordinateDerivList_eq_iteratedFDerivWithin
    isOpen_univ hB.contDiffOn ds (mem_univ x)
  dsimp only at hword
  rw [iteratedFDerivWithin_of_isOpen ds.length isOpen_univ (mem_univ x)] at hword
  have he := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv
    ((matrixEntryEvaluation a c).contDiff.comp hB) ds.get x
  rw [List.ofFn_get] at he
  change _ = euclideanCoordinateDerivList ds ((matrixEntryEvaluation a c) ∘ B) x
  rw [hword, he, (matrixEntryEvaluation a c).iteratedFDeriv_comp_left hB.contDiffAt (by simp)]
  simp only [EuclideanSpace.basisFun_apply]
  rfl

/-- Fixed physical matrix/order factor for one branch, chosen before the input
sample type, measure, mask, band count or current source
(`app:ch_mean_pairs:eq:block-bilinear`). -/
def matrixForwardBranchConstant (n N ell : ℕ) (a p : ℕ → ℝ)
    {s : ℕ} (b : SliceDerivativeBranch s) : ℝ :=
  ((N * n : ℕ) : ℝ) * cartesianCNormComparisonConstant n ell *
    forwardBranchConstant ell a p b

/-- Nonnegativity of the same fixed matrix branch constant. -/
theorem matrixForwardBranchConstant_nonneg (n N ell : ℕ) {a p : ℕ → ℝ}
    {s : ℕ} (b : SliceDerivativeBranch s) (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ matrixForwardBranchConstant n N ell a p b :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (cartesianCNormComparisonConstant_pos n ell).le)
    (forwardBranchConstant_nonneg b ha hp)

/-- The FULL matrix branch costs precisely `T^(s-phaseCount-s0)` in physical
`C^ell`. The scalar-test reserve `ell` is paid once. Only the original entrywise
primitive amplitude/phase profiles on the original active mask are inputs;
no matrix derivative estimate is assumed (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem cNorm_matrixForwardBranch_le_of_localPrimitiveJets
    (θ : X → E → ℝ) (A : Fin N → Fin n → X → E → ℂ) (m : X → ℝ)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u))
    (hA : ∀ a c u, ContDiff ℝ ∞ (A a c u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    {s ell s0 : ℕ} {T : ℝ} (hT : 1 ≤ T) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (hAj : ∀ a0 c0 u, m u ≠ 0 → ∀ x ∈ K, ∀ j ≤ s + ell,
      ‖iteratedFDeriv ℝ j (A a0 c0 u) x‖ ≤ a j * T ^ (j - (s0 + ell)))
    (hθj : ∀ u, m u ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ s + ell →
      ‖iteratedFDeriv ℝ j (θ u) x‖ ≤ p j * T ^ (j - 1 - (s0 + ell)))
    (dirs : Fin s → E) (hdirs : ∀ i, ‖dirs i‖ ≤ 1) (b : SliceDerivativeBranch s)
    (u : X) (hu : m u ≠ 0) :
    cNorm K ell (matrixForwardBranchAmplitude θ A dirs b u) ≤
      matrixForwardBranchConstant n N ell a p b * T ^ (s - b.phaseCount - s0) := by
  let M := forwardBranchConstant ell a p b * T ^ (s - b.phaseCount - s0)
  have hM : 0 ≤ M := mul_nonneg (forwardBranchConstant_nonneg b ha hp)
    (pow_nonneg (zero_le_one.trans hT) _)
  have hentry (a0 : Fin N) (c0 : Fin n) :
      cartesianCNorm K ell (fun x ↦ matrixForwardBranchAmplitude θ A dirs b u x a0 c0) ≤ M := by
    apply cartesianCNorm_le_of_bound hM
    intro α hα x _hx
    let ds := sobolevDerivativeList (fun i ↦ α (some i))
    have ho : ds.length ≤ ell := by
      rw [sobolevDerivativeList_length]
      have hh := mem_sobolevMultiindices.mp hα
      omega
    have hb := coordinateJet_branch_le_of_localPrimitiveJets
      (hθ u) (hA a0 c0 u) (hAK a0 c0 u) hT ha hp
      (hAj a0 c0 u hu) (hθj u hu) dirs hdirs b ds ho x
    have hsm := contDiffOn_univ.mp (contDiffOn_sliceDerivativeAmplitude isOpen_univ
      (hθ u).contDiffOn (hA a0 c0 u).contDiffOn dirs b)
    have he := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv hsm ds.get x
    rw [List.ofFn_get] at he
    rw [he] at hb
    simpa only [M, matrixForwardBranchAmplitude, cartesianJetDerivative,
      EuclideanSpace.basisFun_apply, ds] using hb
  have hmax : matrixCartesianCNorm K ell (matrixForwardBranchAmplitude θ A dirs b u) ≤ M :=
    Real.sSup_le (by rintro t ⟨⟨a0, c0⟩, rfl⟩; exact hentry a0 c0) hM
  have hsm := (matrixForwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK dirs b u).1
  have hc : 0 ≤ ((N * n : ℕ) : ℝ) * cartesianCNormComparisonConstant n ell :=
    mul_nonneg (Nat.cast_nonneg _) (cartesianCNormComparisonConstant_pos n ell).le
  calc
    _ ≤ (((N * n : ℕ) : ℝ) * cartesianCNormComparisonConstant n ell) *
        matrixCartesianCNorm K ell (matrixForwardBranchAmplitude θ A dirs b u) := by
      simpa only [Fintype.card_fin] using
        (matrixCartesianCNorm_comparison hK isOpen_univ (subset_univ K) ell hsm.contDiffOn).2.2
    _ ≤ (((N * n : ℕ) : ℝ) * cartesianCNormComparisonConstant n ell) * M :=
      mul_le_mul_of_nonneg_left hmax hc
    _ = _ := by unfold matrixForwardBranchConstant; dsimp only [M]; ring

section AggregateIntegral
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]

omit [SecondCountableTopology X] in
/-- Actual matrix integrability and exact entrywise evaluation are derived from
primitive compact kernels and the original input's membership. This works for
the SAME aggregate measure and the SAME weighted input, without estimating a
sample count or a frequency ceiling (`app:ch_mean_pairs:eq:block-bilinear`). -/
theorem physicalMatrixForwardIntegral_integrable_apply
    (φ : X → E → ℝ) (m : X → ℝ) (A : Fin N → Fin n → X → E → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hAc : ∀ a c, Continuous (Function.uncurry (A a c)))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    (v : X → ℂ) (hv : MemLp v 2 μ) (x : E) :
    Integrable (ε := Mat) (fun u ↦ fun a c ↦ physicalForwardKernel φ m (A a c) x u * v u) μ ∧
      ∀ a c, (∫ u, (fun a c ↦ physicalForwardKernel φ m (A a c) x u * v u) ∂μ : Mat) a c =
        ∫ u, physicalForwardKernel φ m (A a c) x u * v u ∂μ := by
  have hi (a : Fin N) (c : Fin n) :
      Integrable (fun u ↦ physicalForwardKernel φ m (A a c) x u * v u) μ := by
    have he := integrable_compactKernel_mul_L2
      (continuous_sampledMomentKernel φ m (fun u y ↦ star (A a c u y)) hφ hm (hAc a c).star)
      (hasCompactSupport_sampledMomentKernel φ m (fun u y ↦ star (A a c u y)) hms hK
        (fun u ↦ by
          apply closure_minimal _ hK.isClosed
          intro y hy
          exact hAK a c u (subset_tsupport _ (fun hz ↦ hy (by simp only [hz, star_zero])))))
      (hv.toLp v) x
    apply he.congr
    filter_upwards [hv.coeFn_toLp] with u hu
    exact congrArg (_ * ·) hu
  have hpi : Integrable (fun u (ac : Fin N × Fin n) ↦
      physicalForwardKernel φ m (A ac.1 ac.2) x u * v u) μ :=
    integrable_pi_iff.mpr (fun ac ↦ hi ac.1 ac.2)
  refine ⟨(matrixEntryEquiv (I := Fin N) (J := Fin n)).symm.toContinuousLinearMap.integrable_comp hpi, ?_⟩
  exact fun a c ↦ matrix_integral_apply _ hi a c

/-- Smoothness and compact physical support of the SAME full matrix Bochner
field follow from the original primitive kernels, entrywise integration and
the existing scalar producer. No output-regularity premise is added
(`app:ch_mean_pairs:eq:block-fields`). -/
theorem physicalMatrixForwardIntegral_smooth_supported
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : Fin N → Fin n → X → E → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hAc : ∀ a c, Continuous (Function.uncurry (A a c)))
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ a c u, ContDiff ℝ ∞ (A a c u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x)
    (hjets : ∀ a c j, Continuous (fun p : E × X ↦ iteratedFDeriv ℝ j
      (fun y ↦ physicalForwardKernel φ m (A a c) y p.2) p.1))
    (w : Lp ℂ 2 μ) :
    let B : E → Mat := fun x ↦ ∫ u,
      ((fun a c ↦ physicalForwardKernel φ m (A a c) x u * w u) : Mat) ∂μ
    ContDiff ℝ ∞ B ∧ tsupport B ⊆ K := by
  intro B
  have he (a : Fin N) (c : Fin n) : (fun x ↦ B x a c) =
      fun x ↦ ∫ u, physicalForwardKernel φ m (A a c) x u * w u ∂μ := by
    funext x
    exact (physicalMatrixForwardIntegral_integrable_apply φ m A hφ hm hms hAc hK hAK
      (fun u ↦ w u) (Lp.memLp w) x).2 a c
  have hs (a : Fin N) (c : Fin n) := physicalForwardIntegral_smooth
    φ θ lam m (A a c) hθ (hA a c) hK (hAK a c) hms hphase (hjets a c) w
  constructor
  · let e : Mat ≃L[ℂ] (Fin N × Fin n → ℂ) := matrixEntryEquiv
    have hc : ContDiff ℝ ∞ (fun (x : E) (ac : Fin N × Fin n) ↦ B x ac.1 ac.2) :=
      contDiff_pi.mpr (fun ac ↦ by rw [he ac.1 ac.2]; exact (hs ac.1 ac.2).1)
    exact (e.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hc
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    apply hx
    ext a c
    change (fun y ↦ B y a c) x = 0
    rw [he a c]
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ ∫ u, physicalForwardKernel φ m (A a c) y u * w u ∂μ)
      (fun ht ↦ hxK ((hs a c).2.1 ht))

/-- Literal ordered physical differentiation of the original FULL matrix
Bochner field is the finite sum of the actual matrix branches. Each exact
frequency factor remains INSIDE the SAME aggregate input integral. The phase,
complete mask (including halfweight and square-root sample weights), source
measure and raw input are unchanged. The explicit matrix codomain and outer
integral annotations retain the original Frobenius instances
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-bilinear`). -/
theorem physicalMatrixForwardIntegral_coordinate_eq_branchSum
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : Fin N → Fin n → X → E → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hAc : ∀ a c, Continuous (Function.uncurry (A a c)))
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ a c u, ContDiff ℝ ∞ (A a c u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ a c u, tsupport (A a c u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x)
    (hjets : ∀ a c j, Continuous (fun p : E × X ↦ iteratedFDeriv ℝ j
      (fun y ↦ physicalForwardKernel φ m (A a c) y p.2) p.1))
    (ds : List (Fin n))
    (hbc : ∀ a c (b : SliceDerivativeBranch ds.length), Continuous (fun p : X × E ↦
      sliceDerivativeAmplitude (θ p.1) (A a c p.1)
        (fun i ↦ EuclideanSpace.single (ds.get i) 1) b p.2))
    (w : Lp ℂ 2 μ)
    (hweight : ∀ k ≤ ds.length, MemLp (fun u ↦ (lam u : ℂ)^k * w u) 2 μ)
    (x : E) :
    cartesianCoordinateDerivList (F := Mat) ds
      (fun y ↦ ∫ u, ((fun a c ↦ physicalForwardKernel φ m (A a c) y u * w u) : Mat) ∂μ) x =
      ∑ b : SliceDerivativeBranch ds.length, (∫ u,
        ((fun a c ↦ physicalForwardKernel φ m
          (fun u y ↦ matrixForwardBranchAmplitude θ A
            (fun i ↦ EuclideanSpace.single (ds.get i) 1) b u y a c) x u *
              ((lam u : ℂ)^b.phaseCount * w u)) : Mat) ∂μ : Mat) := by
  let dirs := fun i : Fin ds.length ↦ EuclideanSpace.single (ds.get i) (1 : ℝ)
  let B : E → Mat := fun y ↦ ∫ u,
    ((fun a c ↦ physicalForwardKernel φ m (A a c) y u * w u) : Mat) ∂μ
  have hsm : ContDiff ℝ ∞ B :=
    (physicalMatrixForwardIntegral_smooth_supported
      φ θ lam m A hφ hm hms hAc hθ hA hK hAK hphase hjets w).1
  have he (a : Fin N) (c : Fin n) : (fun y ↦ B y a c) =
      fun y ↦ ∫ u, physicalForwardKernel φ m (A a c) y u * w u ∂μ := by
    funext y
    exact (physicalMatrixForwardIntegral_integrable_apply φ m A hφ hm hms hAc hK hAK
      (fun u ↦ w u) (Lp.memLp w) y).2 a c
  have hbranch (b : SliceDerivativeBranch ds.length) :
      ∀ a c u, tsupport (fun y ↦ matrixForwardBranchAmplitude θ A dirs b u y a c) ⊆ K := by
    intro a c u
    exact (tsupport_sliceDerivativeAmplitude_subset (θ u) (A a c u) dirs b).trans (hAK a c u)
  change cartesianCoordinateDerivList ds B x = _
  ext a c
  rw [matrix_cartesianCoordinateDerivList_apply hsm ds a c x, he a c,
    physicalForwardIntegral_coordinate_eq_branchSum φ θ lam m (A a c)
      hφ hm hms hθ (hA a c) hK (hAK a c) hphase (hjets a c) ds (hbc a c) w hweight x]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  exact ((physicalMatrixForwardIntegral_integrable_apply φ m
    (fun a c u y ↦ matrixForwardBranchAmplitude θ A dirs b u y a c)
    hφ hm hms (fun a c ↦ hbc a c b) hK (hbranch b)
    (fun u ↦ (lam u : ℂ)^b.phaseCount * w u)
    (hweight b.phaseCount b.phaseCount_le) x).2 a c).symm

end AggregateIntegral
end JanetCartan.PhysicalForwardMean
