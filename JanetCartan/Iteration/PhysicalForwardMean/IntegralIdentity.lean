module

public import JanetCartan.Iteration.PhysicalForwardMean.CompactJets
public import JanetCartan.Iteration.PhysicalForwardMean.KernelIdentity

/-!
# Exact native forward derivative integrals

Physical differentiation commutes with the ORIGINAL compact kernel integral,
and the literal binary branch identity is integrated with its precise powers
of the input frequency. Weighted input membership is genuine input regularity;
it is automatic for the original bounded shell measure, and the mean adjoint
producer proves it with sharp norms. No frequency cutoff bound is used in the
quantitative estimate and no output derivative bound is an input.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open RawPrimary.SliceBounds PhysicalMean Pseudodifferential AmplitudeBound
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

variable {n : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
local notation "E" => Euclidean n

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- The original compact physical amplitude support controls every physical
kernel section, with no phase regularity hypothesis. -/
theorem physicalForwardKernel_tsupport_subset
    (φ : X → E → ℝ) (m : X → ℝ) (A : X → E → ℂ)
    {K : Set E} (hK : IsClosed K) (hAK : ∀ u, tsupport (A u) ⊆ K) (u : X) :
    tsupport (fun x ↦ physicalForwardKernel φ m A x u) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  exact hAK u (subset_tsupport _ (fun hz ↦ hx
    (by simp [physicalForwardKernel, sampledMomentKernel, hz])))

/-- The SAME literal compact integral is smooth and all its coordinate jets
belong to physical L², for every native L² input. All regularity and domination
are derived, not assumed of the output (`app:ch_mean_pairs:eq:block-fields`). -/
theorem physicalForwardIntegral_smooth
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : X → E → ℂ)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ u, tsupport (A u) ⊆ K)
    (hms : HasCompactSupport m)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x)
    (hjets : ∀ j : ℕ, Continuous (fun p : E × X ↦ iteratedFDeriv ℝ j
      (fun y ↦ physicalForwardKernel φ m A y p.2) p.1)) (v : Lp ℂ 2 μ) :
    let w := fun x ↦ ∫ u, physicalForwardKernel φ m A x u * v u ∂μ
    ContDiff ℝ ∞ w ∧ tsupport w ⊆ K ∧
      ∀ ds : List (Fin n), MemLp (euclideanCoordinateDerivList ds w) 2 volume := by
  apply compactKernel_L2Integral_smooth hK hms (physicalForwardKernel φ m A)
    (physicalForwardKernel_smooth φ θ lam m A hθ hA hAK hphase) hjets
    (physicalForwardKernel_tsupport_subset φ m A hK.isClosed hAK)
  intro u hu x
  simp [physicalForwardKernel, sampledMomentKernel, image_eq_zero_of_notMem_tsupport hu]

/-- An actual physical coordinate derivative of the original forward field is
EXACTLY the finite sum of the original branch rows applied to the corresponding
frequency moments. In particular neither the sample count nor shell count is
summed (`app:ch_mean_pairs:eq:block-normal`). -/
theorem physicalForwardIntegral_coordinate_eq_branchSum
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : X → E → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ u, tsupport (A u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x)
    (hjets : ∀ j : ℕ, Continuous (fun p : E × X ↦ iteratedFDeriv ℝ j
      (fun y ↦ physicalForwardKernel φ m A y p.2) p.1))
    (ds : List (Fin n))
    (hbc : ∀ b : SliceDerivativeBranch ds.length, Continuous (fun p : X × E ↦
      sliceDerivativeAmplitude (θ p.1) (A p.1)
        (fun i ↦ EuclideanSpace.single (ds.get i) 1) b p.2))
    (v : Lp ℂ 2 μ)
    (hweight : ∀ k ≤ ds.length, MemLp (fun u ↦ (lam u : ℂ)^k * v u) 2 μ)
    (x : E) :
    euclideanCoordinateDerivList ds
      (fun y ↦ ∫ u, physicalForwardKernel φ m A y u * v u ∂μ) x =
      ∑ b : SliceDerivativeBranch ds.length, ∫ u,
        physicalForwardKernel φ m (fun u y ↦ sliceDerivativeAmplitude (θ u) (A u)
          (fun i ↦ EuclideanSpace.single (ds.get i) 1) b y) x u *
            ((lam u : ℂ)^b.phaseCount * v u) ∂μ := by
  let dirs := fun i : Fin ds.length ↦ EuclideanSpace.single (ds.get i) (1 : ℝ)
  have hsmooth := (physicalForwardIntegral_smooth φ θ lam m A hθ hA hK hAK hms hphase hjets v).1
  have hjet := compactKernel_L2Integral_physicalJets hK hms (physicalForwardKernel φ m A)
    (physicalForwardKernel_smooth φ θ lam m A hθ hA hAK hphase) hjets
    (physicalForwardKernel_tsupport_subset φ m A hK.isClosed hAK)
    (fun u hu x ↦ by
      simp [physicalForwardKernel, sampledMomentKernel, image_eq_zero_of_notMem_tsupport hu])
    v ds.length x
  have hi (b : SliceDerivativeBranch ds.length) : Integrable (fun u ↦
      physicalForwardKernel φ m (fun u y ↦ sliceDerivativeAmplitude (θ u) (A u) dirs b y) x u *
        ((lam u : ℂ)^b.phaseCount * v u)) μ := by
    have hb := forwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK dirs b
    have hwi := hweight b.phaseCount b.phaseCount_le
    have he := integrable_compactKernel_mul_L2
      (continuous_sampledMomentKernel φ m
        (fun u y ↦ star (sliceDerivativeAmplitude (θ u) (A u) dirs b y)) hφ hm (hbc b).star)
      (hasCompactSupport_sampledMomentKernel φ m
        (fun u y ↦ star (sliceDerivativeAmplitude (θ u) (A u) dirs b y))
        hms hK (fun u ↦ (hb u).2))
      (hwi.toLp (fun u ↦ (lam u : ℂ)^b.phaseCount * v u)) x
    apply he.congr
    filter_upwards [hwi.coeFn_toLp] with u hu
    exact congrArg (_ * ·) hu
  have hcoord := euclideanCoordinateDerivList_ofFn_eq_iteratedFDeriv hsmooth ds.get x
  rw [List.ofFn_get] at hcoord
  rw [hcoord, hjet.2, ContinuousMultilinearMap.integral_apply hjet.1]
  calc
    _ = ∫ u, ∑ b : SliceDerivativeBranch ds.length,
        physicalForwardKernel φ m (fun u y ↦ sliceDerivativeAmplitude (θ u) (A u) dirs b y) x u *
          ((lam u : ℂ)^b.phaseCount * v u) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [smul_apply,
        physicalForwardKernel_jet_eq_branches φ θ lam m A hθ hA hAK hphase ds.length dirs x u]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := integral_finsetSum _ (fun b _ ↦ hi b)

end JanetCartan.PhysicalForwardMean
