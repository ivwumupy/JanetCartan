module

public import JanetCartan.Iteration.PhysicalForwardMean.IntegralIdentity

/-!
# Physical forward coordinate norms from original native frequency moments

The exact finite binary expansion is estimated by the SAME scalar auxiliary
row, not by summing sample norms. Constants depend on physical order, dimension,
fixed support box and primitive profiles only. Original input-frequency moment
membership is retained explicitly, before any ENNReal.toReal operation. No
output norm, sample event, frequency derivative bound or sample-count loss is
an assumption. Actual primary13 and phase28 instantiate the primitive jets.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open RawPrimary.SliceBounds PhysicalMean Pseudodifferential AmplitudeBound AmplitudeBound.PaperEstimates

/-- The complete physical forward constant. Its finite sum is over binary
PHYSICAL differentiation branches, never over original samples or shells
(`app:ch_mean_pairs:eq:block-normal`). -/
def forwardDerivativeConstant (n : ℕ) (Rbox : ℝ) (a p : ℕ → ℝ) (s : ℕ) : ℝ :=
  finiteRowAmplitudeConstant n Rbox *
    ∑ b : SliceDerivativeBranch s, forwardBranchConstant (n / 2 + 1) a p b

/-- Positivity of the fixed all-branch budget. -/
theorem forwardDerivativeConstant_nonneg (n : ℕ) (Rbox : ℝ) (a p : ℕ → ℝ) (s : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ forwardDerivativeConstant n Rbox a p s :=
  mul_nonneg (finiteRowAmplitudeConstant_nonneg n Rbox)
    (Finset.sum_nonneg fun b _ ↦ forwardBranchConstant_nonneg b ha hp)

variable {n : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
local notation "E" => Euclidean n

/-- The exact forward physical coordinate bound required in Step 3 of
`app:ch_mean_pairs:eq:block-normal`. The field is the SAME original integral.
Quantitative input jets are required only on the active original mask and
original physical support. Weighted moment membership is a source regularity
condition, not a desired output estimate. All constants precede the arbitrary
native sample space and scale. -/
theorem norm_physicalForwardIntegral_coordinate_le
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : X → E → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hK : IsCompact K) (hAK : ∀ u, tsupport (A u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x)
    (hjets : ∀ j : ℕ, Continuous (fun p : E × X ↦ iteratedFDeriv ℝ j
      (fun y ↦ physicalForwardKernel φ m A y p.2) p.1))
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
    {s0 : ℕ} {T : ℝ} (hT : 1 ≤ T) (a p : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j, 0 ≤ p j)
    (ds : List (Fin n))
    (hAj : ∀ u, m u ≠ 0 → ∀ x ∈ K, ∀ j ≤ ds.length + (n / 2 + 1),
      ‖iteratedFDeriv ℝ j (A u) x‖ ≤ a j * T ^ (j - (s0 + (n / 2 + 1))))
    (hθj : ∀ u, m u ≠ 0 → ∀ x ∈ K, ∀ j, 1 ≤ j → j ≤ ds.length + (n / 2 + 1) →
      ‖iteratedFDeriv ℝ j (θ u) x‖ ≤ p j * T ^ (j - 1 - (s0 + (n / 2 + 1))))
    (hbc : ∀ b : SliceDerivativeBranch ds.length, Continuous (fun q : X × E ↦
      sliceDerivativeAmplitude (θ q.1) (A q.1)
        (fun i ↦ EuclideanSpace.single (ds.get i) 1) b q.2))
    (T0 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT0 : ∀ f : Lp ℂ 2 μ, T0 f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u * f u ∂μ)
    (v : Lp ℂ 2 μ) (hweight : ∀ k ≤ ds.length, MemLp (fun u ↦ (lam u : ℂ)^k * v u) 2 μ) :
    let w := fun x ↦ ∫ u, physicalForwardKernel φ m A x u * v u ∂μ
    MemLp (euclideanCoordinateDerivList ds w) 2 volume ∧
      (eLpNorm (euclideanCoordinateDerivList ds w) 2 volume).toReal ≤
        forwardDerivativeConstant n Rbox a p ds.length * ‖T0‖ *
          ∑ k ∈ Finset.range (ds.length+1), T ^ (ds.length-k-s0) *
            (eLpNorm (fun u ↦ (lam u : ℂ)^k * v u) 2 μ).toReal := by
  classical
  intro w
  let dirs := fun i : Fin ds.length ↦ EuclideanSpace.single (ds.get i) (1 : ℝ)
  have hdirs (i : Fin ds.length) : ‖dirs i‖ ≤ 1 := by simp [dirs, EuclideanSpace.single, PiLp.norm_single]
  let bA := fun b : SliceDerivativeBranch ds.length ↦
    fun u x ↦ star (sliceDerivativeAmplitude (θ u) (A u) dirs b x)
  have hb := fun b ↦ forwardBranch_smooth_supported θ A hθ hA hK.isClosed hAK dirs b
  let Op := fun b ↦ sampledMomentOperator μ φ m (bA b) hφ hm (hbc b).star hms hK
    (fun u ↦ (hb b u).2)
  let vin := fun b : SliceDerivativeBranch ds.length ↦
    (hweight b.phaseCount b.phaseCount_le).toLp (fun u ↦ (lam u : ℂ)^b.phaseCount * v u)
  let V := ∑ b : SliceDerivativeBranch ds.length, Op b (vin b)
  have hae (b : SliceDerivativeBranch ds.length) : Op b (vin b) =ᵐ[volume] fun x ↦
      ∫ u, physicalForwardKernel φ m
        (fun u y ↦ sliceDerivativeAmplitude (θ u) (A u) dirs b y) x u *
          ((lam u : ℂ)^b.phaseCount * v u) ∂μ := by
    apply (sampledMomentOperator_ae_kernel μ φ m (bA b) hφ hm (hbc b).star hms hK
      (fun u ↦ (hb b u).2) (vin b)).trans
    apply Eventually.of_forall
    intro x
    apply integral_congr_ae
    filter_upwards [(hweight b.phaseCount b.phaseCount_le).coeFn_toLp] with u hu
    exact congrArg (_ * ·) hu
  have heq : V =ᵐ[volume] euclideanCoordinateDerivList ds w := by
    have hall := ae_all_iff.mpr hae
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun b ↦ Op b (vin b)), hall] with x hx hxall
    change (∑ b, Op b (vin b)) x = _
    rw [hx, physicalForwardIntegral_coordinate_eq_branchSum φ θ lam m A hφ hm hms hθ hA
      hK hAK hphase hjets ds hbc v hweight x]
    exact Finset.sum_congr rfl (fun b _ ↦ hxall b)
  have hmem := (physicalForwardIntegral_smooth φ θ lam m A hθ hA hK hAK hms hphase hjets v).2.2 ds
  refine ⟨hmem, ?_⟩
  let M := ∑ k ∈ Finset.range (ds.length+1), T ^ (ds.length-k-s0) *
    (eLpNorm (fun u ↦ (lam u : ℂ)^k * v u) 2 μ).toReal
  have hmoment (b : SliceDerivativeBranch ds.length) :
      T ^ (ds.length-b.phaseCount-s0) *
        (eLpNorm (fun u ↦ (lam u : ℂ)^b.phaseCount * v u) 2 μ).toReal ≤ M := by
    apply Finset.single_le_sum (f := fun k ↦ T ^ (ds.length-k-s0) *
      (eLpNorm (fun u ↦ (lam u : ℂ)^k * v u) 2 μ).toReal)
    · intro k _
      exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le b.phaseCount_le)
  have hop (b : SliceDerivativeBranch ds.length) : ‖Op b‖ ≤
      (finiteRowAmplitudeConstant n Rbox * forwardBranchConstant (n / 2 + 1) a p b) *
        ‖T0‖ * T ^ (ds.length-b.phaseCount-s0) :=
    norm_forwardBranchOperator_le_scalarTest μ φ θ m A hφ hm hms hθ hA hK hAK
      χ hχ hχs hχK Rbox hbox hT a p ha hp hAj hθj dirs hdirs b (hbc b) T0 hT0
  have hbound (b : SliceDerivativeBranch ds.length) : ‖Op b (vin b)‖ ≤
      (finiteRowAmplitudeConstant n Rbox * forwardBranchConstant (n / 2 + 1) a p b) * ‖T0‖ * M := by
    calc
      _ ≤ ‖Op b‖ * ‖vin b‖ := (Op b).le_opNorm (vin b)
      _ ≤ ((finiteRowAmplitudeConstant n Rbox * forwardBranchConstant (n / 2 + 1) a p b) *
          ‖T0‖ * T ^ (ds.length-b.phaseCount-s0)) * ‖vin b‖ :=
        mul_le_mul_of_nonneg_right (hop b) (norm_nonneg _)
      _ = ((finiteRowAmplitudeConstant n Rbox * forwardBranchConstant (n / 2 + 1) a p b) * ‖T0‖) *
          (T ^ (ds.length-b.phaseCount-s0) *
            (eLpNorm (fun u ↦ (lam u : ℂ)^b.phaseCount * v u) 2 μ).toReal) := by
        simp only [vin, Lp.norm_toLp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmoment b)
        (mul_nonneg (mul_nonneg (finiteRowAmplitudeConstant_nonneg n Rbox)
          (forwardBranchConstant_nonneg b ha hp)) (norm_nonneg _))
  calc
    _ = ‖V‖ := by rw [Lp.norm_def, eLpNorm_congr_ae heq]
    _ ≤ ∑ b : SliceDerivativeBranch ds.length, ‖Op b (vin b)‖ := norm_sum_le _ _
    _ ≤ ∑ b : SliceDerivativeBranch ds.length,
        (finiteRowAmplitudeConstant n Rbox * forwardBranchConstant (n / 2 + 1) a p b) * ‖T0‖ * M :=
      Finset.sum_le_sum (fun b _ ↦ hbound b)
    _ = _ := by
      change _ = forwardDerivativeConstant n Rbox a p ds.length * ‖T0‖ * M
      simp only [forwardDerivativeConstant, Finset.sum_mul, Finset.mul_sum]

end JanetCartan.PhysicalForwardMean
