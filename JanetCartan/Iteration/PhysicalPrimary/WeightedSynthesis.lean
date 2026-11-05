module

public import JanetCartan.Iteration.PhysicalPrimary.Synthesis

/-!
# Sharp synthesis retaining every original zero-weight label

Only labels with nonzero OUTER weight require local smoothness or sharp jets.
The literal `sampledPrimary b μ Z` still sums over the original entire family;
zero-weight summands vanish before differentiation. The fixed final physical
cutoff acts on this unchanged real sum, never on the raw waves or native
response. No inner-angular factor is inserted into the positive baseline.

These are conditional deductions, not an actual current-wave or primary
existence theorem. Task77 supplies actual active-label local smoothness,
task13 supplies the sharp corrected-wave jets, and task26 supplies the same
sample's count and mass. The constants below precede scale, amplitude and
wave choice and retain the literal revised forcing exponent, square-root
count loss, physical frequency `2π ξ`, and inverse carrier at order zero.
Consumers: the final common-cutoff primary and
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`
(`main:eq:primary`, `main:eq:primary-fixed-scales`, `main:eq:self-off`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory FourierTransform Filter
open scoped ContDiff Topology

namespace JanetCartan.PhysicalPrimary

open UniformStep Pseudodifferential

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The original real sampled field is unchanged when the complex fields
agree at every nonzero outer weight. No label is deleted and no weight is
divided (`main:eq:primary`). -/
theorem sampledPrimary_congr_of_weighted (b : ℝ) (μ : ι → ℝ)
    {Z W : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (h : ∀ i, μ i ≠ 0 → Z i = W i) :
    sampledPrimary b μ Z = sampledPrimary b μ W := by
  unfold sampledPrimary
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : μ i = 0
  · simp only [hi, Real.sqrt_zero, zero_smul]
  · rw [h i hi]

/-- Local smoothness of the SAME weighted primary needs smoothness only at
nonzero outer weights. A zero-weight summand is the zero function, regardless
of the unused complex field (`main:eq:primary`). -/
theorem contDiffOn_sampledPrimary_of_weighted (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)} {U : Set (Euclidean n)}
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) U) :
    ContDiffOn ℝ ∞ (sampledPrimary b μ Z) U := by
  have ht (i : ι) : ContDiffOn ℝ ∞
      (Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) U := by
    by_cases hi : μ i = 0
    · simp only [hi, Real.sqrt_zero, zero_smul]
      exact contDiffOn_const
    · exact (euclideanRealPart.contDiff.comp_contDiffOn (hZ i hi)).const_smul (Real.sqrt (μ i))
  convert (ContDiffOn.sum (s := Finset.univ) (fun i _ ↦ ht i)).const_smul
    (b * Real.sqrt 2) using 1
  funext x
  simp only [sampledPrimary, Pi.smul_apply, Finset.sum_apply]

/-- Pointwise weighted jet synthesis differentiates only the original weighted
summands. The bound needs no sign assumption on `M`: when all weights vanish,
both sides vanish even for negative `M` (`main:eq:primary-fixed-scales`). -/
theorem norm_iteratedFDeriv_sampledPrimary_le_of_weighted {b : ℝ} (hb : 0 ≤ b)
    (μ : ι → ℝ) (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (q : ℕ) (x : Euclidean n)
    (hZ : ∀ i, μ i ≠ 0 → ContDiffAt ℝ q (Z i) x) {M : ℝ}
    (hjet : ∀ i, μ i ≠ 0 → ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ q (sampledPrimary b μ Z) x‖ ≤
      (b * Real.sqrt 2) * ((∑ i, Real.sqrt (μ i)) * M) := by
  have ht (i : ι) : ContDiffAt ℝ q
      (Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x := by
    by_cases hi : μ i = 0
    · simp only [hi, Real.sqrt_zero, zero_smul]
      exact contDiffAt_const
    · exact (euclideanRealPart.contDiff.contDiffAt.comp x (hZ i hi)).const_smul (Real.sqrt (μ i))
  have hterm (i : ι) :
      ‖iteratedFDeriv ℝ q (Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x‖ ≤
        Real.sqrt (μ i) * M := by
    by_cases hi : μ i = 0
    · simp only [hi, Real.sqrt_zero, zero_smul, iteratedFDeriv_zero,
        Pi.zero_apply, norm_zero, zero_mul, le_refl]
    · have hr : ContDiffAt ℝ q (euclideanRealPart ∘ Z i) x :=
        euclideanRealPart.contDiff.contDiffAt.comp x (hZ i hi)
      have hreal : ‖iteratedFDeriv ℝ q (euclideanRealPart ∘ Z i) x‖ ≤ M := by
        apply (euclideanRealPart.norm_iteratedFDeriv_comp_left (hZ i hi) le_rfl).trans
        exact ((mul_le_mul_of_nonneg_right euclideanRealPart_norm_le (norm_nonneg _)).trans_eq
          (one_mul _)).trans (hjet i hi)
      rw [iteratedFDeriv_const_smul_apply hr, norm_smul,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left hreal (Real.sqrt_nonneg _)
  have hsum : ContDiffAt ℝ q
      (∑ i, Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x := by
    convert ContDiffAt.sum (s := Finset.univ) (fun i _ ↦ ht i) using 1
    ext y a
    simp only [Pi.smul_apply, Finset.sum_apply]
  rw [sampledPrimary, iteratedFDeriv_const_smul_apply hsum,
    iteratedFDeriv_sum_apply (f := fun i ↦ Real.sqrt (μ i) • (euclideanRealPart ∘ Z i))
      (u := Finset.univ) (fun i _ ↦ ht i), norm_smul,
    Real.norm_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb (Real.sqrt_nonneg _))
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ q (Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, Real.sqrt (μ i) * M := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = _ := by rw [Finset.sum_mul]

/-- Active-label sharp jets give the SAME local norm of the literal original
sample. The `λ^(r-1)` factor includes `λ⁻¹` at order zero; inactive labels need
neither smoothness nor bounds (`main:eq:primary-fixed-scales`). -/
theorem cNorm_sampledPrimary_le_of_weighted_sharp_jets (D : LocalDomain)
    {b : ℝ} (hb : 0 ≤ b) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n))
    (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q) {lam : ℝ} (hlam : 1 ≤ lam)
    (hjet : ∀ i, μ i ≠ 0 → ∀ q,
      ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
        ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ Cphys q * lam ^ ((q : ℝ) - 1)) (r : ℕ) :
    cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
        r (sampledPrimary b μ Z) ≤
      (b * Real.sqrt 2) * (∑ i, Real.sqrt (μ i)) *
        (∑ j ∈ Finset.range (r + 1), Cphys j) * lam ^ ((r : ℝ) - 1) := by
  have hcut : (physicalCutoff (n := n) D).rOut < D.chartRadius := by
    dsimp only [physicalCutoff]
    linarith [D.coreRadius_lt_chartRadius]
  have hjets (q : ℕ) (hq : q ≤ r) (x : Euclidean n)
      (hx : x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) :
      ‖iteratedFDeriv ℝ q (sampledPrimary b μ Z) x‖ ≤
        (b * Real.sqrt 2) * ((∑ i, Real.sqrt (μ i)) * (Cphys q * lam ^ ((r : ℝ) - 1))) := by
    apply norm_iteratedFDeriv_sampledPrimary_le_of_weighted hb μ Z q x
      (fun i hi ↦ ((hZ i hi).contDiffAt
        (isOpen_ball.mem_nhds (closedBall_subset_ball hcut hx))).of_le (by simp))
    intro i hi
    exact (hjet i hi q x hx).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlam (sub_le_sub_right (by exact_mod_cast hq) 1)) (hCphys q))
  have hc := cNorm_le_sum_of_bounds
    (C := fun q ↦ (b * Real.sqrt 2) * ((∑ i, Real.sqrt (μ i)) * (Cphys q * lam ^ ((r : ℝ) - 1))))
    (fun q _ ↦ mul_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))
      (mul_nonneg (Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg (μ i))
        (mul_nonneg (hCphys q) (Real.rpow_nonneg (zero_le_one.trans hlam) _)))) hjets
  apply hc.trans_eq
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The common final cutoff acts on the SAME literal primary at every physical
point. Its smoothness proof only uses active labels (`main:eq:primary`). -/
theorem cutSchwartz_sampledPrimary_apply_of_weighted (D : LocalDomain)
    (b : ℝ) (μ : ι → ℝ) (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n)) (x : Euclidean n) :
    cutSchwartz D (sampledPrimary b μ Z)
        (contDiffOn_sampledPrimary_of_weighted b μ hZ) x =
      physicalCutoff D x • sampledPrimary b μ Z x := rfl

/-- The SAME fixed final cutoff preserves the complete core germ of the
original all-label weighted sum (`main:eq:metric-ledger`). -/
theorem cutSchwartz_sampledPrimary_eventuallyEq_of_weighted (D : LocalDomain)
    (b : ℝ) (μ : ι → ℝ) (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    (cutSchwartz D (sampledPrimary b μ Z) (contDiffOn_sampledPrimary_of_weighted b μ hZ) :
        Euclidean n → Euclidean N) =ᶠ[𝓝 x] sampledPrimary b μ Z :=
  cutSchwartz_eventuallyEq D _ (contDiffOn_sampledPrimary_of_weighted b μ hZ) hx

/-- All core jets remain those of the literal original primary, without
regularizing or replacing any zero-weight complex wave (`main:eq:primary`). -/
theorem iteratedFDeriv_cutSchwartz_sampledPrimary_eq_of_weighted (D : LocalDomain)
    (b : ℝ) (μ : ι → ℝ) (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n)) (q : ℕ)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    iteratedFDeriv ℝ q (cutSchwartz D (sampledPrimary b μ Z)
        (contDiffOn_sampledPrimary_of_weighted b μ hZ)) x =
      iteratedFDeriv ℝ q (sampledPrimary b μ Z) x :=
  ((cutSchwartz_sampledPrimary_eventuallyEq_of_weighted D b μ Z hZ hx).iteratedFDeriv ℝ q).self_of_nhds

/-- The literal derivative matrix of the original weighted sum is the original
weighted derivative matrix sum. A zero-weight field is never differentiated
under a false regularity claim (`app:ch_pairs:eq:pairs-exact-offself`). -/
theorem differentialMatrix_sampledPrimary_of_weighted (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hZ : ∀ i, μ i ≠ 0 → DifferentiableAt ℝ (Z i) x) :
    differentialMatrix (sampledPrimary b μ Z) x =
      realWaveMatrixSum b μ (fun i ↦ sampledDerivative Z i x) := by
  have ht (i : ι) : DifferentiableAt ℝ
      (Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x := by
    by_cases hi : μ i = 0
    · simp only [hi, Real.sqrt_zero, zero_smul]
      exact differentiableAt_const _
    · exact (euclideanRealPart.differentiableAt.comp x (hZ i hi)).const_smul _
  have hd (i : ι) : fderiv ℝ (Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)) x =
      Real.sqrt (μ i) • euclideanRealPart.comp (fderiv ℝ (Z i) x) := by
    by_cases hi : μ i = 0
    · simp only [hi, Real.sqrt_zero, zero_smul, fderiv_zero, Pi.zero_apply]
      apply ContinuousLinearMap.ext
      intro v
      change (0 : Euclidean N) = (0 : ℝ) • euclideanRealPart (fderiv ℝ (Z i) x v)
      exact (zero_smul ℝ _).symm
    · rw [fderiv_const_smul (euclideanRealPart.differentiableAt.comp x (hZ i hi))]
      congr 1
      exact (euclideanRealPart.hasFDerivAt.comp x (hZ i hi).hasFDerivAt).fderiv
  ext a j
  simp only [differentialMatrix, sampledPrimary, partialDeriv,
    fderiv_const_smul (DifferentiableAt.sum (fun i _ ↦ ht i)),
    fderiv_sum (fun i _ ↦ ht i), hd]
  simp [realWaveMatrixSum, Matrix.sum_apply, sampledDerivative, partialDeriv, Finset.sum_apply]

/-- The complete off/self source remains the literal metric minus the same
Hermitian self tensor when only active labels are differentiable. No global
regularity is claimed for zero-weight waves (`main:eq:self-off`). -/
theorem offSelfSource_sampledDerivative_of_weighted (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, μ i ≠ 0 → Differentiable ℝ (Z i))
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ) :
    ProductSum.offSelfSource b μ (sampledDerivative Z) A =
      inducedMetric (sampledPrimary b μ Z) -
        b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun x i ↦ A i x) := by
  funext x
  rw [Pi.sub_apply, inducedMetric_eq_transpose_mul,
    differentialMatrix_sampledPrimary_of_weighted b μ (fun i hi ↦ hZ i hi x)]
  rfl

/-- The complete plus/minus ledger uses the original weights, including the
plus diagonal. Both differentiability and derivative factorization are needed
only at nonzero outer weights (`app:ch_pairs:eq:pairs-exact-offself`). -/
theorem sampledPrimary_offSelf_eq_signedSum_of_weighted [DecidableEq ι]
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, μ i ≠ 0 → Differentiable ℝ (Z i))
    (θ : ι → Euclidean n → ℝ) (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hderivative : ∀ i, μ i ≠ 0 → ∀ x,
      sampledDerivative Z i x = wavePhase (θ i x) • A i x) :
    inducedMetric (sampledPrimary b μ Z) -
        b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun x i ↦ A i x) =
      ProductSum.weightedSignedSum b μ (ProductSum.plusSource θ A) (ProductSum.minusSource θ A) := by
  have hd (x : Euclidean n) :
      realWaveMatrixSum b μ (fun i ↦ sampledDerivative Z i x) =
        realWaveMatrixSum b μ (fun i ↦ wavePhase (θ i x) • A i x) := by
    unfold realWaveMatrixSum
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : μ i = 0
    · simp only [hi, Real.sqrt_zero, zero_smul]
    · exact congrArg (fun T : Matrix (Fin N) (Fin n) ℂ ↦ Real.sqrt (μ i) • T.map Complex.re)
        (hderivative i hi x)
  rw [← offSelfSource_sampledDerivative_of_weighted b μ hZ A]
  calc
    _ = ProductSum.offSelfSource b μ (fun i x ↦ wavePhase (θ i x) • A i x) A := by
      funext x
      unfold ProductSum.offSelfSource
      rw [hd x]
    _ = _ := ProductSum.offSelfSource_eq_weightedSignedSum b μ hμ θ _ A (fun _ _ ↦ rfl)

/-- The SAME fixed cutoff preserves the linearized metric on the original
core, using only active-label local smoothness (`main:eq:primary-strain`). -/
theorem linearizedMetric_cutSchwartz_sampledPrimary_eq_of_weighted (D : LocalDomain)
    (F : Euclidean n → Euclidean N) (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    linearizedMetric F (cutSchwartz D (sampledPrimary b μ Z)
        (contDiffOn_sampledPrimary_of_weighted b μ hZ)) x =
      linearizedMetric F (sampledPrimary b μ Z) x := by
  have hd := (cutSchwartz_sampledPrimary_eventuallyEq_of_weighted D b μ Z hZ hx).fderiv_eq (𝕜 := ℝ)
  ext i j
  simp only [linearizedMetric, partialDeriv, hd]

/-- The real Schwartz primary's core self tensor and off/self source use the
SAME literal original complex derivative family, including every zero-weight
label. The uncut waves need only active-label local smoothness
(`main:eq:self-off`). -/
theorem inducedMetric_cutSchwartz_sampledPrimary_eq_self_add_off_of_weighted (D : LocalDomain)
    (b : ℝ) (μ : ι → ℝ) (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ)
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    inducedMetric (cutSchwartz D (sampledPrimary b μ Z)
        (contDiffOn_sampledPrimary_of_weighted b μ hZ)) x =
      b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun y i ↦ sampledDerivative Z i y) x +
        ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x := by
  have hxc : x ∈ D.chart n := closedBall_subset_ball D.coreRadius_lt_chartRadius hx
  have hd (i : ι) (hi : μ i ≠ 0) : DifferentiableAt ℝ (Z i) x :=
    ((hZ i hi).contDiffAt (isOpen_ball.mem_nhds hxc)).differentiableAt (by simp)
  have he : inducedMetric (cutSchwartz D (sampledPrimary b μ Z)
        (contDiffOn_sampledPrimary_of_weighted b μ hZ)) x =
      inducedMetric (sampledPrimary b μ Z) x := by
    have hdcut := (cutSchwartz_sampledPrimary_eventuallyEq_of_weighted D b μ Z hZ hx).fderiv_eq (𝕜 := ℝ)
    ext i j
    simp only [inducedMetric, partialDeriv, hdcut]
  rw [he, weightedHermitian_sampledDerivativeAmplitude μ Z θ,
    inducedMetric_eq_transpose_mul, differentialMatrix_sampledPrimary_of_weighted b μ hd]
  simp only [ProductSum.offSelfSource, hermitianSelfSum, CurrentMean.weightedHermitianTensor]
  abel

/-- On the original core, the same final physical cutoff has the complete
signed quadratic source of the original derivative amplitudes, with no extra
smoothness or phase-factorization premise for inactive labels
(`app:ch_pairs:lem:pairs-ledger`). -/
theorem cutSchwartz_sampledPrimary_signed_sum_of_weighted [DecidableEq ι] (D : LocalDomain)
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    inducedMetric (cutSchwartz D (sampledPrimary b μ Z)
        (contDiffOn_sampledPrimary_of_weighted b μ hZ)) x -
        b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun y i ↦ sampledDerivative Z i y) x =
      ProductSum.weightedSignedSum b μ
        (ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ))
        (ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ)) x := by
  rw [inducedMetric_cutSchwartz_sampledPrimary_eq_self_add_off_of_weighted D b μ Z θ hZ hx,
    add_sub_cancel_left]
  exact congrFun (ProductSum.offSelfSource_eq_weightedSignedSum b μ hμ θ
    (sampledDerivative Z) (sampledDerivativeAmplitude Z θ)
    (sampledDerivative_eq_phase_smul_amplitude Z θ)) x

/-- The unchanged final physical cutoff has the original all-order Sobolev
profiles. Constants are chosen BEFORE scale, amplitude, weights and fields.
Only active-label local smoothness/sharp jets are assumed; the internal
zero-family is used solely to reuse the existing quantitative theorem, and
the exported Schwartz field is proved equal on ALL of physical space
(`main:eq:primary-fixed-scales`). -/
theorem exists_cutSampledPrimary_physical_profiles_of_weighted (D : LocalDomain)
    (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q)
    {Ccount Cmass : ℝ} (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      ∀ (R δ : ℝ), 1 ≤ R → 0 ≤ δ →
      ∀ (μ : ι → ℝ), (∀ i, 0 ≤ μ i) →
      (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack) →
      (∑ i, μ i) ≤ Cmass →
      ∀ (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
        (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n)),
      (∀ i, μ i ≠ 0 → ∀ q,
        ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
          ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ Cphys q * (R ^ carrierExponent) ^ ((q : ℝ) - 1)) →
      ∀ r : ℕ, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (PhysicalCutoff.complexify
            (cutSchwartz D (sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z)
              (contDiffOn_sampledPrimary_of_weighted _ μ hZ))) ξ) 2 volume).toReal ≤
        C r * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1) := by
  classical
  obtain ⟨C, hC, hprofiles⟩ := exists_cutSampledPrimary_physical_profiles
    (n := n) (N := N) (ι := ι) D Cphys hCphys hCcount hCmass
  refine ⟨C, hC, ?_⟩
  intro R δ hR hδ μ hμ hcount hmass Z hZ hjet r
  let W : ι → Euclidean n → EuclideanSpace ℂ (Fin N) :=
    fun i ↦ if μ i = 0 then 0 else Z i
  have hW (i : ι) : ContDiffOn ℝ ∞ (W i) (D.chart n) := by
    by_cases hi : μ i = 0
    · have hz : W i = fun _ : Euclidean n ↦ (0 : EuclideanSpace ℂ (Fin N)) := by
        funext y
        simp only [W, ite_eq_left hi, Pi.zero_apply]
      rw [hz]
      exact contDiffOn_const
    · simpa only [W, ite_eq_right hi] using hZ i hi
  have hWjet (i : ι) (q : ℕ)
      (x : Euclidean n) (hx : x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) :
      ‖iteratedFDeriv ℝ q (W i) x‖ ≤ Cphys q * (R ^ carrierExponent) ^ ((q : ℝ) - 1) := by
    by_cases hi : μ i = 0
    · simp only [W, ite_eq_left hi, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (hCphys q)
        (Real.rpow_nonneg (Real.rpow_nonneg (zero_le_one.trans hR) _) _)
    · simpa only [W, ite_eq_right hi] using hjet i hi q x hx
  have hsum : sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z =
      sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ W := by
    apply sampledPrimary_congr_of_weighted
    intro i hi
    simp only [W, ite_eq_right hi]
  have hcut : cutSchwartz D (sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z)
      (contDiffOn_sampledPrimary_of_weighted _ μ hZ) =
      cutSampledPrimary D (δ * R ^ RevisedScales.forcingExponent n) μ W hW := by
    apply SchwartzMap.ext
    intro x
    change physicalCutoff D x • sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z x =
      physicalCutoff D x • sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ W x
    rw [hsum]
  rw [hcut]
  exact hprofiles R δ hR hδ μ hμ hcount hmass W hW hWjet r

open SeparatedSampling CanonicalRowComparison in
/-- Uniform profiles for the *actual varying sample enumeration*. The original
`SampleIndex` depends on the stage and global shifts, so a constant chosen for
one fixed finite label type is not a stage-uniform witness. Here the cutoff
constants are chosen before both, and the deterministic budgets of the native
sample supply the whole square-root weight sum, for these very same labels and
shifts. No cardinality, mass or positivity of sampled weights is an input.
The patch weights may be the original outer χ²; neither the event nor the
unchanged corrected waves are selected here (`main:eq:sampling`,
`main:eq:primary-fixed-scales`). -/
theorem exists_cutSampledPrimary_physical_profiles_on_original_sample {A : Type*} [Fintype A]
    (D : LocalDomain) (p : ℕ) {B W : ℝ} (hB : 0 ≤ B) {P : A → ℝ}
    {weights : A → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hweights : ∀ a, PatchBounds (weights a) B (P a))
    (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      ∀ (R δ : ℝ), 1 ≤ R → 0 ≤ δ → ∀ (shifts : A → Lattice → Point),
      let mesh := R ^ (-separationExponent)
      let μ := sampleWeight (p := p) B weights w mesh shifts
      ∀ (Z : SampleIndex p B weights w mesh shifts → Euclidean n → EuclideanSpace ℂ (Fin N))
        (hZ : ∀ i, μ i ≠ 0 → ContDiffOn ℝ ∞ (Z i) (D.chart n)),
      (∀ i, μ i ≠ 0 → ∀ q,
        ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
          ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ Cphys q * (R ^ carrierExponent) ^ ((q : ℝ) - 1)) →
      ∀ r : ℕ, (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (PhysicalCutoff.complexify
            (cutSchwartz D (sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z)
              (contDiffOn_sampledPrimary_of_weighted _ μ hZ))) ξ) 2 volume).toReal ≤
        C r * δ * R ^ (RevisedScales.forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1) := by
  choose Ccut hCcut hcut using fun r ↦ exists_cutSchwartz_physicalWeightedNorm_bound (n := n) (N := N) D r
  let Ccount := (Fintype.card A : ℝ) * countConstant p B
  let Cmass := countConstant p B * ((∑ a, P a) * W ^ 3)
  let C (r : ℕ) := Ccut r * Real.sqrt 2 * Real.sqrt (Ccount * Cmass) *
    (∑ j ∈ Finset.range (r + 1), Cphys j)
  have hCtotal (r : ℕ) : 0 ≤ ∑ j ∈ Finset.range (r + 1), Cphys j :=
    Finset.sum_nonneg fun j _ ↦ hCphys j
  refine ⟨C, fun r ↦ mul_nonneg
    (mul_nonneg (mul_nonneg (hCcut r) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (hCtotal r), ?_⟩
  intro R δ hR hδ shifts mesh μ Z hZ hjet r
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsum : (∑ i, Real.sqrt (μ i)) ≤ Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2) :=
    (sampled_weight_budgets_originalScale p hB hw hweights hR shifts).2.2.2.2.2.2
  have hlam : 1 ≤ R ^ carrierExponent := Real.one_le_rpow hR (by norm_num [carrierExponent])
  have hc := cNorm_sampledPrimary_le_of_weighted_sharp_jets D
    (b := δ * R ^ RevisedScales.forcingExponent n) (by positivity) μ Z hZ Cphys hCphys hlam hjet r
  have hCcutr := hCcut r
  have hCtotalr := hCtotal r
  calc
    _ ≤ Ccut r * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
        r (sampledPrimary (δ * R ^ RevisedScales.forcingExponent n) μ Z) :=
      hcut r _ (contDiffOn_sampledPrimary_of_weighted _ μ hZ)
    _ ≤ Ccut r * ((δ * R ^ RevisedScales.forcingExponent n * Real.sqrt 2) *
        (∑ i, Real.sqrt (μ i)) * (∑ j ∈ Finset.range (r + 1), Cphys j) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hc (hCcut r)
    _ ≤ Ccut r * ((δ * R ^ RevisedScales.forcingExponent n * Real.sqrt 2) *
        (Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2)) *
          (∑ j ∈ Finset.range (r + 1), Cphys j) *
          (R ^ carrierExponent) ^ ((r : ℝ) - 1)) := by gcongr
    _ = _ := by rw [Real.rpow_add hRp]; dsimp only [C]; ring

end JanetCartan.PhysicalPrimary
end
