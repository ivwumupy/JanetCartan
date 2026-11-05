module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.ProductAccuracy

/-!
# One response on the sampled complete signed tensor

The response used below is fixed on the whole source space. Its actual
source-domain admission and individual estimates belong to
`both-response-transfer`. Given those estimates, the literal signed correction
is smooth and its full strain error satisfies the pair budget. In particular,
linearity of the derivative on arbitrary nonsmooth fields is never assumed.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep

variable {n N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem differentiableAt_signedSum (b : ℝ) (μ : ι → ℝ)
    (p m : ι → ι → Euclidean n → Euclidean N) {x : Euclidean n}
    (hp : ∀ i j, DifferentiableAt ℝ (p i j) x)
    (hm : ∀ i j, j ≠ i → DifferentiableAt ℝ (m i j) x) :
    DifferentiableAt ℝ (ProductSum.weightedSignedSum b μ p m) x := by
  exact ((DifferentiableAt.sum (fun i _ ↦ DifferentiableAt.sum
      (fun j _ ↦ (hp i j).const_smul _))).add
    (DifferentiableAt.sum (fun i _ ↦ DifferentiableAt.sum
      (fun j hj ↦ (hm i j (Finset.ne_of_mem_erase hj)).const_smul _)))).const_smul _

private theorem strain_signedSum (F : Euclidean n → Euclidean N) (b : ℝ) (μ : ι → ℝ)
    (p m : ι → ι → Euclidean n → Euclidean N) {x : Euclidean n}
    (hp : ∀ i j, DifferentiableAt ℝ (p i j) x)
    (hm : ∀ i j, j ≠ i → DifferentiableAt ℝ (m i j) x) :
    linearizedMetric F (ProductSum.weightedSignedSum b μ p m) x =
      ProductSum.weightedSignedSum b μ (fun i j ↦ linearizedMetric F (p i j) x)
        (fun i j ↦ linearizedMetric F (m i j) x) := by
  have hp' (i : ι) : DifferentiableAt ℝ
      (∑ j, Real.sqrt (μ i * μ j) • p i j) x :=
    DifferentiableAt.sum (fun j _ ↦ (hp i j).const_smul _)
  have hm' (i : ι) : DifferentiableAt ℝ
      (∑ j ∈ Finset.univ.erase i, Real.sqrt (μ i * μ j) • m i j) x :=
    DifferentiableAt.sum (fun j hj ↦ (hm i j (Finset.ne_of_mem_erase hj)).const_smul _)
  rw [ProductSum.weightedSignedSum,
    linearizedMetric_smul_apply ((DifferentiableAt.sum (fun i _ ↦ hp' i)).add
      (DifferentiableAt.sum (fun i _ ↦ hm' i))),
    linearizedMetric_add_apply (DifferentiableAt.sum (fun i _ ↦ hp' i))
      (DifferentiableAt.sum (fun i _ ↦ hm' i)),
    linearizedMetric_sum_apply Finset.univ _ (fun i _ ↦ hp' i),
    linearizedMetric_sum_apply Finset.univ _ (fun i _ ↦ hm' i)]
  apply congrArg (b ^ 2 • ·)
  apply congrArg₂ (· + ·)
  · exact Finset.sum_congr rfl (fun i _ ↦
      linearizedMetric_sum_smul_apply Finset.univ _ _ (fun j _ ↦ hp i j))
  · exact Finset.sum_congr rfl (fun i _ ↦
      linearizedMetric_sum_smul_apply (Finset.univ.erase i) _ _
        (fun j hj ↦ hm i j (Finset.ne_of_mem_erase hj)))

/-- `app:ch_pairs:eq:pairs-weighted-U`: one fixed response `B` gives
the literal correction `-B Qoff`, smooth by its signed-source
outputs. Only the difference diagonal is omitted. This supplies the physical
`S` regularity in `identities_sampled_history_fields` on the same final atoms. -/
theorem contDiff_sampled_product_correction
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ) (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hderivative : ∀ i x, sampledDerivative Z i x = wavePhase (θ i x) • A i x)
    (hp : ∀ i j, ContDiff ℝ ∞ (B (ProductSum.plusSource θ A i j)))
    (hm : ∀ i j, j ≠ i → ContDiff ℝ ∞ (B (ProductSum.minusSource θ A i j))) :
    ContDiff ℝ ∞ (-B (ProductSum.offSelfSource b μ (sampledDerivative Z) A)) := by
  rw [ProductSum.solve_offSelfSource B b μ hμ θ _ A hderivative]
  convert (((ContDiff.sum (s := Finset.univ) (fun i _ ↦ ContDiff.sum (s := Finset.univ)
      (fun j _ ↦ (hp i j).const_smul (Real.sqrt (μ i * μ j))))).add
    (ContDiff.sum (s := Finset.univ) (fun i _ ↦ ContDiff.sum (s := Finset.univ.erase i)
      (fun j hj ↦ (hm i j (Finset.ne_of_mem_erase hj)).const_smul
        (Real.sqrt (μ i * μ j)))))).const_smul (b ^ 2)).neg using 1
  funext x
  simp only [ProductSum.weightedSignedSum, Pi.neg_apply, Pi.smul_apply, Pi.add_apply,
    Finset.sum_apply]

/-- The signed-source triangle estimate `app:ch_pairs:eq:pairs-lag-sum-error`
for the literal physical correction in `SampledStage`. Smoothness of the
individual responses justifies every derivative sum. The supplied errors are
for individual complete sources, including doubled carriers, through the SAME
response `B` with residual `Dγ_F Bq - q`; no estimate for the full off-self
tensor is assumed. -/
theorem sampled_product_correction_error_le
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ) (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hderivative : ∀ i x, sampledDerivative Z i x = wavePhase (θ i x) • A i x)
    {x : Euclidean n} {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ i j, DifferentiableAt ℝ (B (ProductSum.plusSource θ A i j)) x)
    (hm : ∀ i j, j ≠ i → DifferentiableAt ℝ (B (ProductSum.minusSource θ A i j)) x)
    (hep : ∀ i j, ‖linearizedMetric F (B (ProductSum.plusSource θ A i j)) x -
      ProductSum.plusSource θ A i j x‖ ≤ C)
    (hem : ∀ i j, j ≠ i →
      ‖linearizedMetric F (B (ProductSum.minusSource θ A i j)) x -
        ProductSum.minusSource θ A i j x‖ ≤ C) :
    ‖linearizedMetric F (-B (ProductSum.offSelfSource b μ (sampledDerivative Z) A)) x +
      ProductSum.offSelfSource b μ (sampledDerivative Z) A x‖ ≤
        2 * C * b ^ 2 * ProductSum.coefficientMass μ := by
  let p := ProductSum.plusSource θ A
  let m := ProductSum.minusSource θ A
  have hsolve := ProductSum.solve_offSelfSource B b μ hμ θ _ A hderivative
  have hd : DifferentiableAt ℝ (B (ProductSum.offSelfSource b μ (sampledDerivative Z) A)) x := by
    rw [hsolve]
    exact differentiableAt_signedSum b μ _ _ hp hm
  have hstrain : linearizedMetric F (B (ProductSum.offSelfSource b μ (sampledDerivative Z) A)) x =
      ProductSum.weightedSignedSum b μ (fun i j ↦ linearizedMetric F (B (p i j)) x)
        (fun i j ↦ linearizedMetric F (B (m i j)) x) := by
    rw [hsolve]
    exact strain_signedSum F b μ _ _ hp hm
  have herr : linearizedMetric F (-B (ProductSum.offSelfSource b μ (sampledDerivative Z) A)) x +
      ProductSum.offSelfSource b μ (sampledDerivative Z) A x =
      -ProductSum.weightedSignedSum b μ
        (fun i j ↦ linearizedMetric F (B (p i j)) x - p i j x)
        (fun i j ↦ linearizedMetric F (B (m i j)) x - m i j x) := by
    rw [show -B (ProductSum.offSelfSource b μ (sampledDerivative Z) A) =
        (-1 : ℝ) • B (ProductSum.offSelfSource b μ (sampledDerivative Z) A) by simp,
      linearizedMetric_smul_apply hd, neg_one_smul, hstrain,
      ProductSum.offSelfSource_eq_weightedSignedSum b μ hμ θ _ A hderivative]
    simp only [ProductSum.weightedSignedSum, Pi.smul_apply, Finset.sum_apply, Pi.add_apply,
      smul_sub, Finset.sum_sub_distrib, smul_add]
    dsimp only [p, m]
    abel
  rw [herr, norm_neg]
  exact ProductSum.norm_map_weightedSignedSum_le (LinearMap.id : MetricTensor n →ₗ[ℝ] MetricTensor n)
    b μ hμ _ _ hC hep hem

/-- `StageConstants.ComponentEstimates.pair` for the literal one-response
correction on the final sampled family. `both-response-transfer` must produce
the individual complete-source errors at the protected frequency `λh`; this
theorem performs their signed summation, stage-accuracy absorption and physical
cutoff transfer. Its internal order is chosen by `exists_pair_accuracy_order`
before the scale and history, and the minus diagonal is never requested. -/
theorem cut_sampled_product_stage_error_le (D : LocalDomain)
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ) (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hderivative : ∀ i x, sampledDerivative Z i x = wavePhase (θ i x) • A i x)
    (hp : ∀ i j, ContDiff ℝ ∞ (B (ProductSum.plusSource θ A i j)))
    (hm : ∀ i j, j ≠ i → ContDiff ℝ ∞ (B (ProductSum.minusSource θ A i j)))
    {R δ C Ccount Cmass : ℝ} {k q : ℕ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hC : 0 ≤ C) (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hq : 2 * forcingExponent n + 1 + samplingSlack + 2 * (k : ℝ) ≤
      (carrierExponent - separationExponent) * q)
    (hep : ∀ i j, ∀ x ∈ D.core n,
      ‖linearizedMetric F (B (ProductSum.plusSource θ A i j)) x -
        ProductSum.plusSource θ A i j x‖ ≤
          C * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹)
    (hem : ∀ i j, j ≠ i → ∀ x ∈ D.core n,
      ‖linearizedMetric F (B (ProductSum.minusSource θ A i j)) x -
        ProductSum.minusSource θ A i j x‖ ≤
          C * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) :
    let Qoff := ProductSum.offSelfSource (δ * R ^ forcingExponent n) μ (sampledDerivative Z) A
    ∀ x ∈ D.core n,
      ‖linearizedMetric F (periodicLift (Periodization.cutToTorus (physicalCutoff D)
        (-B Qoff))) x + Qoff x‖ ≤
          (2 * C * (Ccount * Cmass)) * δ * R ^ (-2 * (k : ℝ)) := by
  dsimp only
  obtain ⟨_, _, hs, hcore, hone⟩ := physicalCutoff_properties (n := n) D
  intro x hx
  rw [Periodization.linearizedMetric_cutToTorus_eqOn D D.chartRadius_lt_half hs
    Metric.isOpen_ball hcore hone F _ hx]
  have hraw := sampled_product_correction_error_le F B (δ * R ^ forcingExponent n)
    μ hμ Z θ A hderivative
    (C := C * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹)
    (by positivity) (fun i j ↦ (hp i j).differentiable (by simp) x)
    (fun i j hij ↦ (hm i j hij).differentiable (by simp) x)
    (fun i j ↦ hep i j x hx) (fun i j hij ↦ hem i j hij x hx)
  apply pair_error_after_stage_scaling μ hμ hR hδ hδone
    (C := 2 * C) (by positivity) hCcount hCmass hcount hmass hq
  apply hraw.trans_eq
  ring

end JanetCartan.UniformStep
