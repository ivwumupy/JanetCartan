module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSampleMass
public import JanetCartan.Iteration.PhysicalPairs.OriginalCorrectedLag
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledProduct

/-! # Honest signed summation on the common completed physical waves

Only the algebraic expansion is independent of phase spelling: it is the exact
Hermitian self subtraction of the full derivative, not a quadratic expression
on leading envelopes. The individual analytic prices keep their true ρ. Pay
the half-mesh loss explicitly before multiplying by the original mass.
`app:ch_pairs:eq:pairs-exact-offself`, `app:ch_pairs:eq:pairs-lag-sum-error`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff BigOperators SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalLagAlgebra
open UniformStep OriginalSignedSum
variable {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "E" => Euclidean n
local notation "V" => Euclidean N

def strainAt (F : E → V) (x : E) : 𝓢(E,V) →ₗ[ℝ] MetricTensor n where
  toFun S := linearizedMetric F S x
  map_add' S T := linearizedMetric_add_apply (S.smooth'.differentiable (by simp) x) (T.smooth'.differentiable (by simp) x)
  map_smul' c S := linearizedMetric_smul_apply (S.smooth'.differentiable (by simp) x) c

def offSelf (δ R : ℝ) (μ : I → ℝ) (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N))) (θ : I → E → ℝ) : MetricField n :=
  ProductSum.offSelfSource (δ*R^(RevisedScales.forcingExponent n)) μ
    (sampledDerivative (fun k ↦ (Z k : E → EuclideanSpace ℂ (Fin N))))
    (sampledDerivativeAmplitude (fun k ↦ (Z k : E → EuclideanSpace ℂ (Fin N))) θ)

omit [Fintype I] [DecidableEq I] in
theorem signed_tensor_on_plateau (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N))) (θ θ' : I → E → ℝ) (η : E → ℝ) {x : E} (he : η x = 1)
    (minus : Bool) (i j : I) : OriginalSignedPackets.originalTensor Z θ' minus i j η x = SampledInput.tensor Z θ minus i j x := by
  unfold OriginalSignedPackets.originalTensor
  rw [he,one_smul,SampledInput.tensor_formula,SampledInput.tensor_formula]

theorem sum_strain (F : E → V) (packet : Members n N I)
    (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N))) (θ : I → E → ℝ)
    (angles : (minus : Bool) → (i j : I) → (minus = true → i ≠ j) → I → E → ℝ)
    (η : E → ℝ) (δ R : ℝ) (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) {x : E} (hη : η x = 1) (C : ℝ) (hC : 0 ≤ C)
    (hsingle : ∀ minus i j hd, ‖linearizedMetric F (packet minus i j hd) x - OriginalSignedPackets.originalTensor Z (angles minus i j hd) minus i j η x‖ ≤ C) :
    ‖linearizedMetric F (OriginalSignedSum.sum packet δ R μ) x + offSelf δ R μ Z θ x‖ ≤
      2*C*(δ*R^(RevisedScales.forcingExponent n))^2*ProductSum.coefficientMass μ := by
  let b := δ*R^(RevisedScales.forcingExponent n)
  let A := sampledDerivativeAmplitude (fun k ↦ (Z k : E → EuclideanSpace ℂ (Fin N))) θ
  let L := strainAt F x
  let p (i j : I) := packet false i j (by simp)
  let m := OriginalSignedSum.ordinaryMinus packet
  let P := ProductSum.plusSource θ A
  let M := ProductSum.minusSource θ A
  let ep := fun i j ↦ L (p i j) - P i j x
  let em := fun i j ↦ L (m i j) - M i j x
  have hh (sg i j hd) := (hsingle sg i j hd).trans_eq (rfl : C = C)
  have hp (i j : I) : ‖ep i j‖ ≤ C := by
    have a := hh false i j (by simp)
    rw [signed_tensor_on_plateau Z θ _ η hη] at a
    exact a
  have hm (i j : I) (hne : j ≠ i) : ‖em i j‖ ≤ C := by
    have a := hh true i j (fun _ ↦ hne.symm)
    rw [signed_tensor_on_plateau Z θ _ η hη] at a
    have hm' : m i j = packet true i j (fun _ ↦ hne.symm) := by simp [m,OriginalSignedSum.ordinaryMinus,hne.symm]
    change ‖L (m i j) - M i j x‖ ≤ C
    rw [hm']
    exact a
  have source := ProductSum.offSelfSource_eq_weightedSignedSum b μ hμ θ _ A
    (sampledDerivative_eq_phase_smul_amplitude (fun k ↦ (Z k : E → EuclideanSpace ℂ (Fin N))) θ)
  have he : L (-ProductSum.weightedSignedSum b μ p m) + offSelf δ R μ Z θ x = -ProductSum.weightedSignedSum b μ ep em := by
    change L (-ProductSum.weightedSignedSum b μ p m) + ProductSum.offSelfSource b μ _ A x = _
    rw [map_neg, ProductSum.map_weightedSignedSum,source]
    simp only [ep,em,P,M,ProductSum.weightedSignedSum,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,smul_sub,Finset.sum_sub_distrib,smul_add]
    abel
  change ‖L (-ProductSum.weightedSignedSum b μ p m) + offSelf δ R μ Z θ x‖ ≤ _
  rw [he,norm_neg]
  exact ProductSum.norm_map_weightedSignedSum_le (LinearMap.id : MetricTensor n →ₗ[ℝ] MetricTensor n) b μ hμ ep em hC hp hm

theorem true_rate {R beat : ℝ} (hR : 1 ≤ R) (hb : R^(-separationExponent)/2 ≤ beat) (q : ℕ) :
    (R^carrierExponent*beat)^(-(q:ℝ)) ≤ (2:ℝ)^q * R^(-((carrierExponent-separationExponent)*(q:ℝ))) := by
  have hp := zero_lt_one.trans_le hR
  have hlow : R^(carrierExponent-separationExponent)/2 ≤ R^carrierExponent*beat := by
    rw [sub_eq_add_neg,Real.rpow_add hp]
    exact (by ring : R^carrierExponent*R^(-separationExponent)/2 = R^carrierExponent*(R^(-separationExponent)/2)).le.trans
      (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _))
  calc
    _ ≤ (R^(carrierExponent-separationExponent)/2)^(-(q:ℝ)) := Real.rpow_le_rpow_of_nonpos (half_pos (Real.rpow_pos_of_pos hp _)) hlow (neg_nonpos.mpr (Nat.cast_nonneg _))
    _ = _ := by
      rw [Real.div_rpow (Real.rpow_nonneg hp.le _) (by norm_num),← Real.rpow_mul hp.le, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, div_inv_eq_mul,mul_comm, mul_neg]

theorem total_price {R δ A G M mass : ℝ} (hR : 1 ≤ R) (hG : 0 ≤ G) (q : ℕ)
    (hm : mass ≤ M*R^(1+samplingSlack)) :
    2*(G*(2:ℝ)^q*R^(-((carrierExponent-separationExponent)*(q:ℝ))))*(δ*R^A)^2*mass ≤
    (2*G*(2:ℝ)^q*M)*δ^2*R^(2*A+1+samplingSlack-(carrierExponent-separationExponent)*(q:ℝ)) := by
  have hp := zero_lt_one.trans_le hR
  set l := (carrierExponent-separationExponent)*(q:ℝ)
  have pow_two : (R^A)^2 = R^(2*A) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp.le]; congr 1; push_cast; ring
  calc
    _ ≤ 2*(G*(2:ℝ)^q*R^(-l))*(δ*R^A)^2*(M*R^(1+samplingSlack)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (2*G*(2:ℝ)^q*M)*δ^2*(R^(-l)*R^(2*A)*R^(1+samplingSlack)) := by rw [mul_pow,pow_two]; ring
    _ = _ := by rw [← Real.rpow_add hp,← Real.rpow_add hp]; congr 1; congr 1; ring
end JanetCartan.PhysicalPairs.OriginalLagAlgebra
end
