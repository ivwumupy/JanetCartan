module

public import JanetCartan.Iteration.PhysicalMean.LinearProfiles

/-!
# The original initializer plus the positive-current raw source correction

Consumer: `exists_history_fixedSourceBase_profile`, followed by the physical
mean completion. The correction is the SAME uncut current raw right inverse,
not a sampled carrier slot or a v=0 inverse. The exact paired current bound is
produced by PhysicalNormalInverse.Adjoint from the positive coefficient profile.
The original initializer keeps its own genuine membership and profile.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open CurrentMean ContinuumRow CarrierSobolev CoerciveInverse

private theorem sourceRaw_gradeNorm_add_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : GradedScale E) {s : ℕ} {x y : E}
    (hx : x ∈ S.level s) (hy : y ∈ S.level s) :
    S.gradeNorm s (x+y) ≤ S.gradeNorm s x+S.gradeNorm s y := by
  rw [S.gradeNorm_eq ((S.level s).add_mem hx hy), S.gradeNorm_eq hx, S.gradeNorm_eq hy]
  exact map_add_le_add (S.seminorm s) ⟨x, hx⟩ ⟨y, hy⟩

/-- Apply the actual positive-current paired bound to the SAME smooth source
profile. The original raw Hilbert membership is retained at every order, and
the small source factor is not discarded (`main:prop:mean`). -/
theorem currentRaw_source_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (Craw M : ℕ → ℝ) (hCraw : ∀ s, 0 ≤ Craw s)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {T R h : ℝ} {s₀ : ℕ} (hT : 1 ≤ T) (hTR : T ≤ R)
    (hpair : ∀ s w, w ∈ (periodicSobolevScale n (Euclidean n)).level s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s ((augmentedNormal image U ψ).inverse w) +
        (augmentedInputSobolevScale n ι).gradeNorm s (rightInverse (augmentedRow image U ψ) w) ≤
          Craw s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-s₀)*‖w‖))
    (e : SmoothResidual n)
    (hreg : ∀ s, rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ augmentedInputLevel n ι s)
    (hsource : ∀ s, residualSobolevSeminorm n s e ≤ M s*h*R^(s-s₀)) :
    ∀ s, rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ augmentedInputLevel n ι s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s (rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e)) ≤
        (Craw s*(M s+M 0))*h*R^(s-s₀) := by
  intro s
  refine ⟨hreg s, ?_⟩
  have hR : 1 ≤ R := hT.trans hTR
  have hz : ‖smoothResidualToL2 n e‖ ≤ M 0*h := by
    simpa only [residualSobolevSeminorm_zero, Nat.zero_sub, pow_zero, mul_one] using hsource 0
  have hs := hsource s
  rw [residualSobolevSeminorm_eq_gradeNorm] at hs
  have hlow : T^(s-s₀)*‖smoothResidualToL2 n e‖ ≤ M 0*h*R^(s-s₀) := by
    calc
      _ ≤ R^(s-s₀)*(M 0*h) := mul_le_mul
        (pow_le_pow_left₀ (zero_le_one.trans hT) hTR _) hz (norm_nonneg _)
        (pow_nonneg (zero_le_one.trans hR) _)
      _ = _ := by ring
  have hb := (le_add_of_nonneg_left ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s
    ((augmentedNormal image U ψ).inverse (smoothResidualToL2 n e)))).trans
      (hpair s _ (smoothResidualToL2_mem e s))
  apply hb.trans
  calc
    _ ≤ Craw s*(M s*h*R^(s-s₀)+M 0*h*R^(s-s₀)) :=
      mul_le_mul_of_nonneg_left (add_le_add hs hlow) (hCraw s)
    _ = _ := by ring

/-- The actual initializer and the positive-current correction are added in
one original augmented raw space. No inverse choices are identified: the
initializer's independent v=0 construction is merely retained as a datum.
This produces precisely the raw input required by the actual base/full-strain
producer, with constants fixed before either raw field (`main:prop:mean`). -/
theorem initializedRaw_source_profile {n : ℕ} {ι : Type*} [Fintype ι]
    (Dinit Craw M : ℕ → ℝ) (hDinit : ∀ s, 0 ≤ Dinit s)
    (hCraw : ∀ s, 0 ≤ Craw s) (hM : ∀ s, 0 ≤ M s)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {T R h : ℝ} {s₀ : ℕ} (hT : 1 ≤ T) (hTR : T ≤ R) (hh1 : h ≤ 1)
    (hpair : ∀ s w, w ∈ (periodicSobolevScale n (Euclidean n)).level s →
      (periodicSobolevScale n (Euclidean n)).gradeNorm s ((augmentedNormal image U ψ).inverse w) +
        (augmentedInputSobolevScale n ι).gradeNorm s (rightInverse (augmentedRow image U ψ) w) ≤
          Craw s*((periodicSobolevScale n (Euclidean n)).gradeNorm s w + T^(s-s₀)*‖w‖))
    (initial : AugmentedInput n ι) (hinitial : ∀ s, initial ∈ augmentedInputLevel n ι s)
    (hinitialBound : ∀ s, (augmentedInputSobolevScale n ι).gradeNorm s initial ≤ Dinit s*R^(s-s₀))
    (e : SmoothResidual n)
    (hreg : ∀ s, rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ augmentedInputLevel n ι s)
    (hsource : ∀ s, residualSobolevSeminorm n s e ≤ M s*h*R^(s-s₀)) :
    (∀ s, 0 ≤ Dinit s+Craw s*(M s+M 0)) ∧
    ∀ s, initial+rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ augmentedInputLevel n ι s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s
        (initial+rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e)) ≤
          (Dinit s+Craw s*(M s+M 0))*R^(s-s₀) := by
  have hC (s : ℕ) : 0 ≤ Craw s*(M s+M 0) := mul_nonneg (hCraw s) (add_nonneg (hM s) (hM 0))
  refine ⟨fun s ↦ add_nonneg (hDinit s) (hC s), ?_⟩
  intro s
  let X := augmentedInputSobolevScale n ι
  have hsum : initial+rightInverse (augmentedRow image U ψ) (smoothResidualToL2 n e) ∈ X.level s :=
    (X.level s).add_mem (hinitial s) (hreg s)
  refine ⟨hsum, ?_⟩
  have hadd := sourceRaw_gradeNorm_add_le X (hinitial s) (hreg s)
  have hc := (currentRaw_source_profile Craw M hCraw image U ψ hT hTR hpair e hreg hsource s).2
  have hdrop : (Craw s*(M s+M 0))*h*R^(s-s₀) ≤ (Craw s*(M s+M 0))*R^(s-s₀) :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hC s) hh1)
      (pow_nonneg (zero_le_one.trans (hT.trans hTR)) _)
  exact (hadd.trans (add_le_add (hinitialBound s) (hc.trans hdrop))).trans_eq (by ring)

end JanetCartan.PhysicalMean
