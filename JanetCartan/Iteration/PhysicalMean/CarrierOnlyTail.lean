module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.RawEnergy
public import JanetCartan.Iteration.PhysicalNormalInverse.MeanFrontend
public import JanetCartan.Iteration.PhysicalMean.LinearProfiles

/-!
# The actual carrier-only cutoff and the faithful two-term linear source error

The cutoff is applied only to the ORIGINAL leading carrier input. The image
and exterior auxiliary channels stay uncut. Its source-dependent tail is
proved from genuine raw Sobolev membership, then added to corrected-normal
transport and sampling on the SAME current inverse
(`app:ch_background:eq:bg-carrier-tail`, `new:sec:mean-source-equation`).
No all-L² cutoff error or high-order contraction is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open MeasureTheory
open scoped ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open ContinuumRow CurrentMean SmoothPeriodicFamily RawCutoffBounds RawInputPartition CarrierSobolev

variable {n : ℕ} {ν : Type*} [Fintype ν]

/-- Literal carrier-only diagonal square. Both original auxiliary inputs are
left unchanged, including the global exterior input. -/
def carrierOnlySquaredCutoff (m : ν → Lp ℝ ∞ (carrierMeasure n)) :
    AugmentedInput n ν →L[ℝ] AugmentedInput n ν where
  toFun u := WithLp.toLp 2 (WithLp.toLp 2 (u.fst.fst,
    WithLp.toLp 2 (fun i ↦ carrierSquaredCutoff (m i) (u.fst.snd i))), u.snd)
  map_add' u v := by
    simp only [WithLp.add_fst, WithLp.add_snd, PiLp.add_apply, map_add,
      ← WithLp.toLp_add, Pi.add_def, Prod.mk_add_mk]
  map_smul' c u := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, PiLp.smul_apply, map_smul,
      ← WithLp.toLp_smul, Pi.smul_def, Prod.smul_mk, RingHom.id_apply]
  cont := by fun_prop

/-- Exact component action, so no output or auxiliary cutoff is hidden. -/
theorem carrierOnlySquaredCutoff_apply (m : ν → Lp ℝ ∞ (carrierMeasure n)) (u : AugmentedInput n ν) :
    carrierOnlySquaredCutoff m u = WithLp.toLp 2 (WithLp.toLp 2 (u.fst.fst,
      WithLp.toLp 2 (fun i ↦ carrierSquaredCutoff (m i) (u.fst.snd i))), u.snd) := rfl

/-- Discarding the two auxiliary tail components only decreases the original
Hilbert norm. This compares errors, not the different normal operators. -/
theorem norm_carrierOnlySquaredCutoff_error_le_full (K : ℝ)
    (m : ν → Lp ℝ ∞ (carrierMeasure n)) (u : AugmentedInput n ν) :
    ‖u-carrierOnlySquaredCutoff m u‖ ≤ ‖u-rawSquaredCutoff K m u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd,
    carrierOnlySquaredCutoff_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, add_zero, rawSquaredCutoff]
  nlinarith [sq_nonneg ‖u.fst.fst-auxiliarySquaredCutoff K u.fst.fst‖,
    sq_nonneg ‖u.snd-auxiliarySquaredCutoff K u.snd‖]

/-- The literal rounded original carrier input has the desired source-only
tail. The paired current raw-inverse producer supplies this genuine membership. -/
theorem carrierOnlySquaredCutoff_rounded_tail {K : ℝ} (hK : 1 ≤ K)
    (q : ℕ) (u : AugmentedInput n ν)
    (hu : u ∈ (augmentedInputSobolevScale n ν).level q) :
    ‖u-carrierOnlySquaredCutoff (fun _ ↦ roundedCarrierMask n K) u‖ ≤
      (K^q)⁻¹*(augmentedInputSobolevScale n ν).gradeNorm q u := by
  apply (norm_carrierOnlySquaredCutoff_error_le_full K _ u).trans
  simpa only [Real.rpow_neg (zero_le_one.trans hK), Real.rpow_natCast] using
    CanonicalTailRealization.rawSquaredCutoff_rounded_tail_of_augmentedInputLevel hK hu

/-- The continuous LEADING normal with only its carrier input cut at the SAME
fixed K. Its inverse is never selected here; the mean uses the uncut normal's
current inverse. -/
def leadingCarrierCutNormal (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) (K : ℝ) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  (augmentedRow image U ψ).comp
    ((carrierOnlySquaredCutoff (fun _ ↦ roundedCarrierMask n K)).comp (augmentedRow image U ψ).adjoint)

/-- Both auxiliary channels remain exactly their uncut original normal; only
the leading carrier input receives the original rounded square mask. -/
theorem leadingCarrierCutNormal_apply (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)) (K : ℝ) (w : OutputL2 n) :
    leadingCarrierCutNormal image U ψ K w = preparationAuxiliaryOutput image ψ w +
      carrierRow U (WithLp.toLp 2 (fun i ↦ carrierSquaredCutoff (roundedCarrierMask n K)
        ((carrierChannel (U i)).adjoint w))) := by
  simp only [leadingCarrierCutNormal, ContinuousLinearMap.comp_apply, augmentedRow_adjoint_apply,
    physicalRow_adjoint_apply, carrierRow_adjoint_apply, carrierOnlySquaredCutoff_apply,
    augmentedRow_apply, physicalRow_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  simp only [preparationAuxiliaryOutput, add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- Actual normal tail evaluated on its actual datum. This is NOT an operator
norm estimate and retains the high raw source norm. -/
theorem leadingCarrierCutNormal_defect_le (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ))
    {K : ℝ} (hK : 1 ≤ K) (q : ℕ) (w : OutputL2 n)
    (hw : (augmentedRow image U ψ).adjoint w ∈ (augmentedInputSobolevScale n ν).level q) :
    ‖(augmentedNormal image U ψ-leadingCarrierCutNormal image U ψ K) w‖ ≤
      (‖augmentedRow image U ψ‖/(K^q)) *
        (augmentedInputSobolevScale n ν).gradeNorm q ((augmentedRow image U ψ).adjoint w) := by
  have he : (augmentedNormal image U ψ-leadingCarrierCutNormal image U ψ K) w =
      augmentedRow image U ψ ((augmentedRow image U ψ).adjoint w-
        carrierOnlySquaredCutoff (fun _ ↦ roundedCarrierMask n K) ((augmentedRow image U ψ).adjoint w)) := by
    simp only [augmentedNormal, leadingCarrierCutNormal, sub_apply,
      ContinuousLinearMap.comp_apply, map_sub]
  rw [he]
  exact ((augmentedRow image U ψ).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (carrierOnlySquaredCutoff_rounded_tail hK q _ hw) (norm_nonneg _)).trans_eq
      (by rw [div_eq_mul_inv]; ring))

/-- DIRECT low source error for the literal fixed smooth E. Coercivity gives
the inverse norm and exact inverse identity; the actual paired raw-inverse
profile gives the source-only tail; the original corrected-normal and sampling
bounds contribute only the low-order term. No desired E bound is assumed. -/
theorem fixedSourceLinear_low_error
    {ι m : Type*} [Fintype ι] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ i, IsSmoothPeriodic (c i : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ν → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ w, γ*‖w‖^2 ≤ ‖(augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint w‖^2)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse (smoothResidualToL2 n e)) ∈ augmentedInputLevel n ν s)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (hraw : ∀ i v, smoothResidualToL2 n (CanonicalChange.smoothRawCrossResponse base C hC G i v) = A i v)
    (q s₀ : ℕ) {K T Crow Craw δtransport δsample : ℝ} (hK : 1 ≤ K)
    (hCrow : ‖augmentedRow (imageChannel c χmeas χsrc) U ψ‖ ≤ Crow)
    (hδtransport : 0 ≤ δtransport) (hδsample : 0 ≤ δsample)
    (NcorrK : OutputL2 n →L[ℝ] OutputL2 n)
    (htransport : ‖leadingCarrierCutNormal (imageChannel c χmeas χsrc) U ψ K-NcorrK‖ ≤ δtransport)
    (hsampling : ‖NcorrK-uncutSampledNormal c χmeas χsrc ψ weight A‖ ≤ δsample)
    (u : SmoothResidual n)
    (hrawProfile : (augmentedInputSobolevScale n ν).gradeNorm q
      ((augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        ((augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse (smoothResidualToL2 n u))) ≤
      Craw*(residualSobolevSeminorm n q u+T^(q-s₀)*residualSobolevSeminorm n 0 u)) :
    residualSobolevSeminorm n 0
      (u-fixedSourceLinear c hc χmeas χsrc ψ hm hs hψ U
        (augmentedNormal (imageChannel c χmeas χsrc) U ψ).inverse hreg weight base C hC A G u) ≤
      ((δtransport+δsample)*γ⁻¹)*residualSobolevSeminorm n 0 u+
        (Crow*Craw/K^q)*(residualSobolevSeminorm n q u+T^(q-s₀)*residualSobolevSeminorm n 0 u) := by
  let row := augmentedRow (imageChannel c χmeas χsrc) U ψ
  let normal := augmentedNormal (imageChannel c χmeas χsrc) U ψ
  have hnormalGap : ∀ w, γ*‖w‖^2 ≤ inner ℝ (normal w) w := CoerciveInverse.normalOperator_gap row hgap
  have hN : normal.comp normal.inverse = ContinuousLinearMap.id ℝ (OutputL2 n) :=
    (CoerciveInverse.isInvertible_of_gap normal hγ hnormalGap).self_comp_inverse
  have hInv := CoerciveInverse.norm_inverse_apply_le normal hγ hnormalGap (smoothResidualToL2 n u)
  have hsplit := PhysicalNormalInverse.MeanFrontend.current_mean_defect_le_three_terms
    c χmeas χsrc ψ U weight A (leadingCarrierCutNormal (imageChannel c χmeas χsrc) U ψ K) NcorrK hN (smoothResidualToL2 n u)
  have htail := leadingCarrierCutNormal_defect_le (imageChannel c χmeas χsrc) U ψ hK q
    (normal.inverse (smoothResidualToL2 n u)) (hreg u q)
  have hCrow0 : 0 ≤ Crow := (norm_nonneg row).trans hCrow
  have hKq : 0 < K^q := pow_pos (zero_lt_one.trans_le hK) _
  have htail' : ‖(normal-leadingCarrierCutNormal (imageChannel c χmeas χsrc) U ψ K)
      (normal.inverse (smoothResidualToL2 n u))‖ ≤
      (Crow*Craw/K^q)*(residualSobolevSeminorm n q u+T^(q-s₀)*residualSobolevSeminorm n 0 u) := by
    apply htail.trans
    calc
      _ ≤ (Crow/K^q)*(Craw*(residualSobolevSeminorm n q u+T^(q-s₀)*residualSobolevSeminorm n 0 u)) :=
        mul_le_mul (div_le_div_of_nonneg_right hCrow hKq.le) hrawProfile
          (GradedScale.gradeNorm_nonneg _ _ _) (div_nonneg hCrow0 hKq.le)
      _ = _ := by ring
  have hlow : (‖leadingCarrierCutNormal (imageChannel c χmeas χsrc) U ψ K-NcorrK‖+
      ‖NcorrK-uncutSampledNormal c χmeas χsrc ψ weight A‖)*‖normal.inverse (smoothResidualToL2 n u)‖ ≤
      ((δtransport+δsample)*γ⁻¹)*residualSobolevSeminorm n 0 u := by
    rw [residualSobolevSeminorm_zero]
    exact (mul_le_mul (add_le_add htransport hsampling) hInv (norm_nonneg _)
      (add_nonneg hδtransport hδsample)).trans_eq (by ring)
  rw [residualSobolevSeminorm_zero, map_sub,
    fixedSourceLinear_toL2 c hc χmeas χsrc ψ hm hs hψ U normal.inverse hreg weight base C hC A G hweight hraw]
  exact (hsplit.trans (add_le_add htail' hlow)).trans_eq (add_comm _ _)

end JanetCartan.PhysicalMean
