module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliaryBounds

/-!
# One-high bounds for the uncut preparation output

The high-profile argument of `app:ch_mean_pairs:prop:mean-coarse` must not
multiply the highest coefficient norm by the highest raw-data norm. Apply
the allocated product bounds for the actual source/Bessel/image factors to
the SAME uncut representative. Interpolation leaves one high coefficient
factor multiplying only the raw L² norm, and retains the exterior output.

The consuming construction is `preparationAuxiliaryCorrection`. Its original
inverse/adjoint still has to supply raw regularity and its one-high estimate;
the geometric coefficient producer supplies the primitive jets below. No
bound on an auxiliary output or on a preparation iterate is assumed.
-/

@[expose] public noncomputable section

namespace JanetCartan.CurrentMean

open ContinuumRow PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ}

private theorem preparation_factor_tame_bound {ι : Type*}
    (e : ImageFactorExpression n ι) (he : e.jetOrderLe 1)
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ι → C(Torus n, ℝ))
      (hq : ∀ a, IsSmoothPeriodic (q a)) (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ M) →
      (∀ a j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ H) →
      ∀ u : PeriodicSobolevSpace n (Euclidean n) s,
      ‖e.onSobolev q hq s u‖ ≤ C * (‖u‖ + (1 + H) * ‖toL2 s u‖) := by
  obtain ⟨K, hK, hprofile⟩ := exists_coefficient_jet_profile n s hM
  obtain ⟨C, hC, hb⟩ := e.exists_weighted_action_bound he s
    (show 0 ≤ (s + 1) * K by positivity)
  refine ⟨C, hC, ?_⟩
  intro q hq H hH hlow hhigh u
  have hcoeff : ∀ a js, js.length ≤ 1 → ∀ j ≤ s,
      cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient (q a) (hq a) js)) ≤
        ((s + 1) * K) * (1 + H) ^ ((j : ℝ) / s) := by
    intro a js hjs j hj
    calc
      _ ≤ (j + 1) * cNorm (fundamentalCell n) (j + js.length) (periodicLift (q a)) :=
        cNorm_periodicCoordinateDerivList_le (q a) (hq a) js j
      _ ≤ (s + 1) * (K * (1 + H) ^ ((j : ℝ) / s)) := by
        apply mul_le_mul
        · exact_mod_cast Nat.add_le_add_right hj 1
        · apply (hprofile (q a) (hq a) H hH (hlow a) (hhigh a) _ (by omega)).trans
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
          exact_mod_cast (show j + js.length - 1 ≤ j by omega)
        · exact cNorm_nonneg _ _ _
        · positivity
      _ = _ := by ring
  let R := ‖u‖ + (1 + H) * ‖toL2 s u‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu : ∀ r (hr : r ≤ s), ‖inclusion hr u‖ ≤
      (1 + H) ^ ((r : ℝ) / s + (-1)) * R := by
    intro r hr
    have hi := periodic_gradeNorm_weighted_interpolate hr (by positivity : 0 ≤ 1 + H) u
    rw [← multiplier_norm_inclusion_eq_gradeNorm hr] at hi
    have hp : (1 + H) ^ ((r : ℝ) / s + (-1)) *
        (1 + H) ^ (1 - (r : ℝ) / s) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      have hz : (r : ℝ) / s + (-1) + (1 - (r : ℝ) / s) = 0 := by ring
      rw [hz, Real.rpow_zero]
    calc
      _ = (1 + H) ^ ((r : ℝ) / s + (-1)) *
          ((1 + H) ^ (1 - (r : ℝ) / s) * ‖inclusion hr u‖) := by
        rw [← mul_assoc, hp, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (by positivity) _)
  have hout := hb q hq (1 + H) (by linarith) hcoeff s le_rfl (-1) R hR u hu
  have hexp : (s : ℝ) / s + (-1) ≤ 0 := by
    by_cases hs : s = 0
    · simp [hs]
    · rw [div_self (by exact_mod_cast hs)]
      norm_num
  have hp : (1 + H) ^ ((s : ℝ) / s + (-1)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + H by linarith) hexp
  exact hout.trans (mul_le_mul_of_nonneg_left
    (by simpa using mul_le_mul_of_nonneg_right hp hR) hC)

/-- The original uncut source multiplier and Bessel inverse gain one
derivative with a one-high bound. This controls the covector and hence the
derivative in its full strain without multiplying two high norms
(`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem exists_preparationCovector_tame_bound (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χsrc : C(Torus n, ℝ))
      (_hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (H : ℝ), 0 ≤ H →
      (∀ j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift χsrc) x‖ ≤ M) →
      (∀ j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift χsrc) x‖ ≤ H) →
      ∀ (him : OutputL2 n) (_himem : ∀ j, him ∈ periodicSobolevLevel n (Euclidean n) j),
      periodicSobolevNorm (s + 1 : ℕ) (preparationCovector χsrc him) ≤
        C * (periodicSobolevNorm s him + (1 + H) * ‖him‖) := by
  obtain ⟨C, hC, hb⟩ := preparation_factor_tame_bound
    (ImageFactorExpression.coefficient (n := n) () [])
    (by simp [ImageFactorExpression.jetOrderLe]) s hM
  refine ⟨C, hC, ?_⟩
  intro χsrc hs H hH hlow hhigh him himem
  rw [← multiplier_norm_ofSmooth (s + 1) _
    (isSmoothPeriodic_preparationCovector χsrc hs him himem),
    ofSmooth_preparationCovector_succ χsrc hs him himem, norm_periodicBesselGain]
  have h := hb (fun _ : Unit ↦ χsrc) (fun _ ↦ hs) H hH
    (fun _ ↦ hlow) (fun _ ↦ hhigh) (ofL2 s him (himem s))
  change ‖cutoffSobolev χsrc hs s (ofL2 s him (himem s))‖ ≤ _ at h
  simpa only [norm_eq s (ofL2 s him (himem s)), toL2_ofL2] using h

/-- Primitive low and high jets bound the SAME complete uncut output by
one high raw norm plus one high coefficient times its raw L² norm. The
constant precedes the coefficients, high budget and datum. The exterior
summand remains global (`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem exists_uncutAuxiliaryRepresentative_tame_bound (s : ℕ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc ψ : C(Torus n, ℝ))
        (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
        (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
        (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)) (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ M) →
      (∀ a j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ H) →
      (∀ j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ M) →
      (∀ j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ H) →
      ∀ (him hout : OutputL2 n)
        (himem : ∀ j, him ∈ periodicSobolevLevel n (Euclidean n) j)
        (homem : ∀ j, hout ∈ periodicSobolevLevel n (Euclidean n) j),
      periodicSobolevNorm s (fun x ↦
        (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ him hout himem homem).val x ()) ≤
          C * (periodicSobolevNorm s him + periodicSobolevNorm s hout +
            (1 + H) * (‖him‖ + ‖hout‖)) := by
  have he : (imageForwardExpression n).jetOrderLe 1 := by
    simp [imageForwardExpression, ImageFactorExpression.jetOrderLe]
  obtain ⟨Ci, hCi, hi⟩ := preparation_factor_tame_bound (imageForwardExpression n) he s hM
  obtain ⟨Co, hCo, ho⟩ := preparation_factor_tame_bound
    (ImageFactorExpression.coefficient (n := n) () []) (by simp [ImageFactorExpression.jetOrderLe]) s hM
  refine ⟨Ci + Co, add_nonneg hCi hCo, ?_⟩
  intro c hc χmeas χsrc ψ hm hs hψ H hH hlow hhigh hextLow hextHigh him hout himem homem
  let q := imageFactorCoefficients c χmeas χsrc
  let hq := smooth_imageFactorCoefficients c hc χmeas χsrc hm hs
  let u := ofL2 s him (himem s)
  let v := ofL2 s hout (homem s)
  have hψ' : IsSmoothPeriodic ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ) :=
    ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩
  let w := (imageForwardExpression n).onSobolev q hq s u + cutoffSobolev (1 - ψ) hψ' s v
  have hid : toL2 s w = imageChannel c χmeas χsrc him + exteriorChannel ψ hout := by
    simp only [w, map_add, ImageFactorExpression.toL2_onSobolev, toL2_cutoffSobolev,
      u, v, toL2_ofL2]
    rw [onL2_imageForwardExpression c hc χmeas χsrc hm hs]
    rfl
  have heq : DensityDiscrepancy.densitySobolevRealization s
      (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ him hout himem homem) = w := by
    apply toL2_injective s
    rw [DensityDiscrepancy.densitySobolevRealization_toL2, hid]
    exact uncutAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ him hout himem homem
  rw [← DensityDiscrepancy.norm_densitySobolevRealization, heq]
  have hi' := hi q hq H hH hlow hhigh u
  have ho' := ho (fun _ : Unit ↦ 1 - ψ) (fun _ ↦ hψ') H hH
    (fun _ ↦ hextLow) (fun _ ↦ hextHigh) v
  change ‖cutoffSobolev (1 - ψ) hψ' s v‖ ≤ _ at ho'
  have hb := (norm_add_le _ _).trans (add_le_add hi' ho')
  change ‖w‖ ≤ _ at hb
  simp only [u, v, norm_eq, toL2_ofL2] at hb
  rw [norm_eq]
  apply hb.trans
  have hp (z : OutputL2 n) : 0 ≤ periodicSobolevNorm s z + (1 + H) * ‖z‖ := by
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
  nlinarith [mul_nonneg hCi (hp hout), mul_nonneg hCo (hp him)]

section OriginalRow

variable {ι : Type*} [Fintype ι]

/-- Apply the one-high estimate to the actual uncut auxiliary correction
of the SAME original augmented adjoint of `Q₀`. Both raw component norms
are bounded by the full original input norm, including all carrier variables.
Only raw regularity is required on smooth sources; this does not assert a
smooth inverse on arbitrary L² data
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem exists_preparationAuxiliaryCorrection_tame_bound (s : ℕ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc ψ : C(Torus n, ℝ))
        (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
        (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
        (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)) (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ M) →
      (∀ a j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ H) →
      (∀ j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ M) →
      (∀ j, j ≤ s + 1 → ∀ x, ‖iteratedFDeriv ℝ j
        (periodicLift ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ)) x‖ ≤ H) →
      ∀ (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
        (hreg : ∀ (e : SmoothResidual n) (j : ℕ),
          (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
            (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ι j)
        (e : SmoothResidual n),
      let raw := (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        (Q₀ (smoothResidualToL2 n e))
      SmoothPeriodicFamily.sobolevSeminorm (fun _ : Unit ↦ (1 : ℝ))
        (fun _ ↦ zero_le_one) s
        (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e) ≤
      C * ((CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s raw +
        (1 + H) * ‖raw‖) := by
  obtain ⟨C, hC, hb⟩ := exists_uncutAuxiliaryRepresentative_tame_bound (n := n) s hM
  refine ⟨2 * C, by positivity, ?_⟩
  intro c hc χmeas χsrc ψ hm hs hψ H hH hlow hhigh hextLow hextHigh U Q₀ hreg e
  let raw := (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
    (Q₀ (smoothResidualToL2 n e))
  have hi (j : ℕ) : (imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) j := by
    rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ]
    exact ((CarrierSobolev.mem_augmentedInputLevel_iff j _).mp (hreg e j)).1
  have ho (j : ℕ) : exteriorChannel ψ (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) j := by
    rw [← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
    exact ((CarrierSobolev.mem_augmentedInputLevel_iff j _).mp (hreg e j)).2.2
  rw [DensityDiscrepancy.densitySobolevSeminorm_eq_norm,
    DensityDiscrepancy.norm_densitySobolevRealization]
  have hout := hb c hc χmeas χsrc ψ hm hs hψ H hH hlow hhigh hextLow hextHigh _ _ hi ho
  change periodicSobolevNorm s (fun x ↦
    (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e).val x ()) ≤ _
      at hout
  apply hout.trans
  rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ,
    ← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
  let b := (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s raw
  have hb₀ : 0 ≤ b := (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm_nonneg s raw
  have hsq := CarrierSobolev.augmentedInputSobolevScale_gradeNorm_sq (hreg e s)
  have hsum : 0 ≤ ∑ a, CarrierSobolev.rawSobolevNorm s (raw.fst.snd a) ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  change b ^ 2 = _ at hsq
  have h₁ : periodicSobolevNorm s raw.fst.fst ≤ b := by
    nlinarith [sq_nonneg (periodicSobolevNorm s raw.snd)]
  have h₂ : periodicSobolevNorm s raw.snd ≤ b := by
    nlinarith [sq_nonneg (periodicSobolevNorm s raw.fst.fst)]
  have hi₀ : ‖raw.fst.fst‖ ≤ ‖raw‖ :=
    (WithLp.norm_fst_le _ _).trans (WithLp.norm_fst_le _ _)
  have ho₀ : ‖raw.snd‖ ≤ ‖raw‖ := WithLp.norm_snd_le _ _
  calc
    _ ≤ C * (b + b + (1 + H) * (‖raw‖ + ‖raw‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add (add_le_add h₁ h₂)
        (mul_le_mul_of_nonneg_left (add_le_add hi₀ ho₀) (by positivity))
    _ = _ := by ring

end OriginalRow

end JanetCartan.CurrentMean
