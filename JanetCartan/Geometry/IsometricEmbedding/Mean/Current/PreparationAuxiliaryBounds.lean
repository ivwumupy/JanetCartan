module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.DensityDiscrepancy.Sobolev
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Normal
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.WeightedEstimates

/-!
# Bounds for the same uncut auxiliary preparation update

For `app:ch_mean_pairs:eq:mean-density-recursion`, the source multiplier
followed by the original Bessel inverse gains one derivative. The complete
output has the same Sobolev order as its raw image and exterior inputs.
These facts concern the representatives already used by preparation, with
no Fourier cutoff and no change of inverse or exterior channel.

The bounds below are derived from primitive coefficient jets and the
constructed Sobolev actions of the literal image factors. They supply the
auxiliary estimates at the finite backward reserves. They do not assert
the sharp all-order prepared profile from these coarse finite-jet constants.
The corrected-positive inverse and its raw-adjoint bounds still require
instantiation; no bound for that composition is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CurrentMean
open ContinuumRow PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ}

private theorem norm_inclusion_le {r s : ℕ} (hrs : r ≤ s)
    (u : PeriodicSobolevSpace n (Euclidean n) s) : ‖inclusion hrs u‖ ≤ ‖u‖ :=
  periodicSobolevSeminorm_mono hrs (toLevel s u)

private theorem norm_ofL2_eq (s : ℕ) (u : OutputL2 n)
    (hu : u ∈ periodicSobolevLevel n (Euclidean n) s) :
    ‖ofL2 s u hu‖ = periodicSobolevNorm s u := by
  rw [norm_eq, toL2_ofL2]

section Covector

variable (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (him : OutputL2 n) (himem : ∀ s, him ∈ periodicSobolevLevel n (Euclidean n) s)

include hs himem

/-- At every order, the SAME smooth uncut covector is the original Bessel
gain applied after source multiplication (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem ofSmooth_preparationCovector_succ (s : ℕ) :
    ofSmooth (s + 1) (preparationCovector χsrc him)
      (isSmoothPeriodic_preparationCovector χsrc hs him himem) =
        periodicBesselGain s (cutoffSobolev χsrc hs s (ofL2 s him (himem s))) := by
  apply toL2_injective (s + 1)
  rw [toL2_periodicBesselGain, toL2_cutoffSobolev, toL2_ofL2]
  apply Lp.ext
  exact (toL2_ofSmooth_ae _ _ _).trans (preparationCovector_ae χsrc hs him himem).symm

/-- The uncut source-to-covector estimate retains complementary derivative
orders on the source mask and raw datum. The Bessel gain cancels the derivative
in the full strain (`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem periodicSobolevNorm_preparationCovector_succ_le (s : ℕ) :
    periodicSobolevNorm (s + 1 : ℕ) (preparationCovector χsrc him) ≤
      AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ j ∈ Finset.range (s + 1), cNorm (fundamentalCell n) j (periodicLift χsrc) *
          periodicSobolevNorm (s - j : ℕ) him := by
  rw [← multiplier_norm_ofSmooth (s + 1) _
    (isSmoothPeriodic_preparationCovector χsrc hs him himem),
    ofSmooth_preparationCovector_succ χsrc hs him himem, norm_periodicBesselGain]
  have h := norm_cutoffSobolev_le_gradeNorm χsrc hs s (ofL2 s him (himem s))
  simp only [toL2_ofL2] at h
  convert h using 1
  apply congrArg (fun z : ℝ ↦ AuxiliaryRawBand.coefficientProductConstant n s * z)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [(periodicSobolevScale n (Euclidean n)).gradeNorm_eq (himem (s-j))]
  exact (periodicSobolevSeminorm_eq (s-j) ⟨him, himem (s-j)⟩).symm

/-- The actual differentiated covector has the same raw-order bound. This
is the derivative needed by the uncut auxiliary strain, not a band estimate
for a separately cut datum (`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem periodicSobolevNorm_coordinateDeriv_preparationCovector_le (s : ℕ) (i : Fin n) :
    periodicSobolevNorm s (periodicCoordinateDeriv i (preparationCovector χsrc him)) ≤
      AuxiliaryRawBand.coefficientProductConstant n s *
        ∑ j ∈ Finset.range (s + 1), cNorm (fundamentalCell n) j (periodicLift χsrc) *
          periodicSobolevNorm (s - j : ℕ) him := by
  have h := norm_ofSmooth_coordinateDeriv_le s i (preparationCovector χsrc him)
    (isSmoothPeriodic_preparationCovector χsrc hs him himem)
  simp only [multiplier_norm_ofSmooth] at h
  exact h.trans (periodicSobolevNorm_preparationCovector_succ_le χsrc hs him himem s)

end Covector

private theorem exists_imageForward_sobolev_bound (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ImageCoefficientSlot n → C(Torus n, ℝ))
        (hq : ∀ a, IsSmoothPeriodic (q a)),
      (∀ a, cNorm (fundamentalCell n) (s + 1) (periodicLift (q a)) ≤ M) →
      ∀ u : PeriodicSobolevSpace n (Euclidean n) s,
        ‖(imageForwardExpression n).onSobolev q hq s u‖ ≤ C * ‖u‖ := by
  have he : (imageForwardExpression n).jetOrderLe 1 := by
    simp [imageForwardExpression, ImageFactorExpression.jetOrderLe]
  obtain ⟨C, hC, hb⟩ := (imageForwardExpression n).exists_weighted_action_bound he s
    (show 0 ≤ (s + 1 : ℝ) * M by positivity)
  refine ⟨C, hC, ?_⟩
  intro q hq hqM u
  have hcoeff (a : ImageCoefficientSlot n) (js : List (Fin n)) (hjs : js.length ≤ 1)
      (j : ℕ) (hj : j ≤ s) :
      cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient (q a) (hq a) js)) ≤
        ((s + 1 : ℝ) * M) * (1 : ℝ) ^ ((j : ℝ) / s) := by
    rw [Real.one_rpow, mul_one]
    apply (cNorm_periodicCoordinateDerivList_le (q a) (hq a) js j).trans
    have hjq := (cNorm_mono_order (show j + js.length ≤ s + 1 by omega)
      (s := fundamentalCell n) (f := periodicLift (q a))).trans (hqM a)
    exact mul_le_mul (by exact_mod_cast Nat.add_le_add_right hj 1) hjq
      (cNorm_nonneg _ _ _) (by positivity)
  have hh := hb q hq 1 le_rfl hcoeff s le_rfl 0 ‖u‖ (norm_nonneg _) u
    (fun r hr ↦ by simpa using norm_inclusion_le hr u)
  simpa using hh

/-- Uniform finite-order bound for the complete uncut smooth output from
its raw image and exterior inputs. The constant precedes the coefficients
and data; only their indicated primitive jets are bounded. No Sobolev
operator estimate is an input (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem exists_uncutAuxiliaryRepresentative_sobolev_bound (s : ℕ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc ψ : C(Torus n, ℝ))
        (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
        (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
        (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ)),
      (∀ a, cNorm (fundamentalCell n) (s + 1)
        (periodicLift (imageFactorCoefficients c χmeas χsrc a)) ≤ M) →
      cNorm (fundamentalCell n) s (periodicLift ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ)) ≤ M →
      ∀ (him hout : OutputL2 n)
        (himem : ∀ j, him ∈ periodicSobolevLevel n (Euclidean n) j)
        (homem : ∀ j, hout ∈ periodicSobolevLevel n (Euclidean n) j),
      periodicSobolevNorm s (fun x ↦
        (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ him hout himem homem).val x ()) ≤
          C * (periodicSobolevNorm s him + periodicSobolevNorm s hout) := by
  obtain ⟨C, hC, hb⟩ := exists_imageForward_sobolev_bound (n := n) s hM
  let D := AuxiliaryRawBand.coefficientProductConstant n s * (s + 1) * M
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (AuxiliaryRawBand.coefficientProductConstant_nonneg n s)
      (by positivity)) hM
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro c hc χmeas χsrc ψ hm hs hψ hcoeff hext him hout himem homem
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
  have hi := hb q hq hcoeff u
  have ho : ‖cutoffSobolev (1 - ψ) hψ' s v‖ ≤ D * ‖v‖ := by
    apply (norm_cutoffSobolev_le (1 - ψ) hψ' s v).trans
    calc
      _ ≤ AuxiliaryRawBand.coefficientProductConstant n s *
          ∑ _j ∈ Finset.range (s + 1), M * ‖v‖ := by
        apply mul_le_mul_of_nonneg_left _ (AuxiliaryRawBand.coefficientProductConstant_nonneg n s)
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul ((cNorm_mono_order (by simpa using hj)).trans hext)
          (norm_inclusion_le (Nat.sub_le s j) v) (norm_nonneg _) hM
      _ = D * ‖v‖ := by simp [D, mul_assoc]
  have hbound := (norm_add_le _ _).trans (add_le_add hi ho)
  change ‖w‖ ≤ _ at hbound
  simp only [u, v, norm_ofL2_eq] at hbound
  exact hbound.trans (by
    nlinarith [mul_nonneg hC (show 0 ≤ periodicSobolevNorm s hout from Real.sqrt_nonneg _),
      mul_nonneg hD (show 0 ≤ periodicSobolevNorm s him from Real.sqrt_nonneg _)])

section OriginalRow

variable {ι : Type*} [Fintype ι]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))

/-- The auxiliary estimate for the SAME original augmented adjoint of `Q₀`,
in preparation's genuine Sobolev seminorm. The raw norm includes both periodic
channels and every carrier derivative; the bound does not discard the exterior
channel or assert regularity for arbitrary L² sources
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem exists_preparationAuxiliaryCorrection_seminorm_bound
    (s : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ a, cNorm (fundamentalCell n) (s + 1)
      (periodicLift (imageFactorCoefficients c χmeas χsrc a)) ≤ M)
    (hext : cNorm (fundamentalCell n) s
      (periodicLift ((1 - ψ : C(Torus n, ℝ)) : Torus n → ℝ)) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
        (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
        (hreg : ∀ (e : SmoothResidual n) (j : ℕ),
          (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
            (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ι j)
        (e : SmoothResidual n),
      SmoothPeriodicFamily.sobolevSeminorm (fun _ : Unit ↦ (1 : ℝ))
        (fun _ ↦ zero_le_one) s
        (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e) ≤
      C * (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s
        ((augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
          (Q₀ (smoothResidualToL2 n e))) := by
  obtain ⟨C, hC, hb⟩ := exists_uncutAuxiliaryRepresentative_sobolev_bound (n := n) s hM
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro U Q₀ hreg e
  let u := (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
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
  have hout := hb c hc χmeas χsrc ψ hm hs hψ hcoeff hext _ _ hi ho
  change periodicSobolevNorm s (fun x ↦
    (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e).val x ()) ≤ _
      at hout
  apply hout.trans
  rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ,
    ← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
  let b := (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm s u
  have hb₀ : 0 ≤ b := (CarrierSobolev.augmentedInputSobolevScale n ι).gradeNorm_nonneg s u
  have hsq := CarrierSobolev.augmentedInputSobolevScale_gradeNorm_sq (hreg e s)
  have hsum : 0 ≤ ∑ a, CarrierSobolev.rawSobolevNorm s (u.fst.snd a) ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  change b ^ 2 = _ at hsq
  have h₁ : periodicSobolevNorm s u.fst.fst ≤ b := by
    nlinarith [sq_nonneg (periodicSobolevNorm s u.snd)]
  have h₂ : periodicSobolevNorm s u.snd ≤ b := by
    nlinarith [sq_nonneg (periodicSobolevNorm s u.fst.fst)]
  calc
    _ ≤ C * (b + b) := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hC
    _ = _ := by ring

end OriginalRow

end JanetCartan.CurrentMean
