module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Multiplication
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Physical
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.GradedAtoms

/-!
# Polynomial demodulation cost for the actual inverse remainder

The observation in `app:ch_response:eq:response-graded-reduced` includes the
literal multiplication by the negative primary carrier. This file derives its
Sobolev cost from the smooth compact phase and its primitive derivative profile.
It is used after the normalized solver and before the finite Neumann remainder
estimate. Compact support is required of the phase, not of the Sobolev datum;
the multiplier is written as the identity plus its compactly supported defect.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FixedDomainInverse

open Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open IsometricEmbedding.Reconstruction

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

private theorem negativeCarrier_jet_bound
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {ρ : ℝ} (hρ : 1 ≤ ρ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : ℕ)
    (hphase : ∀ j, 1 ≤ j → j ≤ s → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ P j * ρ ^ j) :
    ∀ j, j ≤ s → ∀ x,
      ‖iteratedFDeriv ℝ j (carrier (-ρ) φ) x‖ ≤
        (RawPrimary.phaseJetConstant P j * 2 ^ j) * ρ ^ (2 * j) := by
  intro j hj x
  have hρ₀ : 0 ≤ ρ := zero_le_one.trans hρ
  have hscaled : ContDiff ℝ ∞ ((-ρ) • φ) := hφ.const_smul (-ρ)
  have hb (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ‖iteratedFDeriv ℝ k ((-ρ) • φ) x‖ ≤ P k * ρ ^ 2 * ρ ^ (k - 1) := by
    rw [iteratedFDeriv_const_smul_apply (hφ.contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hρ₀]
    calc
      _ ≤ ρ * (P k * ρ ^ k) := mul_le_mul_of_nonneg_left (hphase k hk (hkj.trans hj) x) hρ₀
      _ = P k * ρ ^ 2 * ρ ^ (k - 1) := by
        have he : ρ ^ k = ρ * ρ ^ (k - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hk]
        rw [he]
        ring
  have h := RawPrimary.norm_iteratedFDeriv_oscillation_le
    (hscaled.contDiffAt.of_le (by simp) : ContDiffAt ℝ j ((-ρ) • φ) x)
    (sq_nonneg ρ) hρ₀ (fun k _ _ ↦ hP k) hb
  have hbase : ρ ^ 2 + ρ ≤ 2 * ρ ^ 2 := by
    have hsq : ρ ≤ ρ ^ 2 := by
      simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hρ hρ₀
    linarith
  have hpc : 0 ≤ RawPrimary.phaseJetConstant P j :=
    RawPrimary.phaseJetConstant_nonneg (fun k _ _ ↦ hP k)
  change ‖iteratedFDeriv ℝ j (carrier (-ρ) φ) x‖ ≤ _ at h
  refine h.trans ?_
  calc
    _ ≤ RawPrimary.phaseJetConstant P j * (2 * ρ ^ 2) ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase j) hpc
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

private theorem negativeCarrier_sub_one_jet_bound
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {ρ : ℝ} (hρ : 1 ≤ ρ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s : ℕ)
    (hphase : ∀ j, 1 ≤ j → j ≤ s → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ P j * ρ ^ j) :
    ∀ j, j ≤ s → ∀ x,
      ‖iteratedFDeriv ℝ j (carrier (-ρ) φ - 1) x‖ ≤
        (2 + RawPrimary.phaseJetConstant P j * 2 ^ j) * ρ ^ (2 * s) := by
  intro j hj x
  have hpj : 0 ≤ RawPrimary.phaseJetConstant P j * 2 ^ j :=
    mul_nonneg (RawPrimary.phaseJetConstant_nonneg (fun k _ _ ↦ hP k)) (by positivity)
  have hpow : 1 ≤ ρ ^ (2 * s) := one_le_pow₀ hρ
  by_cases hj0 : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    have hmod : ‖carrier (-ρ) φ x‖ = 1 := by simp [carrier, Complex.norm_exp]
    have hn : ‖(carrier (-ρ) φ - 1) x‖ ≤ 2 := by
      simpa only [Pi.sub_apply, Pi.one_apply, hmod, norm_one, one_add_one_eq_two]
        using norm_sub_le (carrier (-ρ) φ x) (1 : ℂ)
    exact hn.trans (by nlinarith)
  · have hc : ContDiff ℝ ∞ (carrier (-ρ) φ) := by
      unfold carrier
      exact (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ))).cexp
    change ‖iteratedFDeriv ℝ j (carrier (-ρ) φ - fun _ : E ↦ (1 : ℂ)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hc.contDiffAt.of_le (by simp))
      (contDiffAt_const : ContDiffAt ℝ j (fun _ : E ↦ (1 : ℂ)) x),
      iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, sub_zero]
    have h := negativeCarrier_jet_bound P hP hρ hφ s hphase j hj x
    exact h.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hρ (Nat.mul_le_mul_left 2 hj)) hpj).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
        (pow_nonneg (zero_le_one.trans hρ) _)))

/-- The actual negative carrier has a polynomial cost on the original vector
Fourier Sobolev space. The constant precedes the phase, frequency, and datum.
The phase profile comes from the retained compact primary-phase extension in
the normalized initializer. This supplies the demodulation factor of the
observation in `app:ch_regular:eq:inverse-remainder` and
`app:ch_response:eq:response-graded-reduced`; it does not supply finite-word
envelope estimates. -/
theorem exists_compactPhase_demodulation_fourier_cost
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (s : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ : ℝ), 1 ≤ ρ →
      ∀ (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ), HasCompactSupport φ →
        (∀ j, 1 ≤ j → j ≤ s → ∀ x,
          ‖iteratedFDeriv ℝ j φ x‖ ≤ P j * ρ ^ j) →
      ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (carrierMultiplication (-ρ) φ hφ.continuous u) ∧
        vectorFourierSobolevNorm (s : ℝ) (carrierMultiplication (-ρ) φ hφ.continuous u) ≤
          D * ρ ^ (2 * s) * vectorFourierSobolevNorm (s : ℝ) u := by
  let C := fun j ↦ 2 + RawPrimary.phaseJetConstant P j * 2 ^ j
  have hC : ∀ j, 0 ≤ C j := fun j ↦ add_nonneg (by norm_num)
    (mul_nonneg (RawPrimary.phaseJetConstant_nonneg (fun k _ _ ↦ hP k)) (by positivity))
  let D := localizedMultiplierConstant n s * ∑ j ∈ Finset.range (s + 1), C (s - j)
  have hD : 0 ≤ D := mul_nonneg (localizedMultiplierConstant_pos n s).le
    (Finset.sum_nonneg fun _ _ ↦ hC _)
  refine ⟨D + 1, by positivity, ?_⟩
  intro ρ hρ φ hφ hcφ hphase u hu
  let c := carrier (-ρ) φ - 1
  have hc : ContDiff ℝ ∞ c := by
    dsimp only [c]
    apply ContDiff.sub _ contDiff_const
    unfold carrier
    exact (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ))).cexp
  have hcs : HasCompactSupport c := by
    exact hcφ.comp_left (g := fun t : ℝ ↦ Complex.exp (Complex.I * ((-ρ * t : ℝ) : ℂ)) - 1)
      (by simp)
  let v := carrierMultiplication (-ρ) φ hφ.continuous u
  have he (i : Fin r) : finiteL2CoordinateIsometry volume v i =
      localizedScalarProduct c hc hcs (finiteL2CoordinateIsometry volume u i) +
        finiteL2CoordinateIsometry volume u i := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume v i,
      finiteL2Coordinates_apply_ae volume u i,
      carrierMultiplication_ae (-ρ) φ hφ.continuous u,
      localizedScalarProduct_ae c hc hcs (finiteL2CoordinateIsometry volume u i),
      Lp.coeFn_add (localizedScalarProduct c hc hcs (finiteL2CoordinateIsometry volume u i))
        (finiteL2CoordinateIsometry volume u i)] with x hvx hux hcx hpx hax
    change (finiteL2CoordinateIsometry volume v i : E → ℂ) x = v x i at hvx
    change (finiteL2CoordinateIsometry volume u i : E → ℂ) x = u x i at hux
    rw [hvx, hcx, PiLp.smul_apply, smul_eq_mul, hax, Pi.add_apply, hpx, hux]
    dsimp only [c, Pi.sub_apply, Pi.one_apply]
    ring
  have hprod (i : Fin r) := localizedScalarProduct_frechet_bound s c hc hcs
    (fun j ↦ C j * ρ ^ (2 * s))
    (fun j ↦ mul_nonneg (hC j) (pow_nonneg (zero_le_one.trans hρ) _))
    (negativeCarrier_sub_one_jet_bound P hP hρ hφ s hphase)
    (finiteL2CoordinateIsometry volume u i) (hu i)
  have hmem : MemVectorFourierSobolev (s : ℝ) v := by
    intro i
    rw [he i]
    exact (hprod i).1.add (hu i)
  refine ⟨hmem, vectorFourierSobolevNorm_le_of_coordinate_bounds
    (mul_nonneg (by positivity : 0 ≤ D + 1) (pow_nonneg (zero_le_one.trans hρ) _)) v u ?_⟩
  intro i
  rw [he i]
  apply (fourierSobolevNorm_add_le (hprod i).1 (hu i)).trans
  have hbound : fourierSobolevNorm (s : ℝ)
      (localizedScalarProduct c hc hcs (finiteL2CoordinateIsometry volume u i)) ≤
      D * ρ ^ (2 * s) * fourierSobolevNorm (s : ℝ) (finiteL2CoordinateIsometry volume u i) := by
    apply (hprod i).2.trans
    unfold mixedAmplitudeSobolevSum
    calc
      _ ≤ localizedMultiplierConstant n s *
          (∑ j ∈ Finset.range (s + 1),
            (C (s-j) * ρ ^ (2*s)) *
              fourierSobolevNorm (s : ℝ) (finiteL2CoordinateIsometry volume u i)) := by
        apply mul_le_mul_of_nonneg_left _ (localizedMultiplierConstant_pos n s).le
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (hC _) (pow_nonneg (zero_le_one.trans hρ) _))
        exact fourierSobolevNorm_mono (hu i)
          (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = _ := by simp only [← Finset.sum_mul, D]; ring
  have hpow : 1 ≤ ρ ^ (2*s) := one_le_pow₀ hρ
  have hnorm := fourierSobolevNorm_nonneg (s : ℝ) (finiteL2CoordinateIsometry volume u i)
  nlinarith only [hbound, mul_nonneg hnorm (sub_nonneg.mpr hpow)]

end JanetCartan.FixedDomainInverse
