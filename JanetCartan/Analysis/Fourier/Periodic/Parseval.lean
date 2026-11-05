module

public import JanetCartan.Analysis.Fourier.Periodic

/-!
# Parseval for real vector-valued periodic fields

Appendix A, `app:not:fourier`, of `paper.tex` uses normalized Fourier coefficients.
For the unit torus its volume is one. We identify the volume measure in the periodic
conventions with Mathlib's normalized Haar measure, apply the `UnitAddTorus` Fourier
basis theorem to real scalar coordinates, and sum over a finite orthonormal basis.

The principal result is a `HasSum` statement for every square-integrable field with
values in a finite-dimensional real inner product space. In particular, the squared
coefficient norms are summable; the Parseval identities do not rely on a totalized
sum of a divergent series. Continuity, and hence `IsSmoothPeriodic`, suffices.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan

variable {n : ℕ}

/-- Appendix A, `app:not:fourier`: unit-period volume agrees with the normalized
product Haar measure used by the `UnitAddTorus` Fourier basis. -/
theorem torus_volume_eq_pi_haarAddCircle :
    (volume : Measure (Torus n)) =
      Measure.pi (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  change Measure.pi _ = _
  congr 1
  funext i
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

/-- Appendix A, `app:not:fourier`: scalar coefficients use the project's volume measure. -/
private theorem mFourierCoeff_eq_integral_volume (f : Torus n → ℂ) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff f k = ∫ x, UnitAddTorus.mFourier (-k) x * f x := by
  rw [torus_volume_eq_pi_haarAddCircle]
  rfl

/-- Appendix A, `app:not:fourier`: scalar Parseval transported to volume measure. -/
private theorem hasSum_sq_mFourierCoeff_of_memLp {f : Torus n → ℂ} (hf : MemLp f 2) :
    HasSum (fun k ↦ ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
  let μ := Measure.pi (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
  have hμ : MemLp f 2 μ := by
    simpa only [torus_volume_eq_pi_haarAddCircle] using hf
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (hμ.toLp f)
  rw [torus_volume_eq_pi_haarAddCircle]
  convert h using 1
  · funext k
    congr 2
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hμ.coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ ↦ UnitAddTorus.mFourier (-k) x • z) hx.symm
  · apply integral_congr_ae
    filter_upwards [hμ.coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx.symm

/-- Appendix A, `app:not:fourier`: the complex scalar norm splits into the two real
coefficient components. -/
private theorem norm_sq_mFourierCoeff_ofReal {f : Torus n → ℝ} (hf : MemLp f 2)
    (k : Fin n → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ ^ 2 =
      ‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2 := by
  have hi : Integrable (fun x ↦ UnitAddTorus.mFourier (-k) x * (f x : ℂ)) :=
    (hf.ofReal (K := ℂ)).integrable (by norm_num) |>.bdd_mul
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x))
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [mFourierCoeff_eq_integral_volume]
  change (RCLike.re : ℂ → ℝ) _ * (RCLike.re : ℂ → ℝ) _ +
    (RCLike.im : ℂ → ℝ) _ * (RCLike.im : ℂ → ℝ) _ = _
  rw [← integral_re hi, ← integral_im hi]
  simp [periodicFourierCoeff, sq]

/-- Appendix A, `app:not:fourier`: Parseval for a real scalar field. -/
private theorem hasSum_sq_periodicFourierCoeff_real {f : Torus n → ℝ} (hf : MemLp f 2) :
    HasSum (fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff_of_memLp (hf.ofReal (K := ℂ))
  simpa using h.congr_fun (fun k ↦ (norm_sq_mFourierCoeff_ofReal hf k).symm)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Appendix A, `app:not:fourier`: taking a real scalar coordinate commutes with
both components of a Fourier coefficient. -/
theorem periodicFourierCoeff_inner {f : Torus n → F} (hf : MemLp f 2) (v : F)
    (k : Fin n → ℤ) :
    periodicFourierCoeff (fun x ↦ ⟪v, f x⟫) k =
      (⟪v, (periodicFourierCoeff f k).1⟫, ⟪v, (periodicFourierCoeff f k).2⟫) := by
  have hr := (hf.integrable (by norm_num)).smul_of_top_right
    ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous
      ).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) volume)
  have hi := (hf.integrable (by norm_num)).smul_of_top_right
    ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous
      ).memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) volume)
  apply Prod.ext
  · simpa [periodicFourierCoeff, inner_smul_right] using
      (innerSL ℝ v).integral_comp_comm hr
  · simpa [periodicFourierCoeff, inner_smul_right] using
      (innerSL ℝ v).integral_comp_comm hi

/-- Appendix A, `app:not:fourier`: the squared norms of both real Fourier components
sum to the integral of the squared field norm, for every square-integrable field. -/
theorem hasSum_sq_periodicFourierCoeff_integral {f : Torus n → F} (hf : MemLp f 2) :
    HasSum (fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
  let b := stdOrthonormalBasis ℝ F
  have hc (i : Fin (Module.finrank ℝ F)) : MemLp (fun x ↦ ⟪b i, f x⟫) 2 :=
    hf.continuousLinearMap_comp (innerSL ℝ (b i))
  have h := hasSum_sum (s := Finset.univ) (fun i _ ↦ hasSum_sq_periodicFourierCoeff_real (hc i))
  simp_rw [periodicFourierCoeff_inner hf, Real.norm_eq_abs, sq_abs] at h
  simp_rw [Finset.sum_add_distrib, b.sum_sq_inner_right] at h
  convert h using 1
  rw [← integral_finsetSum _ (fun i _ ↦ by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hc i).integrable_norm_pow (by decide : 2 ≠ 0))]
  simp_rw [b.sum_sq_inner_right]

/-- Appendix A, `app:not:fourier`: Parseval as a convergent series, with the normalized
periodic L² norm on the right. -/
theorem hasSum_sq_periodicFourierCoeff {f : Torus n → F} (hf : MemLp f 2) :
    HasSum (fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) (periodicL2Norm f ^ 2) := by
  rw [periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))]
  exact hasSum_sq_periodicFourierCoeff_integral hf

/-- Appendix A, `app:not:fourier`: the series of squared Fourier coefficient norms
is summable for square-integrable fields. -/
theorem summable_sq_periodicFourierCoeff {f : Torus n → F} (hf : MemLp f 2) :
    Summable (fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) :=
  (hasSum_sq_periodicFourierCoeff hf).summable

/-- Appendix A, `app:not:fourier`: Parseval's squared-norm identity for the unit torus.
The summability of this series is `summable_sq_periodicFourierCoeff`. -/
theorem periodicL2Norm_sq_eq_tsum {f : Torus n → F} (hf : MemLp f 2) :
    periodicL2Norm f ^ 2 = ∑' k, (‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) :=
  (hasSum_sq_periodicFourierCoeff hf).tsum_eq.symm

/-- Appendix A, `app:not:fourier`: the L² norm is the square root of the convergent
sum of squared Fourier coefficient norms. -/
theorem periodicL2Norm_eq_sqrt_tsum {f : Torus n → F} (hf : MemLp f 2) :
    periodicL2Norm f = Real.sqrt (∑' k, (‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2)) := by
  rw [(hasSum_sq_periodicFourierCoeff_integral hf).tsum_eq]
  rfl

/-- Appendix A, `app:not:fourier`: continuous periodic fields satisfy Parseval,
including convergence of the coefficient-energy series. -/
theorem hasSum_sq_periodicFourierCoeff_of_continuous {f : Torus n → F}
    (hf : Continuous f) :
    HasSum (fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) (periodicL2Norm f ^ 2) :=
  hasSum_sq_periodicFourierCoeff
    (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))

/-- Appendix A, `app:not:fourier`: smooth periodic fields satisfy the convergent
Parseval identity in the shared Fourier convention. -/
theorem IsSmoothPeriodic.hasSum_sq_periodicFourierCoeff {f : Torus n → F}
    (hf : IsSmoothPeriodic f) :
    HasSum (fun k ↦ ‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) (periodicL2Norm f ^ 2) :=
  hasSum_sq_periodicFourierCoeff_of_continuous hf.1

/-- Appendix A, `app:not:fourier`: the manuscript's Parseval formula for smooth
periodic fields, on the unit torus of volume one. -/
theorem IsSmoothPeriodic.periodicL2Norm_sq_eq_tsum {f : Torus n → F}
    (hf : IsSmoothPeriodic f) :
    periodicL2Norm f ^ 2 = ∑' k, (‖(periodicFourierCoeff f k).1‖ ^ 2 +
      ‖(periodicFourierCoeff f k).2‖ ^ 2) :=
  hf.hasSum_sq_periodicFourierCoeff.tsum_eq.symm

end JanetCartan
