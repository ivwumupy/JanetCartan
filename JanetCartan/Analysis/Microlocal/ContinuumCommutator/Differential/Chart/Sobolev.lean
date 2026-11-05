module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.FiniteRows

/-!
# Local integer Sobolev comparison

The fixed compact source extension in `app:ch_background:eq:bg-commutator`
is bounded from periodic Hⁿ to Euclidean Hⁿ. The proof uses the product rule,
exact unit-cell measure comparison, and actual Fourier derivative norms.
-/

@[expose] public noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => EuclideanL2 d ℂ

private def multiplierExtension (a : E → ℂ) (ha : ContDiff ℝ ∞ a)
    (hs : HasCompactSupport a) {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) : L² :=
  ((ha.mul hu.2).continuous.memLp_of_hasCompactSupport hs.mul_right).toLp
    (fun x ↦ a x * periodicLift u x)

private theorem multiplierExtension_coe (a : E → ℂ) (ha : ContDiff ℝ ∞ a)
    (hs : HasCompactSupport a) {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) :
    multiplierExtension a ha hs hu =ᵐ[volume] fun x ↦ a x * periodicLift u x :=
  MemLp.coeFn_toLp _

private theorem multiplierExtension_mem (a : E → ℂ) (ha : ContDiff ℝ ∞ a)
    (hs : HasCompactSupport a) {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) (n : ℕ) :
    MemFourierSobolev (n : ℝ) (multiplierExtension a ha hs hu) :=
  memFourierSobolev_nat_toLp n _ (ha.mul hu.2) hs.mul_right

private theorem norm_ofSmooth_mono {u : Torus d → ℂ} (hu : IsSmoothPeriodic u)
    {n m : ℕ} (hnm : n ≤ m) :
    ‖PeriodicSobolevSpace.ofSmooth n u hu‖ ≤ ‖PeriodicSobolevSpace.ofSmooth m u hu‖ :=
  periodicSobolevSeminorm_mono hnm
    (PeriodicSobolevSpace.toLevel m (PeriodicSobolevSpace.ofSmooth m u hu))

private theorem multiplierExtension_norm_le (a : E → ℂ) (ha : ContDiff ℝ ∞ a)
    (hs : HasCompactSupport a) (hc : tsupport a ⊆ halfOpenCell d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Torus d → ℂ) (hu : IsSmoothPeriodic u),
      ‖multiplierExtension a ha hs hu‖ ≤ C * ‖PeriodicSobolevSpace.ofSmooth 0 u hu‖ := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous ha.continuous
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro u hu
  let f := PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 u hu)
  have hf := PeriodicSobolevSpace.toL2_ofSmooth_ae 0 u hu
  have hlift := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hf)
  have he : ‖multiplierExtension a ha hs hu‖ ≤ max 0 C * ‖toEuclidean (𝕜 := ℂ) f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [multiplierExtension_coe a ha hs hu, toEuclidean_coe (𝕜 := ℂ) f,
      hlift] with x hx hy hz
    rw [hx, hy]
    by_cases hxcell : x ∈ halfOpenCell d
    · rw [indicator_of_mem hxcell]
      change ‖a x * periodicLift u x‖ ≤ max 0 C * ‖periodicLift f x‖
      rw [show periodicLift f x = periodicLift u x from hz hxcell, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hC x).trans (le_max_right _ _)) (norm_nonneg _)
    · have hz : a x = 0 := by
        by_contra hn
        exact hxcell (hc (subset_tsupport a hn))
      simp [hz, hxcell]
  rw [(toEuclidean (𝕜 := ℂ)).norm_map] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (PeriodicSobolevSpace.norm_toL2_le 0 _) (le_max_left _ _))

private theorem multiplierExtension_derivative
    (a : E → ℂ) (ha : ContDiff ℝ ∞ a) (hs : HasCompactSupport a)
    {u : Torus d → ℂ} (hu : IsSmoothPeriodic u) (i : Fin d) :
    HasEuclideanL2CoordinateDerivative i (multiplierExtension a ha hs hu)
      (multiplierExtension (euclideanCoordinateDerivList [i] a)
          (contDiff_euclideanCoordinateDerivList ha [i])
          (hasCompactSupport_euclideanCoordinateDerivList hs [i]) hu +
        multiplierExtension a ha hs (hu.coordinateDeriv i)) := by
  have h := hasEuclideanL2CoordinateDerivative_toLp
    (fun x ↦ a x * periodicLift u x) (ha.mul hu.2) hs.mul_right i
  convert h using 1
  · rfl
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add
        (multiplierExtension (euclideanCoordinateDerivList [i] a)
          (contDiff_euclideanCoordinateDerivList ha [i])
          (hasCompactSupport_euclideanCoordinateDerivList hs [i]) hu)
        (multiplierExtension a ha hs (hu.coordinateDeriv i)),
      multiplierExtension_coe (euclideanCoordinateDerivList [i] a)
        (contDiff_euclideanCoordinateDerivList ha [i])
        (hasCompactSupport_euclideanCoordinateDerivList hs [i]) hu,
      multiplierExtension_coe a ha hs (hu.coordinateDeriv i),
      ((contDiff_euclideanCoordinateDerivList (ha.mul hu.2) [i]).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList hs.mul_right [i])).coeFn_toLp]
        with x hx h₁ h₂ h₃
    simp only [Pi.add_apply] at hx
    rw [hx, h₁, h₂, h₃]
    have hp := congrFun (periodicLift_coordinateDerivList_eq hu [i]) x
    change periodicLift (periodicCoordinateDeriv i u) x =
      fderiv ℝ (periodicLift u) x (EuclideanSpace.single i 1) at hp
    rw [hp]
    change _ = fderiv ℝ (a * periodicLift u) x (EuclideanSpace.single i 1)
    rw [fderiv_mul (ha.differentiable (by simp) x) (hu.2.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    simp only [euclideanCoordinateDerivList]
    ring

private theorem exists_multiplierExtension_sobolev_bound (n : ℕ)
    (a : E → ℂ) (ha : ContDiff ℝ ∞ a) (hs : HasCompactSupport a)
    (hc : tsupport a ⊆ halfOpenCell d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Torus d → ℂ) (hu : IsSmoothPeriodic u),
      fourierSobolevNorm (n : ℝ) (multiplierExtension a ha hs hu) ≤
        C * ‖PeriodicSobolevSpace.ofSmooth n u hu‖ := by
  induction n generalizing a with
  | zero =>
    simpa only [Nat.cast_zero, fourierSobolevNorm_zero] using
      multiplierExtension_norm_le a ha hs hc
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih a ha hs hc
    have hdc (i : Fin d) : tsupport (euclideanCoordinateDerivList [i] a) ⊆ halfOpenCell d :=
      (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hc
    choose B hB hdbound using fun i : Fin d ↦ ih (euclideanCoordinateDerivList [i] a)
      (contDiff_euclideanCoordinateDerivList ha [i])
      (hasCompactSupport_euclideanCoordinateDerivList hs [i]) (hdc i)
    refine ⟨C + ∑ i, (B i + C), add_nonneg hC (Finset.sum_nonneg fun i _ ↦
      add_nonneg (hB i) hC), ?_⟩
    intro u hu
    let v := fun i ↦ multiplierExtension (euclideanCoordinateDerivList [i] a)
      (contDiff_euclideanCoordinateDerivList ha [i])
      (hasCompactSupport_euclideanCoordinateDerivList hs [i]) hu +
        multiplierExtension a ha hs (hu.coordinateDeriv i)
    have hvm (i : Fin d) : MemFourierSobolev (n : ℝ) (v i) :=
      (multiplierExtension_mem _ _ _ hu n).add
        (multiplierExtension_mem a ha hs (hu.coordinateDeriv i) n)
    have hroot : fourierSobolevNorm (n : ℝ) (multiplierExtension a ha hs hu) ≤
        C * ‖PeriodicSobolevSpace.ofSmooth (n + 1) u hu‖ :=
      (hbound u hu).trans (mul_le_mul_of_nonneg_left
        (norm_ofSmooth_mono hu (Nat.le_succ n)) hC)
    have hvb (i : Fin d) : fourierSobolevNorm (n : ℝ) (v i) ≤
        (B i + C) * ‖PeriodicSobolevSpace.ofSmooth (n + 1) u hu‖ := by
      calc
        _ ≤ fourierSobolevNorm (n : ℝ) (multiplierExtension
              (euclideanCoordinateDerivList [i] a)
              (contDiff_euclideanCoordinateDerivList ha [i])
              (hasCompactSupport_euclideanCoordinateDerivList hs [i]) hu) +
            fourierSobolevNorm (n : ℝ) (multiplierExtension a ha hs (hu.coordinateDeriv i)) :=
          fourierSobolevNorm_add_le (multiplierExtension_mem _ _ _ hu n)
            (multiplierExtension_mem _ _ _ (hu.coordinateDeriv i) n)
        _ ≤ B i * ‖PeriodicSobolevSpace.ofSmooth n u hu‖ +
            C * ‖PeriodicSobolevSpace.ofSmooth n (periodicCoordinateDeriv i u)
              (hu.coordinateDeriv i)‖ :=
          add_le_add (hdbound i u hu) (hbound _ (hu.coordinateDeriv i))
        _ ≤ B i * ‖PeriodicSobolevSpace.ofSmooth (n + 1) u hu‖ +
            C * ‖PeriodicSobolevSpace.ofSmooth (n + 1) u hu‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (norm_ofSmooth_mono hu (Nat.le_succ n)) (hB i))
            (mul_le_mul_of_nonneg_left
              (PeriodicSobolevSpace.norm_ofSmooth_coordinateDeriv_le n i u hu) hC)
        _ = _ := (add_mul _ _ _).symm
    rw [Nat.cast_succ]
    calc
      _ ≤ fourierSobolevNorm (n : ℝ) (multiplierExtension a ha hs hu) +
          ∑ i, fourierSobolevNorm (n : ℝ) (v i) :=
        fourierSobolevNorm_le_coordinateDerivatives (by positivity)
          (multiplierExtension_mem a ha hs hu n) hvm
          (multiplierExtension_derivative a ha hs hu)
      _ ≤ C * ‖PeriodicSobolevSpace.ofSmooth (n + 1) u hu‖ +
          ∑ i, (B i + C) * ‖PeriodicSobolevSpace.ofSmooth (n + 1) u hu‖ :=
        add_le_add hroot (Finset.sum_le_sum fun i _ ↦ hvb i)
      _ = _ := by rw [add_mul, Finset.sum_mul]

/-- The fixed artificial source extension is bounded from periodic Hⁿ to
literal Euclidean Hⁿ. The constant is chosen from the cutoff and order alone,
before any amplitude or high budget (`app:ch_background:eq:bg-commutator`). -/
theorem SourceCutoff.exists_sobolev_extension_bound {r : ℝ} (χ : SourceCutoff d r) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Torus d → ℂ) (hu : IsSmoothPeriodic u),
      fourierSobolevNorm (n : ℝ) (χ.extendL2 hu) ≤ C * periodicSobolevNorm n u := by
  obtain ⟨C, hC, hb⟩ := exists_multiplierExtension_sobolev_bound n
    (fun x ↦ (χ.toFun x : ℂ)) (Complex.ofRealCLM.contDiff.comp χ.smooth)
    (χ.compact.comp_left Complex.ofReal_zero)
    (fun x hx ↦ subset_halfOpenCell_of_strict (fun y hy ↦ hy)
      (χ.support_cell ((tsupport_comp_subset Complex.ofReal_zero χ.toFun) hx)))
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  have he : ‖PeriodicSobolevSpace.ofSmooth n u hu‖ = periodicSobolevNorm n u := by
    rw [PeriodicSobolevSpace.norm_eq]
    simp only [periodicSobolevNorm,
      periodicFourierCoeff_congr_ae (PeriodicSobolevSpace.toL2_ofSmooth_ae n u hu)]
  have hext : multiplierExtension (fun x ↦ (χ.toFun x : ℂ))
      (Complex.ofRealCLM.contDiff.comp χ.smooth)
      (χ.compact.comp_left Complex.ofReal_zero) hu = χ.extendL2 hu := by
    apply Lp.ext
    exact (multiplierExtension_coe _ _ _ hu).trans (χ.extendL2_coe hu).symm
  simpa only [he, hext] using hb u hu

/-- The same fixed comparison constant works for finite Hilbert sums of
source extensions (`app:ch_background:eq:bg-commutator`). -/
theorem SourceCutoff.exists_matrix_sobolev_extension_bound {r : ℝ}
    (χ : SourceCutoff d r) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Type*) [Fintype J]
      (u : J → Torus d → ℂ) (hu : ∀ j, IsSmoothPeriodic (u j)),
      ‖WithLp.toLp 2 (fun j ↦ fourierSobolevNorm (n : ℝ) (χ.extendL2 (hu j)))‖ ≤
        C * ‖WithLp.toLp 2 (fun j ↦ periodicSobolevNorm n (u j))‖ := by
  obtain ⟨C, hC, hb⟩ := χ.exists_sobolev_extension_bound n
  refine ⟨C, hC, fun J _ u hu ↦ ?_⟩
  let N : PiLp 2 (fun _ : J ↦ ℝ) := WithLp.toLp 2 (fun j ↦ periodicSobolevNorm n (u j))
  calc
    _ ≤ ‖C • N‖ := by
      rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      have hn : 0 ≤ periodicSobolevNorm n (u j) := Real.sqrt_nonneg _
      simpa only [PiLp.toLp_apply, PiLp.smul_apply, N, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (fourierSobolevNorm_nonneg _ _),
        abs_of_nonneg (mul_nonneg hC hn)] using hb (u j) (hu j)
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg hC]

end JanetCartan.Pseudodifferential.DifferentialChart
