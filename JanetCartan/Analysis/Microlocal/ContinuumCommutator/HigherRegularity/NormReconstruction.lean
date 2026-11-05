module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.WeakDerivatives

/-!
# Reconstructing the Fourier Sobolev norm from top weak derivatives

For `app:ch_background:prop:bg-inverse` and `app:ch_background:eq:bg-r-inverse`,
the top derivative bounds must control the existing periodic Sobolev norm.
The exact Fourier energy identity at successive levels first bounds the norm
when all ordered derivatives through that level have a common L² bound.
Lower derivatives are then bounded by the preceding Sobolev norm, leaving only
the supplied top derivative bound. The resulting constant depends only on the
dimension and order. Empty coordinate sums cover dimension zero.

The consumer is the quantitative `hstep` in higher inverse regularity, after
`exists_top_weakDerivative_norm_le` has supplied the top derivative bounds.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.HigherRegularity

open PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Identify the scale norm with its actual Fourier expression for the
reconstruction in `app:ch_background:eq:bg-r-inverse`. -/
private theorem gradeNorm_eq_fourier (s : ℕ) (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F s) :
    (periodicSobolevScale n F).gradeNorm s u = periodicSobolevNorm s u := by
  rw [(periodicSobolevScale n F).gradeNorm_eq hu]
  exact periodicSobolevSeminorm_eq s ⟨u, hu⟩

omit [FiniteDimensional ℝ F] in
/-- The squared Fourier norm is its nonnegative energy series
(`app:not:fourier`; `app:ch_background:eq:bg-r-inverse`). -/
private theorem fourierNorm_sq (s : ℕ) (u : PeriodicL2 n F) :
    periodicSobolevNorm s u ^ 2 =
      ∑' k : Fin n → ℤ, (1 + frequencyNorm k ^ 2) ^ (s : ℝ) *
        (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2) := by
  rw [periodicSobolevNorm, Real.sq_sqrt]
  exact tsum_nonneg (fun k ↦ by positivity)

/-- The physical coordinate symbols give the exact energy decomposition used
in the norm reconstruction (`app:ch_background:prop:bg-inverse`). -/
private theorem gradeNorm_succ_sq (s : ℕ) (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F (s + 1))
    (v : Fin n → PeriodicL2 n F)
    (hv : ∀ i, v i ∈ periodicSobolevLevel n F s)
    (hd : ∀ i, HasPeriodicWeakDerivative i u (v i)) :
    (periodicSobolevScale n F).gradeNorm (s + 1) u ^ 2 =
      (periodicSobolevScale n F).gradeNorm s u ^ 2 +
        ∑ i, (periodicSobolevScale n F).gradeNorm s (v i) ^ 2 := by
  have hu0 := antitone_periodicSobolevLevel (Nat.le_succ s) hu
  simp_rw [gradeNorm_eq_fourier (s + 1) u hu, gradeNorm_eq_fourier s u hu0,
    fun i ↦ gradeNorm_eq_fourier s (v i) (hv i), fourierNorm_sq]
  have hs := (mem_periodicSobolevLevel_iff s u).mp hu0
  have hvs := fun i ↦ (mem_periodicSobolevLevel_iff s (v i)).mp (hv i)
  apply HasSum.tsum_eq
  apply (hs.hasSum.add (hasSum_sum (s := Finset.univ) (fun i _ ↦ (hvs i).hasSum))).congr_fun
  intro k
  simp only [Real.rpow_natCast, (hd _).sq_periodicFourierCoeff]
  rw [pow_succ (1 + frequencyNorm k ^ 2) s]
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← frequencyNorm_sq_eq_sum]
  ring
/-- A common L² bound for all derivative lists bounds the Fourier energy.
This is the intermediate estimate for reconstruction from top derivatives
(`app:ch_background:eq:bg-r-inverse`). -/
private theorem gradeNorm_sq_le_of_weakDerivativeLists (m : ℕ) (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F m) (N : ℝ) (hN : 0 ≤ N)
    (h : ∀ is : List (Fin n), is.length ≤ m →
      ∃ w : PeriodicL2 n F, HasPeriodicWeakDerivativeList is u w ∧ ‖w‖ ≤ N) :
    (periodicSobolevScale n F).gradeNorm m u ^ 2 ≤ ((n : ℝ) + 1) ^ m * N ^ 2 := by
  induction m generalizing u with
  | zero =>
    obtain ⟨w, hw, hn⟩ := h [] (by simp)
    have hw' := (hasPeriodicWeakDerivativeList_nil u w).mp hw
    subst w
    simpa only [GradedScale.gradeNorm_zero, pow_zero, one_mul] using
      (sq_le_sq₀ (norm_nonneg u) hN).mpr hn
  | succ m ih =>
    obtain ⟨hu0, hv⟩ := exists_periodicWeakDerivatives_of_mem_succ m u hu
    choose v hv hd using hv
    rw [gradeNorm_succ_sq m u hu v hv hd]
    calc
      _ ≤ ((n : ℝ) + 1) ^ m * N ^ 2 +
          ∑ _i : Fin n, ((n : ℝ) + 1) ^ m * N ^ 2 := by
        apply add_le_add
        · exact ih u hu0 (fun is his ↦ h is (his.trans (Nat.le_succ m)))
        · apply Finset.sum_le_sum
          intro i _
          apply ih (v i) (hv i)
          intro is his
          obtain ⟨w, hw, hn⟩ := h (is ++ [i]) (by simpa using Nat.succ_le_succ his)
          exact ⟨w, hw.of_append_singleton (hd i), hn⟩
      _ = _ := by simp [pow_succ]; ring

/-- Reconstruction of the existing Fourier Sobolev norm from a common bound
on all top weak derivatives and the preceding Sobolev norm. This is the
quantitative step needed after `exists_top_weakDerivative_norm_le` for
`app:ch_background:prop:bg-inverse` and `app:ch_background:eq:bg-r-inverse`.
The constant is independent of the field and also applies when `n = 0`. -/
theorem gradeNorm_succ_le_of_top_weakDerivativeLists (s : ℕ) (u : PeriodicL2 n F)
    (hu : u ∈ periodicSobolevLevel n F (s + 1)) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ is : List (Fin n), is.length = s + 1 →
      ∃ w : PeriodicL2 n F, HasPeriodicWeakDerivativeList is u w ∧ ‖w‖ ≤ M) :
    (periodicSobolevScale n F).gradeNorm (s + 1) u ≤
      Real.sqrt (((n : ℝ) + 1) ^ (s + 1)) *
        ((periodicSobolevScale n F).gradeNorm s u + M) := by
  have hu0 := antitone_periodicSobolevLevel (Nat.le_succ s) hu
  have hnorm : ‖ofL2 s u hu0‖ = (periodicSobolevScale n F).gradeNorm s u := by
    rw [norm_eq, toL2_ofL2, gradeNorm_eq_fourier s u hu0]
  have hN : 0 ≤ (periodicSobolevScale n F).gradeNorm s u + M :=
    add_nonneg ((periodicSobolevScale n F).gradeNorm_nonneg s u) hM
  have hb := gradeNorm_sq_le_of_weakDerivativeLists (s + 1) u hu
    ((periodicSobolevScale n F).gradeNorm s u + M) hN (by
      intro is his
      by_cases heq : is.length = s + 1
      · obtain ⟨w, hw, hn⟩ := h is heq
        exact ⟨w, hw, hn.trans (le_add_of_nonneg_left
          ((periodicSobolevScale n F).gradeNorm_nonneg s u))⟩
      · have hlen : is.length ≤ s := by omega
        refine ⟨Exterior.derivativeToL2 s is hlen (ofL2 s u hu0),
          hasWeakDerivativeList_derivativeToL2 s is hlen (ofL2 s u hu0), ?_⟩
        exact (norm_derivativeToL2_le s is hlen (ofL2 s u hu0)).trans
          (hnorm.le.trans (le_add_of_nonneg_right hM)))
  have hsqrt := Real.sqrt_le_sqrt hb
  simpa only [Real.sqrt_sq ((periodicSobolevScale n F).gradeNorm_nonneg (s + 1) u),
    Real.sqrt_mul (by positivity : 0 ≤ ((n : ℝ) + 1) ^ (s + 1)),
    Real.sqrt_sq hN] using hsqrt

/-- A constant depending only on dimension and order reconstructs the actual
periodic Sobolev norm from the preceding level and bounded top weak derivatives.
This supplies the norm-reconstruction input to `HigherRegularity`'s `hstep`
for `app:ch_background:eq:bg-r-inverse`, including dimension zero. -/
theorem exists_gradeNorm_succ_le_of_top_weakDerivativeLists (n s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : PeriodicL2 n (EuclideanSpace ℝ (Fin n))),
      u ∈ periodicSobolevLevel n (EuclideanSpace ℝ (Fin n)) (s + 1) →
      ∀ M : ℝ, 0 ≤ M →
        (∀ is : List (Fin n), is.length = s + 1 →
          ∃ w : PeriodicL2 n (EuclideanSpace ℝ (Fin n)),
            HasPeriodicWeakDerivativeList is u w ∧ ‖w‖ ≤ M) →
        (periodicSobolevScale n (EuclideanSpace ℝ (Fin n))).gradeNorm (s + 1) u ≤
          B * ((periodicSobolevScale n (EuclideanSpace ℝ (Fin n))).gradeNorm s u + M) := by
  exact ⟨Real.sqrt (((n : ℝ) + 1) ^ (s + 1)), Real.sqrt_nonneg _,
    fun u hu M hM h ↦ gradeNorm_succ_le_of_top_weakDerivativeLists s u hu M hM h⟩

end JanetCartan.ContinuumCommutator.HigherRegularity
