module

public import JanetCartan.Analysis.Fourier.Periodic.Deriv.Coefficient
public import JanetCartan.Analysis.Fourier.Periodic.Deriv.RealPair

/-!
# Fourier coefficients of periodic derivatives

The unit-torus convention of paper.tex, `app:not:fourier`: each coordinate derivative
has symbol `2π i kᵢ`. Iterating this identity gives the finite-order coefficient
decay used in Appendix B, `app:lem:sharp-fourier-embedding`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {n : ℕ}

/-- The derivative/Fourier identity for smooth complex fields (`app:not:fourier`). -/
theorem mFourierCoeff_coordinateDeriv {f : Torus n → ℂ} (hf : IsSmoothPeriodic f)
    (i : Fin n) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (periodicCoordinateDeriv i f) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * UnitAddTorus.mFourierCoeff f k :=
  mFourierCoeff_of_hasDerivAt_coordinate hf.1 (hf.coordinateDeriv i).1 i
    (hf.hasDerivAt_coordinate i) k

/-- The componentwise complex identity for real fields (`app:not:fourier`). -/
theorem mFourierCoeff_real_coordinateDeriv {f : Torus n → ℝ} (hf : IsSmoothPeriodic f)
    (i : Fin n) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ ((periodicCoordinateDeriv i f x : ℝ) : ℂ)) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k :=
  mFourierCoeff_of_hasDerivAt_coordinate (Complex.continuous_ofReal.comp hf.1)
    (Complex.continuous_ofReal.comp (hf.coordinateDeriv i).1) i
    (fun x t ↦ (hf.hasDerivAt_coordinate i x t).ofReal_comp) k

/-- Coordinate functionals of a real vector field satisfy the complex multiplier identity
(`app:not:fourier`). This applies in particular to fixed Euclidean or matrix coordinates. -/
theorem mFourierCoeff_component_coordinateDeriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (L : F →L[ℝ] ℝ) (i : Fin n) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (L (periodicCoordinateDeriv i f x) : ℂ)) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (L (f x) : ℂ)) k := by
  simpa only [periodicCoordinateDeriv_comp_clm hf L] using
    mFourierCoeff_real_coordinateDeriv (hf.comp_clm L) i k

/-- Differentiation rotates the shared real pair by `2π kᵢ` (`app:not:fourier`). -/
theorem periodicFourierCoeff_coordinateDeriv {f : Torus n → ℝ} (hf : IsSmoothPeriodic f)
    (i : Fin n) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicCoordinateDeriv i f) k =
      (-(2 * Real.pi * (k i : ℝ)) * (periodicFourierCoeff f k).2,
        (2 * Real.pi * (k i : ℝ)) * (periodicFourierCoeff f k).1) := by
  rw [periodicFourierCoeff_eq_complex_parts (hf.coordinateDeriv i).1,
    mFourierCoeff_real_coordinateDeriv hf, periodicFourierCoeff_eq_complex_parts hf.1]
  ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The derivative symbol in the shared real-pair representation for real Banach-valued
fields (`app:not:fourier`). -/
theorem periodicFourierCoeff_coordinateDeriv_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : Torus n → F} (hf : IsSmoothPeriodic f)
    (i : Fin n) (k : Fin n → ℤ) :
    periodicFourierCoeff (periodicCoordinateDeriv i f) k =
      (-(2 * Real.pi * (k i : ℝ)) • (periodicFourierCoeff f k).2,
        (2 * Real.pi * (k i : ℝ)) • (periodicFourierCoeff f k).1) := by
  apply Prod.ext
  · apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have heq := periodicFourierCoeff_coordinateDeriv (hf.comp_clm L) i k
    rw [periodicCoordinateDeriv_comp_clm hf L,
      periodicFourierCoeff_map L (hf.coordinateDeriv i).1,
      periodicFourierCoeff_map L hf.1] at heq
    simpa only [map_smul, smul_eq_mul] using congrArg Prod.fst heq
  · apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    have heq := periodicFourierCoeff_coordinateDeriv (hf.comp_clm L) i k
    rw [periodicCoordinateDeriv_comp_clm hf L,
      periodicFourierCoeff_map L (hf.coordinateDeriv i).1,
      periodicFourierCoeff_map L hf.1] at heq
    simpa only [map_smul, smul_eq_mul] using congrArg Prod.snd heq

/-- An ordered list of Cartesian derivatives (`app:not:fourier`). -/
def periodicCoordinateDerivList {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    List (Fin n) → (Torus n → F) → Torus n → F
  | [], f => f
  | i :: is, f => periodicCoordinateDeriv i (periodicCoordinateDerivList is f)

/-- Every finite Cartesian derivative of a smooth periodic field is smooth (`app:not:fourier`). -/
theorem IsSmoothPeriodic.coordinateDerivList {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (is : List (Fin n)) :
    IsSmoothPeriodic (periodicCoordinateDerivList is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact ih.coordinateDeriv i

/-- Taking any finite list of derivatives commutes with real continuous linear maps
(`app:not:fourier`). -/
theorem periodicCoordinateDerivList_comp_clm {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (L : F →L[ℝ] G)
    (is : List (Fin n)) : periodicCoordinateDerivList is (fun x ↦ L (f x)) =
      fun x ↦ L (periodicCoordinateDerivList is f x) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [periodicCoordinateDerivList, ih]
    exact periodicCoordinateDeriv_comp_clm (hf.coordinateDerivList is) L i

/-- The mixed derivative symbol is the product of the coordinate symbols (`app:not:fourier`). -/
theorem mFourierCoeff_real_coordinateDerivList {f : Torus n → ℝ} (hf : IsSmoothPeriodic f)
    (is : List (Fin n)) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ ((periodicCoordinateDerivList is f x : ℝ) : ℂ)) k =
      (is.map (fun i ↦ 2 * Real.pi * Complex.I * (k i : ℂ))).prod *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  induction is with
  | nil => simp [periodicCoordinateDerivList]
  | cons i is ih =>
    rw [periodicCoordinateDerivList, mFourierCoeff_real_coordinateDeriv (hf.coordinateDerivList is), ih]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- Mixed derivatives of each real coordinate have the product Fourier symbol
(`app:not:fourier`). -/
theorem mFourierCoeff_component_coordinateDerivList {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (L : F →L[ℝ] ℝ) (is : List (Fin n)) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (L (periodicCoordinateDerivList is f x) : ℂ)) k =
      (is.map (fun i ↦ 2 * Real.pi * Complex.I * (k i : ℂ))).prod *
        UnitAddTorus.mFourierCoeff (fun x ↦ (L (f x) : ℂ)) k := by
  simpa only [periodicCoordinateDerivList_comp_clm hf L] using
    mFourierCoeff_real_coordinateDerivList (hf.comp_clm L) is k

/-- The pure order-`r` derivative has symbol `(2π i kᵢ)^r` (`app:not:fourier`). -/
theorem mFourierCoeff_real_iteratedCoordinateDeriv {f : Torus n → ℝ} (hf : IsSmoothPeriodic f)
    (i : Fin n) (r : ℕ) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x ↦ ((periodicCoordinateDerivList (List.replicate r i) f x : ℝ) : ℂ)) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) ^ r *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  simpa using mFourierCoeff_real_coordinateDerivList hf (List.replicate r i) k

/-- Finite-order polynomial coefficient bound, without division at zero frequency
(Appendix B, `app:lem:sharp-fourier-embedding`). -/
theorem pow_mul_norm_mFourierCoeff_le {f : Torus n → ℝ} (hf : IsSmoothPeriodic f)
    (i : Fin n) (r : ℕ) {C : ℝ}
    (hC : ∀ x, ‖periodicCoordinateDerivList (List.replicate r i) f x‖ ≤ C)
    (k : Fin n → ℤ) :
    (2 * Real.pi * |(k i : ℝ)|) ^ r *
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ ≤ C := by
  have h := norm_mFourierCoeff_le
    (fun x ↦ ((periodicCoordinateDerivList (List.replicate r i) f x : ℝ) : ℂ)) k
    (fun x ↦ by simpa only [Complex.norm_real] using hC x)
  rw [mFourierCoeff_real_iteratedCoordinateDeriv hf, norm_mul, norm_pow] at h
  simpa [norm_mul, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_intCast, Int.cast_abs] using h

/-- Polynomial decay away from a coordinate hyperplane (Appendix B,
`app:lem:sharp-fourier-embedding`). -/
theorem norm_mFourierCoeff_le_div_pow {f : Torus n → ℝ} (hf : IsSmoothPeriodic f)
    (i : Fin n) (r : ℕ) {C : ℝ}
    (hC : ∀ x, ‖periodicCoordinateDerivList (List.replicate r i) f x‖ ≤ C)
    (k : Fin n → ℤ) (hk : k i ≠ 0) :
    ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ ≤
      C / (2 * Real.pi * |(k i : ℝ)|) ^ r := by
  have hp : 0 < (2 * Real.pi * |(k i : ℝ)|) ^ r := by
    apply pow_pos
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (by exact_mod_cast hk))
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using pow_mul_norm_mFourierCoeff_le hf i r hC k

private lemma frequencyNorm_le_coordinate_max (k : Fin n → ℤ) (i : Fin n) (hi : ∀ j, |(k j : ℝ)| ≤ |(k i : ℝ)|) :
    frequencyNorm k ≤ (n : ℝ) * (2 * Real.pi * |(k i : ℝ)|) := by
  have he : (WithLp.toLp 2 (fun j ↦ (k j : ℝ)) : EuclideanSpace ℝ (Fin n)) =
      ∑ j, EuclideanSpace.single j (k j : ℝ) := by
    ext j
    simp
  unfold frequencyNorm
  rw [he]
  calc
    _ ≤ 2 * Real.pi * ∑ j : Fin n, ‖EuclideanSpace.single j (k j : ℝ)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ 2 * Real.pi * ∑ _j : Fin n, |(k i : ℝ)| := by
      gcongr with j
      simpa using hi j
    _ = _ := by simp; ring

/-- Radial polynomial coefficient bound from the order-`r` pure Cartesian derivatives
(Appendix B, `app:lem:sharp-fourier-embedding`). -/
theorem frequencyNorm_pow_mul_norm_mFourierCoeff_le {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) (hn : 0 < n) (r : ℕ) {C : ℝ}
    (hC : ∀ i x, ‖periodicCoordinateDerivList (List.replicate r i) f x‖ ≤ C)
    (k : Fin n → ℤ) :
    frequencyNorm k ^ r * ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ ≤
      (n : ℝ) ^ r * C := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n ↦ |(k i : ℝ)|) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hfreq := frequencyNorm_le_coordinate_max k i (fun j ↦ hi j (Finset.mem_univ _))
  calc
    _ ≤ ((n : ℝ) * (2 * Real.pi * |(k i : ℝ)|)) ^ r *
        ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ := by
      gcongr
      · exact mul_nonneg (by positivity) (norm_nonneg _)
    _ = (n : ℝ) ^ r * ((2 * Real.pi * |(k i : ℝ)|) ^ r *
        ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_norm_mFourierCoeff_le hf i r (hC i) k)
      (by positivity)

/-- Compactness supplies a uniform polynomial coefficient bound at every finite order
(Appendix B, `app:lem:sharp-fourier-embedding`). -/
theorem IsSmoothPeriodic.exists_frequencyNorm_pow_mul_norm_mFourierCoeff_bound {f : Torus n → ℝ} (hf : IsSmoothPeriodic f) (hn : 0 < n) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Fin n → ℤ,
      frequencyNorm k ^ r * ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ ≤ C := by
  choose C hC using fun i : Fin n ↦ isCompact_univ.exists_bound_of_continuousOn
    (hf.coordinateDerivList (List.replicate r i)).1.continuousOn
  have hbound (i : Fin n) (x : Torus n) :
      ‖periodicCoordinateDerivList (List.replicate r i) f x‖ ≤ ∑ j : Fin n, |C j| := by
    exact (hC i x (Set.mem_univ _)).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)))
  refine ⟨(n : ℝ) ^ r * ∑ j : Fin n, |C j|, by positivity, ?_⟩
  exact fun k ↦ frequencyNorm_pow_mul_norm_mFourierCoeff_le hf hn r hbound k

/-- Every nonzero lattice frequency has positive physical norm (`app:not:fourier`). -/
theorem frequencyNorm_pos_of_ne_zero (k : Fin n → ℤ) (hk : k ≠ 0) : 0 < frequencyNorm k := by
  apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
  apply norm_pos_iff.mpr
  intro heq
  apply hk
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) heq
  simpa using hi


/-- Smooth periodic fields have polynomially decaying coefficients at every finite order,
with no additional analytic assumptions (Appendix B, `app:lem:sharp-fourier-embedding`). -/
theorem IsSmoothPeriodic.exists_mFourierCoeff_decay {f : Torus n → ℝ}
    (hf : IsSmoothPeriodic f) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Fin n → ℤ, k ≠ 0 →
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k‖ ≤ C / frequencyNorm k ^ r := by
  by_cases hn : 0 < n
  · obtain ⟨C, hC, hbound⟩ := hf.exists_frequencyNorm_pow_mul_norm_mFourierCoeff_bound hn r
    refine ⟨C, hC, fun k hk ↦
      (le_div_iff₀ (pow_pos (frequencyNorm_pos_of_ne_zero k hk) r)).mpr ?_⟩
    simpa only [mul_comm] using hbound k
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨0, le_rfl, fun k hk ↦ ?_⟩
    exact False.elim (hk (funext fun i ↦ Fin.elim0 i))

end JanetCartan

