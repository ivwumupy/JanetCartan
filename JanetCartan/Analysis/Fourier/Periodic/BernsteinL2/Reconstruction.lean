module

public import JanetCartan.Analysis.Fourier.Periodic.Deriv.RealPair
public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Basic
public import JanetCartan.Analysis.Fourier.Periodic.Lattice
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Reconstruction of fields with finite Fourier support

Finite real Fourier inversion for `main:eq:history-bernstein` and
`main:eq:final-Cr` of paper.tex. Scalar inversion uses the continuous Fourier
series theorem; continuous linear functionals give the real Banach-valued result.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ}

/-- `app:not:fourier`: finite scalar inversion from the convergent complex Fourier series. -/
private lemma eq_sum_periodicFourierMode_scalar {f : Torus n → ℝ} (hf : Continuous f)
    (s : Finset (Fin n → ℤ)) (hs : ∀ k ∉ s, periodicFourierCoeff f k = 0)
    (x : Torus n) : f x = ∑ k ∈ s, periodicFourierMode k (periodicFourierCoeff f k) x := by
  let g : C(Torus n, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp hf⟩
  have hz (k : Fin n → ℤ) (hk : k ∉ s) : UnitAddTorus.mFourierCoeff g k = 0 := by
    have hp := hs k hk
    rw [periodicFourierCoeff_eq_complex_parts hf] at hp
    apply Complex.ext
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  have hsum : Summable (UnitAddTorus.mFourierCoeff g) := summable_of_ne_finset_zero hz
  have he := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum x).tsum_eq
  rw [tsum_eq_sum (s := s) (fun k hk ↦ by rw [hz k hk]; simp)] at he
  have hr := congrArg Complex.reCLM he.symm
  simp only [map_sum, Complex.reCLM_apply, smul_eq_mul, Complex.mul_re] at hr
  convert hr using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [periodicFourierMode, periodicFourierCoeff_eq_complex_parts hf]
  simp [g, mul_comm]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `app:not:fourier`, `main:eq:final-Cr`: a continuous real field with finite
Fourier support equals its finite sum of real Fourier modes. -/
theorem eq_sum_periodicFourierMode_of_finite_support {f : Torus n → F} (hf : Continuous f)
    (s : Finset (Fin n → ℤ)) (hs : ∀ k ∉ s, periodicFourierCoeff f k = 0)
    (x : Torus n) : f x = ∑ k ∈ s, periodicFourierMode k (periodicFourierCoeff f k) x := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro A
  have hz : ∀ k ∉ s, periodicFourierCoeff (A ∘ f) k = 0 := by
    intro k hk
    rw [periodicFourierCoeff_comp_clm A hf, hs k hk]
    simp
  have h := eq_sum_periodicFourierMode_scalar (A.continuous.comp hf) s hz x
  change A (f x) = ∑ k ∈ s,
    periodicFourierMode k (periodicFourierCoeff (A ∘ f) k) x at h
  simp only [periodicFourierCoeff_comp_clm A hf] at h
  simpa only [map_sum, periodicFourierMode, map_sub, map_smul] using h

/-- `main:eq:history-bernstein`, `main:eq:final-Cr`: reconstruct a band-limited
continuous field using precisely the finite physical-frequency ball. -/
theorem eq_sum_periodicFourierMode_of_hasFourierSupport {f : Torus n → F} (hf : Continuous f) {L : ℝ}
    (hs : HasFourierSupport L f) (x : Torus n) :
    f x = ∑ k ∈ frequencyBall n L, periodicFourierMode k (periodicFourierCoeff f k) x := by
  apply eq_sum_periodicFourierMode_of_finite_support hf
  intro k hk
  exact hs k (lt_of_not_ge (fun h ↦ hk (mem_frequencyBall.mpr h)))

end JanetCartan
