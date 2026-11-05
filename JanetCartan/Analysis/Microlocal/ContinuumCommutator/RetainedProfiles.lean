module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry.TransportBudget

/-!
# Common profiles on the retained row's original norm domains

The retained row exports reserve-fourteen bounds separately for each carrier
and reserve-two image coefficient bounds. These imply one monotone high
profile, with constants chosen before the current map and initial scalars.
The common measurement restriction costs no derivative reserve. The image's
fixed C¹ budget is derived from the actual admissible history.

The two map domains below are exactly the carrier and image domains exported
by `ContinuumRow.Initialized`, rather than an unproved containment between
them. In particular the construction also works for an empty carrier family.
No carrier low bound at order `2*(n+1)+1` is asserted here: the published
reserve-fourteen estimate at that order requires an initial-scalar derivative
beyond `canonicalCarrierLowOrder n`. The original finite-low scalar class is
unchanged. The consumer is the same-row application of `AugmentedRegularity`.

Sources: `app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`,
`app:ch_waves:eq:joint-tame`, and `main:eq:displacement-budget`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator
open ContinuumRow ContinuumRow.CommonMeasurement AmplitudeBound

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- One additive high profile on the SAME carrier, image and initial-scalar
norm domains (`app:ch_background:prop:bg-inverse`). The leading one is supplied
by the commutator endpoints, not duplicated in each finite summand. -/
def retainedCoefficientProfile (K Kimage : Set (Euclidean n))
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (F : Euclidean n → Euclidean N)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) (m : ℕ) : ℝ :=
  cNorm K m F + cNorm Kimage m F + ∑ i, cNorm (Kin i) m (initial i)

/-- Nonnegativity of the original finite coefficient profile
(`app:ch_background:prop:bg-inverse`). -/
theorem retainedCoefficientProfile_nonneg (K Kimage : Set (Euclidean n))
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (F : Euclidean n → Euclidean N)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) (m : ℕ) :
    0 ≤ retainedCoefficientProfile K Kimage Kin F initial m :=
  add_nonneg (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..))
    (Finset.sum_nonneg fun _ _ ↦ cNorm_nonneg ..)

/-- The same profile is monotone in the derivative order, as required by the
single-inverse bootstrap (`app:ch_background:eq:bg-r-inverse`). -/
theorem retainedCoefficientProfile_monotone (K Kimage : Set (Euclidean n))
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (F : Euclidean n → Euclidean N)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) :
    Monotone (retainedCoefficientProfile K Kimage Kin F initial) := by
  intro p q hpq
  exact add_le_add (add_le_add (cNorm_mono_order hpq) (cNorm_mono_order hpq))
    (Finset.sum_le_sum fun _ _ ↦ cNorm_mono_order hpq)

/-- Each retained carrier's high norm is absorbed once, without products of
high norms (`app:ch_background:eq:bg-commutator`). -/
theorem carrier_profile_le_retainedCoefficientProfile
    (K Kimage : Set (Euclidean n))
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (F : Euclidean n → Euclidean N)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) (i : ι) (m : ℕ) :
    cNorm K m F + cNorm (Kin i) m (initial i) ≤
      retainedCoefficientProfile K Kimage Kin F initial m := by
  classical
  have hsum := Finset.single_le_sum (s := Finset.univ)
    (f := fun a ↦ cNorm (Kin a) m (initial a))
    (fun _ _ ↦ cNorm_nonneg ..) (Finset.mem_univ i)
  dsimp only [retainedCoefficientProfile]
  linarith [cNorm_nonneg Kimage m F]

/-- The original image norm is absorbed in the same high profile, with no
containment assumption on the carrier norm domain (`app:ch_background:eq:bg-commutator`). -/
theorem image_profile_le_retainedCoefficientProfile
    (K Kimage : Set (Euclidean n))
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (F : Euclidean n → Euclidean N)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) (m : ℕ) :
    cNorm Kimage m F ≤ retainedCoefficientProfile K Kimage Kin F initial m := by
  have hsum : 0 ≤ ∑ i, cNorm (Kin i) m (initial i) :=
    Finset.sum_nonneg fun _ _ ↦ cNorm_nonneg ..
  dsimp only [retainedCoefficientProfile]
  linarith [cNorm_nonneg K m F]

/-- Instantiation of the actual retained reserve-fourteen amplitude budgets
after the original common measurement restriction. The finite constants are
chosen before the varying history and initial scalars, the shift is exactly
`2*(n+1)+14`, and there is a SINGLE high profile. The input `hhigh` is the
all-order conclusion retained by `exists_initialized_retained_continuum_row`;
no differential commutator or inverse estimate is assumed
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_fixedMeasurement_retained_high_bounds {r : ℝ} (hr : 0 < r)
    (Cpdo : ι → ℕ → ℝ) (hCpdo : ∀ i p, 0 ≤ Cpdo i p) :
    ∃ Q : ℕ → ℝ, (∀ s, 0 ≤ Q s) ∧
      ∀ (K Kimage : Set (Euclidean n))
        (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
        (F : Euclidean n → Euclidean N)
        (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
        (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ),
      (∀ i, ContDiff ℝ ∞ (Function.uncurry (b i))) →
      (∀ i p, 2 * (n + 1) ≤ p → ∀ l j,
        HasAmplitudeDerivativeBound (fun ξ z ↦ b i ξ z l j) p
          (Cpdo i p * (1 + cNorm K (p + 14) F + cNorm (Kin i) (p + 14) (initial i)))) →
      ∀ s i l j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ restrictAmplitude (b i) (FixedCutoffs.physical hr 1) ξ z l j)
        (2 * (n + 1) + (s + 1))
        (Q s * (1 + retainedCoefficientProfile K Kimage Kin F initial
          (s + 1 + (2 * (n + 1) + 14)))) := by
  classical
  obtain ⟨C, hC, hrestrict⟩ := exists_restrictAmplitude_derivative_constants
    (FixedCutoffs.physical (n := n) hr 1) (FixedCutoffs.physical hr 1).contDiff
    (FixedCutoffs.physical hr 1).hasCompactSupport
  refine ⟨fun s ↦ C (2 * (n + 1) + (s + 1)) *
      ∑ i, Cpdo i (2 * (n + 1) + (s + 1)),
    fun s ↦ mul_nonneg (hC _) (Finset.sum_nonneg fun i _ ↦ hCpdo i _), ?_⟩
  intro K Kimage Kin F initial b hb hhigh s i l j ξ is his z
  let p := 2 * (n + 1) + (s + 1)
  have hp : 2 * (n + 1) ≤ p := by dsimp [p]; omega
  have h := hrestrict (b i) (hb i) p _ (hhigh i p hp) l j ξ is his z
  apply h.trans
  have hsum : Cpdo i p ≤ ∑ a, Cpdo a p :=
    Finset.single_le_sum (fun a _ ↦ hCpdo a p) (Finset.mem_univ i)
  have hprofile := carrier_profile_le_retainedCoefficientProfile K Kimage Kin F initial i (p + 14)
  have horder : p + 14 = s + 1 + (2 * (n + 1) + 14) := by dsimp [p]; omega
  rw [← horder, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hC p)
  apply mul_le_mul hsum _
    (add_nonneg (add_nonneg zero_le_one (cNorm_nonneg ..)) (cNorm_nonneg ..))
    (Finset.sum_nonneg fun a _ ↦ hCpdo a p)
  linarith

/-- Close the image's fixed C¹ budget from an actual admissible history, and
put every high image derivative into the same retained profile. The image
arrays are the SAME arrays from `Initialized`/`HistoryImage`; their reserve-two
jet theorem is used directly. Thresholds and the low constant precede all
histories and positive initial scalars (`app:ch_background:eq:bg-commutator`,
`main:eq:displacement-budget`). -/
theorem exists_history_imageCoefficient_profile_bounds
    (G : Euclidean n → Euclidean N) (hG : ContDiff ℝ ∞ G)
    (Kimage : Set (Euclidean n)) (hKimage : IsCompact Kimage)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) {kMin : ℕ}
    (horder : displacementLoss n + bandExponent * (3 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ L T : ℝ, 0 ≤ L ∧ 2 ≤ T ∧ ∀ R₀, T ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean N) (ell : Fin stage → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)),
      (∀ j a x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + cNorm Kimage (j + 2) (finiteHistoryMap G u))) →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ L) ∧
      ∀ (K : Set (Euclidean n))
        (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
        (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ),
        ∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
          P j * (1 + retainedCoefficientProfile K Kimage Kin
            (finiteHistoryMap G u) initial (j + 2)) := by
  obtain ⟨T, hT, hhistory⟩ := HistoryGeometry.exists_initialScale_for_fixed_immersion_bound
    3 G hG Kimage hKimage horder
  let L := (P 0 + P 1) * (2 + cNorm Kimage 3 G)
  refine ⟨L, T, mul_nonneg (add_nonneg (hP 0) (hP 1))
    (add_nonneg (by norm_num) (cNorm_nonneg ..)), hT, ?_⟩
  intro R₀ hR₀ stage u ell hu c hc
  have hlow := hhistory R₀ hR₀ stage u ell hu
  refine ⟨?_, ?_⟩
  · intro a j hj x
    have hjP : P j ≤ P 0 + P 1 := by
      interval_cases j <;> linarith [hP 0, hP 1]
    have hjF : cNorm Kimage (j + 2) (finiteHistoryMap G u) ≤ cNorm Kimage 3 G + 1 :=
      (cNorm_mono_order (by omega : j + 2 ≤ 3)).trans hlow
    exact (hc j a x).trans (mul_le_mul hjP (by linarith)
      (add_nonneg zero_le_one (cNorm_nonneg ..)) (add_nonneg (hP 0) (hP 1)))
  · intro K Kin initial a j x
    exact (hc j a x).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (image_profile_le_retainedCoefficientProfile
        K Kimage Kin (finiteHistoryMap G u) initial (j + 2))) (hP j))

end JanetCartan.ContinuumCommutator
