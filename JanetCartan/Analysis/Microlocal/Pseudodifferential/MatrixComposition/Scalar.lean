module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PrimitiveComposition
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Scalar superpositions for finite matrix composition

The finite sums in `app:ch_regular_base:thm:actual-calculus` require absolute
convergence before distributing the full operator. This file exposes those
convergence conditions, including their derivation from separate primitive jets.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap ContDiff
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: finite source superposition. -/
theorem sourceAmplitudeTransform_sum {J : Type*} [Fintype J]
    (c : V → V → V → F) (v : J → V → ℂ) (x ξ : V)
    (hy : ∀ j, Integrable (fun y ↦ v j y • c x y ξ)) :
    sourceAmplitudeTransform c (fun y ↦ ∑ j, v j y) x ξ =
      ∑ j, sourceAmplitudeTransform c (v j) x ξ := by
  simp only [sourceAmplitudeTransform, Real.fourier_eq, Finset.sum_smul, Finset.smul_sum]
  exact integral_finsetSum _ (fun j _ ↦ (Real.fourierIntegral_convergent_iff ξ).2 (hy j))

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: finite superposition for the
actual full operator, with both convergence conditions retained. -/
theorem fullAmplitudeOperator_sum {J : Type*} [Fintype J]
    (c : V → V → V → F) (v : J → V → ℂ) (x : V)
    (hy : ∀ j ξ, Integrable (fun y ↦ v j y • c x y ξ))
    (hξ : ∀ j, Integrable (sourceAmplitudeTransform c (v j) x)) :
    fullAmplitudeOperator c (fun y ↦ ∑ j, v j y) x =
      ∑ j, fullAmplitudeOperator c (v j) x := by
  simp only [fullAmplitudeOperator, Real.fourierInv_eq,
    sourceAmplitudeTransform_sum c v x _ (fun j ↦ hy j _), Finset.smul_sum]
  apply integral_finsetSum
  intro j _
  simpa only [inner_neg_right, neg_neg] using
    (Real.fourierIntegral_convergent_iff (-x)).2 (hξ j)

/-- `app:ch_regular_base:thm:actual-calculus`: the two scalar Fubini budgets
also imply convergence after applying the inner operator. -/
theorem integrable_fullAmplitudeOperator_inner
    (c : V → V → V → F) (b : V → V → ℂ) (u : 𝓢(V, ℂ)) (x : V)
    (hy : ∀ ξ, Integrable (fun p : V × V ↦
      ((𝓕 u : 𝓢(V, ℂ)) p.2 * symbolPlaneWave b p.2 p.1) • c x p.1 ξ))
    (hξ : Integrable (fun p : V × V ↦ (𝓕 u : 𝓢(V, ℂ)) p.2 •
      sourceAmplitudeTransform c (symbolPlaneWave b p.2) x p.1)) :
    (∀ ξ, Integrable (fun y ↦ sourceIndependentOperator b u y • c x y ξ)) ∧
      Integrable (sourceAmplitudeTransform c (sourceIndependentOperator b u) x) := by
  have hu : sourceIndependentOperator b u = fun y ↦
      ∫ η, (𝓕 u : 𝓢(V, ℂ)) η * symbolPlaneWave b η y := by
    funext y
    simp only [sourceIndependentOperator, Real.fourierInv_eq, symbolPlaneWave]
    apply integral_congr_ae
    filter_upwards [] with η
    exact smul_comm _ _ _
  constructor
  · intro ξ
    simpa only [hu, integral_smul_const] using (hy ξ).integral_prod_left
  · have heq : sourceAmplitudeTransform c (sourceIndependentOperator b u) x =
        fun ξ ↦ ∫ η, (𝓕 u : 𝓢(V, ℂ)) η •
          sourceAmplitudeTransform c (symbolPlaneWave b η) x ξ := by
      funext ξ
      rw [hu, sourceAmplitudeTransform_integral c _ x ξ (hy ξ)]
      simp_rw [sourceAmplitudeTransform_const_smul]
    rw [heq]
    exact hξ.integral_prod_left

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: joint frequency convergence
implies convergence of the actual composite symbol against Schwartz data. -/
theorem integrable_composedSymbol_test
    (c : V → V → V → F) (b : V → V → ℂ) (u : 𝓢(V, ℂ)) (x : V)
    (hξ : Integrable (fun p : V × V ↦ (𝓕 u : 𝓢(V, ℂ)) p.2 •
      sourceAmplitudeTransform c (symbolPlaneWave b p.2) x p.1)) :
    Integrable (fun η ↦ (𝓕 u : 𝓢(V, ℂ)) η • composedSymbol c b x η) := by
  have hphase : Continuous (fun p : V × V ↦ Real.fourierChar ⟪p.1, x⟫) := by fun_prop
  have hI : Integrable (fun p : V × V ↦ Real.fourierChar ⟪p.1, x⟫ •
      ((𝓕 u : 𝓢(V, ℂ)) p.2 • sourceAmplitudeTransform c (symbolPlaneWave b p.2) x p.1)) := by
    apply hξ.norm.mono' (hphase.aestronglyMeasurable.smul hξ.aestronglyMeasurable)
    filter_upwards [] with p
    simp
  have hi := (Real.fourierIntegral_convergent_iff x).2 hI.integral_prod_right
  simp only [composedSymbol, fullAmplitudeOperator, Real.fourierInv_eq]
  simp_rw [smul_comm ((𝓕 u : 𝓢(V, ℂ)) _), ← integral_smul,
    smul_comm ((𝓕 u : 𝓢(V, ℂ)) _)]
  exact hi

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: a compact physical mask makes
the intermediate plane-wave source integral absolutely convergent. -/
theorem integrable_symbolPlaneWave_mask
    (a : V → F) (b : V → V → ℂ) (χ : V → ℂ) (η : V) (n : ℕ)
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n (fun y ↦ b y η))
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) :
    Integrable (fun y ↦ symbolPlaneWave b η y • (χ y • a y)) := by
  have hc : HasCompactSupport (fun y ↦ χ y • a y) := hχc.smul_right
  exact (contDiff_symbolPlaneWave_smul _ b η n (hχ.smul ha) hb).continuous.integrable_of_hasCompactSupport
    hc.smul_left

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: separate primitive jets and
a compact physical mask imply both composition Fubini budgets. The reserve
is exactly `m + dim V + 1`; no product estimate is assumed. -/
theorem composition_integrable_of_sourceSymbolBounds
    (a : V → V → V → F) (b : V → V → ℂ) (χ : V → ℂ) (u : 𝓢(V, ℂ))
    (x : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1))
    (hb : ContDiff ℝ (m + Module.finrank ℝ V + 1) (Function.uncurry b))
    (B C : ℝ)
    (hB : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y η,
      ‖iteratedFDeriv ℝ j (fun z ↦ b z η) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ a x z ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    (∀ ξ, Integrable (fun p : V × V ↦
      ((𝓕 u : 𝓢(V, ℂ)) p.2 * symbolPlaneWave b p.2 p.1) • (χ p.1 • a x p.1 ξ))) ∧
    Integrable (fun p : V × V ↦ (𝓕 u : 𝓢(V, ℂ)) p.2 •
      sourceAmplitudeTransform (fun x y ξ ↦ χ y • a x y ξ) (symbolPlaneWave b p.2) x p.1) := by
  let n := m + Module.finrank ℝ V + 1
  have haξ (ξ : V) : ContDiff ℝ n (fun y ↦ a x y ξ) :=
    ha.comp (f := fun y ↦ (ξ, y)) (by fun_prop)
  have hbη (η : V) : ContDiff ℝ n (fun y ↦ b y η) :=
    hb.comp (f := fun y ↦ (y, η)) (by fun_prop)
  have hB0 : 0 ≤ B := by
    have hh := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0 0)
    simpa using hh
  have hC0 : 0 ≤ C := by
    have hh := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0 0)
    simpa using hh
  have hD := compositionSourceBound_nonneg χ n B C hB0 hC0
  have hgrowth (r : ℕ) (η : V) : (1 + ‖η‖) ^ r ≤ 2 ^ (r - 1) * (1 + ‖η‖ ^ r) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg η) r
  constructor
  · intro ξ
    apply integrable_symbolPlaneWave_test (fun x y ξ ↦ χ y • a x y ξ) b (𝓕 u) x ξ
      (hχ.smul (haξ ξ)).continuous
      ((hχ.smul (haξ ξ)).continuous.integrable_of_hasCompactSupport hχc.smul_right)
      hb.continuous (B * 2 ^ (l - 1)) l
    intro y η
    have hh : ‖b y η‖ ≤ B * (1 + ‖η‖) ^ l := by
      simpa only [norm_iteratedFDeriv_zero] using hB 0 (Nat.zero_le _) y η
    exact hh.trans ((mul_le_mul_of_nonneg_left (hgrowth l η) hB0).trans_eq (by ring))
  · apply integrable_schwartz_sourceFourier_of_compact_derivativeMass
      (fun ξ η y ↦ symbolPlaneWave b η y • (χ y • a x y ξ)) _ m (n + l)
      (fun ξ η ↦ contDiff_symbolPlaneWave_smul _ b η n (hχ.smul (haξ ξ)) (hbη η))
      (fun _ _ ↦ hχc.smul_right.smul_left)
      (compositionSourceBound χ n B C * 2 ^ (n + l - 1)) _ (𝓕 u)
    · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
        (hb.continuous.comp (f := fun p : (V × V) × V ↦ (p.2, p.1.2)) (by fun_prop))).smul
        ((hχ.continuous.comp continuous_snd).smul
          (ha.continuous.comp (f := fun p : (V × V) × V ↦ (p.1.1, p.2)) (by fun_prop)))
    · intro ξ η
      apply (sourceDerivativeMass_composition_le a b χ x ξ η m l n hχ hχc
        (haξ ξ) (hbη η) B C (fun j hj y ↦ hB j hj y η)
        (fun j hj y ↦ hC j hj y ξ)).trans
      calc
        _ ≤ compositionSourceBound χ n B C *
            (2 ^ (n + l - 1) * (1 + ‖η‖ ^ (n + l))) * (1 + ‖ξ‖) ^ m := by
          gcongr
          exact hgrowth (n + l) η
        _ = _ := by ring
end JanetCartan.Pseudodifferential
