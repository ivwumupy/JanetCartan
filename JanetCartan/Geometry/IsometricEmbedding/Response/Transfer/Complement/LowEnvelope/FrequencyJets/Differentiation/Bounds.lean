module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Support
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels

/-!
# Compact frequency majorants for output jets

Primitive amplitude and target-phase bounds give a common integrable majorant
for every target coordinate jet in
`app:ch_response:thm:response-literal-transfer`. These estimates use the original
source and frequency carriers and only the Fourier datum's L¹ norm. They are
consumed by dominated frequency differentiation, without any source phase gap
or frequency differentiability premise.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison JanetCartan.Localization

variable {n r : ℕ}

/-- The unscaled primitive profiles bound the actual modified amplitude in
`app:ch_response:thm:response-literal-transfer`. This is the scale-one
specialization used for compact frequency domination. -/
theorem norm_outputJetAmplitude_le_primitive
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (η : Euclidean n) (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hAj : ∀ (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k)
    (hτj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j)
    (α : List (Fin n)) (x y : Euclidean n) :
    ‖outputJetAmplitude τ α A x y η‖ ≤ outputJetAmplitudeGrade P C α.length 0 := by
  simpa only [norm_iteratedFDeriv_zero, one_pow, mul_one] using
    norm_iteratedFDeriv_outputJetAmplitude_le τ A η C P hC hP
      (a := 1) (L := 1) (R := 1) zero_le_one le_rfl le_rfl 0 hτ hA
      (by simpa only [one_pow, mul_one] using hAj)
      (by simpa only [one_pow, mul_one] using hτj) α 0 x y

/-- Compact-source domination for the true differentiated kernel in
`app:ch_response:thm:response-literal-transfer`. Oscillation has modulus one,
so this estimate needs no regularity or lower gradient bound for `ψ`. -/
theorem norm_sourceKernel_outputJetAmplitude_le_compact
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ψ : Euclidean n → ℝ) (η : Euclidean n)
    (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {Ks : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (hAj : ∀ (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k)
    (hτj : ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j)
    (α : List (Fin n)) (x : Euclidean n) :
    ‖sourceKernel ψ (outputJetAmplitude τ α A) x η‖ ≤
      outputJetAmplitudeGrade P C α.length 0 * volume.real Ks := by
  have he : sourceKernel ψ (outputJetAmplitude τ α A) x η =
      ∫ y in Ks, phaseOscillation ψ y • outputJetAmplitude τ α A x y η := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by
      simp [outputJetAmplitude_eq_zero_off_source τ α A hs x y η hy])).symm
  rw [he]
  apply norm_setIntegral_le_of_norm_le_const hKs.measure_lt_top
  intro y _
  rw [norm_smul, norm_phaseOscillation, one_mul]
  exact norm_outputJetAmplitude_le_primitive τ A η C P hC hP hτ hA hAj hτj α x y

/-- The common frequency majorant for the low-envelope output jets in
`app:ch_response:thm:response-literal-transfer`. Its frequency cutoff is exactly
the original full amplitude's carrier. -/
def compactFrequencyJetMajorant (r : ℕ) (Ks Kη : Set (Euclidean n))
    (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ) (α : List (Fin n))
    (H : Euclidean n → EuclideanSpace ℂ (Fin r)) (p : Euclidean n × Euclidean n) : ℝ :=
  Kη.indicator (fun _ ↦ (r : ℝ) *
    (outputJetAmplitudeGrade P C α.length 0 * volume.real Ks)) p.1 * ‖H p.2‖

/-- The frequency majorant is integrable for every L¹ Fourier datum, as needed
by dominated differentiation in `app:ch_response:thm:response-literal-transfer`.
No physical L¹ premise is used. -/
theorem integrable_compactFrequencyJetMajorant
    (Ks : Set (Euclidean n)) {Kη : Set (Euclidean n)} (hKη : IsCompact Kη)
    (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ) (α : List (Fin n))
    {H : Euclidean n → EuclideanSpace ℂ (Fin r)} (hH : Integrable H) :
    Integrable (compactFrequencyJetMajorant r Ks Kη C P α H) (volume.prod volume) := by
  let : IsFiniteMeasure (volume.restrict Kη) := ⟨by simpa using hKη.measure_lt_top⟩
  exact ((integrable_indicator_iff hKη.measurableSet).mpr (integrable_const _)).mul_prod hH.norm

private theorem norm_mulVec_fourierDatum_le (M : Matrix (Fin r) (Fin r) ℂ)
    (v : EuclideanSpace ℂ (Fin r)) : ‖M.mulVec v‖ ≤ (r : ℝ) * ‖M‖ * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖M.mulVec v i‖ ≤ ∑ j, ‖M i j * v j‖ := by
      simpa only [Matrix.mulVec, dotProduct] using
        norm_sum_le Finset.univ (fun j ↦ M i j * v j)
    _ ≤ ∑ _j : Fin r, ‖M‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (AmplitudeBound.norm_matrixEntry_le_frobenius M i j)
        (PiLp.norm_apply_le v j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- Every true output-jet integrand is dominated on the whole target space by
the original compact frequency majorant
(`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_sourceKernel_outputJetAmplitude_mulVec_le_majorant
    (τ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ψ : Euclidean n → Euclidean n → Euclidean n → ℝ)
    (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    (hτ : ∀ η, ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hA : ∀ η, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {Ks Kη : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (hf : ∀ x y η, η ∉ Kη → A x y η = 0)
    (hAj : ∀ η (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k)
    (hτj : ∀ η ∈ Kη, ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j)
    (α : List (Fin n)) (H : Euclidean n → EuclideanSpace ℂ (Fin r))
    (x : Euclidean n) (p : Euclidean n × Euclidean n) :
    ‖(sourceKernel (ψ p.1 p.2) (outputJetAmplitude τ α A) x p.1).mulVec (H p.2)‖ ≤
      compactFrequencyJetMajorant r Ks Kη C P α H p := by
  by_cases hp : p.1 ∈ Kη
  · rw [compactFrequencyJetMajorant, Set.indicator_of_mem hp]
    exact (norm_mulVec_fourierDatum_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (norm_sourceKernel_outputJetAmplitude_le_compact τ A (ψ p.1 p.2) p.1
            C P hC hP (hτ p.1) (hA p.1) hKs hs (hAj p.1) (hτj p.1 hp) α x)
          (Nat.cast_nonneg r)) (norm_nonneg _))
  · have hz : sourceKernel (ψ p.1 p.2) (outputJetAmplitude τ α A) x p.1 = 0 := by
      simp [sourceKernel, outputJetAmplitude_eq_zero_off_frequency τ α A hf x _ p.1 hp]
    simp [hz, compactFrequencyJetMajorant, Set.indicator_of_notMem hp]

/-- Domination of the actual scalar coordinate derivatives before frequency
integration in `app:ch_response:thm:response-literal-transfer`. The source
identity is proved in `SourceCoordinates`, and the majorant is integrable by
`integrable_compactFrequencyJetMajorant` whenever `Kη` is compact and `H` is L¹. -/
theorem norm_euclideanCoordinateDerivList_sourceKernel_splitPhase_le_majorant
    (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    (hτ : ∀ η, ContDiff ℝ ∞ (fun x ↦ τ x η))
    (hσ : ∀ η θ, ContDiff ℝ ∞ (σ η θ))
    (hA : ∀ η, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {Ks Kη : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (hf : ∀ x y η, η ∉ Kη → A x y η = 0)
    (hAj : ∀ η (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun z ↦ normalMatrixDerivList β (fun w ↦ A w z η) x) y‖ ≤
        C β.length k)
    (hτj : ∀ η ∈ Kη, ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j)
    (α : List (Fin n)) (H : Euclidean n → EuclideanSpace ℂ (Fin r))
    (x : Euclidean n) (p : Euclidean n × Euclidean n) (i : Fin r) :
    ‖AmplitudeBound.euclideanCoordinateDerivList α (fun z ↦
      (sourceKernel (fun y ↦ τ z p.1 + σ p.1 p.2 y) A z p.1).mulVec (H p.2) i) x‖ ≤
      compactFrequencyJetMajorant r Ks Kη C P α H p := by
  rw [euclideanCoordinateDerivList_sourceKernel_splitPhase τ (σ p.1 p.2) A p.1
    (hτ p.1) (hσ p.1 p.2) (hA p.1) hKs (fun x y hy ↦ hs x y p.1 hy)]
  exact (norm_le_pi_norm _ i).trans
    (norm_sourceKernel_outputJetAmplitude_mulVec_le_majorant τ A
      (fun η θ y ↦ τ x η + σ η θ y) C P hC hP hτ hA hKs hs hf hAj hτj α H x p)

end JanetCartan.ResponseTransfer.LowEnvelope
