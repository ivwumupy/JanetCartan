module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.FullOperator

/-!
# Composition by intermediate source Fourier integration

For `app:ch_regular_base:thm:actual-calculus`, construct the composite symbol
by applying the actual full-amplitude operator to the inner symbol's plane
waves. Two justified Fubini swaps identify its action on scalar Schwartz data.
The outer amplitude retains both physical positions. The inner symbol is
scalar and source-independent; matrix composition is not asserted here.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap
namespace JanetCartan.Pseudodifferential
variable {V : Type} {F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: A constant complex scalar commutes with the source
Fourier integral. -/
theorem sourceAmplitudeTransform_const_smul (c : V → V → V → F) (v : V → ℂ)
    (a : ℂ) (x ξ : V) :
    sourceAmplitudeTransform c (fun y ↦ a * v y) x ξ =
      a • sourceAmplitudeTransform c v x ξ := by
  simp only [sourceAmplitudeTransform, Real.fourier_eq, mul_smul]
  simp_rw [smul_comm (Real.fourierChar _) a]
  rw [integral_smul]

/-- `app:ch_regular_base:thm:actual-calculus`: Source Fourier integration commutes with an
integrable superposition of physical data. -/
theorem sourceAmplitudeTransform_integral (c : V → V → V → F)
    (v : V → V → ℂ) (x ξ : V)
    (hi : Integrable (fun p : V × V ↦ v p.2 p.1 • c x p.1 ξ)) :
    sourceAmplitudeTransform c (fun y ↦ ∫ η, v η y) x ξ =
      ∫ η, sourceAmplitudeTransform c (v η) x ξ := by
  have hphase : Continuous (fun p : V × V ↦ Real.fourierChar (-⟪p.1, ξ⟫)) := by
    fun_prop
  have hI : Integrable (fun p : V × V ↦
      Real.fourierChar (-⟪p.1, ξ⟫) • (v p.2 p.1 • c x p.1 ξ)) := by
    apply hi.norm.mono' (hphase.aestronglyMeasurable.smul hi.aestronglyMeasurable)
    filter_upwards [] with p
    simp
  simp only [sourceAmplitudeTransform, Real.fourier_eq]
  simp only [Circle.smul_def, ← integral_smul_const, ← integral_smul]
  exact integral_integral_swap hI

/-- `app:ch_regular_base:thm:actual-calculus`: Two Fubini swaps prove superposition for the actual
unregularized full operator. Both absolute convergence conditions are explicit. -/
theorem fullAmplitudeOperator_integral (c : V → V → V → F)
    (v : V → V → ℂ) (x : V)
    (hy : ∀ ξ, Integrable (fun p : V × V ↦ v p.2 p.1 • c x p.1 ξ))
    (hξ : Integrable (fun p : V × V ↦ sourceAmplitudeTransform c (v p.2) x p.1)) :
    fullAmplitudeOperator c (fun y ↦ ∫ η, v η y) x =
      ∫ η, fullAmplitudeOperator c (v η) x := by
  have hphase : Continuous (fun p : V × V ↦ Real.fourierChar ⟪p.1, x⟫) := by fun_prop
  have hI : Integrable (fun p : V × V ↦
      Real.fourierChar ⟪p.1, x⟫ • sourceAmplitudeTransform c (v p.2) x p.1) := by
    apply hξ.norm.mono' (hphase.aestronglyMeasurable.smul hξ.aestronglyMeasurable)
    filter_upwards [] with p
    simp
  simp only [fullAmplitudeOperator, Real.fourierInv_eq]
  simp only [sourceAmplitudeTransform_integral c v x _ (hy _), Circle.smul_def, ← integral_smul]
  exact integral_integral_swap hI

omit [CompleteSpace F] in
/-- `app:ch_regular_base:thm:actual-calculus`: A constant complex scalar commutes with the full
operator. -/
theorem fullAmplitudeOperator_const_smul (c : V → V → V → F) (v : V → ℂ)
    (a : ℂ) (x : V) :
    fullAmplitudeOperator c (fun y ↦ a * v y) x = a • fullAmplitudeOperator c v x := by
  simp only [fullAmplitudeOperator, Real.fourierInv_eq, sourceAmplitudeTransform_const_smul]
  simp_rw [smul_comm (Real.fourierChar _) a]
  rw [integral_smul]

/-- `app:ch_regular_base:thm:actual-calculus`: The plane wave of a scalar inner symbol at the
incoming frequency, with the unit-frequency `2π` convention. -/
def symbolPlaneWave (b : V → V → ℂ) (η y : V) : ℂ :=
  Real.fourierChar ⟪η, y⟫ • b y η

/-- `app:ch_regular_base:thm:actual-calculus`: The composite symbol is an actual iterated integral
over intermediate position and frequency. Removing the incoming plane wave gives the standard
left symbol. -/
def composedSymbol (c : V → V → V → F) (b : V → V → ℂ) (x η : V) : F :=
  Real.fourierChar (-⟪η, x⟫) • fullAmplitudeOperator c (symbolPlaneWave b η) x

/-- `app:ch_regular_base:thm:actual-calculus`: exact composition with a scalar source-independent
inner symbol on Schwartz data. The two displayed integrability hypotheses justify the actual
integral swaps. -/
theorem fullAmplitudeOperator_comp_sourceIndependentOperator
    (c : V → V → V → F) (b : V → V → ℂ) (u : 𝓢(V, ℂ)) (x : V)
    (hy : ∀ ξ, Integrable (fun p : V × V ↦
      ((𝓕 u : 𝓢(V, ℂ)) p.2 * symbolPlaneWave b p.2 p.1) • c x p.1 ξ))
    (hξ : Integrable (fun p : V × V ↦ (𝓕 u : 𝓢(V, ℂ)) p.2 •
      sourceAmplitudeTransform c (symbolPlaneWave b p.2) x p.1)) :
    fullAmplitudeOperator c (sourceIndependentOperator b u) x =
      sourceIndependentOperator (composedSymbol c b) u x := by
  have hu : sourceIndependentOperator b u = fun y ↦
      ∫ η, (𝓕 u : 𝓢(V, ℂ)) η * symbolPlaneWave b η y := by
    funext y
    simp only [sourceIndependentOperator, Real.fourierInv_eq, symbolPlaneWave]
    apply integral_congr_ae
    filter_upwards [] with η
    exact smul_comm _ _ _
  rw [hu, fullAmplitudeOperator_integral c _ x hy]
  · simp_rw [fullAmplitudeOperator_const_smul]
    simp only [sourceIndependentOperator, Real.fourierInv_eq, composedSymbol]
    apply integral_congr_ae
    filter_upwards [] with η
    rw [smul_comm ((𝓕 u : 𝓢(V, ℂ)) η), ← mul_smul, ← AddChar.map_add_eq_mul]
    simp
  · simpa only [sourceAmplitudeTransform_const_smul] using hξ
end JanetCartan.Pseudodifferential
