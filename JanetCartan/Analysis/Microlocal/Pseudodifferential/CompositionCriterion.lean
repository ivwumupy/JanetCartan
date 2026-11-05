module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.CompositionBounds

/-!
# Composition under finite source derivative budgets

For `app:ch_regular_base:thm:actual-calculus`, the composite symbol is an actual
convergent intermediate Fourier integral. Compact intermediate source support,
polynomial growth of the scalar inner symbol, and finite source derivative
mass bounds justify both integral swaps. The quantitative reserve is
`m + dim V + 1`. These mass bounds concern the plane-wave-weighted product;
their specialization from primitive symbol seminorms remains separate.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap ContDiff
namespace JanetCartan.Pseudodifferential
variable {V : Type} {F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: Compact-source applications use this Fubini
criterion: integrability of the outer amplitude in its source and polynomial growth of the
inner symbol suffice after Schwartz testing. -/
theorem integrable_symbolPlaneWave_test
    (c : V → V → V → F) (b : V → V → ℂ) (ψ : 𝓢(V, ℂ)) (x ξ : V)
    (hc : Continuous (fun y ↦ c x y ξ)) (hci : Integrable (fun y ↦ c x y ξ))
    (hb : Continuous (Function.uncurry b)) (B : ℝ) (k : ℕ)
    (hB : ∀ y η, ‖b y η‖ ≤ B * (1 + ‖η‖ ^ k)) :
    Integrable (fun p : V × V ↦ (ψ p.2 * symbolPlaneWave b p.2 p.1) • c x p.1 ξ) := by
  have hcont : Continuous (fun p : V × V ↦ (ψ p.2 * symbolPlaneWave b p.2 p.1) • c x p.1 ξ) := by
    unfold symbolPlaneWave
    exact ((ψ.continuous.comp continuous_snd).mul
      ((Real.continuous_fourierChar.comp (by fun_prop)).smul hb)).smul
      (hc.comp continuous_fst)
  have hi := hci.norm.mul_prod
    ((ψ.integrable.norm.add (ψ.integrable_pow_mul volume k)).const_mul B)
  apply hi.mono' hcont.aestronglyMeasurable
  filter_upwards [] with p
  simp only [norm_smul, norm_mul, symbolPlaneWave, Circle.norm_smul]
  calc
    _ ≤ (‖ψ p.2‖ * (B * (1 + ‖p.2‖ ^ k))) * ‖c x p.1 ξ‖ := by
      gcongr
      exact hB _ _
    _ = _ := by dsimp only [Pi.add_apply]; ring

/-- `app:ch_regular_base:thm:actual-calculus`: The constructed composite symbol has an absolutely
convergent intermediate frequency integral from a finite source derivative budget. -/
theorem integrable_composedSymbol_frequency_of_derivativeMass
    (c : V → V → V → F) (b : V → V → ℂ) (x η : V)
    (hc : Continuous (fun p : V × V ↦ c x p.2 p.1))
    (hb : Continuous (Function.uncurry b)) (m : ℕ)
    (hs : ∀ ξ, ContDiff ℝ (m + Module.finrank ℝ V + 1)
      (fun y ↦ symbolPlaneWave b η y • c x y ξ))
    (hcc : ∀ ξ, HasCompactSupport (fun y ↦ c x y ξ))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass
      (fun y ↦ symbolPlaneWave b η y • c x y ξ) (m + Module.finrank ℝ V + 1) ≤
      A * (1 + ‖ξ‖) ^ m) :
    Integrable (sourceAmplitudeTransform c (symbolPlaneWave b η) x) := by
  apply integrable_sourceFourier_of_compact_derivativeMass _ _ m _ (Nat.lt_succ_self _)
    hs (fun ξ ↦ (hcc ξ).smul_left) A hA
  exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
    (hb.comp (f := fun p : V × V ↦ (p.2, η)) (by fun_prop))).smul hc

/-- `app:ch_regular_base:thm:actual-calculus`: An explicit bound for the constructed symbol, linear
in its source derivative mass bound. The integral constant is finite since its decay exponent
is `dim V + 1`. -/
theorem norm_composedSymbol_le_of_derivativeMass
    (c : V → V → V → F) (b : V → V → ℂ) (x η : V) (m : ℕ)
    (hs : ∀ ξ, ContDiff ℝ (m + Module.finrank ℝ V + 1)
      (fun y ↦ symbolPlaneWave b η y • c x y ξ))
    (hcc : ∀ ξ, HasCompactSupport (fun y ↦ c x y ξ))
    (A : ℝ) (hA : ∀ ξ, sourceDerivativeMass
      (fun y ↦ symbolPlaneWave b η y • c x y ξ) (m + Module.finrank ℝ V + 1) ≤
      A * (1 + ‖ξ‖) ^ m) :
    ‖composedSymbol c b x η‖ ≤
      ((2 ^ (m + Module.finrank ℝ V) * (1 + 2 ^ (m + Module.finrank ℝ V + 1))) *
        (∫ ξ : V, (1 + ‖ξ‖) ^ (-((Module.finrank ℝ V : ℝ) + 1)))) * A := by
  let n := m + Module.finrank ℝ V + 1
  let C : ℝ := 2 ^ (n - 1) * (1 + 2 ^ n)
  have hi := (integrable_one_add_norm (μ := (volume : Measure V))
    (show (Module.finrank ℝ V : ℝ) < (Module.finrank ℝ V : ℝ) + 1 by linarith)).const_mul (C * A)
  have hbound (ξ : V) : ‖sourceAmplitudeTransform c (symbolPlaneWave b η) x ξ‖ ≤
      C * A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ V : ℝ) + 1)) := by
    have hh := norm_fourier_le_of_sourceDerivativeMass _ m n (hs ξ) (fun j hj ↦
      ((hs ξ).continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
        ((hcc ξ).smul_left.iteratedFDeriv j)) A ξ (hA ξ)
    have he : (n : ℝ) - m = (Module.finrank ℝ V : ℝ) + 1 := by
      dsimp [n]
      push_cast
      ring
    rw [he] at hh
    exact hh
  simp only [composedSymbol, Circle.norm_smul, fullAmplitudeOperator, Real.fourierInv_eq]
  calc
    _ ≤ ∫ ξ, C * A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ V : ℝ) + 1)) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with ξ
      simpa only [Circle.norm_smul] using hbound ξ
    _ = _ := by rw [integral_const_mul]; dsimp [C, n]; ring

variable [CompleteSpace F]
/-- `app:ch_regular_base:thm:actual-calculus`: Exact unregularized composition on scalar Schwartz
data from compact source support and finite derivative mass bounds. Both Fubini integrability
conditions are discharged. -/
theorem fullAmplitudeOperator_comp_sourceIndependentOperator_of_derivativeMass
    (c : V → V → V → F) (b : V → V → ℂ) (u : 𝓢(V, ℂ)) (x : V)
    (hc : Continuous (fun p : V × V ↦ c x p.2 p.1))
    (hb : Continuous (Function.uncurry b))
    (hcc : ∀ ξ, HasCompactSupport (fun y ↦ c x y ξ)) (m k l : ℕ)
    (hs : ∀ ξ η, ContDiff ℝ (m + Module.finrank ℝ V + 1)
      (fun y ↦ symbolPlaneWave b η y • c x y ξ))
    (A B : ℝ) (hB : ∀ y η, ‖b y η‖ ≤ B * (1 + ‖η‖ ^ l))
    (hA : ∀ ξ η, sourceDerivativeMass (fun y ↦ symbolPlaneWave b η y • c x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ A * (1 + ‖η‖ ^ k) * (1 + ‖ξ‖) ^ m) :
    fullAmplitudeOperator c (sourceIndependentOperator b u) x =
      sourceIndependentOperator (composedSymbol c b) u x := by
  apply fullAmplitudeOperator_comp_sourceIndependentOperator c b u x
  · intro ξ
    have hcξ := hc.comp (f := fun y : V ↦ (ξ, y)) (by fun_prop)
    exact integrable_symbolPlaneWave_test c b (𝓕 u) x ξ hcξ
      (hcξ.integrable_of_hasCompactSupport (hcc ξ)) hb B l hB
  · apply integrable_schwartz_sourceFourier_of_compact_derivativeMass
      (fun ξ η y ↦ symbolPlaneWave b η y • c x y ξ) _ m k hs
      (fun ξ _ ↦ (hcc ξ).smul_left) A hA (𝓕 u)
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hb.comp (f := fun p : (V × V) × V ↦ (p.2, p.1.2)) (by fun_prop))).smul
      (hc.comp (f := fun p : (V × V) × V ↦ (p.1.1, p.2)) (by fun_prop))

/-- `app:ch_regular_base:thm:actual-calculus`: Joint smoothness of the primitive amplitudes
discharges the plane-wave product regularity in the finite composition criterion. The
quantitative hypothesis uses only `m + dim V + 1` source derivatives. -/
theorem fullAmplitudeOperator_comp_sourceIndependentOperator_of_joint_smooth
    (c : V → V → V → F) (b : V → V → ℂ) (u : 𝓢(V, ℂ)) (x : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hcc : ∀ ξ, HasCompactSupport (fun y ↦ c x y ξ)) (m k l : ℕ)
    (A B : ℝ) (hB : ∀ y η, ‖b y η‖ ≤ B * (1 + ‖η‖ ^ l))
    (hA : ∀ ξ η, sourceDerivativeMass (fun y ↦ symbolPlaneWave b η y • c x y ξ)
      (m + Module.finrank ℝ V + 1) ≤ A * (1 + ‖η‖ ^ k) * (1 + ‖ξ‖) ^ m) :
    fullAmplitudeOperator c (sourceIndependentOperator b u) x =
      sourceIndependentOperator (composedSymbol c b) u x := by
  apply fullAmplitudeOperator_comp_sourceIndependentOperator_of_derivativeMass c b u x
    (hc.continuous.comp (f := fun p : V × V ↦ (x, p.2, p.1)) (by fun_prop))
    hb.continuous hcc m k l _ A B hB hA
  intro ξ η
  apply ContDiff.of_le (n := (∞ : WithTop ℕ∞)) _ (by simp)
  have hbη : ContDiff ℝ ∞ (fun y ↦ b y η) :=
    hb.comp (f := fun y ↦ (y, η)) (by fun_prop)
  have hcξ : ContDiff ℝ ∞ (fun y ↦ c x y ξ) :=
    hc.comp (f := fun y ↦ (x, y, ξ)) (by fun_prop)
  simp only [symbolPlaneWave, Circle.smul_def, Real.fourierChar_apply]
  have hi : ContDiff ℝ ∞ (fun y : V ↦ ⟪η, y⟫) := (innerSL ℝ η).contDiff
  have hr : ContDiff ℝ ∞ (fun y : V ↦ 2 * Real.pi * ⟪η, y⟫) :=
    contDiff_const.mul hi
  have ho : ContDiff ℝ ∞ (fun y : V ↦ ((2 * Real.pi * ⟪η, y⟫ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  have hphase : ContDiff ℝ ∞ (fun y : V ↦
      Complex.exp ((2 * Real.pi * ⟪η, y⟫ : ℝ) * Complex.I)) := by fun_prop
  exact (hphase.smul hbη).smul hcξ
end JanetCartan.Pseudodifferential
