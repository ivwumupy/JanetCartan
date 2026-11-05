module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.PrimitiveCompositionBounds
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.CompositionCriterion

/-!
# Actual composition from primitive finite symbol bounds

For `app:ch_regular_base:thm:actual-calculus`, a fixed compact source mask and
separate source jets of the two amplitudes imply absolute convergence and the
exact integral composition formula. The derivative count is `m + dim V + 1`.
The incoming growth bound is deliberately coarse; no sharp symbol order or
Sobolev boundedness assertion is made here.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap FourierTransform
namespace JanetCartan.Pseudodifferential
variable {V : Type} {F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:thm:actual-calculus`: finite primitive source symbol
bounds give an absolutely convergent integral defining the composite symbol. -/
theorem integrable_composedSymbol_frequency_of_sourceSymbolBounds
    (a : V → V → V → F) (b : V → V → ℂ) (χ : V → ℂ) (x η : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1))
    (hb : ContDiff ℝ (m + Module.finrank ℝ V + 1) (Function.uncurry b))
    (B C : ℝ)
    (hB : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y,
      ‖iteratedFDeriv ℝ j (fun z ↦ b z η) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ a x z ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    Integrable (sourceAmplitudeTransform (fun x y ξ ↦ χ y • a x y ξ)
      (symbolPlaneWave b η) x) := by
  let n := m + Module.finrank ℝ V + 1
  have haξ (ξ : V) : ContDiff ℝ n (fun y ↦ a x y ξ) :=
    ha.comp (f := fun y ↦ (ξ, y)) (by fun_prop)
  have hbη : ContDiff ℝ n (fun y ↦ b y η) :=
    hb.comp (f := fun y ↦ (y, η)) (by fun_prop)
  apply integrable_composedSymbol_frequency_of_derivativeMass (fun x y ξ ↦ χ y • a x y ξ) b x η
    ((hχ.continuous.comp continuous_snd).smul ha.continuous) hb.continuous m
    (fun ξ ↦ contDiff_symbolPlaneWave_smul (fun y ↦ χ y • a x y ξ) b η n (hχ.smul (haξ ξ)) hbη)
    (fun _ ↦ hχc.smul_right)
    (compositionSourceBound χ n B C * (1 + ‖η‖) ^ (n + l))
  intro ξ
  exact sourceDerivativeMass_composition_le a b χ x ξ η m l n hχ hχc
    (haξ ξ) hbη B C hB (fun j hj y ↦ hC j hj y ξ)

/-- `app:ch_regular_base:thm:actual-calculus`: an explicit coarse polynomial
bound for the composite symbol, bilinear in the separate primitive bounds. -/
theorem norm_composedSymbol_le_of_sourceSymbolBounds
    (a : V → V → V → F) (b : V → V → ℂ) (χ : V → ℂ) (x η : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ∀ ξ, ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun y ↦ a x y ξ))
    (hb : ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun y ↦ b y η))
    (B C : ℝ)
    (hB : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y,
      ‖iteratedFDeriv ℝ j (fun z ↦ b z η) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ a x z ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    ‖composedSymbol (fun x y ξ ↦ χ y • a x y ξ) b x η‖ ≤
      ((2 ^ (m + Module.finrank ℝ V) * (1 + 2 ^ (m + Module.finrank ℝ V + 1))) *
        (∫ ξ : V, (1 + ‖ξ‖) ^ (-((Module.finrank ℝ V : ℝ) + 1)))) *
      (compositionSourceBound χ (m + Module.finrank ℝ V + 1) B C *
        (1 + ‖η‖) ^ (m + Module.finrank ℝ V + 1 + l)) := by
  apply norm_composedSymbol_le_of_derivativeMass (fun x y ξ ↦ χ y • a x y ξ) b x η m
    (fun ξ ↦ contDiff_symbolPlaneWave_smul (fun y ↦ χ y • a x y ξ) b η _ (hχ.smul (ha ξ)) hb)
    (fun _ ↦ hχc.smul_right)
  intro ξ
  exact sourceDerivativeMass_composition_le a b χ x ξ η m l _ hχ hχc
    (ha ξ) hb B C hB (fun j hj y ↦ hC j hj y ξ)

variable [CompleteSpace F]
/-- `app:ch_regular_base:thm:actual-calculus`: exact composition on scalar
Schwartz data from the separate primitive source symbol bounds. The physical
source mask remains in the outer amplitude, and every Fubini hypothesis is proved.
Only source derivatives through `m + dim V + 1` are used. -/
theorem fullAmplitudeOperator_comp_sourceIndependentOperator_of_sourceSymbolBounds
    (a : V → V → V → F) (b : V → V → ℂ) (χ : V → ℂ) (u : 𝓢(V, ℂ)) (x : V) (m l : ℕ)
    (hχ : ContDiff ℝ (m + Module.finrank ℝ V + 1) χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ (m + Module.finrank ℝ V + 1) (fun p : V × V ↦ a x p.2 p.1))
    (hb : ContDiff ℝ (m + Module.finrank ℝ V + 1) (Function.uncurry b))
    (B C : ℝ)
    (hB : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y η,
      ‖iteratedFDeriv ℝ j (fun z ↦ b z η) y‖ ≤ B * (1 + ‖η‖) ^ l)
    (hC : ∀ j ≤ m + Module.finrank ℝ V + 1, ∀ y ξ,
      ‖iteratedFDeriv ℝ j (fun z ↦ a x z ξ) y‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    fullAmplitudeOperator (fun x y ξ ↦ χ y • a x y ξ) (sourceIndependentOperator b u) x =
      sourceIndependentOperator (composedSymbol (fun x y ξ ↦ χ y • a x y ξ) b) u x := by
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
  have hgrowth (r : ℕ) (η : V) : (1 + ‖η‖) ^ r ≤
      2 ^ (r - 1) * (1 + ‖η‖ ^ r) := by
    simpa using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg η) r
  apply fullAmplitudeOperator_comp_sourceIndependentOperator_of_derivativeMass (fun x y ξ ↦ χ y • a x y ξ) b u x
    ((hχ.continuous.comp continuous_snd).smul ha.continuous) hb.continuous
    (fun _ ↦ hχc.smul_right) m (n + l) l
    (fun ξ η ↦ contDiff_symbolPlaneWave_smul (fun y ↦ χ y • a x y ξ) b η n (hχ.smul (haξ ξ)) (hbη η))
    (compositionSourceBound χ n B C * 2 ^ (n + l - 1))
    (B * 2 ^ (l - 1))
  · intro y η
    have hh : ‖b y η‖ ≤ B * (1 + ‖η‖) ^ l := by
      simpa only [norm_iteratedFDeriv_zero] using hB 0 (Nat.zero_le _) y η
    exact hh.trans ((mul_le_mul_of_nonneg_left (hgrowth l η) hB0).trans_eq (by ring))
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
