module

public import JanetCartan.Analysis.Operator.RetardedSobolev.TimeMultiplication

/-!
# All-order time energies of the cutoff retarded operators

The time part of `app:ch_osc:prop:osc-retarded-tube`, with both real cutoffs.
Multiplication, primitive integration, and multiplication give a gain of one
classical time derivative. These estimates are anisotropic; mixed transverse
estimates and the spatial Sobolev assembly are separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.RetardedSobolev

variable {Y : Type*} [MeasurableSpace Y]

/-- The concrete lower operator gains one time order with both cutoffs
(`app:ch_osc:prop:osc-retarded-tube`). The constant is uniform in the input and
uses bounded measurable cutoff jets through the indicated orders. -/
theorem lower_timeSobolev_succ_bound (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hin : ∀ y, ContDiff ℝ m (fun t ↦ χin (t, y)))
    (hout : ∀ y, ContDiff ℝ (m + 1 : ℕ) (fun t ↦ χout (t, y)))
    (hfcont : ∀ y, ContDiff ℝ m (fun t ↦ f (t, y)))
    (hmi : ∀ j ≤ m, AEStronglyMeasurable
      (fun p : Y × ℝ ↦ timeJet j (fun x ↦ (χin x : ℂ)) (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))))
    (hmo : ∀ j ≤ m + 1, AEStronglyMeasurable
      (fun p : Y × ℝ ↦ timeJet j (fun x ↦ (χout x : ℂ)) (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))))
    {Cin Cout : ℝ} (hCin : 0 ≤ Cin) (hCout : 0 ≤ Cout)
    (hbi : ∀ j ≤ m, ∀ᵐ p : Y × ℝ ∂ν.prod (volume.restrict (Icc a b)),
      ‖timeJet j (fun x ↦ (χin x : ℂ)) (p.2, p.1)‖ ≤ Cin)
    (hbo : ∀ j ≤ m + 1, ∀ᵐ p : Y × ℝ ∂ν.prod (volume.restrict (Icc a b)),
      ‖timeJet j (fun x ↦ (χout x : ℂ)) (p.2, p.1)‖ ≤ Cout)
    (hf : TimeJetsMemLp ν a b m f) :
    TimeJetsMemLp ν a b (m + 1) (Retarded.lower a χin χout f) ∧
      timeSobolevEnergy ν a b (m + 1) (Retarded.lower a χin χout f) ≤
        (timeMultiplierConstant (m + 1) Cout * (1 + (b - a) ^ 2) *
          timeMultiplierConstant m Cin) * timeSobolevEnergy ν a b m f := by
  let g : ℝ × Y → ℂ := fun x ↦ (χin x : ℂ) * f x
  let P := Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) g
  have hci y : ContDiff ℝ m (fun t ↦ (χin (t, y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hin y)
  have hco y : ContDiff ℝ (m + 1 : ℕ) (fun t ↦ (χout (t, y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hout y)
  have hcg y : ContDiff ℝ m (fun t ↦ g (t, y)) := (hci y).mul (hfcont y)
  have hinner := timeSobolev_mul_bound ν a b m (fun x ↦ (χin x : ℂ)) f
    hci hfcont hmi hCin hbi hf
  have hprim := lower_one_timeSobolev_bound ν a b hab m g
    (fun y ↦ (hcg y).continuous) hinner.1
  have hcp y : ContDiff ℝ (m + 1 : ℕ) (fun t ↦ P (t, y)) := by
    simpa only [P, Retarded.lower, Complex.ofReal_one, one_mul] using
      contDiff_lowerPrimitive (hcg y) a
  have houter := timeSobolev_mul_bound ν a b (m + 1) (fun x ↦ (χout x : ℂ)) P
    hco hcp hmo hCout hbo hprim.1
  have heq : (fun x ↦ (χout x : ℂ) * P x) = Retarded.lower a χin χout f := by
    funext x
    simp only [P, g, Retarded.lower, Complex.ofReal_one, one_mul]
  rw [heq] at houter
  refine ⟨houter.1, houter.2.trans ?_⟩
  calc
    _ ≤ timeMultiplierConstant (m + 1) Cout *
        ((1 + (b - a) ^ 2) * timeSobolevEnergy ν a b m g) :=
      mul_le_mul_of_nonneg_left hprim.2 (timeMultiplierConstant_nonneg _ _)
    _ ≤ timeMultiplierConstant (m + 1) Cout *
        ((1 + (b - a) ^ 2) *
          (timeMultiplierConstant m Cin * timeSobolevEnergy ν a b m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner.2 (by positivity))
        (timeMultiplierConstant_nonneg _ _)
    _ = _ := by ring

/-- The same time-order gain for the literal upper adjoint
(`app:ch_osc:eq:retarded-literal-adjoint`). The exterior cutoff is `χin`. -/
theorem upper_timeSobolev_succ_bound (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (χin χout : ℝ × Y → ℝ) (f : ℝ × Y → ℂ)
    (hout : ∀ y, ContDiff ℝ m (fun t ↦ χout (t, y)))
    (hin : ∀ y, ContDiff ℝ (m + 1 : ℕ) (fun t ↦ χin (t, y)))
    (hfcont : ∀ y, ContDiff ℝ m (fun t ↦ f (t, y)))
    (hmo : ∀ j ≤ m, AEStronglyMeasurable
      (fun p : Y × ℝ ↦ timeJet j (fun x ↦ (χout x : ℂ)) (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))))
    (hmi : ∀ j ≤ m + 1, AEStronglyMeasurable
      (fun p : Y × ℝ ↦ timeJet j (fun x ↦ (χin x : ℂ)) (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))))
    {Cout Cin : ℝ} (hCout : 0 ≤ Cout) (hCin : 0 ≤ Cin)
    (hbo : ∀ j ≤ m, ∀ᵐ p : Y × ℝ ∂ν.prod (volume.restrict (Icc a b)),
      ‖timeJet j (fun x ↦ (χout x : ℂ)) (p.2, p.1)‖ ≤ Cout)
    (hbi : ∀ j ≤ m + 1, ∀ᵐ p : Y × ℝ ∂ν.prod (volume.restrict (Icc a b)),
      ‖timeJet j (fun x ↦ (χin x : ℂ)) (p.2, p.1)‖ ≤ Cin)
    (hf : TimeJetsMemLp ν a b m f) :
    TimeJetsMemLp ν a b (m + 1) (Retarded.upper b χin χout f) ∧
      timeSobolevEnergy ν a b (m + 1) (Retarded.upper b χin χout f) ≤
        (timeMultiplierConstant (m + 1) Cin * (1 + (b - a) ^ 2) *
          timeMultiplierConstant m Cout) * timeSobolevEnergy ν a b m f := by
  let g : ℝ × Y → ℂ := fun x ↦ (χout x : ℂ) * f x
  let P := Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) g
  have hco y : ContDiff ℝ m (fun t ↦ (χout (t, y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hout y)
  have hci y : ContDiff ℝ (m + 1 : ℕ) (fun t ↦ (χin (t, y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hin y)
  have hcg y : ContDiff ℝ m (fun t ↦ g (t, y)) := (hco y).mul (hfcont y)
  have hinner := timeSobolev_mul_bound ν a b m (fun x ↦ (χout x : ℂ)) f
    hco hfcont hmo hCout hbo hf
  have hprim := upper_one_timeSobolev_bound ν a b hab m g
    (fun y ↦ (hcg y).continuous) hinner.1
  have hcp y : ContDiff ℝ (m + 1 : ℕ) (fun t ↦ P (t, y)) := by
    simpa only [P, Retarded.upper, Complex.ofReal_one, one_mul] using
      contDiff_upperPrimitive (hcg y) b
  have houter := timeSobolev_mul_bound ν a b (m + 1) (fun x ↦ (χin x : ℂ)) P
    hci hcp hmi hCin hbi hprim.1
  have heq : (fun x ↦ (χin x : ℂ) * P x) = Retarded.upper b χin χout f := by
    funext x
    simp only [P, g, Retarded.upper, Complex.ofReal_one, one_mul]
  rw [heq] at houter
  refine ⟨houter.1, houter.2.trans ?_⟩
  calc
    _ ≤ timeMultiplierConstant (m + 1) Cin *
        ((1 + (b - a) ^ 2) * timeSobolevEnergy ν a b m g) :=
      mul_le_mul_of_nonneg_left hprim.2 (timeMultiplierConstant_nonneg _ _)
    _ ≤ timeMultiplierConstant (m + 1) Cin *
        ((1 + (b - a) ^ 2) *
          (timeMultiplierConstant m Cout * timeSobolevEnergy ν a b m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner.2 (by positivity))
        (timeMultiplierConstant_nonneg _ _)
    _ = _ := by ring

end JanetCartan.RetardedSobolev
