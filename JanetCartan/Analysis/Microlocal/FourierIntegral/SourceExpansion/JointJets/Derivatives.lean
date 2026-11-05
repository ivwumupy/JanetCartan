module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets.ParameterIntegral

/-!
# Ordered output and physical covector jets

Specialized coordinate jets for the source coefficient estimate in
`app:ch_regular_base:thm:actual-calculus`, Step 1. Left indices differentiate
output; right indices differentiate the original physical covector.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}

/-- Physical output/covector direction for the source expansion in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def coefficientDirection : Fin n ⊕ Fin n → Euclidean n × Euclidean n
  | Sum.inl i => (EuclideanSpace.single i 1, 0)
  | Sum.inr i => (0, EuclideanSpace.single i 1)

/-- Ordered actual derivatives in the two retained variables, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def scalarCoefficientJet : List (Fin n ⊕ Fin n) →
    ((Euclidean n × Euclidean n) → ℂ) → (Euclidean n × Euclidean n) → ℂ
  | [], f => f
  | i :: is, f => fun p ↦ fderiv ℝ (scalarCoefficientJet is f) p (coefficientDirection i)

/-- The same physical derivatives, entrywise in the Frobenius matrix,
for `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
def matrixCoefficientJet (is : List (Fin n ⊕ Fin n))
    (a : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x η : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j ↦ scalarCoefficientJet is (fun p ↦ a p.1 p.2 i j) (x, η)

/-- Output/covector derivatives of the full amplitude, retaining its source
variable and every original cutoff (`app:ch_regular_base:thm:actual-calculus`,
Step 1). The source derivatives are the existing matrix coordinate API. -/
def fullAmplitudeParameterJet (is : List (Fin n ⊕ Fin n)) (A : FullAmplitude n r) :
    FullAmplitude n r := fun x y η ↦ matrixCoefficientJet is (fun x η ↦ A x y η) x η

/-- Smoothness of the actual mixed parameter jets, also jointly in source,
used in the coefficient estimate of `app:ch_regular_base:thm:actual-calculus`. -/
theorem contDiff_scalarCoefficientJet_joint
    {f : (Euclidean n × Euclidean n) × Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin n ⊕ Fin n)) :
    ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      scalarCoefficientJet is (fun q ↦ f (q, p.2)) p.1) := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    exact (ContDiff.fderiv
      (ih.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst
        (by simp)).clm_apply contDiff_const

private theorem scalarCoefficientJet_zero (is : List (Fin n ⊕ Fin n)) :
    scalarCoefficientJet is (fun _ ↦ 0) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [scalarCoefficientJet, ih]; rfl

/-- All mixed parameter derivatives commute with the actual integral,
with no loss of physical covector normalization
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem scalarCoefficientJet_scalarCoefficient
    {f : (Euclidean n × Euclidean n) × Euclidean n → ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin n ⊕ Fin n))
    (ℓ : ℝ) (k : Fin n → ℤ) (p : Euclidean n × Euclidean n) :
    scalarCoefficientJet is (fun q ↦ scalarCoefficient ℓ (fun y ↦ f (q, y)) k) p =
      scalarCoefficient ℓ (fun y ↦ scalarCoefficientJet is (fun q ↦ f (q, y)) p) k := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
    simp only [scalarCoefficientJet]
    have he := funext ih
    rw [he]
    exact fderiv_scalarCoefficient_parameter_apply
      (contDiff_scalarCoefficientJet_joint hf is) ℓ k p (coefficientDirection i)

/-- Matrix coefficients retain every actual output/covector derivative.
This is the derivative identity used by the final source operator-series
assembly (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem matrixCoefficientJet_matrixCoefficient (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2))
    (is : List (Fin n ⊕ Fin n)) (ℓ : ℝ) (k : Fin n → ℤ) (x η : Euclidean n) :
    matrixCoefficientJet is (matrixCoefficient ℓ A k) x η =
      matrixCoefficient ℓ (fullAmplitudeParameterJet is A) k x η := by
  ext i j
  exact scalarCoefficientJet_scalarCoefficient
    (((matrixEntryEvaluation i j).contDiff.comp hA).comp
      (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd))) is ℓ k (x, η)

/-- Each actual matrix coefficient is jointly smooth entrywise in output
and physical covector, as required by the symbol seminorm of
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem contDiff_matrixCoefficient_entry (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) (ℓ : ℝ) (k : Fin n → ℤ) (i j : Fin r) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ matrixCoefficient ℓ A k p.1 p.2 i j) :=
  contDiff_scalarCoefficient_parameter
    (((matrixEntryEvaluation i j).contDiff.comp hA).comp
      (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd))) ℓ k

/-- Joint smoothness supplies the source smoothness of each mixed jet;
consumed by source integration by parts in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem contDiff_fullAmplitudeParameterJet_entry (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2)) (is : List (Fin n ⊕ Fin n)) (x η : Euclidean n)
    (i j : Fin r) :
    ContDiff ℝ ∞ (fun y ↦ fullAmplitudeParameterJet is A x y η i j) :=
  (contDiff_scalarCoefficientJet_joint
    (((matrixEntryEvaluation i j).contDiff.comp hA).comp
      (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd))) is).comp
        (contDiff_const.prodMk contDiff_id)

/-- Uniform source support is retained by all actual output/covector jets.
No support hypothesis on derivatives is needed in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem supportedInCenteredBox_fullAmplitudeParameterJet {R : ℝ} (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (is : List (Fin n ⊕ Fin n)) (x η : Euclidean n) (i j : Fin r) :
    SupportedInCenteredBox R (fun y ↦ fullAmplitudeParameterJet is A x y η i j) := by
  intro y hy a
  by_contra ha
  have he : (fun p : Euclidean n × Euclidean n ↦ A p.1 y p.2 i j) = fun _ ↦ 0 := by
    funext p
    by_contra h
    exact ha (hs p.1 p.2 i j y h a)
  apply hy
  change scalarCoefficientJet is (fun p ↦ A p.1 y p.2 i j) (x, η) = 0
  rw [he, scalarCoefficientJet_zero]
  rfl

end JanetCartan.FourierIntegral.SourceExpansion
