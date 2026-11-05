module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.TransferAmplitudes

/-!
# Frequency cutoffs commute with nonlinear transfer

For `app:ch_regular_base:eq:graph-derivative-transfer`, all transfers differentiate
physical positions only. The literal frequency regularization therefore commutes
with every branch of the shared finite expansion. This supplies the identification
of the regularized coefficients in the weak-limit argument of `WeakTransfer`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Literal frequency regularization retaining both physical positions and masks.
Source: the regularization of `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def frequencyCutFullAmplitude (χ : Euclidean n → ℂ) (A : FullAmplitude n r) :
    FullAmplitude n r := fun x y η ↦ χ η • A x y η

private theorem partialDeriv_const_smul_matrix (c : ℂ)
    (f : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (x : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ c • f z) x i = c • partialDeriv f x i := by
  have h := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := f) c) x
  exact congrArg (fun L : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
    L (EuclideanSpace.single i 1)) h

/-- Frequency regularization commutes with the full forward remainder, including
both physical derivatives (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem graphTransferRemainder_frequencyCutFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (χ : Euclidean n → ℂ)
    (A : FullAmplitude n r) (i : Fin n) :
    graphTransferRemainder S i (frequencyCutFullAmplitude χ A) =
      frequencyCutFullAmplitude χ (graphTransferRemainder S i A) := by
  funext x y η
  simp only [graphTransferRemainder, frequencyCutFullAmplitude,
    partialDeriv_const_smul_matrix, smul_add, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

/-- Frequency regularization commutes with each forward datum branch.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphTransferDatum_frequencyCutFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (χ : Euclidean n → ℂ)
    (A : FullAmplitude n r) (i j : Fin n) :
    graphTransferDatum S i j (frequencyCutFullAmplitude χ A) =
      frequencyCutFullAmplitude χ (graphTransferDatum S i j A) := by
  funext x y η
  exact smul_comm _ _ _

/-- The literal reverse datum branch commutes with a frequency cutoff.
`C` is already conjugate-transposed at initialization, as in
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjointTransferDatum_frequencyCutFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (χ : Euclidean n → ℂ)
    (C : FullAmplitude n r) (i j : Fin n) :
    adjointTransferDatum S i j (frequencyCutFullAmplitude χ C) =
      frequencyCutFullAmplitude χ (adjointTransferDatum S i j C) := by
  funext x y η
  exact smul_comm _ _ _

/-- Frequency regularization commutes with the reverse remainder, including the
whole inverse-coefficient derivative (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem adjointTransferRemainder_frequencyCutFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (χ : Euclidean n → ℂ)
    (C : FullAmplitude n r) (i : Fin n) :
    adjointTransferRemainder S i (frequencyCutFullAmplitude χ C) =
      frequencyCutFullAmplitude χ (adjointTransferRemainder S i C) := by
  funext x y η
  simp only [adjointTransferRemainder, adjointTransferDatum_frequencyCutFullAmplitude,
    frequencyCutFullAmplitude, partialDeriv_const_smul_matrix, smul_add, Finset.smul_sum]

private theorem fullAmplitudeDerivativeTerms_map
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (F : FullAmplitude n r → FullAmplitude n r)
    (hR : ∀ i A, R i (F A) = F (R i A))
    (hP : ∀ i j A, P i j (F A) = F (P i j A))
    (A : FullAmplitude n r) (is : List (Fin n)) :
    fullAmplitudeDerivativeTerms R P (F A) is =
      (fullAmplitudeDerivativeTerms R P A is).map (fun p ↦ (F p.1, p.2)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [fullAmplitudeDerivativeTerms, ih, List.flatMap_map, List.map_flatMap]
    congr 1
    funext p
    simp [fullAmplitudeDerivativeStep, hR, hP, List.map_ofFn, Function.comp_def]

/-- Every regularized forward coefficient is the same frequency cutoff times the
corresponding unregularized coefficient, with datum word and multiplicity intact.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeTerms_forward_frequencyCutFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (χ : Euclidean n → ℂ)
    (A : FullAmplitude n r) (is : List (Fin n)) :
    fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S)
        (frequencyCutFullAmplitude χ A) is =
      (fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A is).map
        (fun p ↦ (frequencyCutFullAmplitude χ p.1, p.2)) := by
  exact fullAmplitudeDerivativeTerms_map _ _ _
    (fun i A ↦ graphTransferRemainder_frequencyCutFullAmplitude S χ A i)
    (fun i j A ↦ graphTransferDatum_frequencyCutFullAmplitude S χ A i j) A is

/-- The same cutoff compatibility for literal reverse amplitudes in original
coordinate order. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem fullAmplitudeDerivativeTerms_adjoint_frequencyCutFullAmplitude
    (S : Euclidean n → Euclidean n → ℝ) (χ : Euclidean n → ℂ)
    (C : FullAmplitude n r) (is : List (Fin n)) :
    fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S)
        (frequencyCutFullAmplitude χ C) is =
      (fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S) C is).map
        (fun p ↦ (frequencyCutFullAmplitude χ p.1, p.2)) := by
  exact fullAmplitudeDerivativeTerms_map _ _ _
    (fun i C ↦ adjointTransferRemainder_frequencyCutFullAmplitude S χ C i)
    (fun i j C ↦ adjointTransferDatum_frequencyCutFullAmplitude S χ C i j) C is

end JanetCartan.FourierIntegral
