module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Physical covector dilations for the full normal amplitude

The rescaling identities used by `exists_extendedCrossNormalAmplitude_symbol_bound`
retain both positions and every primitive cutoff in
`app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Dilate only the physical covector (`app:ch_regular_base:setup:finite-calculus`). -/
def normalFrequencyDilation (ρ : ℝ) : NormalVariables n →L[ℝ] NormalVariables n :=
  let X := ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n × Euclidean n)
  let Y := (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))
  let Z := (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp
    (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n × Euclidean n))
  X.prod (Y.prod (ρ • Z))

/-- Both physical positions are fixed by the dilation of
`app:ch_regular_base:setup:finite-calculus`. -/
@[simp] theorem normalFrequencyDilation_apply (ρ : ℝ) (z : NormalVariables n) :
    normalFrequencyDilation ρ z = (z.1, (z.2.1, ρ • z.2.2)) := rfl

private def dilationEquiv (ρ : ℝ) (hρ : ρ ≠ 0) :
    NormalVariables n ≃L[ℝ] NormalVariables n :=
  (ContinuousLinearEquiv.refl ℝ (Euclidean n)).prodCongr
    ((ContinuousLinearEquiv.refl ℝ (Euclidean n)).prodCongr
      (LinearEquiv.smulOfNeZero ℝ (Euclidean n) ρ hρ).toContinuousLinearEquiv)

/-- Linear rescaling of every mixed jet, without a regularity assumption.
This also applies to the literal zero extension at a chart boundary.
Source: `app:ch_regular_base:setup:finite-calculus`. -/
theorem iteratedFDeriv_normalFrequencyDilation
    (f : NormalVariables n → Matrix (Fin r) (Fin r) ℂ)
    {ρ : ℝ} (hρ : ρ ≠ 0) (k : ℕ) (z : NormalVariables n)
    (v : Fin k → NormalVariables n) :
    iteratedFDeriv ℝ k (f ∘ normalFrequencyDilation ρ) z v =
      iteratedFDeriv ℝ k f (normalFrequencyDilation ρ z)
        (fun i ↦ normalFrequencyDilation ρ (v i)) := by
  have h := (dilationEquiv (n := n) ρ hρ).iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (x := z) (mem_univ _) k
  have he : (dilationEquiv (n := n) ρ hρ : NormalVariables n → NormalVariables n) =
      normalFrequencyDilation ρ := by
    funext w
    rfl
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe, he]
    using congrArg (fun T ↦ T v) h

/-- Constant nonzero normalization commutes with all jets, including jets
of an extension. Source: `app:ch_regular_base:setup:finite-calculus`. -/
theorem iteratedFDeriv_normalization
    (f : NormalVariables n → Matrix (Fin r) (Fin r) ℂ)
    {a : ℝ} (ha : a ≠ 0) (k : ℕ) (z : NormalVariables n) :
    iteratedFDeriv ℝ k (fun z ↦ a • f z) z = a • iteratedFDeriv ℝ k f z := by
  exact (LinearEquiv.smulOfNeZero ℝ (Matrix (Fin r) (Fin r) ℂ) a ha).toContinuousLinearEquiv.iteratedFDeriv_comp_left

/-- Normalize an original order-`m` matrix, with all its cutoffs retained.
Source: `app:ch_regular_base:setup:finite-calculus`. -/
def normalizedNormalMatrix (ρ m : ℝ)
    (A : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (x u : Euclidean n) := ρ ^ (-m) • A x (ρ • u)

/-- The supplied full inverse has order one, with positions unscaled.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
def normalizedNormalInverse (ρ : ℝ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (x y ξ : Euclidean n) := ρ⁻¹ • η x y (ρ • ξ)

/-- The original averaged-gradient Jacobian has order zero.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
def normalizedNormalJacobian (ρ : ℝ)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (x y u : Euclidean n) := J x y (ρ • u)

/-- Exact normalization of the full two-position numerator and Jacobian.
No homogeneity or transformed-amplitude estimate is assumed.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem crossNormalAmplitude_normalized
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {ρ : ℝ} (hρ : 0 < ρ) (p q : ℝ) (z : NormalVariables n) :
    crossNormalAmplitude (normalizedNormalMatrix ρ p A) (normalizedNormalMatrix ρ q B)
      (normalizedNormalInverse ρ η) (normalizedNormalJacobian ρ J) z.1 z.2.1 z.2.2 =
      ρ ^ (-(p + q)) • crossNormalAmplitude A B η J z.1 z.2.1 (ρ • z.2.2) := by
  simp only [crossNormalAmplitude, crossNormalNumerator, normalizedNormalMatrix,
    normalizedNormalInverse, normalizedNormalJacobian, smul_inv_smul₀ hρ.ne',
    Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul]
  simp only [smul_smul]
  rw [neg_add, Real.rpow_add hρ]
  congr 1
  ring

/-- Mixed physical/covector derivatives acquire exactly one inverse frequency
power per covector direction. The set `s` records those directions; all other
directions may vary either or both physical positions. Source:
`app:ch_regular_base:setup:finite-calculus`. -/
theorem iteratedFDeriv_normalized_mixed
    (f : NormalVariables n → Matrix (Fin r) (Fin r) ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℝ) (k : ℕ) (z : NormalVariables n)
    (s : Finset (Fin k)) (v : Fin k → NormalVariables n)
    (hvξ : ∀ i ∈ s, (v i).1 = 0 ∧ (v i).2.1 = 0)
    (hvxy : ∀ i ∉ s, (v i).2.2 = 0) :
    iteratedFDeriv ℝ k f (normalFrequencyDilation ρ z) v =
      ρ ^ (m - s.card) • iteratedFDeriv ℝ k
        (fun w ↦ ρ ^ (-m) • f (normalFrequencyDilation ρ w)) z v := by
  have hd (i : Fin k) : normalFrequencyDilation ρ (v i) =
      (if i ∈ s then ρ else 1) • v i := by
    by_cases hi : i ∈ s
    · rcases hvξ i hi with ⟨hx, hy⟩
      apply Prod.ext
      · simp [hi, hx]
      apply Prod.ext <;> simp [hi, hy]
    · apply Prod.ext
      · simp [hi]
      apply Prod.ext <;> simp [hi, hvxy i hi]
  have hp : (∏ i : Fin k, if i ∈ s then ρ else 1) = ρ ^ s.card := by
    rw [Finset.prod_ite]
    simp
  rw [iteratedFDeriv_normalization _ (Real.rpow_pos_of_pos hρ _).ne']
  change _ = ρ ^ (m - s.card) • (ρ ^ (-m) •
    iteratedFDeriv ℝ k (f ∘ normalFrequencyDilation ρ) z v)
  rw [iteratedFDeriv_normalFrequencyDilation f hρ.ne', show
    (fun i ↦ normalFrequencyDilation ρ (v i)) =
      (fun i ↦ (if i ∈ s then ρ else 1) • v i) from funext hd,
    ContinuousMultilinearMap.map_smul_univ, hp]
  simp only [smul_smul]
  rw [← Real.rpow_natCast, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
  rw [show m - (s.card : ℝ) + (-m + (s.card : ℝ)) = 0 by ring, Real.rpow_zero, one_smul]

/-- A normalized joint Frobenius bound implies every weighted mixed bound
with the exact covector derivative count. Source:
`app:ch_regular_base:setup:finite-calculus`. -/
theorem norm_iteratedFDeriv_mixed_le_of_normalized
    (f : NormalVariables n → Matrix (Fin r) (Fin r) ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℝ) (k : ℕ) (z : NormalVariables n)
    (s : Finset (Fin k)) (v : Fin k → NormalVariables n)
    (hvξ : ∀ i ∈ s, (v i).1 = 0 ∧ (v i).2.1 = 0)
    (hvxy : ∀ i ∉ s, (v i).2.2 = 0) (hv : ∀ i, ‖v i‖ ≤ 1)
    {C : ℝ} (hC : ‖iteratedFDeriv ℝ k
      (fun w ↦ ρ ^ (-m) • f (normalFrequencyDilation ρ w)) z‖ ≤ C) :
    ‖iteratedFDeriv ℝ k f (normalFrequencyDilation ρ z) v‖ ≤
      ρ ^ (m - s.card) * C := by
  rw [iteratedFDeriv_normalized_mixed f hρ m k z s v hvξ hvxy,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hρ _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hρ.le _)
  have heval := (iteratedFDeriv ℝ k
    (fun w ↦ ρ ^ (-m) • f (normalFrequencyDilation ρ w)) z).le_opNorm v
  have hprod : (∏ i, ‖v i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg (v i)) (fun i _ ↦ hv i)
  exact heval.trans ((mul_le_of_le_one_right (norm_nonneg _) hprod).trans hC)

end JanetCartan.FourierIntegral
