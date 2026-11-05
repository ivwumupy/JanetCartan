module

public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingTemplate

/-!
# One measured-target budget, independent of the smoothing accuracy

For `new:eq:source-bound` and the fixed constants of `main:thm:step`, the
finite-moment order may vary from stage to stage but the Picard and Fourier
mass budgets cannot simply depend on every future order. The sharp estimate
for the specified original tensor has the extra power `1 - separationExponent`.
Use it at the per-order frequency threshold for finitely many low orders. At
all higher derivatives only finitely many smaller smoothing orders have to be
included in the uniform constant. No regularity in the smoothing order or
bound on the growth of its constants is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing

/-- Zero-extension in the unused order zero, solely for the finite sums of
prehistory constants. The underlying finite-moment source is never changed. -/
def targetOrderCost (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (m q : ℕ) : ℝ :=
  if hm : 1 ≤ m then targetBudget n D m hm CM q else 0

theorem targetOrderCost_nonneg (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (m q : ℕ) :
    0 ≤ targetOrderCost n D CM m q := by
  unfold targetOrderCost
  split
  · exact targetBudget_nonneg _ _ _ _ _ _
  · rfl

/-- Fixed at each derivative order before the smoothing order and the history.
In particular this choice never takes a supremum over unbounded future orders. -/
def uniformTargetBudget (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (q : ℕ) : ℝ :=
  1 + ∑ m ∈ Finset.range (q+1), targetOrderCost n D CM m q

theorem one_le_uniformTargetBudget (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (q : ℕ) :
    1 ≤ uniformTargetBudget n D CM q := by
  unfold uniformTargetBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ ↦ targetOrderCost_nonneg n D CM m q)

/-- A single numerical threshold per smoothing order, before any history, that
also reaches the true finite-moment threshold on the same physical core. -/
def uniformTargetFrequency (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  max (targetFrequency n D m hm) (max 1
    ((∑ q ∈ Finset.range (m+1), targetOrderCost n D CM m q) ^ (1 / (1 - separationExponent))))

theorem targetFrequency_le_uniform (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    targetFrequency n D m hm ≤ uniformTargetFrequency n D CM m hm := le_max_left _ _

/-- The same `h R^(q-s₀)_+` bound holds for every derivative order, with a
budget before the variable smoothing order. Only the numerical stage reach
is allowed to depend on that accuracy (`new:eq:source-bound`). -/
theorem target_sharp_le_uniform (n : ℕ) (D : LocalDomain) (CM : ℕ → ℝ)
    (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : uniformTargetFrequency n D CM m hm ≤ R) (q : ℕ) :
    targetBudget n D m hm CM q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) ≤
      uniformTargetBudget n D CM q * R ^ (-separationExponent) * R ^ (q - RevisedScales.sourceOrder n) := by
  let A := targetOrderCost n D CM
  let K := ∑ k ∈ Finset.range (m+1), A m k
  let C := uniformTargetBudget n D CM q
  have hα : 0 < 1 - separationExponent := by norm_num [separationExponent]
  have h1 : 1 ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRp : 0 < R := zero_lt_one.trans_le h1
  have hK : 0 ≤ K := Finset.sum_nonneg fun k _ ↦ targetOrderCost_nonneg _ _ _ _ _
  have hp : K ^ (1 / (1 - separationExponent)) ≤ R :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hKp : K ≤ R ^ (1 - separationExponent) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hK _) hp hα.le
    rwa [← Real.rpow_mul hK, div_mul_cancel₀ _ hα.ne', Real.rpow_one] at h
  have hC : 1 ≤ C := one_le_uniformTargetBudget _ _ _ _
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hpow : 1 ≤ R ^ (1 - separationExponent) := Real.one_le_rpow h1 hα.le
  have hcost : A m q ≤ C * R ^ (1 - separationExponent) := by
    by_cases hq : q ≤ m
    · have hk : A m q ≤ K := Finset.single_le_sum (f := fun k ↦ A m k)
        (fun k _ ↦ targetOrderCost_nonneg _ _ _ _ _) (Finset.mem_range.mpr (by omega))
      exact (hk.trans hKp).trans (le_mul_of_one_le_left (zero_le_one.trans hpow) hC)
    · have hm' : m ∈ Finset.range (q+1) := Finset.mem_range.mpr (by omega)
      have hsmall := Finset.single_le_sum (f := fun k ↦ A k q)
        (fun k _ ↦ targetOrderCost_nonneg _ _ _ _ _) hm'
      have he : A m q ≤ C := hsmall.trans (le_add_of_nonneg_left zero_le_one)
      exact he.trans (le_mul_of_one_le_right hC₀ hpow)
  have hn : targetBudget n D m hm CM q = A m q := by simp [A, targetOrderCost, hm]
  have hq : (q : ℝ) ≤ (RevisedScales.sourceOrder n : ℝ) + ((q - RevisedScales.sourceOrder n : ℕ) : ℝ) := by
    exact_mod_cast (show q ≤ RevisedScales.sourceOrder n + (q - RevisedScales.sourceOrder n) by omega)
  have hgap := (RevisedScales.source_order_and_forcing_gap n).2.2.1
  calc
    _ ≤ (C * R ^ (1 - separationExponent)) * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by
      rw [hn]; exact mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hRp.le _)
    _ = C * R ^ ((1 - separationExponent) + ((q : ℝ) - 2 * RevisedScales.forcingExponent n)) := by
      rw [mul_assoc, ← Real.rpow_add hRp]
    _ ≤ C * R ^ (-separationExponent + ((q - RevisedScales.sourceOrder n : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 ?_) hC₀
      linarith only [hgap,hq]
    _ = _ := by rw [Real.rpow_add hRp, Real.rpow_natCast, ← mul_assoc]

open DefectSmoothing LocalSobolev CurrentMean PhysicalSmoothing
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

/-- The target constructed from the actual finite-moment tensor enjoys the
prehistory budget simultaneously at all derivatives, while its numerical stage
reach is allowed to depend on the requested approximation order. -/
theorem measure_normalized_history_uniform {n : ℕ} (D : LocalDomain) (G : FlatReference n)
    (CM : ℕ → ℝ) (hCM : ∀ q, 0 ≤ CM q) (R₀ : ℝ) (hR₀ : 2 ≤ R₀) (j : ℕ)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
    (reserve : ℕ) (Cper : Torus n → MetricTensor n →L[ℝ] Euclidean n)
    (hCper : IsSmoothPeriodic Cper)
    (hprofile : HasDerivativeProfile (fundamentalCell n) (periodicLift Cper) reserve (currentCoefficientScale R₀ j) CM)
    (m : ℕ) (hm : 1 ≤ m) (gs : MetricField n) (hgs : ContDiffOn ℝ ∞ gs (D.chart n))
    (δ : ℝ) (hpos : 0 < δ) (hR : uniformTargetFrequency n D CM m hm ≤ iterationScale R₀ growthExponent j)
    (hsmall : cNorm (D.core n) 0 (inducedMetric (RevisedGlobal.finiteMap G.map u) - gs) ≤ δ ^ 2) :
    let R := iterationScale R₀ growthExponent j
    ∃ target : SmoothResidual n,
      (∀ z, target.val z () = Cper z (tensorPeriodization (normalizedSource D R m δ gs G.map u) z)) ∧
      (∀ q : ℕ, periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
        targetBudget n D m hm CM q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n)) ∧
      ∀ q : ℕ, periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
        uniformTargetBudget n D CM q * R ^ (-separationExponent) * R ^ (q - RevisedScales.sourceOrder n) := by
  intro R
  obtain ⟨target,ht,hsharp,_⟩ := measure_normalized_history D G CM hCM R₀ hR₀ j u reserve Cper hCper hprofile
    m hm gs hgs δ hpos ((targetFrequency_le_uniform n D CM m hm).trans hR) hsmall
  exact ⟨target,ht,hsharp,fun q ↦ (hsharp q).trans (target_sharp_le_uniform n D CM m hm hR q)⟩

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end
