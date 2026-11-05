module

public import JanetCartan.Analysis.Iteration.BandHistory

/-!
# Extending an actual finite history

For `main:lem:history` and the Section 9 construction, the already constructed
increments have domain `Fin j`. Zero extension permits use of the all-index
history estimates without requiring any future correction.
-/

@[expose] public noncomputable section

namespace JanetCartan.FiniteHistoryBounds

/-- `main:eq:history-data`: extend only the known prefix, with zero afterwards. -/
def extendByZero {A : Type*} [Zero A] {j : ℕ} (u : Fin j → A) (i : ℕ) : A :=
  if h : i < j then u ⟨i, h⟩ else 0

/-- `main:eq:history-data`: future zero increments may use the fixed baseline order. -/
def extendOrder {j : ℕ} (k₀ : ℝ) (k : Fin j → ℝ) (i : ℕ) : ℝ :=
  if h : i < j then k ⟨i, h⟩ else k₀

/-- `main:lem:history`: zero extension agrees with every constructed increment. -/
@[simp] theorem extendByZero_coe {A : Type*} [Zero A] {j : ℕ}
    (u : Fin j → A) (i : Fin j) : extendByZero u i = u i := by
  simp [extendByZero, i.isLt]

/-- `main:lem:history`: the extension preserves the actual orders. -/
@[simp] theorem extendOrder_coe {j : ℕ} (k₀ : ℝ) (k : Fin j → ℝ) (i : Fin j) :
    extendOrder k₀ k i = k i := by
  simp [extendOrder, i.isLt]

variable {n j : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:history`: the actual current map, expressed using only `Fin j`. -/
def currentMap (G : EuclideanSpace ℝ (Fin n) → F) (u : Fin j → Torus n → F) :
    EuclideanSpace ℝ (Fin n) → F :=
  fun x ↦ G x + ∑ i, periodicLift (u i) x

omit [NormedSpace ℝ F] in
/-- `main:eq:history-current`: the all-index history map is the actual prefix sum. -/
theorem currentHistoryMap_extendByZero (G : EuclideanSpace ℝ (Fin n) → F)
    (u : Fin j → Torus n → F) :
    currentHistoryMap G (fun i ↦ periodicLift (extendByZero u i)) j = currentMap G u := by
  funext x
  simp only [currentHistoryMap, currentMap]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendByZero_coe]

/-- `main:eq:history-data`: smoothness of the extension is proved, including its tail. -/
theorem isSmoothPeriodic_extendByZero {u : Fin j → Torus n → F}
    (hu : ∀ i, IsSmoothPeriodic (u i)) (i : ℕ) :
    IsSmoothPeriodic (extendByZero u i) := by
  by_cases hi : i < j
  · simpa [extendByZero, hi] using hu ⟨i, hi⟩
  · simp only [extendByZero, dite_eq_right hi]
    exact ⟨continuous_const, contDiff_const⟩

/-- `main:eq:history-data`: exact support of the extension needs only prefix data. -/
theorem hasFourierSupport_extendByZero {u : Fin j → Torus n → F} {L : ℕ → ℝ}
    (hu : ∀ i : Fin j, HasFourierSupport (L i) (u i)) (i : ℕ) :
    HasFourierSupport (L i) (extendByZero u i) := by
  by_cases hi : i < j
  · simpa [extendByZero, hi] using hu ⟨i, hi⟩
  · simp [extendByZero, hi, HasFourierSupport, periodicFourierCoeff]

omit [NormedSpace ℝ F] in
/-- `main:eq:history-data`: the zero tail satisfies every nonnegative L² budget. -/
theorem periodicL2Norm_extendByZero_le {u : Fin j → Torus n → F}
    {R v B k₀ : ℝ} {k : Fin j → ℝ} (hR : 0 ≤ R)
    (hu : ∀ i, periodicL2Norm (u i) ≤ historyScale R v i ^ (-k i + B + 1))
    (i : ℕ) : periodicL2Norm (extendByZero u i) ≤
      historyScale R v i ^ (-extendOrder k₀ k i + B + 1) := by
  by_cases hi : i < j
  · simpa [extendByZero, extendOrder, hi] using hu ⟨i, hi⟩
  · simpa [extendByZero, hi, periodicL2Norm, historyScale] using
      Real.rpow_nonneg (Real.rpow_nonneg hR (v ^ i)) (-extendOrder k₀ k i + B + 1)

/-- `main:eq:history-data`: the fixed initial order also bounds the artificial tail. -/
theorem le_extendOrder {k₀ : ℝ} {k : Fin j → ℝ} (hk : ∀ i, k₀ ≤ k i) (i : ℕ) :
    k₀ ≤ extendOrder k₀ k i := by
  by_cases hi : i < j
  · simpa [extendOrder, hi] using hk ⟨i, hi⟩
  · simp [extendOrder, hi]

end JanetCartan.FiniteHistoryBounds
