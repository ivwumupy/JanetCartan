module

public import JanetCartan.Analysis.Fourier.Periodic
public import JanetCartan.Analysis.Iteration.AdaptiveSchedule
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Scales
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.Neighborhood
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite prefixes for the Section 9 correction step

`main:eq:history-data` and `main:sec:convergence`. The correction producer and
adaptive recursion share ordinary `Fin j` functions. Appending is `Fin.snoc`;
restricting to a shorter prefix is composition with `Fin.castLE`. No entries
after the current stage are part of the data.

`finiteHistoryMap_eq_currentHistoryMap` connects this finite API to the existing
history estimates and the smooth-series consumer in `Iteration.MetricLimit`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {n N j : ℕ}

/-- Section 9, `main:sec:convergence`: the current map formed from exactly the
already constructed increments. This is the finite-prefix variant of
`currentHistoryMap`, with periodic lifts in the existing unit-torus convention. -/
def finiteHistoryMap (G : Euclidean n → Euclidean N)
    (u : Fin j → Torus n → Euclidean N) : Euclidean n → Euclidean N :=
  fun x ↦ G x + ∑ i, periodicLift (u i) x

/-- `main:eq:history-data`: the prospective increment budgets for a finite
history. Each order is at least `kMin`; the Fourier support constant is exactly
two, and the extra power one in the L² bound absorbs the step constant later.
The scale and all losses are the fixed manuscript definitions. -/
def IsAdmissibleHistory (R₀ : ℝ) (kMin : ℕ)
    (u : Fin j → Torus n → Euclidean N) (ell : Fin j → ℕ) : Prop :=
  ∀ i, kMin ≤ ell i ∧ IsSmoothPeriodic (u i) ∧
    HasFourierSupport (2 * iterationScale R₀ growthExponent i.val ^ bandExponent) (u i) ∧
    periodicL2Norm (u i) ≤
      iterationScale R₀ growthExponent i.val ^ (-(ell i : ℝ) + displacementLoss n + 1)

/-- `main:sec:convergence`: the empty prefix starts at the reference map. -/
@[simp] theorem finiteHistoryMap_empty (G : Euclidean n → Euclidean N)
    (u : Fin 0 → Torus n → Euclidean N) : finiteHistoryMap G u = G := by
  funext x
  simp [finiteHistoryMap]

/-- `main:sec:convergence`: the current map after appending one correction. -/
@[simp] theorem finiteHistoryMap_snoc (G : Euclidean n → Euclidean N)
    (u : Fin j → Torus n → Euclidean N) (U : Torus n → Euclidean N) :
    finiteHistoryMap G (Fin.snoc u U) = finiteHistoryMap G u + periodicLift U := by
  funext x
  simp [finiteHistoryMap, Fin.sum_univ_castSucc, add_assoc]

/-- `main:sec:convergence`: the finite-prefix map agrees with the existing
natural-index partial sum, used by the history estimates and metric-limit API. -/
theorem finiteHistoryMap_eq_currentHistoryMap (G : Euclidean n → Euclidean N)
    (u : ℕ → Torus n → Euclidean N) (j : ℕ) :
    finiteHistoryMap G (fun i : Fin j ↦ u i.val) =
      currentHistoryMap G (fun i ↦ periodicLift (u i)) j := by
  funext x
  exact congrArg (G x + ·) (Fin.sum_univ_eq_sum_range (fun i ↦ periodicLift (u i) x) j)

/-- `main:eq:history-data`: an empty history has no increment obligations. -/
@[simp] theorem isAdmissibleHistory_empty (R₀ : ℝ) (kMin : ℕ)
    (u : Fin 0 → Torus n → Euclidean N) (ell : Fin 0 → ℕ) :
    IsAdmissibleHistory R₀ kMin u ell := by
  intro i
  exact Fin.elim0 i

/-- `main:eq:history-data`: appending checks precisely the new increment at
scale `R_j`, in addition to the old finite history. -/
@[simp] theorem isAdmissibleHistory_snoc_iff {R₀ : ℝ} {kMin k : ℕ}
    {u : Fin j → Torus n → Euclidean N} {ell : Fin j → ℕ}
    {U : Torus n → Euclidean N} :
    IsAdmissibleHistory R₀ kMin (Fin.snoc u U) (Fin.snoc ell k) ↔
      IsAdmissibleHistory R₀ kMin u ell ∧ kMin ≤ k ∧ IsSmoothPeriodic U ∧
        HasFourierSupport (2 * iterationScale R₀ growthExponent j ^ bandExponent) U ∧
        periodicL2Norm U ≤
          iterationScale R₀ growthExponent j ^ (-(k : ℝ) + displacementLoss n + 1) := by
  simp only [IsAdmissibleHistory, Fin.forall_fin_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

/-- `main:eq:history-data`: every shorter prefix of an admissible finite
history is admissible, with the same initial scale and minimum order. -/
theorem IsAdmissibleHistory.prefix {R₀ : ℝ} {kMin m : ℕ}
    {u : Fin j → Torus n → Euclidean N} {ell : Fin j → ℕ}
    (h : IsAdmissibleHistory R₀ kMin u ell) (hm : m ≤ j) :
    IsAdmissibleHistory R₀ kMin (fun i : Fin m ↦ u (i.castLE hm))
      (fun i : Fin m ↦ ell (i.castLE hm)) := by
  intro i
  exact h (i.castLE hm)

/-- `main:sec:convergence`: appending an increment with the prospective budgets
preserves admissibility. The recursion must establish its L² budget explicitly. -/
theorem IsAdmissibleHistory.snoc {R₀ : ℝ} {kMin k : ℕ}
    {u : Fin j → Torus n → Euclidean N} {ell : Fin j → ℕ}
    {U : Torus n → Euclidean N} (h : IsAdmissibleHistory R₀ kMin u ell)
    (hk : kMin ≤ k) (hU : IsSmoothPeriodic U)
    (hband : HasFourierSupport (2 * iterationScale R₀ growthExponent j ^ bandExponent) U)
    (hL2 : periodicL2Norm U ≤
      iterationScale R₀ growthExponent j ^ (-(k : ℝ) + displacementLoss n + 1)) :
    IsAdmissibleHistory R₀ kMin (Fin.snoc u U) (Fin.snoc ell k) :=
  isAdmissibleHistory_snoc_iff.mpr ⟨h, hk, hU, hband, hL2⟩

/-- `main:sec:convergence`: finite current maps are smooth when the reference
is smooth. This supplies regularity to the history and metric-limit consumers. -/
theorem IsAdmissibleHistory.contDiff_finiteHistoryMap {R₀ : ℝ} {kMin : ℕ}
    {G : Euclidean n → Euclidean N} {u : Fin j → Torus n → Euclidean N}
    {ell : Fin j → ℕ} (h : IsAdmissibleHistory R₀ kMin u ell)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (finiteHistoryMap G u) :=
  hG.add (ContDiff.sum (fun i _ ↦ (h i).2.1.2))

end JanetCartan
