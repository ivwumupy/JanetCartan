module

public import JanetCartan.Analysis.PhysicalBernstein.Basic
public import JanetCartan.Analysis.Iteration.AdaptiveSchedule
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised.StageLosses
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Physical finite histories for the revised iteration

In `main:eq:history-data` (paper-v2, §§16–18), the increments are functions on
Euclidean space, not periodic lifts. A smooth Fourier cutoff of the smooth,
compactly supported uncut field of `main:thm:step` gives a Schwartz function.
We use that concrete class, not a class with an assumed Bernstein estimate.
The metric, the radian Fourier band, and the Lebesgue L² norm are all evaluated
on the same global representatives.

`UniformHistoryCorrection` is the analytic obligation of `main:thm:step` and
`main:prop:current-scale`, not a proof of either. In particular its constants
and thresholds precede *all* histories and target parameters. Its recursive
consumer only needs accuracies `Q = 2k`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RevisedGlobal

variable {n N j : ℕ}

/-- `main:eq:history-current`: the current map formed from just the known prefix
of real global increments. There is no extension or periodization. -/
def finiteMap (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) : Euclidean n → Euclidean N :=
  fun x ↦ G x + ∑ i, u i x

/-- `main:eq:history-data`: the exact radian Fourier support and the absorbed
physical L² budget on every previously constructed increment. The fixed support
constant `B` is independent of the accuracy, the prefix and the target. -/
def IsAdmissibleHistory (B R₀ : ℝ) (kMin : ℕ)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin j → ℕ) : Prop :=
  ∀ i, let R := iterationScale R₀ growthExponent i.val
    kMin ≤ ell i ∧ PhysicalBernstein.HasFourierSupport (B * R ^ bandExponent) (u i) ∧
      PhysicalBernstein.physicalL2Norm (u i) ≤
        R ^ (-(ell i : ℝ) + RevisedScales.displacementLoss n + 1)

/-- `main:eq:initial-error`: the map of the empty physical prefix is exactly the reference. -/
@[simp] theorem finiteMap_empty (G : Euclidean n → Euclidean N)
    (u : Fin 0 → SchwartzMap (Euclidean n) (Euclidean N)) : finiteMap G u = G := by
  funext x
  simp [finiteMap]

/-- `main:eq:metric-induction`: appending a Schwartz increment adds its actual
pointwise representative to the current map. -/
@[simp] theorem finiteMap_snoc (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N))
    (U : SchwartzMap (Euclidean n) (Euclidean N)) :
    finiteMap G (Fin.snoc u U) = finiteMap G u + ⇑U := by
  funext x
  simp [finiteMap, Fin.sum_univ_castSucc, add_assoc]

/-- `main:eq:metric-induction`: the metric-limit consumer's partial sum is the
same map as the appropriate finite prefix, with no change of representatives. -/
theorem finiteMap_eq_currentHistoryMap (G : Euclidean n → Euclidean N)
    (u : ℕ → SchwartzMap (Euclidean n) (Euclidean N)) (j : ℕ) :
    finiteMap G (fun i : Fin j ↦ u i.val) = currentHistoryMap G (fun i ↦ ⇑(u i)) j := by
  funext x
  exact congrArg (G x + ·) (Fin.sum_univ_eq_sum_range (fun i ↦ u i x) j)

/-- `main:lem:history`: smoothness of each prefix on the chart needs only
smoothness of the reference there; a global extension of the reference is not needed. -/
theorem contDiffOn_finiteMap {G : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hG : ContDiffOn ℝ ∞ G W) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) :
    ContDiffOn ℝ ∞ (finiteMap G u) W :=
  hG.add (ContDiffOn.sum (fun i _ ↦ (u i).smooth'.contDiffOn))

/-- `main:eq:history-data`: an empty prefix has no increment obligations. -/
theorem isAdmissibleHistory_empty (B R₀ : ℝ) (kMin : ℕ)
    (u : Fin 0 → SchwartzMap (Euclidean n) (Euclidean N)) (ell : Fin 0 → ℕ) :
    IsAdmissibleHistory B R₀ kMin u ell := fun i ↦ Fin.elim0 i

/-- `main:eq:history-data`: admissibility of an extension is exactly admissibility
of its old prefix and the two physical budgets for the new increment. -/
theorem isAdmissibleHistory_snoc_iff {B R₀ : ℝ} {kMin k : ℕ}
    {u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)} {ell : Fin j → ℕ}
    {U : SchwartzMap (Euclidean n) (Euclidean N)} :
    IsAdmissibleHistory B R₀ kMin (Fin.snoc u U) (Fin.snoc ell k) ↔
      IsAdmissibleHistory B R₀ kMin u ell ∧ kMin ≤ k ∧
        PhysicalBernstein.HasFourierSupport
          (B * iterationScale R₀ growthExponent j ^ bandExponent) U ∧
        PhysicalBernstein.physicalL2Norm U ≤ iterationScale R₀ growthExponent j ^
          (-(k : ℝ) + RevisedScales.displacementLoss n + 1) := by
  simp only [IsAdmissibleHistory, Fin.forall_fin_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

/-- `main:eq:history-data`: restricting an admissible prefix never changes the
order, scale, support or field at a retained index. -/
theorem IsAdmissibleHistory.prefix {B R₀ : ℝ} {kMin m : ℕ}
    {u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)} {ell : Fin j → ℕ}
    (hu : IsAdmissibleHistory B R₀ kMin u ell) (hm : m ≤ j) :
    IsAdmissibleHistory B R₀ kMin (fun i : Fin m ↦ u (i.castLE hm))
      (fun i : Fin m ↦ ell (i.castLE hm)) := fun i ↦ hu (i.castLE hm)

/-- Uniform physical finite-step obligation at `Q = 2k` (`main:thm:step`,
`main:prop:current-scale`, `main:eq:step-error`, `main:eq:step-band`,
`main:eq:step-L2`). Analytic input to the recursion: one `U` must have the
specified band and physical norm and correct the metric of this very prefix
for this very `g s`. The fixed support constant can be enlarged to `B ≥ 1`.
Neither a correction sequence nor its convergence is part of the assumptions. -/
structure UniformHistoryCorrection (G : Euclidean n → Euclidean N)
    (D : Set (Euclidean n)) (g : ℝ → MetricField n)
    (s₀ : ℝ) (kMin : ℕ) (B Tref : ℝ) (C T : ℕ → ℝ) : Prop where
  /-- The fixed compact defect core of `main:thm:step`. -/
  isCompact : IsCompact D
  /-- The fixed target interval in `main:prop:seed` is nonempty. -/
  parameter_pos : 0 < s₀
  /-- An accuracy-independent support constant in `main:eq:step-band`. -/
  one_le_band : 1 ≤ B
  /-- Initial reference-neighborhood threshold from `main:eq:displacement-budget`. -/
  two_le_referenceThreshold : 2 ≤ Tref
  /-- Nonnegativity of the common step-error/displacement constant at `Q = 2k`. -/
  constant_nonneg : ∀ k, 0 ≤ C k
  /-- The unabsorbed same-history estimates in `main:thm:step`. The producer must
  work at every admissible physical prefix above the prescribed thresholds. -/
  correction : ∀ {R₀ s : ℝ} {j k : ℕ}
    {u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)} {ell : Fin j → ℕ},
    Tref ≤ R₀ → 0 < s → s ≤ s₀ → kMin ≤ k → T k ≤ iterationScale R₀ growthExponent j →
    IsAdmissibleHistory B R₀ kMin u ell →
    let R := iterationScale R₀ growthExponent j
    let δ := R ^ (-(k : ℝ))
    cNorm D 0 (inducedMetric (finiteMap G u) - g s) ≤ δ ^ 2 →
    ∃ U : SchwartzMap (Euclidean n) (Euclidean N),
      PhysicalBernstein.HasFourierSupport (B * R ^ bandExponent) U ∧
      PhysicalBernstein.physicalL2Norm U ≤ C k * δ * R ^ RevisedScales.displacementLoss n ∧
      cNorm D 0 (inducedMetric (finiteMap G u + ⇑U) - g s) ≤
        C k * (δ * R ^ (-2 * (k : ℝ)) + δ ^ 3 * R ^ RevisedScales.cubicLoss n)

end JanetCartan.RevisedGlobal
