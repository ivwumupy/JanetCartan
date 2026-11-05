module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.LowBounds
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.Step.History

/-!
# The literal finite-history defect

Shared concrete objects for `main:lem:smoothing`. The small and high estimates
must concern these same fields, also used by the normalized current-mean source.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.DefectSmoothing

variable {n N j : ℕ}

/-- The signed defect of the actual finite history (`main:lem:smoothing`). -/
def historyDefect (g : MetricField n) (G : Euclidean n → Euclidean N)
    (u : Fin j → Torus n → Euclidean N) : MetricField n :=
  g - inducedMetric (finiteHistoryMap G u)

/-- The one smoothed history defect, with no order-dependent operator choices
(`main:lem:smoothing`). -/
def smoothedHistoryDefect (D : LocalDomain) (R : ℝ) (g : MetricField n)
    (G : Euclidean n → Euclidean N) (u : Fin j → Torus n → Euclidean N) :
    Torus n → MetricTensor n := smoothTensor D R (historyDefect g G u)

/-- The normalized source for the current mean is this same smoothed defect
with the actual `b = δ R^A` (`main:lem:smoothing`, following
`main:eq:smoothing-combined`). -/
def normalizedHistorySource (D : LocalDomain) (R δ : ℝ) (g : MetricField n)
    (G : Euclidean n → Euclidean N) (u : Fin j → Torus n → Euclidean N) :
    Torus n → MetricTensor n :=
  ((δ * R ^ forcingExponent n) ^ 2)⁻¹ • smoothedHistoryDefect D R g G u

/-- Local smoothness of the actual defect follows from an admissible history
and primitive target/reference smoothness (`main:lem:smoothing`). -/
theorem contDiffOn_historyDefect {D : LocalDomain} {g : MetricField n}
    (hg : ContDiffOn ℝ ∞ g (D.chart n)) {G : Euclidean n → Euclidean N}
    (hG : ContDiff ℝ ∞ G) {R₀ : ℝ} {kMin : ℕ}
    {u : Fin j → Torus n → Euclidean N} {ell : Fin j → ℕ}
    (hu : IsAdmissibleHistory R₀ kMin u ell) :
    ContDiffOn ℝ ∞ (historyDefect g G u) (D.chart n) :=
  hg.sub (contDiff_inducedMetric (hu.contDiff_finiteHistoryMap hG) (by simp)).contDiffOn

/-- A symmetric target yields a symmetric signed history defect; no positive
or negative definiteness is required (`main:lem:smoothing`). -/
theorem historyDefect_isSymm {g : MetricField n} {x : Euclidean n}
    (hg : (g x).IsSymm) (G : Euclidean n → Euclidean N)
    (u : Fin j → Torus n → Euclidean N) : (historyDefect g G u x).IsSymm := by
  apply hg.sub
  ext a b
  exact real_inner_comm (partialDeriv (finiteHistoryMap G u) x a)
    (partialDeriv (finiteHistoryMap G u) x b)

/-- Smoothness of the same actual smoothed defect (`main:lem:smoothing`). -/
theorem isSmoothPeriodic_smoothedHistoryDefect (D : LocalDomain) (R : ℝ)
    (g : MetricField n) (G : Euclidean n → Euclidean N)
    (u : Fin j → Torus n → Euclidean N) :
    IsSmoothPeriodic (smoothedHistoryDefect D R g G u) :=
  isSmoothPeriodic_smoothTensor D R _

/-- The actual smoothed history has Fourier support at most `2R`
(`main:lem:smoothing`). -/
theorem hasFourierSupport_smoothedHistoryDefect {D : LocalDomain} {R : ℝ}
    (hR : 0 < R) {g : MetricField n} (hg : ContDiffOn ℝ ∞ g (D.chart n))
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {R₀ : ℝ} {kMin : ℕ}
    {u : Fin j → Torus n → Euclidean N} {ell : Fin j → ℕ}
    (hu : IsAdmissibleHistory R₀ kMin u ell) :
    HasFourierSupport (2 * R) (smoothedHistoryDefect D R g G u) :=
  hasFourierSupport_smoothTensor D hR ((contDiffOn_historyDefect hg hG hu).mono
    (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius))

/-- The actual smoothed history defect is real symmetric when the target is
symmetric on the core. The signed defect needs no positivity hypothesis
(`main:lem:smoothing`). -/
theorem smoothedHistoryDefect_isSymm {D : LocalDomain} {R : ℝ}
    {g : MetricField n} (hg : ContDiffOn ℝ ∞ g (D.chart n))
    (hs : ∀ x ∈ D.core n, (g x).IsSymm)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {R₀ : ℝ} {kMin : ℕ}
    {u : Fin j → Torus n → Euclidean N} {ell : Fin j → ℕ}
    (hu : IsAdmissibleHistory R₀ kMin u ell) (z : Torus n) :
    (smoothedHistoryDefect D R g G u z).IsSymm :=
  smoothTensor_isSymm D ((contDiffOn_historyDefect hg hG hu).mono
    (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius))
    (fun x hx ↦ historyDefect_isSymm (hs x hx) G u) z

end JanetCartan.DefectSmoothing
