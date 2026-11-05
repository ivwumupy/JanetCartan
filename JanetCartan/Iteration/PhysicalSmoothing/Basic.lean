module

public import JanetCartan.Iteration.RevisedGlobal.History
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.FiniteMoment.RevisedSource

/-!
# The actual finite-moment defect and normalized source on physical histories

The fields in `main:lem:smoothing` of `paper-v2.tex` are defined on the same
real Euclidean current map used by `RevisedGlobal.UniformHistoryCorrection`.
The smoothing operator is the existing real finite-moment ball operator, not
a periodic Fourier projector. The normalized source uses the revised forcing
exponent and is literally the same output divided by the same forcing square.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSmoothing

variable {n N j : ℕ}

/-- The signed defect of the actual physical prefix (`main:lem:smoothing`). -/
def historyDefect (g : MetricField n) (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) : MetricField n :=
  g - inducedMetric (RevisedGlobal.finiteMap G u)

/-- The literal finite-moment ball smoother of that SAME defect
(`main:eq:smoothing-low`), with finite approximation order `m`. -/
def smoothedDefect (D : LocalDomain) (R : ℝ) (m : ℕ) (g : MetricField n)
    (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) : MetricField n :=
  DefectSmoothing.finiteMomentTensor D R m (historyDefect g G u)

/-- The actual revised mean source `e_R/b²`, with `b=δ R^A`
(`main:lem:smoothing` and `app:prop:ordered-scale-selection`). -/
def normalizedSource (D : LocalDomain) (R : ℝ) (m : ℕ) (δ : ℝ)
    (g : MetricField n) (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) : MetricField n :=
  DefectSmoothing.revisedFiniteMomentSource D R m δ (historyDefect g G u)

/-- The normalized source is the SAME smoother output, not a new choice. -/
theorem normalizedSource_eq (D : LocalDomain) (R : ℝ) (m : ℕ) (δ : ℝ)
    (g : MetricField n) (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) :
    normalizedSource D R m δ g G u =
      ((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹ • smoothedDefect D R m g G u := rfl

/-- Local smoothness of the actual defect needs only original target/reference
smoothness; the physical Schwartz prefix supplies all increment derivatives. -/
theorem contDiffOn_historyDefect {W : Set (Euclidean n)} {g : MetricField n}
    (hg : ContDiffOn ℝ ∞ g W) {G : Euclidean n → Euclidean N}
    (hG : ContDiff ℝ ∞ G) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) :
    ContDiffOn ℝ ∞ (historyDefect g G u) W := by
  have hF : ContDiff ℝ ∞ (RevisedGlobal.finiteMap G u) :=
    hG.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  exact hg.sub (contDiff_inducedMetric hF (by simp)).contDiffOn

/-- A symmetric original target gives a signed symmetric physical defect;
no definiteness of the defect is assumed (`main:lem:smoothing`). -/
theorem historyDefect_isSymm {g : MetricField n} {x : Euclidean n}
    (hg : (g x).IsSymm) (G : Euclidean n → Euclidean N)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N)) :
    (historyDefect g G u x).IsSymm := by
  apply hg.sub
  ext a b
  exact real_inner_comm (partialDeriv (RevisedGlobal.finiteMap G u) x a)
    (partialDeriv (RevisedGlobal.finiteMap G u) x b)

end JanetCartan.PhysicalSmoothing
