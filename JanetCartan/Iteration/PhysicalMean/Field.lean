module

public import JanetCartan.Iteration.PhysicalMean.Completion
public import JanetCartan.Iteration.PhysicalPrimary.Basic
public import JanetCartan.Iteration.PhysicalSmoothing.Basic

/-!
# The real Schwartz mean field on the original physical core

The field in `main:eq:mean-normal-field` is completed once and multiplied by
the SAME physical cutoff used by the primary field.  Local smoothness on a
buffered domain containing its support suffices.  The full core germ and the
literal normalized metric residual are preserved.  No global periodization,
new sample, new reference, or new source inverse is introduced.

The remaining analytic source iteration must construct the uncompleted field
and sampled self tensor.  These exact field-construction lemmas do not assert
that those original-data estimates have already been supplied.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalMean

open CurrentMean UniformStep

variable {n N : ℕ}

/-- `main:eq:mean-normal-field`: the actual real Schwartz physical mean,
using one normal completion and the prescribed physical cutoff. -/
def cutCompletedMeanField (D : LocalDomain) (F W : Euclidean n → Euclidean N)
    (target H : MetricField n) {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hcut : tsupport (physicalCutoff (n := n) D) ⊆ U) :
    SchwartzMap (Euclidean n) (Euclidean N) :=
  PhysicalPrimary.cutSchwartzOfSupport D (completedMeanField F W target H) hU
    (contDiffOn_completedMeanField hU hF hW ht hH hi hrank) hcut

/-- No physical field is changed when passing to the Schwartz carrier. -/
theorem cutCompletedMeanField_apply (D : LocalDomain) (F W : Euclidean n → Euclidean N)
    (target H : MetricField n) {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hcut : tsupport (physicalCutoff (n := n) D) ⊆ U) (x : Euclidean n) :
    cutCompletedMeanField D F W target H hU hF hW ht hH hi hrank hcut x =
      physicalCutoff D x • completedMeanField F W target H x := rfl

/-- Every core jet is that of the SAME uncut normal completion. -/
theorem cutCompletedMeanField_eventuallyEq (D : LocalDomain)
    (F W : Euclidean n → Euclidean N) (target H : MetricField n)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hcut : tsupport (physicalCutoff (n := n) D) ⊆ U)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    (cutCompletedMeanField D F W target H hU hF hW ht hH hi hrank hcut :
      Euclidean n → Euclidean N) =ᶠ[𝓝 x] completedMeanField F W target H :=
  PhysicalPrimary.cutSchwartzOfSupport_eventuallyEq D _ hU _ hcut hx

/-- `main:eq:mean-equation`: the real Schwartz field has exactly the same
FULL linearized metric as the singly completed field on the physical core. -/
theorem linearizedMetric_cutCompletedMeanField_eq (D : LocalDomain)
    (F W : Euclidean n → Euclidean N) (target H : MetricField n)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ContDiffOn ℝ ∞ target U) (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hcut : tsupport (physicalCutoff (n := n) D) ⊆ U)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    linearizedMetric F (cutCompletedMeanField D F W target H hU hF hW ht hH hi hrank hcut) x =
      linearizedMetric F (completedMeanField F W target H) x := by
  have hd : fderiv ℝ (cutCompletedMeanField D F W target H hU hF hW ht hH hi hrank hcut) x =
      fderiv ℝ (completedMeanField F W target H) x :=
    (cutCompletedMeanField_eventuallyEq D F W target H hU hF hW ht hH hi hrank hcut hx).fderiv_eq
  ext i j
  simp only [linearizedMetric, partialDeriv, hd]

/-- `main:eq:mean-equation` with the literal REVISED smoothing normalization.
This proves the exact stage ledger for the same `eR`, amplitude and physical
mean, rather than identifying independently chosen source fields. -/
theorem cutCompletedMeanField_normalized_ledger
    (D : LocalDomain) (G : Euclidean n → Euclidean N) {j : ℕ}
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean N))
    (g : MetricField n) (Rfreq δ : ℝ) (m : ℕ)
    (W : Euclidean n → Euclidean N) (H : MetricField n)
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ (RevisedGlobal.finiteMap G u) U) (hW : ContDiffOn ℝ ∞ W U)
    (ht : ContDiffOn ℝ ∞ (PhysicalSmoothing.normalizedSource D Rfreq m δ g G u) U)
    (hH : ContDiffOn ℝ ∞ H U)
    (hi : IsImmersionOn (RevisedGlobal.finiteMap G u) U)
    (hrank : HasFullNormalRankOn (RevisedGlobal.finiteMap G u) U)
    (hcut : tsupport (physicalCutoff (n := n) D) ⊆ U)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    let F := RevisedGlobal.finiteMap G u
    let target := PhysicalSmoothing.normalizedSource D Rfreq m δ g G u
    let V := cutCompletedMeanField D F W target H hU hF hW ht hH hi hrank hcut
    linearizedMetric F V x + H x -
        (((δ * Rfreq ^ RevisedScales.forcingExponent n) ^ 2)⁻¹ •
          PhysicalSmoothing.smoothedDefect D Rfreq m g G u) x =
      linearizedMetric F (completedMeanField F W target H) x + H x - target x := by
  dsimp only
  rw [linearizedMetric_cutCompletedMeanField_eq D _ _ _ _ hU hF hW ht hH hi hrank hcut hx]
  rfl

end JanetCartan.PhysicalMean
