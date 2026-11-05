module

public import JanetCartan.Iteration.PhysicalSeed.SelectedBoundary

/-!
# The original selector's literal quarter covector

The already-retained norm and normalized-direction certificates identify the
selected covector with the fixed quarter covector used by all pre-source
sampling geometry. No positivity premise, radial reselection, or alternate
original tuple is introduced (`new:sec:order-of-choices`,
`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open Set Metric
namespace JanetCartan.PhysicalSampling
open PhysicalSeed ActualCarriers FrozenMenu ContinuumRow CanonicalConic

variable {n : ℕ} (hn : 5 ≤ n) (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean n))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean n)
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean n)) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a)
  (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (aExtra : (q : IncidenceCenter (OriginalBoundary.D hn)) →
    (l : Fin ((OriginalBoundary.D hn).patchCount q.1.1)) →
      OriginalBoundary.centers hn ⟨q.1.1, l⟩ → {ε : ℝ // 0 < ε})

local notation "centers" => SelectedBoundary.centers hn εframe hεframe qext hqcenter hqradius
  k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
  incidenceCap hincidenceCap aExtra
local notation "scale" => SelectedBoundary.t hn εframe hεframe qext hqcenter hqradius
  k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
  incidenceCap hincidenceCap aExtra

/-- The original selector already has exactly the quarter-normalized covector,
not merely the same direction. This closes radial as well as angular matching. -/
theorem selected_covector_eq_quarter
    (i : (q : centers) × Fin ((OriginalBoundary.D hn).patchCount q.1.1.1)) :
    scale i • i.1.1.1.2 = (1 / 4 : ℝ) • i.1.1.1.2 := by
  have hnorm : ‖i.1.1.1.2‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using i.1.1.2.1
  have hscale := SelectedBoundary.fact20 hn εframe hεframe qext hqcenter hqradius
    k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
    incidenceCap hincidenceCap aExtra i
  have hnormalize := SelectedBoundary.fact21 hn εframe hεframe qext hqcenter hqradius
    k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
    incidenceCap hincidenceCap aExtra i
  calc
    scale i • i.1.1.1.2 = ‖scale i • i.1.1.1.2‖ •
        NormedSpace.normalize (scale i • i.1.1.1.2) :=
      (NormedSpace.norm_smul_normalize _).symm
    _ = (1 / 4 : ℝ) • i.1.1.1.2 := by
      rw [hscale, hnormalize, NormedSpace.normalize_eq_self_of_norm_eq_one hnorm]

/-- Apply the SAME retained tangential projection to the exact quarter
covector. Its norm and direction therefore match the pre-source factories. -/
theorem selected_tangential_covector_eq_quarter
    (i : (q : centers) × Fin ((OriginalBoundary.D hn).patchCount q.1.1.1)) :
    let T := OriginalBoundary.T hn ⟨i.1.1.1.1, i.2⟩
    T.data.adapted.embedding.toContinuousLinearMap.adjoint (scale i • i.1.1.1.2) =
      T.data.adapted.embedding.toContinuousLinearMap.adjoint ((1 / 4 : ℝ) • i.1.1.1.2) := by
  intro T
  exact congrArg T.data.adapted.embedding.toContinuousLinearMap.adjoint
    (selected_covector_eq_quarter hn εframe hεframe qext hqcenter hqradius
      k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap
      incidenceCap hincidenceCap aExtra i)

end JanetCartan.PhysicalSampling
