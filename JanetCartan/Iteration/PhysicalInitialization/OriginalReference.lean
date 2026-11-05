module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalGeometry
public import JanetCartan.Iteration.PhysicalInitialization.SignedProfiles
public import JanetCartan.Iteration.PhysicalSeed.ContractionBoundary

/-!
# One concrete original source reference and its later contractions

Specialize the strengthened initializer ONCE using its own retained centers and
one extension collar. Its finite margin menu is empty: additional finite regular
margins are imposed by `exists_terminal_physical_inverse_on_source_interval` on
later contractions of this same source reference, never by another selection.
The final contraction keeps its literal map and the original wide chart is
recovered deterministically for physical history estimates.

Consumers: original physical leading admission, the current/source inverse join,
and the regular source interval (`new:sec:order-of-choices`, `main:prop:seed`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization
open PhysicalSeed ProjectedStressFrame

variable {n : ℕ}

/-- One finite tolerance, fixed before the reference callback. -/
def originalFrameTolerance (hn : 5 ≤ n) {extra : ℝ} (hextra : 0 < extra) : ℝ :=
  Classical.choose (exists_original_common_frame_tolerance hn hextra)

/-- Positivity of that SAME selected tolerance. -/
theorem originalFrameTolerance_pos (hn : 5 ≤ n) {extra : ℝ} (hextra : 0 < extra) :
    0 < originalFrameTolerance hn hextra :=
  (Classical.choose_spec (exists_original_common_frame_tolerance hn hextra)).1

/-- It retains the exact leading conversion factor on every original patch. -/
theorem originalFrameTolerance_le_leading (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) (i : OriginalPatchIndex hn) :
    originalFrameTolerance hn hextra ≤
      (OriginalBoundary.η hn i / (2 * (6 + 1 : ℝ))) / 2 :=
  (Classical.choose_spec (exists_original_common_frame_tolerance hn hextra)).2.2.2 i

/-- It also retains the precise full-strain threshold. -/
theorem originalFrameTolerance_le_strain (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) :
    originalFrameTolerance hn hextra ≤ RawPrimary.ambientStrainFrameThreshold hn / 2 :=
  (Classical.choose_spec (exists_original_common_frame_tolerance hn hextra)).2.2.1

/-- No earlier positive geometric tolerance is lost. -/
theorem originalFrameTolerance_le_extra (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) : originalFrameTolerance hn hextra ≤ extra :=
  (Classical.choose_spec (exists_original_common_frame_tolerance hn hextra)).2.1

/-- The center callback is literally the original center of the chart. -/
abbrev originalCenterFamily (hn : 5 ≤ n) : OriginalPatchIndex hn → Euclidean n :=
  fun i ↦ OriginalBoundary.kCenter hn i.1

/-- Its original cover-domain property, without choosing new covectors. -/
theorem originalCenterFamily_mem_domain (hn : 5 ≤ n) (i : OriginalPatchIndex hn) :
    originalCenterFamily hn i ∈ (OriginalBoundary.D hn).domain i.1 :=
  OriginalBoundary.kCenter_mem_domain hn i.1

/-- The one prescribed source reference. Later regular margins are imposed by
contracting this map, not by selecting a second reference. -/
def originalSourceReference (hn : 5 ≤ n) {extra : ℝ} (hextra : 0 < extra) :
    FlatReference n :=
  ReferenceBoundary.H hn (originalFrameTolerance hn hextra)
    (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
    (originalBallExtension_center hn) (originalBallExtension_radius hn)
    (originalCenterFamily hn) (original_kCenter_ne_zero hn)
    (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
    (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one

/-- Its source dilation parameter belongs to that same callback invocation. -/
def originalSourceDilation (hn : 5 ≤ n) {extra : ℝ} (hextra : 0 < extra) : ℝ :=
  ReferenceBoundary.θ hn (originalFrameTolerance hn hextra)
    (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
    (originalBallExtension_center hn) (originalBallExtension_radius hn)
    (originalCenterFamily hn) (original_kCenter_ne_zero hn)
    (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
    (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one

/-- The auxiliary source reference has the original wide chart, even though
its later final contracted reference is supplied on a smaller chart. -/
theorem originalSourceReference_domain (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) :
    (originalSourceReference hn hextra).domain = (OriginalBoundary.G₀ hn).domain := by
  exact ReferenceBoundary.fact5 hn (originalFrameTolerance hn hextra)
    (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
    (originalBallExtension_center hn) (originalBallExtension_radius hn)
    (originalCenterFamily hn) (original_kCenter_ne_zero hn)
    (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
    (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one

/-- The map is exactly the source dilation of the original analytic reference. -/
theorem originalSourceReference_map (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) :
    (originalSourceReference hn hextra).map =
      sourceDilation (OriginalBoundary.G₀ hn).map (originalSourceDilation hn hextra) := by
  exact ReferenceBoundary.fact6 hn (originalFrameTolerance hn hextra)
    (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
    (originalBallExtension_center hn) (originalBallExtension_radius hn)
    (originalCenterFamily hn) (original_kCenter_ne_zero hn)
    (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
    (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one

/-- The actual original physical construction radius stays in that wide chart. -/
theorem originalSourceReference_radius (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) :
    OriginalBoundary.R hn < (originalSourceReference hn hextra).domain.chartRadius := by
  rw [originalSourceReference_domain]
  exact OriginalBoundary.R_lt_chartRadius hn

/-- The final reference is selected by the original contraction continuation,
with the SAME original parameters. The source parameter remains free until all
finite geometric and analytic caps have been intersected. -/
def originalContractedReference (hn : 5 ≤ n) {extra : ℝ} (hextra : 0 < extra)
    {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) : FlatReference n :=
  ContractionBoundary.G hn (originalFrameTolerance hn hextra)
    (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
    (originalBallExtension_center hn) (originalBallExtension_radius hn)
    (originalCenterFamily hn) (original_kCenter_ne_zero hn)
    (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
    (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one σ hσ hσone

/-- Literal contraction of the SAME source reference. -/
theorem originalContractedReference_map (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) :
    (originalContractedReference hn hextra hσ hσone).map =
      sourceDilation (originalSourceReference hn hextra).map σ := by
  exact ContractionBoundary.fact5 hn (originalFrameTolerance hn hextra)
    (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
    (originalBallExtension_center hn) (originalBallExtension_radius hn)
    (originalCenterFamily hn) (original_kCenter_ne_zero hn)
    (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
    (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one σ hσ hσone

/-- The same contracted map satisfies the original componentwise C6 frame
margin. This follows by applying its actual geometric neighborhood to itself,
not by invoking the legacy periodic-history continuation. -/
theorem originalContractedReference_frame (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) (i : Fin n) :
    cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
      (fun x ↦ projectedStress (originalContractedReference hn hextra hσ hσone).map x i -
        cubeStress n i) < originalFrameTolerance hn hextra := by
  let G := originalContractedReference hn hextra hσ hσone
  obtain ⟨δ, C₀, κ, hδ, _hC₀, _hκ, hnear, _hself⟩ :=
    ContractionBoundary.fact11 hn (originalFrameTolerance hn hextra)
      (originalFrameTolerance_pos hn hextra) (originalBallExtension hn)
      (originalBallExtension_center hn) (originalBallExtension_radius hn)
      (originalCenterFamily hn) (original_kCenter_ne_zero hn)
      (originalCenterFamily_mem_domain hn) (originalBallExtension hn) ∅
      (fun _ ↦ 1) (fun _ ↦ 1) (by simp) (by simp) 1 zero_lt_one σ hσ hσone
  have hzero : cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.R hn)) 8
      (G.map - G.map) < δ := by simpa only [sub_self, cNorm_zero] using hδ
  obtain ⟨_hi, _hrank, _hC4, _hmet, _hnormal, _hQ, hframe⟩ :=
    hnear univ G.map isOpen_univ (subset_univ _) G.contDiff.contDiffOn hzero
  exact hframe i

/-- The concrete actual reference closes the retained physical leading
admission's exact componentwise order-six hypothesis on every original patch. -/
theorem originalContractedReference_leading_margin (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    (a : OriginalPatchIndex hn) (i : Fin n) :
    cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
      (fun x ↦ projectedStress (originalContractedReference hn hextra hσ hσone).map x i -
        cubeStress n i) < (OriginalBoundary.η hn a / (2 * (6 + 1 : ℝ))) / 2 :=
  (originalContractedReference_frame hn hextra hσ hσone i).trans_le
    (originalFrameTolerance_le_leading hn hextra a)

end JanetCartan.PhysicalInitialization
