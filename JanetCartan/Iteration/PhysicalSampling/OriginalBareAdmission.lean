module

public import JanetCartan.Iteration.PhysicalScalarChannel.Native
public import JanetCartan.Iteration.PhysicalInitialization.SuppliedLeading
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarCutoffs

/-!
# Admission of the individual bare tester on the original physical family

Choose its native packet on each ORIGINAL patch before `εframe` or `userExtra`.
Its transverse-comparison tolerance need not equal a sampled-row tolerance;
the regular graph's signed tolerance is unchanged (`new:sec:order-of-choices`,
`app:ch_mean_pairs:eq:block-fields`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.PhysicalSampling.OriginalBare
open PhysicalSeed PhysicalNormalInverse PhysicalInitialization PhysicalPrimary
open ActualCarriers.CurrentFullPhase ProjectedStressFrame

variable {d : ℕ} (hn : 5 ≤ d+1)
local notation "Patch" => OriginalPatchIndex hn

set_option quotPrecheck false in
local notation "packet(" a ")" =>
  PhysicalScalarChannel.exists_original_bare_scalar_native_family.{0} (by omega : 2 ≤ d+1)
    (OriginalBoundary.T hn a) (((OriginalBoundary.hD hn).2.2.2.2.1 a.1 a.2).1)
    (zero_lt_one : (0:ℝ)<1) (zero_lt_one : (0:ℝ)<1) (zero_lt_one : (0:ℝ)<1)

/-- Literal spatial radius of the original bare full-band theorem. -/
def radius (a : Patch) : ℝ := (packet(a)).choose

theorem radius_pos (a : Patch) : 0 < radius hn a := (packet(a)).choose_spec.1

/-- Admissible dyadic shift from the same bare packet. -/
def ceiling (a : Patch) : ℝ := (packet(a)).choose_spec.2.2.choose

theorem ceiling_pos (a : Patch) : 0 < ceiling hn a := (packet(a)).choose_spec.2.2.choose_spec.1

/-- Native coefficient tolerance, including the actual transverse-comparison condition. -/
def tolerance (a : Patch) : ℝ := (packet(a)).choose_spec.2.2.choose_spec.2.2.choose

theorem tolerance_pos (a : Patch) : 0 < tolerance hn a :=
  (packet(a)).choose_spec.2.2.choose_spec.2.2.choose_spec.1

set_option quotPrecheck false in
local notation "factory(" a ")" => (packet(a)).choose_spec.2.2.choose_spec.2.2.choose_spec.2.2

/-- The actual analytic continuation behind all three named numerical choices. -/
theorem continuation (a : Patch) : type_of% (factory(a)) := factory(a)

/-- The common raw frame margin precedes even the original reference callback. -/
theorem exists_frame_margin : ∃ η > (0:ℝ), ∀ a : Patch, η ≤ tolerance hn a := by
  obtain ⟨η,hη,hall⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : Patch ↦ (0:ℝ))
    (y := tolerance hn) (tolerance_pos hn)
  exact ⟨η,hη,fun a ↦ by simpa only [zero_add] using (hall a).le⟩

def frameMargin : ℝ := (exists_frame_margin hn).choose

theorem frameMargin_pos : 0 < frameMargin hn := (exists_frame_margin hn).choose_spec.1

theorem frameMargin_le (a : Patch) : frameMargin hn ≤ tolerance hn a :=
  (exists_frame_margin hn).choose_spec.2 a

/-- Retain the strain and leading certificates and all earlier frame caps. -/
theorem exists_frame {extra : ℝ} (h : 0 < extra) :
    ∃ ε > (0:ℝ), ε ≤ extra ∧ ε ≤ frameMargin hn / (2*(6+1:ℝ)) / 2 ∧
      ε ≤ RawPrimary.ambientStrainFrameThreshold hn / 2 ∧
      ∀ a : Patch, ε ≤ (OriginalBoundary.η hn a / (2*(6+1:ℝ))) / 2 := by
  have hmin : 0 < min extra (frameMargin hn / (2*(6+1:ℝ)) / 2) :=
    lt_min h (by have := frameMargin_pos hn; positivity)
  obtain ⟨ε,hε,hle,hr,hl⟩ := exists_original_common_frame_tolerance hn hmin
  exact ⟨ε,hε,hle.trans (min_le_left _ _),hle.trans (min_le_right _ _),hr,hl⟩

/-- The one user cap is specified *before* the sampling and strong minima.
It constrains the two radii required of the literal bare physical bump. -/
def userCap (other : StrongExtraCaps hn) : StrongExtraCaps hn := fun q l j ↦
  ⟨min (other q l j).1 (min (radius hn ⟨q.1.1,l⟩ / 8)
    ((originalSamplingRadius hn q l j).1 / 4)),
    lt_min (other q l j).2 (lt_min (div_pos (radius_pos hn _) (by norm_num))
      (div_pos (originalSamplingRadius hn q l j).2 (by norm_num)))⟩

theorem userCap_le_other (other : StrongExtraCaps hn) (q l j) :
    (userCap hn other q l j).1 ≤ (other q l j).1 := min_le_left _ _

variable (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (d+1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : OriginalPatchIndex hn → Euclidean (d+1)) (hk : ∀ a, k a ≠ 0)
  (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (d+1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ) (hmargin : ∀ j ∈ orders, 0 < margin j)
  (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j) (cap : ℝ) (hcap : 0 < cap)

local notation "H" => ReferenceBoundary.H hn εframe hεframe qext hqcenter hqradius k hk hkD
  p orders margin extendedMargin hmargin hextendedMargin cap hcap

/-- One additional numerical threshold for the SAME finite Schwartz history.
No second graph tolerance, current, or inverse is chosen. -/
theorem exists_frame_on_history (hεbare : εframe ≤ frameMargin hn / (2*(6+1:ℝ)) / 2)
    {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hstar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1:ℕ):ℝ)/2) + 2 < (kMin:ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀ ≥ S,
      ∀ (s : ℕ) (u : Fin s → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap (sourceDilation (H).map σ) u
        ∀ a : Patch, cNorm (closedBall (0 : Euclidean (d+1))
          (OriginalBoundary.T hn a).data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress (d+1)) < tolerance hn a := by
  let G := sourceDilationReference H hσ hσone
  have hR : OriginalBoundary.R hn < G.domain.chartRadius := by
    change OriginalBoundary.R hn < (H).domain.chartRadius
    rw [ReferenceBoundary.fact5 hn εframe hεframe qext hqcenter hqradius k hk hkD
      p orders margin extendedMargin hmargin hextendedMargin cap hcap]
    exact OriginalBoundary.R_lt_chartRadius hn
  have href i := (supplied_original_source_frame hn εframe hεframe qext hqcenter hqradius
    k hk hkD p orders margin extendedMargin hmargin hextendedMargin cap hcap hσ hσone i).trans_le hεbare
  obtain ⟨S,hS,_,_,_,_,admit⟩ := exists_history_leading_admission G
    (OriginalBoundary.b_pos hn) (OriginalBoundary.b_lt_R hn) hR hB hstar horder (frameMargin_pos hn) href
  refine ⟨S,hS,?_⟩
  intro R₀ hR₀ s u ell hu F a
  obtain ⟨hF,hi,hRank,_,_,_,hframe,_⟩ := admit R₀ hR₀ s u ell hu
  have hs : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 (OriginalBoundary.R hn)) :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF.contDiffOn hi hRank)
  let stress : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) :=
    projectedStress F - fun _ ↦ cubeStress (d+1)
  have hreg x (hx : x ∈ closedBall (0 : Euclidean (d+1)) (OriginalBoundary.b hn)) :
      ContDiffAt ℝ (6 : ℕ∞ω) stress x := by
    have hproj := hs.contDiffAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball (OriginalBoundary.b_lt_R hn) hx))
    have hconst : ContDiffAt ℝ ∞
        (fun _ : Euclidean (d+1) ↦ cubeStress (d+1)) x := contDiffAt_const
    exact (hproj.sub hconst).of_le (by simp)
  have hsmall : cNorm (closedBall (0 : Euclidean (d+1))
      (OriginalBoundary.T hn a).data.localReference.stateRadius) 6 stress ≤
      cNorm (closedBall (0 : Euclidean (d+1)) (OriginalBoundary.b hn)) 6 stress :=
    cNorm_mono_set_of_contDiffAt (original_frameBall_subset hn a)
      (isCompact_closedBall _ _) hreg
  change cNorm (closedBall (0 : Euclidean (d+1))
      (OriginalBoundary.T hn a).data.localReference.stateRadius) 6 stress < tolerance hn a
  exact (hsmall.trans_lt hframe).trans_le (frameMargin_le hn a)

end JanetCartan.PhysicalSampling.OriginalBare
