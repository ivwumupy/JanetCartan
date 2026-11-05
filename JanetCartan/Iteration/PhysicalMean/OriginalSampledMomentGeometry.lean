module

public import JanetCartan.Iteration.PhysicalMean.OriginalMomentGeometry
public import JanetCartan.Iteration.PhysicalForwardMean.OriginalPhaseProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterKernel
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareCurrent
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareOuter
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativePhaseMargins
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarBudgets
public import JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalMean.OriginalMomentGeometry
import all JanetCartan.Iteration.PhysicalForwardMean.OriginalPhaseProfiles
import all JanetCartan.Iteration.PhysicalAdjointGeometry.PrimitiveProfiles
public meta import JanetCartan.Iteration.PhysicalMean.OriginalSampledMomentGeometryTemplate

/-!
# The unchanged sampled phase and its common current moment chart

The positive current source and quadratic source must use one physical
radial derivative-trade chart for their literal native finite-rate sampled
phase. The displacement and frame margins below are static even before the
source dilation. Neither an exterior cutoff nor scalar event, inverse,
reference or current is reselected (`app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
open PhysicalAdjointGeometry ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open RawPrimary.SliceBounds LeadingWave.FullModulation ProjectedStressFrame PhysicalSeed PhysicalNormalInverse PhysicalInitialization

establish_original_moment_choice_order

/-- The previously fixed physical chart radius has a strict buffer to the phase boundary. -/
theorem physical_radius_lt {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) : T.physicalRadius < T.family.radius := by
  dsimp [PatchQuantitativeFamily.physicalRadius]
  linarith [min_le_left T.family.radius (3*T.family.sourceRadius), T.family.radius_pos]

variable {d : ℕ} (hn : 5 ≤ d+1)
local notation "A" => OriginalPatchIndex hn
set_option quotPrecheck false in
local notation "T(" a ")" => OriginalBoundary.T hn a
set_option quotPrecheck false in
local notation "hp(" a ")" => ((OriginalBoundary.hD hn).2.2.2.2.1 a.1 a.2).1

/-- Native displacement width for the entire original patch product, not a
chosen translation or a physical/carrier cutoff. -/
def width (a : A) : ℝ := Early.width (T(a)) hp(a) (physical_radius_lt (T(a)))

theorem width_pos (a : A) : 0 < width hn a :=
  Early.width_pos (T(a)) hp(a) (physical_radius_lt (T(a)))

/-- One pre-source margin for both dyadic trade jets and normalized phase jets
on the SAME moment chart. This depends only on the original frozen patch. -/
def patchTolerance (a : A) : ℝ := min (T(a)).family.threshold (min
  (Early.trade.tolerance (T(a)) hp(a) (physical_radius_lt (T(a))))
  (Early.phase.tolerance (T(a))))

theorem patchTolerance_pos (a : A) : 0 < patchTolerance hn a :=
  lt_min (T(a)).family.threshold_pos (lt_min
    (Early.trade.tolerance_pos (T(a)) hp(a) (physical_radius_lt (T(a))))
    (Early.phase.tolerance_pos (T(a))))

/-- Insert this finite numerical margin into the original graph tolerance
before choosing the source scale. It costs no change of original patch,
source, sample or solver. -/
theorem exists_margin : ∃ δ > (0 : ℝ), ∀ a : A, δ ≤ patchTolerance hn a := by
  obtain ⟨δ,hδ,h⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : A ↦ (0:ℝ))
    (y := patchTolerance hn) (patchTolerance_pos hn)
  exact ⟨δ,hδ,fun a ↦ by simpa only [zero_add] using (h a).le⟩

def tolerance : ℝ := (exists_margin hn).choose

theorem tolerance_pos : 0 < tolerance hn := (exists_margin hn).choose_spec.1

theorem tolerance_le (a : A) : tolerance hn ≤ patchTolerance hn a :=
  (exists_margin hn).choose_spec.2 a

/-- The upper fine dyadic ceiling is admitted on every original physical
patch ball by one numerical history threshold. No new sample is selected. -/
theorem exists_shift_threshold : ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀ ≥ S, ∀ s : ℕ,
    let R := historyScale R₀ growthExponent s
    ∀ a : A, ∀ radial : ℝ, 1 ≤ radial → ∀ x : Euclidean (d+1), ‖x‖ ≤ (T(a)).physicalRadius →
    ∀ z ∈ parameterCube (3*((OriginalBoundary.D hn).patches a.1 a.2).radius / 2),
    ∀ η ∈ closedBall (0 : Euclidean (d+1-1)) ((2:ℝ)^RawInputPartition.cutoffCount (R^fineExponent)),
      ((adaptedSpacetimeEquiv (T(a)).data.adapted).symm x,(T(a)).reference.spatialPatch z,
        (radial*R^carrierExponent)⁻¹ • η) ∈ originalTradeCompact (T(a)) (T(a)).physicalRadius (width hn a) := by
  have per (a : A) := exists_originalWideInput_compact_threshold (ρ := (T(a)).physicalRadius)
    (T(a)) (width_pos hn a)
  choose S hS hs using per
  obtain ⟨S',hS',hbig⟩ := PhysicalInitialization.OriginalRegular.common_graph_threshold 2 S
  exact ⟨S',hS',fun R₀ h s a ↦ hs a R₀ ((hbig a).trans h) s⟩

def shiftThreshold : ℝ := (exists_shift_threshold hn).choose

theorem shiftThreshold_ge : 2 ≤ shiftThreshold hn := (exists_shift_threshold hn).choose_spec.1

open PhysicalForwardMean

/-- Joint assertions on the *one* chart for this actual current patch. A
reserve is a subsequent request for this chart, not an input to its selection. -/
def CurrentChart (a : A) (Q : {q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) //
    ContDiffOn ℝ ∞ q (ball 0 (OriginalBoundary.R hn)) ∧
    cNorm (closedBall 0 (T(a)).data.localReference.stateRadius) 6 (q - fun _ ↦ cubeStress (d+1)) <
      (T(a)).family.threshold})
    (Y : Point (Spacetime (d+1-1)) (d+1-1) → Euclidean (d+1-1))
    (L : Point (Spacetime (d+1-1)) (d+1-1) → Euclidean (d+1-1) →L[ℝ] Spacetime (d+1-1))
    (DL DP : ℕ → ℝ) (rStar : ℕ) (Λ : ℝ) : Prop :=
  let e := adaptedSpacetimeEquiv (T(a)).data.adapted
  let K := originalTradeCompact (T(a)) (T(a)).physicalRadius (width hn a)
  ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ L ∧
  (∀ q ∈ K, Y =ᶠ[𝓝 q] averagedCovector (current (T(a)) Q)) ∧
  (∀ q : Point (Euclidean (d+1)) (d+1-1), jointCoordinateEquiv e.symm q ∈ K →
    ∀ h η, fderiv ℝ (fun x ↦ inner ℝ (physicalCovector e Y (x,q.2)) η) q.1
      (physicalTrade e L q h) = inner ℝ h η) ∧
  ∀ rSource : ℕ, rSource + ((d+1)/2+1) + 5 ≤ rStar →
  ∀ q : Point (Euclidean (d+1)) (d+1-1), jointCoordinateEquiv e.symm q ∈ K →
    (∀ h : Euclidean (d+1-1), ‖h‖ ≤ 1 → ∀ j,
      ‖iteratedFDeriv ℝ j (fun x ↦ physicalTrade e L (x,q.2) h) q.1‖ ≤
        DL j * Λ ^ (j - (rSource + ((d+1)/2+1)))) ∧
    (∀ η : Euclidean (d+1-1), η ≠ 0 → ∀ j : ℕ, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun x ↦ inner ℝ (physicalCovector e Y (x,q.2)) η / ‖η‖) q.1‖ ≤
        DP j * Λ ^ (j - 1 - (rSource + ((d+1)/2+1))))

/-- Prehistory constants for each *original* patch on the given source
reference. Only its primitive low-six frame certificate is still required;
the original graph/current frame producer discharges it below. -/
theorem exists_current_family (G : FlatReference (d+1))
    (hR : OriginalBoundary.R hn < G.domain.chartRadius) {B : ℝ} (hB : 1 ≤ B)
    {rStar kMin : ℕ} (hreserve : 20*((d+1)+1)+5 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d+1) + bandExponent *
      ((rStar:ℝ)+((d+1:ℕ):ℝ)/2)+2 < (kMin:ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ DL DP : A → ℕ → ℝ, (∀ a k, 0 < DL a k) ∧ (∀ a k, 0 < DP a k) ∧
    ∀ R₀ ≥ S, ∀ (s : ℕ) (u : Fin s → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
      (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
    let F := RevisedGlobal.finiteMap G.map u
    ∀ a : A, cNorm (closedBall 0 (T(a)).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress (d+1)) < tolerance hn →
    ∃ Q, Q.1 = projectedStress F ∧ ∃ Y L, CurrentChart hn a Q Y L (DL a) (DP a)
      rStar (currentCoefficientScale R₀ s) := by
  let K := closedBall (0 : Euclidean (d+1)) (OriginalBoundary.b hn)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ ball 0 (OriginalBoundary.R hn) := closedBall_subset_ball (OriginalBoundary.b_lt_R hn)
  obtain ⟨S,hS,M,_,κ,hκ,hgeo⟩ := PhysicalSampling.exists_scalar_physical_history_budgets G
    (OriginalBoundary.b_pos hn) (OriginalBoundary.b_lt_R hn) hR hB hreserve horder
  obtain ⟨V,hV,hprof⟩ := PhysicalHistory.exists_prefix_derivative_profile hK
    (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  let DL (a : A) := Early.trade.C (N := embeddingDimension (d+1)) (T(a)) hp(a)
    (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a) M
    (show (0:ℝ)<1/4 by norm_num) hκ V hV
  let DP (a : A) := Early.phase.C (N := embeddingDimension (d+1)) (T(a))
    hK hKU (original_frameBall_subset hn a) M (show (0:ℝ)<1/4 by norm_num) hκ V hV
  refine ⟨S,hS,DL,DP,fun a ↦ Early.trade.C_pos (N := embeddingDimension (d+1)) (T(a)) hp(a)
    (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a) M
    (show (0:ℝ)<1/4 by norm_num) hκ V hV,fun a ↦ Early.phase.C_pos (N := embeddingDimension (d+1))
    (T(a)) hK hKU (original_frameBall_subset hn a) M (show (0:ℝ)<1/4 by norm_num) hκ V hV,?_⟩
  intro R₀ hR₀ s u ell hu F a hframe
  obtain ⟨hs,hi,hr,hFM,hm,hnor⟩ := hgeo R₀ hR₀ s u ell hu
  have hM : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega : 4 ≤ 20*((d+1)+1)+5)).trans hFM
  have hlow := hframe.trans_le ((tolerance_le hn a).trans (min_le_left _ _))
  have h3 := (cNorm_mono_order (by decide : 3 ≤ 6)).trans_lt hframe
  have hother := (tolerance_le hn a).trans (min_le_right _ _)
  have ht := h3.trans_le (hother.trans (min_le_left _ _))
  have hp' := h3.trans_le (hother.trans (min_le_right _ _))
  have ht1 := one_le_currentCoefficientScale ((by norm_num : (1:ℝ)≤2).trans (hS.trans hR₀)) s
  have hmapp := hprof R₀ (hS.trans hR₀) s u ell hu K Subset.rfl
  let Q : {q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ q (ball 0 (OriginalBoundary.R hn)) ∧
        cNorm (closedBall 0 (T(a)).data.localReference.stateRadius) 6 (q - fun _ ↦ cubeStress (d+1)) < (T(a)).family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hs hi hr), hlow⟩
  let Y := Early.Y (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
    M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht
  let L := Early.L (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
    M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht
  have hY := Early.Y_smooth (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
    M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht
  have hL := Early.L_smooth (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
    M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht
  have heY := Early.Y_germ (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
    M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht
  have hid := Early.trade_identity (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
    M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht
  refine ⟨Q,rfl,Y,L,hY,hL,heY,hid,?_⟩
  intro r₀ h₀ q hq
  have inside := Early.inside_joint_domain (T(a)) hp(a) (physical_radius_lt (T(a))) hq
  exact ⟨Early.L_profile (T(a)) hp(a) (physical_radius_lt (T(a))) hK hKU (original_frameBall_subset hn a)
      M (show (0:ℝ)<1/4 by norm_num) hκ V hV F hs hi hr hM hm hnor hlow ht rStar r₀ h₀
      (currentCoefficientScale R₀ s) ht1 hmapp q hq,
    Early.phase.current (T(a)) hK hKU (original_frameBall_subset hn a) M (show (0:ℝ)<1/4 by norm_num)
      hκ V hV F hs hi hr hM hm hnor hlow hp' rStar r₀ h₀ (currentCoefficientScale R₀ s) ht1 hmapp
      Y hY q inside (heY _ hq)⟩

/-- Sum over the fixed original patch set only. This envelope is chosen
before any lattice, color, scale or sampled translation. -/
def patchTotal (D : A → ℕ → ℝ) (j : ℕ) : ℝ := ∑ a, D a j

/-- Every actual patch cost is bounded by the shared prehistory total. -/
theorem le_patchTotal (D : A → ℕ → ℝ) (hD : ∀ a j, 0 < D a j) (a : A) (j : ℕ) :
    D a j ≤ patchTotal hn D j :=
  Finset.single_le_sum (fun b _ ↦ (hD b j).le) (Finset.mem_univ a)

/-- The patch total is nonnegative even without an auxiliary nonemptiness
choice for the finite patch index. -/
theorem patchTotal_nonneg (D : A → ℕ → ℝ) (hD : ∀ a j, 0 < D a j) (j : ℕ) :
    0 ≤ patchTotal hn D j := Finset.sum_nonneg (fun a _ ↦ (hD a j).le)

project_original_current_moment_family

open PhysicalSampling PhysicalBackground RawInputPartition Sampling.MeasuredAmplitude

/-- In the literal bare scalar mask, the nonzero radial band lies under the
full retained dyadic ceiling, regardless of its refined-copy label. -/
theorem mask_in_wide_ceiling {n J : ℕ} {det : Euclidean (n-1) → ℝ}
    {u : RefinedIndex J × Euclidean (n-1)} (hu : singleBareScalarMask det u ≠ 0) :
    u.2 ∈ closedBall 0 ((2:ℝ)^J) := by
  have hb : radialBand n u.1.1.val u.2 ≠ 0 := by
    intro h
    exact hu (by simp only [singleBareScalarMask,h,mul_zero])
  have hw : u.2 ∈ wideBand n u.1.1.val := by
    by_contra h
    exact hb (radialBand_eq_zero_off_wideBand h)
  apply closedBall_subset_closedBall _ hw.1
  calc
    4*dyadicScale u.1.1.val = (2:ℝ)^(u.1.1.val+1) := by rw [dyadicScale,pow_succ]; ring
    _ ≤ (2:ℝ)^J := pow_le_pow_right₀ (by norm_num) u.1.1.isLt

/-- The literal nonzero radial multiplier uses the full wide band. The
already-existing original dyadic rate bound therefore pays exactly a factor
two, as needed with the original scalar `ρ/8` cap. -/
theorem mask_shift_le_two {n J : ℕ} {det : Euclidean (n-1) → ℝ}
    {u : RefinedIndex J × Euclidean (n-1)} (hu : singleBareScalarMask det u ≠ 0)
    {τ ε : ℝ} (hτ : 0 ≤ τ) (hrate : ∀ j : Fin J, τ*(2:ℝ)^j.val ≤ ε) :
    ‖τ • u.2‖ ≤ 2*ε := by
  have hb : radialBand n u.1.1.val u.2 ≠ 0 := by
    intro h
    exact hu (by simp only [singleBareScalarMask,h,mul_zero])
  have hw : u.2 ∈ wideBand n u.1.1.val := by
    by_contra h
    exact hb (radialBand_eq_zero_off_wideBand h)
  have hnorm := mem_closedBall_zero_iff.mp hw.1
  rw [norm_smul,Real.norm_of_nonneg hτ]
  calc
    τ*‖u.2‖ ≤ τ*(4*dyadicScale u.1.1.val) := mul_le_mul_of_nonneg_left hnorm hτ
    _ = 2*(τ*(2:ℝ)^u.1.1.val) := by rw [dyadicScale]; ring
    _ ≤ 2*ε := mul_le_mul_of_nonneg_left (hrate u.1.1) (by norm_num)

/-- Exact finite-rate bare sampler phase on its original domain. The only
carrier substitution here is its already-proved extension plateau. -/
theorem phase_eq_chart (a : A) (Q : _)
    {Y : Point (Spacetime (d+1-1)) (d+1-1) → Euclidean (d+1-1)}
    {z₀ z : Euclidean 3} {r : ℝ} (hr : 0 < r) (hz : z ∈ closedBall z₀ r)
    {x : Euclidean (d+1)} {τ : ℝ} (hτ : τ ≠ 0) {J : ℕ} (u : RefinedIndex J × Euclidean (d+1-1))
    (hq : ((adaptedSpacetimeEquiv (T(a)).data.adapted).symm x,(T(a)).reference.spatialPatch z,τ • u.2) ∈
      originalTradeCompact (T(a)) (T(a)).physicalRadius (width hn a))
    (he : ∀ q ∈ originalTradeCompact (T(a)) (T(a)).physicalRadius (width hn a),
      Y =ᶠ[𝓝 q] averagedCovector (current (T(a)) Q)) :
    singleRetainedForwardPhase (T(a)) Q (0,z₀,(T(a)).reference.spatialPatch z₀) hr τ z u x =
      originalSampledPhysicalPhase (T(a)) Y ((T(a)).reference.spatialPatch z) τ u.2 x := by
  let e := adaptedSpacetimeEquiv (T(a)).data.adapted
  let ζ := (T(a)).reference.spatialPatch z
  have hv := Early.inside_joint_domain (T(a)) hp(a) (physical_radius_lt (T(a))) hq
  have physical (ξ : Euclidean (d+1-1)) (h : (e.symm x,ξ) ∈ ball ((0 : Spacetime (d+1-1)),covectorCenter (T(a))) (T(a)).family.radius) :
      (x,ξ) ∈ phaseDomain (T(a)) := by
    change (x,ξ) ∈ ball ((0 : Euclidean (d+1)),covectorCenter (T(a))) (T(a)).family.radius
    rw [← ball_prod_same] at h ⊢
    exact ⟨by simpa [mem_ball_zero_iff] using h.1,h.2⟩
  have hb : (x,ζ) ∈ phaseDomain (T(a)) := physical _ (by
    simpa only [segment_apply,zero_smul,add_zero] using segment_mem_phaseBall hv (by norm_num : (0:ℝ) ∈ Icc 0 1))
  have hs : (x,ζ+τ • u.2) ∈ phaseDomain (T(a)) := physical _ (by
    simpa only [segment_apply,one_smul] using segment_mem_phaseBall hv (by norm_num : (1:ℝ) ∈ Icc 0 1))
  unfold singleRetainedForwardPhase
  rw [extendedRetainedCarrier_eq (T(a)) z₀ hr hz]
  change (extendedRetainedPhase (T(a)) Q x (ζ + τ • u.2) - extendedRetainedPhase (T(a)) Q x ζ) / τ = _
  rw [extendedRetainedPhase_eq (T(a)) Q hs,extendedRetainedPhase_eq (T(a)) Q hb]
  exact literal_rawPhase_eq_originalSampledPhysicalPhase (T(a)) Q hτ hv (he _ hq)

/-- Fixed-real threshold arithmetic, before substitution of original
history expressions. This does not create any additional threshold. -/
theorem graph_le_joined (g s f : ℝ) : g ≤ max (max g s) f :=
  (le_max_left g s).trans (le_max_left _ _)

theorem shift_le_joined (g s f : ℝ) : s ≤ max (max g s) f :=
  (le_max_right g s).trans (le_max_left _ _)

theorem geometry_le_joined (g s f : ℝ) : f ≤ max (max g s) f := le_max_right _ _

theorem two_le_joined (g s f : ℝ) (hs : 2 ≤ s) : 2 ≤ max (max g s) f :=
  hs.trans (shift_le_joined g s f)

theorem reached_graph (g s f R : ℝ) (hR : max (max g s) f ≤ R) : g ≤ R :=
  (graph_le_joined g s f).trans hR

theorem reached_shift (g s f R : ℝ) (hR : max (max g s) f ≤ R) : s ≤ R :=
  (shift_le_joined g s f).trans hR

theorem reached_geometry (g s f R : ℝ) (hR : max (max g s) f ≤ R) : f ≤ R :=
  (geometry_le_joined g s f).trans hR

realize_original_history_moment_chart 0
realize_original_history_moment_chart 1
realize_original_history_moment_chart 2
realize_original_history_moment_chart 3
realize_original_history_moment_chart 4
realize_original_history_moment_chart 5
realize_original_history_moment_chart 6
aggregate_original_moment_cost 0
aggregate_original_moment_cost 1

/-- Exact geometry fields shared by the positive-current linear and sharp
quadratic estimators. There is no phase, moment, or source estimate premise. -/
def SampledChart {n J : ℕ} (φ : RefinedIndex J × Euclidean (n-1) → Euclidean n → ℝ)
    (Φ : RefinedIndex J → Euclidean (n-1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n-1) → ℝ)
    (L : RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (K : Set (Euclidean n)) (DL DP : ℕ → ℝ) (rStar : ℕ) (Λ : ℝ) : Prop :=
  Continuous (Function.uncurry φ) ∧ (∀ i, ContDiff ℝ ∞ (Function.uncurry (Φ i))) ∧
  (∀ i h, ContDiff ℝ ∞ (fun p : Euclidean (n-1) × Euclidean n ↦ L i p.1 h p.2)) ∧
  (∀ z, ContDiff ℝ ∞ (φ z)) ∧ (∀ u, m u ≠ 0 → 1 ≤ ‖u.2‖) ∧
  (∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = Φ u.1 u.2 x) ∧
  (∀ u, m u ≠ 0 → ∀ h x, x ∈ K → inner ℝ h u.2 = fderiv ℝ (φ u) x (L u.1 u.2 h x)) ∧
  ∀ rSource : ℕ, rSource + (n/2+1)+5 ≤ rStar →
    (∀ i η, m (i,η) ≠ 0 → ∀ h, ‖h‖ ≤ 1 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η h) x‖ ≤ DL j * Λ^(j-(rSource+(n/2+1)))) ∧
    (∀ i η, m (i,η) ≠ 0 → ∀ x ∈ K, ∀ j : ℕ, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (fun y ↦ Φ i η y / ‖η‖) x‖ ≤ DP j * Λ^(j-1-(rSource+(n/2+1))))

namespace Bare
open ContinuumRow CanonicalConic PhysicalSamplingShells
variable (pOrder : ℕ) (εframe : ℝ) (hεframe : 0 < εframe)
    (qext : BallExtension.Parameters (Euclidean (d+1))) (hqcenter : qext.center = 0)
    (hqradius : qext.radius = OriginalBoundary.b hn)
    (k : OriginalPatchIndex hn → Euclidean (d+1)) (hk : ∀ a, k a ≠ 0)
    (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
    (p : BallExtension.Parameters (Euclidean (d+1))) (orders : Finset ℕ)
    (margin extendedMargin : ℕ → ℝ) (hmargin : ∀ j ∈ orders, 0 < margin j)
    (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j)
    (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
    (other : StrongExtraCaps hn)
local notation "user" => OriginalBare.userCap hn other
local notation "capped" => strongCappedExtra hn (samplingCappedExtra hn pOrder user)
set_option quotPrecheck false in
local notation "sel(" f ")" => f hn εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap capped
set_option quotPrecheck false in
local notation "act(" f ")" => f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap user
set_option quotPrecheck false in
local notation "bare(" f ")" => f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap other
local notation "Row" => act(OriginalWeights.Index)
set_option quotPrecheck false in
local notation "pa(" i ")" => (⟨i.1.1.1.1,i.2⟩ : OriginalPatchIndex hn)
set_option quotPrecheck false in
local notation "z₀(" i ")" => (OriginalBoundary.D hn).roots i.1.1.1.1 i.2 i.1.1.1.2
set_option quotPrecheck false in
local notation "ρ(" i ")" => originalSamplingRadius hn i.1.1 i.2 (sel(SelectedBoundary.cell) i.1.1 i.2)
set_option quotPrecheck false in
local notation "ctr(" i ")" => ((0 : Euclidean (d+1)),z₀(i),(T(pa(i))).reference.spatialPatch z₀(i))
local notation "μ" => sel(SelectedBoundary.rMeasure)

/-- Coverage of the *whole* canonical four-measurement-radius compact is a
consequence of the original retained product rectangle. No comparison with an
unrelated smoothing/final defect radius is used. -/
theorem measured_compact (i : Row) : closedBall (0 : Euclidean (d+1)) (4*μ) ⊆
    ball 0 (T(pa(i))).physicalRadius := by
  intro x hx
  let b := sel(NativeReferenceSource.am) i
  let r := sel(NativeReferenceSource.root) i
  have hb : 0 < b := sel(NativeReferenceSource.am_pos) i
  have hμ : 0 < μ := sel(NativeReferenceSource.hr)
  have hlarge : 6*μ < b := sel(NativeReferenceSource.measure_lt_carrier) i
  let w := (r 0,FullPhaseCharts.ActualComparison.spectatorCenter r)
  have hw : w ∈ carrierSupport r (r := b) :=
    ⟨mem_closedBall_self (half_pos hb).le,mem_closedBall_self (half_pos hb).le⟩
  have hx' : x ∈ closedBall 0 (4*b) := closedBall_subset_closedBall (by linarith) hx
  have h := (sel(NativeReferenceSource.inner_support_product) i (q := (x,w)) ⟨hx',hw⟩).1
  exact ball_subset_ball (sel(NativeReferenceSource.product_radius_le_physical) i) h

/-- The common native full phase and physical trade at any original sampling
point, including zero masks. Active carrier membership comes from the original
selector and its original label cap, not from the external mass. -/
theorem at_point (R₀ : ℝ) (hR : shiftThreshold hn ≤ R₀) (s : ℕ)
    (i : Row) (color : Fin 3 → Fin (pOrder+1)) (z : SeparatedSampling.Point)
    (Q : _) (Y : _) (L : _) (DL DP : ℕ → ℝ) (rStar : ℕ) (Λ : ℝ)
    (chart : CurrentChart hn pa(i) Q Y L DL DP rStar Λ) :
    let R := historyScale R₀ growthExponent s
    let J := cutoffCount (R^fineExponent)
    let τ := (act(OriginalColoredProtectionApplication.Rcolor) (i,color) * R^carrierExponent)⁻¹
    let ζ := (T(pa(i))).reference.spatialPatch (WithLp.toLp 2 z)
    let φ := singleRetainedForwardPhase (J := J) (T(pa(i))) Q ctr(i) (ρ(i)).2 τ (WithLp.toLp 2 z)
    let m := fun u ↦ bare(OriginalBare.carrierFactor) i z * singleBareScalarMask (J := J)
      (originalForwardDetector (sel(SelectedBoundary.hηb) i) (sel(SelectedBoundary.hr') i)) u
    let e := adaptedSpacetimeEquiv (T(pa(i))).data.adapted
    SampledChart φ (fun _ ↦ originalSampledPhysicalPhase (T(pa(i))) Y ζ τ) m
      (fun _ η h x ↦ physicalTrade e L (x,ζ,τ • η) h) (closedBall 0 (4*μ)) DL DP rStar Λ := by
  intro R J τ ζ φ m e
  let a := pa(i)
  let Z := WithLp.toLp 2 z
  let det := originalForwardDetector (sel(SelectedBoundary.hηb) i) (sel(SelectedBoundary.hr') i)
  have hrad := act(OriginalColoredProtectionApplication.radial_ge_one) (i,color)
  have hR₀ : 1 ≤ R₀ := (by norm_num : (1:ℝ)≤2).trans ((shiftThreshold_ge hn).trans hR)
  have hRpos : 0 < R := zero_lt_one.trans_le (hR₀.trans (le_historyScale hR₀ s))
  have hτ : τ ≠ 0 := by
    dsimp only [τ]
    exact inv_ne_zero (mul_ne_zero (zero_lt_one.trans_le hrad).ne' (Real.rpow_pos_of_pos hRpos _).ne')
  have raw {u : RefinedIndex J × Euclidean (d+1-1)} (hu : m u ≠ 0) : singleBareScalarMask det u ≠ 0 := by
    intro h
    exact hu (show _ * singleBareScalarMask det u = 0 by rw [h,mul_zero])
  have label {u : RefinedIndex J × Euclidean (d+1-1)} (hu : m u ≠ 0) :
      Z ∈ parameterCube ((OriginalBoundary.D hn).patches a.1 a.2).radius ∧
      (Z,ζ) ∈ ball (ctr(i)).2 ((ρ(i)).1/4) := by
    have hφ : act(OriginalWeights.φ) i z = (bare(OriginalBare.carrierFactor) i z)^2 := rfl
    have hw : act(OriginalWeights.φ) i z ≠ 0 := by
      rw [hφ]
      exact pow_ne_zero _ (fun h ↦ hu (by simp only [m,h,zero_mul]))
    exact ((act(OriginalAdmission.cutoff_on_actual_selected_row) i).2.2.2.2.2 z hw).2
  have within {u : RefinedIndex J × Euclidean (d+1-1)} (hu : m u ≠ 0)
      {x : Euclidean (d+1)} (hx : x ∈ ball 0 (T(a)).physicalRadius) :
      (e.symm x,ζ,τ • u.2) ∈ originalTradeCompact (T(a)) (T(a)).physicalRadius (width hn a) := by
    have hz3 : Z ∈ parameterCube (3*((OriginalBoundary.D hn).patches a.1 a.2).radius/2) :=
      fun j ↦ ((label hu).1 j).trans (by linarith only [(hp(a)).1])
    exact (exists_shift_threshold hn).choose_spec.2 R₀ hR s a _ hrad x (mem_ball_zero_iff.mp hx).le Z hz3 u.2
      (mask_in_wide_ceiling (raw hu))
  have same {u : RefinedIndex J × Euclidean (d+1-1)} (hu : m u ≠ 0)
      {x : Euclidean (d+1)} (hx : x ∈ ball 0 (T(a)).physicalRadius) :
      φ u x = originalSampledPhysicalPhase (T(a)) Y ζ τ u.2 x := by
    have hz : Z ∈ closedBall z₀(i) (ρ(i)).1 := by
      have h := (label hu).2
      rw [mem_ball,Prod.dist_eq,max_lt_iff] at h
      exact mem_closedBall.mpr (h.1.le.trans (by linarith [(ρ(i)).2]))
    exact phase_eq_chart hn a Q (ρ(i)).2 hz hτ u (within hu hx) chart.2.2.1
  have cover := bare(measured_compact) i
  have high {u : RefinedIndex J × Euclidean (d+1-1)} (hu : m u ≠ 0) : 1 < ‖u.2‖ :=
    one_lt_norm_of_singleBareScalarMask_ne_zero (sel(SelectedBoundary.hηb) i) (sel(SelectedBoundary.hr') i) (raw hu)
  refine ⟨continuous_singleRetainedForwardPhase _ _ _ _ _ _,fun _ ↦ contDiff_originalSampledPhysicalPhase _ chart.1 ζ τ,
    fun _ h ↦ ((contDiff_physicalTrade e chart.2.1).comp (show ContDiff ℝ ∞
      (fun p : Euclidean (d+1-1) × Euclidean (d+1) ↦ (p.2,ζ,τ • p.1)) from by fun_prop)).clm_apply contDiff_const,
    ?_,fun _ hu ↦ (high hu).le,fun _ hu _ hx ↦ same hu (cover hx),?_,?_⟩
  · intro u
    let ζ' := extendedRetainedCarrier (T(a)) z₀(i) (ρ(i)).2 Z
    have hs := contDiff_extendedRetainedPhase (T(a)) Q
    change ContDiff ℝ ∞ (fun x : Euclidean (d+1) ↦
      (extendedRetainedPhase (T(a)) Q x (ζ'+τ • u.2) - extendedRetainedPhase (T(a)) Q x ζ')/τ)
    exact ((hs.comp (contDiff_id.prodMk contDiff_const)).sub (hs.comp (contDiff_id.prodMk contDiff_const))).div_const _
  · intro u hu h x hx
    have he : φ u =ᶠ[𝓝 x] originalSampledPhysicalPhase (T(a)) Y ζ τ u.2 := by
      filter_upwards [isOpen_ball.mem_nhds (cover hx)] with y hy
      exact same hu hy
    rw [he.fderiv_eq]
    exact (chart.2.2.2.1 (x,ζ,τ • u.2) (within hu (cover hx)) h u.2).symm
  · intro rSource ho
    refine ⟨fun k η hk h hh x hx j ↦ (chart.2.2.2.2 rSource ho (x,ζ,τ • η) (within (u := (k,η)) hk (cover hx))).1 h hh j,?_⟩
    intro k η hk x hx j hj
    have hnz : η ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans (high (u := (k,η)) hk))
    exact (chart.2.2.2.2 rSource ho (x,ζ,τ • η) (within (u := (k,η)) hk (cover hx))).2 η hnz j hj

end Bare

realize_original_sampled_moment_fields 0
realize_original_sampled_moment_fields 1
realize_original_sampled_moment_fields 2
realize_original_sampled_moment_fields 3
realize_original_sampled_moment_fields 4
realize_original_sampled_moment_fields 5
realize_original_sampled_moment_fields 6
realize_original_sampled_moment_fields 7
realize_original_sampled_moment_fields 8
realize_original_sampled_moment_fields 9
realize_original_sampled_moment_fields 10
realize_original_sampled_moment_fields 11

end JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
end
