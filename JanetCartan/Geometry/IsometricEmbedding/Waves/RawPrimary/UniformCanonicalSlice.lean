module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceLocalization
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.UniformSliceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CarrierMasks
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CarrierTranslation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGrading

/-!
# Uniform canonical raw slices with the original masks

Apply the actual uniform phase geometry and fixed-mask producers. Exact
free-covector translation makes the Sobolev constants independent of the
carrier label. All estimates concern the original integral and its literal
weak jets, with the physical cutoff used only in the norm.

The remaining joint amplitude profiles are the proved outputs of
`GradedFamily`; applying them to the initialized family remains an explicit
parent obligation (`app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open SliceGeometry SliceBounds NormalComparison SingleChannel RawInputPartition
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation ProjectedStressFrame

/-- Construct fixed slice radii, cutoff and Sobolev constants before every
carrier in the original closed cube. The original angular detector and high-pass
supply all normalized-mask jets. The phase geometry is constructed from the
same canonical family. Frequency translation is an exact identity of the
integral and all weak jets, so the constant is uniform even though the original
covector ball varies with the carrier.

The fixed working-ball inclusion is accepted after the immersion, matching
the retained constructor without changing any geometry or choices.

The only coefficient estimates remaining as inputs are the actual joint
amplitude/covector outputs of `exists_finite_actual_graded_raw_family`, with
unchanged reserve. No normal geometry, mask seminorm or channel bound is
assumed (`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_uniform_canonical_rawSliceSobolev_before_workingBall {d : ℕ} (hdim : 1 ≤ d)
    {P : Patch (d + 1)} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ζ₀ : Euclidean d) {σ : ℝ} (hσ : 0 < σ)
    {Kgeom : Set (Euclidean (d + 1))} (hKgeom : IsCompact Kgeom) (hKU : Kgeom ⊆ U)
    (hball : closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius ⊆ Kgeom)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (CA CP : ℕ → ℝ) (hCA : ∀ k, 0 ≤ CA k) (hCP : ∀ k, 0 ≤ CP k) :
    ∃ a b e δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < δ ∧
      4 * a ≤ σ / 2 ∧ b ≤ σ / 4 ∧ 16 * e < b ∧ δ ≤ T.family.threshold ∧
    ∃ χ : Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      EqOn χ 1 (closedBall 0 (a / 8)) ∧ tsupport χ ⊆ closedBall 0 (a / 4) ∧
    ∀ (angular : Euclidean 3 → Euclidean d → ℂ) (H : Euclidean d → ℝ)
      (Vdet : Set (Euclidean 3)), IsOpen Vdet → parameterCube P.radius ⊆ Vdet →
      (∀ z ∈ Vdet, ∀ θ, θ ≠ 0 →
        ContDiffAt ℝ ∞ (fun q : Euclidean 3 × Euclidean d ↦ angular q.1 q.2) (z, θ)) →
      (∀ z, ∀ t : ℝ, 0 < t → ∀ θ, angular z (t • θ) = angular z θ) →
      ContDiff ℝ ∞ H → (∀ η, ‖η‖ ≤ 1 → H η = 0) →
      (∀ η, 2 ≤ ‖η‖ → H η = 1) →
    ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
    ∀ (F : Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm Kgeom (20 * (d + 1) + 5) F ≤ M →
      (∀ x ∈ Kgeom, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kgeom, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean (d + 1))
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress (d + 1)) <
          T.family.threshold} := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ ⊆ domain T →
    ∀ z ∈ parameterCube P.radius,
      (z, T.reference.spatialPatch z) ∈ ball (z₀, ζ₀) (σ / 4) →
    ∀ (row col : Fin (d + 1))
      (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
        Euclidean d × (Euclidean 3 × Euclidean d))
      (r : Euclidean d × Euclidean 3 → ℝ)
      (K L τ : ℝ), 1 ≤ K → 1 ≤ L → L ≤ K → 0 < τ → 2 * (τ * K) ≤ e →
    let A := fullDerivativeAmplitude T Q F row col Φ Y r τ
    let S := fun x η ↦ phase T Q x η;
      ContDiffOn ℝ ∞ A (ball ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ)) →
      (∀ k, ∀ w ∈ closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ,
        ‖iteratedFDeriv ℝ k A w‖ ≤ CA k * L ^ (k - rawSliceParameterOrder (d + 1))) →
      (∀ k, ∀ w ∈ closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ,
        ‖iteratedFDeriv ℝ k
          (fun q : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦
            fderiv ℝ (S q.1) q.2.2) w‖ ≤
          CP k * L ^ (k - 1 - (rawSliceParameterOrder (d + 1) + 2))) →
    let mask := MaskProfiles.detectorMask (n := d + 1) (angular z) H;
    ∀ (v : WideInput (d + 1) (cutoffCount K)) (R : Set (Euclidean (d + 1))) (s : ℕ),
    let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S
      (fun x η ↦ A (x, (z, η))) (T.reference.spatialPatch z) τ volume (weightedWideDensity mask v) x
    let J := rawSliceIntegralJet χ S (fun x η ↦ A (x, (z, η)))
      (T.reference.spatialPatch z) τ volume (weightedWideDensity mask v)
    ∃ u : LocalSobolev.LocalL2 R (Matrix (Fin (embeddingDimension (d + 1))) (Fin (d + 1)) ℂ),
      g =ᵐ[volume.restrict R] u ∧
      ∃ ext : LocalSobolev.SobolevExtension R s u,
        ext.toFun = g ∧ ext.jet = J ∧
        ext.jetNorm ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
        LocalSobolev.cartesianJetNorm univ s J ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
        LocalSobolev.restrictionSobolevNorm R s u ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
  obtain ⟨a, ha, hacap, _haR, b, hb, hbcap, _hbcov, e, he, _hecap, heb,
    δ, hδ, hδcap, G, hGX, _hGD, hGX₀, hGD₀, hGe, _hband, hcore,
    C, hC, hnormal⟩ := UniformSliceGeometry.exists_uniform_canonicalSliceNormalData T
      (by omega : 2 ≤ d + 1) hP (by positivity : 0 < σ / 2)
      (by positivity : 0 < σ / 4) (show (0 : ℝ) < 1 by norm_num)
      hKgeom hKU hball M hγ hκ
  obtain ⟨χ, hχ, hχc, _hχbounds, hχone, hχsmall, hχU, hχsp, hχtime⟩ :=
    exists_rawSlice_measurementCutoff T.data.adapted ha
  have hsmall : closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ ⊆
      ball ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ) :=
    closedBall_subset_ball (by linarith)
  refine ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    χ, hχ, hχc, hχone, hχsmall, ?_⟩
  intro angular H Vdet hVdet hcube hang hhom hH hH₀ hH₁
  obtain ⟨bmask, hbmask, hmasks⟩ := exists_uniform_carrierMask_premises T.data.adapted χ hχ
    angular H (isCompact_parameterCube P.radius) hVdet hcube hang hhom hH hH₀ hH₁ a e
  let ajet := fun k ↦ rawSliceCoordinateCost T.data.adapted ^ k * CA k
  let pjet := fun k ↦ rawSliceCoordinateCost T.data.adapted ^ k * CP k
  have hajet (k) : 0 ≤ ajet k :=
    mul_nonneg (pow_nonneg (rawSliceCoordinateCost_pos _).le _) (hCA k)
  have hpjet (k) : 0 ≤ pjet k :=
    mul_nonneg (pow_nonneg (rawSliceCoordinateCost_pos _).le _) (hCP k)
  have hshift : ∀ t ∈ Ioo (-1 : ℝ) 2, MapsTo (rawSliceShift (0 : Euclidean d) t)
      (sliceShiftDomain T a e) (sliceAdaptedDomain T a ×ˢ ball 0 b) := by
    intro t ht q hq
    have hh := rawSliceShift_mapsTo_sliceShiftDomain T 0 he heb t ht hq
    refine ⟨hh.1, ?_⟩
    simpa only [rawSliceShift, mem_ball, dist_eq_norm, add_sub_cancel_left,
      zero_add, sub_zero] using hh.2
  obtain ⟨B, hB, hbound⟩ := exists_rawPhysicalSliceSobolev_wkbGrades T.data.adapted G C
    (U := slicePhysicalDomain (d + 1) a) (V := ball (0 : Euclidean d) b)
    (Ω := sliceInputExtension (d + 1)) (Q := sliceShiftDomain T a e)
    (H := sliceClosedCore (d + 1) a e) (W := Ioo (-1 : ℝ) 2)
    isOpen_ball isOpen_ball isOpen_ball (isOpen_sliceShiftDomain T a e) isOpen_Ioo
    (fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (isCompact_sliceClosedCore a e) (sliceClosedCore_subset_shiftDomain T ha he)
    wideBand_zero_subset_sliceInputExtension 0 (mem_ball_self hb) hshift (fun _ h ↦ h.2.2)
    ajet pjet bmask hajet hpjet hbmask (-a) a (by linarith)
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnrm hclose hlow Q hworking z hz hzball row col Φ Y r K L τ
    hK hL hLK hτ hwin A S hA hAj hDj mask v R s
  obtain ⟨_, hnormalF⟩ := hnormal F hF hi hrank hFM hmet hnrm hclose
  obtain ⟨N, hN⟩ := hnormalF z hz
  obtain ⟨hmask, hmb, hm, hmsp, hmΩ, hmjet⟩ := hmasks z hz
  let ζ : Euclidean d := T.reference.spatialPatch z
  let shift : Euclidean d → Euclidean d := fun η ↦ ζ + η
  have hprod := rawSlice_product_subset_workingBall T hσ hacap hbcap z₀ z ζ₀ hzball
  have htrans (η : Euclidean d) (hη : η ∈ ball (0 : Euclidean d) b) :
      shift η ∈ ball ζ b := by simpa only [shift, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hη
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (fun x η ↦ S x (shift η)))
      (slicePhysicalDomain (d + 1) a ×ˢ ball (0 : Euclidean d) b) := by
    exact (contDiffOn_fullPhase T Q (Ω := domain T) (fun _ h ↦ h)).comp
      (contDiffOn_fst.prodMk (contDiffOn_const.prodMk (contDiffOn_const.add contDiffOn_snd)))
      (fun q hq ↦ hworking (hprod (q.1, shift q.2) ⟨hq.1, htrans q.2 hq.2⟩))
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry (fun x η ↦ A (x, (z, shift η))))
      (slicePhysicalDomain (d + 1) a ×ˢ ball (0 : Euclidean d) b) :=
    hA.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk (contDiffOn_const.add contDiffOn_snd)))
      (fun q hq ↦ hsmall (hprod (q.1, shift q.2) ⟨hq.1, htrans q.2 hq.2⟩))
  obtain ⟨hε, hstrip, hshiftband, hshift4⟩ :=
    rawSlice_window_containments T z he heb hK hτ.le hwin
  obtain ⟨Md, hMd⟩ := hmb
  have hbnd := hbound K L τ hK hL hLK (ne_of_gt hτ) χ mask
    (fun x η ↦ S x (shift η)) (fun x η ↦ A (x, (z, shift η))) hχ hχc hχU
    (fun q hq ↦ hGX₀.symm ▸ hχsp q hq) hχtime hmask Md hMd hS hA'
    (fun j ↦ hm j.val) (fun j ↦ hGD₀.symm ▸ hmsp j.val) (fun j ↦ hmΩ j.val) s
    (fun j q hq k _ ↦ hmjet j.val q hq k) ?_ ?_
    (fun j ↦ hGe.symm ▸ hε j) hstrip ?_ ?_ (fun _ ↦ N) ?_ ?_ ?_ v R
  · have hi : rawPrimaryDemodulatedIntegral (fun x η ↦ S x (shift η))
        (fun x η ↦ A (x, (z, shift η))) 0 τ volume (weightedWideDensity mask v) =
        rawPrimaryDemodulatedIntegral S (fun x η ↦ A (x, (z, η))) ζ τ volume
          (weightedWideDensity mask v) := by
      dsimp only [shift]
      exact rawPrimaryDemodulatedIntegral_translate S
          (fun x η ↦ A (x, (z, η))) ζ τ volume (weightedWideDensity mask v)
    have hj : rawSliceIntegralJet χ (fun x η ↦ S x (shift η))
        (fun x η ↦ A (x, (z, shift η))) 0 τ volume (weightedWideDensity mask v) =
        rawSliceIntegralJet χ S (fun x η ↦ A (x, (z, η))) ζ τ volume
          (weightedWideDensity mask v) :=
      rawSliceIntegralJet_translate χ S (fun x η ↦ A (x, (z, η))) ζ τ volume _
    obtain ⟨u, hu, ext, hef, hej, heB, hcart, hres⟩ := hbnd
    refine ⟨u, ?_, ext, ?_, ?_, heB, ?_, hres⟩
    · filter_upwards [hu] with x hx
      exact (congrArg (χ x • ·) (congrFun hi x)).symm.trans hx
    · exact hef.trans (funext fun x ↦ congrArg (χ x • ·) (congrFun hi x))
    · exact hej.trans hj
    · rw [← hj]
      exact hcart
  · intro q hq k _
    have hpoint := hprod (adaptedPhysicalCoordinates T.data.adapted q.1, shift q.2)
      ⟨hq.1, htrans q.2 hq.2⟩
    let f := fun w : (ℝ × Euclidean d) × Euclidean d ↦ fun i ↦
      matrixChannelEquiv (embeddingDimension (d + 1)) (d + 1)
        (A (adaptedPhysicalCoordinates T.data.adapted w.1, (z, w.2))) i
    change ‖iteratedFDeriv ℝ k (fun w : (ℝ × Euclidean d) × Euclidean d ↦
      f (w.1, shift w.2)) q‖ ≤ _
    rw [iteratedFDeriv_covector_translate f ζ k q]
    exact fullDerivativeAmplitude_sliceGrade T.data.adapted T Q F row col Φ Y r τ
      isOpen_ball hA z (q := (q.1, shift q.2)) (k := k)
      (rpar := rawSliceParameterOrder (d + 1)) (L := L) (C := CA k)
      (hsmall hpoint) (hAj k _ hpoint)
  · intro q hq k _
    have hpoint := hprod (adaptedPhysicalCoordinates T.data.adapted q.1, shift q.2)
      ⟨hq.1, htrans q.2 hq.2⟩
    change ‖iteratedFDeriv ℝ k (fun w : (ℝ × Euclidean d) × Euclidean d ↦
      fderiv ℝ (fun η ↦ S (adaptedPhysicalCoordinates T.data.adapted w.1) (shift η)) w.2) q‖ ≤ _
    simp only [shift, fderiv_comp_add_left]
    let f := fun w : (ℝ × Euclidean d) × Euclidean d ↦
      fderiv ℝ (S (adaptedPhysicalCoordinates T.data.adapted w.1)) w.2
    change ‖iteratedFDeriv ℝ k (fun w : (ℝ × Euclidean d) × Euclidean d ↦
      f (w.1, shift w.2)) q‖ ≤ _
    rw [iteratedFDeriv_covector_translate f ζ k q]
    exact fullPhase_covector_sliceGrade T.data.adapted T Q z hL (hCP k)
      (q := (q.1, shift q.2)) (k := k) (rpar := rawSliceParameterOrder (d + 1))
      (hworking hpoint) (hDj k _ hpoint)
  · intro j θ hθ
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, zero_add, sub_zero] using hshiftband j θ hθ
  · intro η hη
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, zero_add, sub_zero] using hshift4 η hη
  · intro j t ht q hq
    exact (hN t ht).2.2.2.2 hq
  · intro t ht ε hε q hq
    exact hcore t ht ε hε q ⟨subset_closure hq.1, subset_closure hq.2⟩
  · intro j t ht ε y η
    have he := congrFun (rawSlicePhaseExtension_translate
      (fun q η ↦ S (adaptedPhysicalCoordinates T.data.adapted q) η) ζ) (ε, (t, y), η)
    exact (congrFun (congrFun (congrFun (hN t ht).1 ε) y) η).trans he.symm

/-- The original working-ball-first interface for the uniform canonical slice
construction (`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_uniform_canonical_rawSliceSobolev {d : ℕ} (hdim : 1 ≤ d)
    {P : Patch (d + 1)} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ζ₀ : Euclidean d) {σ : ℝ} (hσ : 0 < σ)
    (hworking : closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ ⊆ domain T)
    {Kgeom : Set (Euclidean (d + 1))} (hKgeom : IsCompact Kgeom) (hKU : Kgeom ⊆ U)
    (hball : closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius ⊆ Kgeom)
    (M : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (CA CP : ℕ → ℝ) (hCA : ∀ k, 0 ≤ CA k) (hCP : ∀ k, 0 ≤ CP k) :
    ∃ a b e δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < δ ∧
      4 * a ≤ σ / 2 ∧ b ≤ σ / 4 ∧ 16 * e < b ∧ δ ≤ T.family.threshold ∧
    ∃ χ : Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      EqOn χ 1 (closedBall 0 (a / 8)) ∧ tsupport χ ⊆ closedBall 0 (a / 4) ∧
    ∀ (angular : Euclidean 3 → Euclidean d → ℂ) (H : Euclidean d → ℝ)
      (Vdet : Set (Euclidean 3)), IsOpen Vdet → parameterCube P.radius ⊆ Vdet →
      (∀ z ∈ Vdet, ∀ θ, θ ≠ 0 →
        ContDiffAt ℝ ∞ (fun q : Euclidean 3 × Euclidean d ↦ angular q.1 q.2) (z, θ)) →
      (∀ z, ∀ t : ℝ, 0 < t → ∀ θ, angular z (t • θ) = angular z θ) →
      ContDiff ℝ ∞ H → (∀ η, ‖η‖ ≤ 1 → H η = 0) →
      (∀ η, 2 ≤ ‖η‖ → H η = 1) →
    ∃ B : ℕ → ℝ, (∀ s, 0 < B s) ∧
    ∀ (F : Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm Kgeom (20 * (d + 1) + 5) F ≤ M →
      (∀ x ∈ Kgeom, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kgeom, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean (d + 1))
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress (d + 1)) <
          T.family.threshold} := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ z ∈ parameterCube P.radius,
      (z, T.reference.spatialPatch z) ∈ ball (z₀, ζ₀) (σ / 4) →
    ∀ (row col : Fin (d + 1))
      (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
        Euclidean d × (Euclidean 3 × Euclidean d))
      (r : Euclidean d × Euclidean 3 → ℝ)
      (K L τ : ℝ), 1 ≤ K → 1 ≤ L → L ≤ K → 0 < τ → 2 * (τ * K) ≤ e →
    let A := fullDerivativeAmplitude T Q F row col Φ Y r τ
    let S := fun x η ↦ phase T Q x η;
      ContDiffOn ℝ ∞ A (ball ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ)) →
      (∀ k, ∀ w ∈ closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ,
        ‖iteratedFDeriv ℝ k A w‖ ≤ CA k * L ^ (k - rawSliceParameterOrder (d + 1))) →
      (∀ k, ∀ w ∈ closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ,
        ‖iteratedFDeriv ℝ k
          (fun q : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦
            fderiv ℝ (S q.1) q.2.2) w‖ ≤
          CP k * L ^ (k - 1 - (rawSliceParameterOrder (d + 1) + 2))) →
    let mask := MaskProfiles.detectorMask (n := d + 1) (angular z) H;
    ∀ (v : WideInput (d + 1) (cutoffCount K)) (R : Set (Euclidean (d + 1))) (s : ℕ),
    let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S
      (fun x η ↦ A (x, (z, η))) (T.reference.spatialPatch z) τ volume (weightedWideDensity mask v) x
    let J := rawSliceIntegralJet χ S (fun x η ↦ A (x, (z, η)))
      (T.reference.spatialPatch z) τ volume (weightedWideDensity mask v)
    ∃ u : LocalSobolev.LocalL2 R (Matrix (Fin (embeddingDimension (d + 1))) (Fin (d + 1)) ℂ),
      g =ᵐ[volume.restrict R] u ∧
      ∃ ext : LocalSobolev.SobolevExtension R s u,
        ext.toFun = g ∧ ext.jet = J ∧
        ext.jetNorm ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
        LocalSobolev.cartesianJetNorm univ s J ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ ∧
        LocalSobolev.restrictionSobolevNorm R s u ≤ B s * K ^ ((s : ℝ) + 1 / 2) * ‖v‖ := by
  obtain ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    χ, hχ, hχc, hχone, hχsmall, hslice⟩ :=
    exists_uniform_canonical_rawSliceSobolev_before_workingBall hdim hP T z₀ ζ₀ hσ
      hKgeom hKU hball M hγ hκ CA CP hCA hCP
  refine ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    χ, hχ, hχc, hχone, hχsmall, ?_⟩
  intro angular H Vdet hVdet hcube hang hhom hH hH₀ hH₁
  obtain ⟨B, hB, hbound⟩ := hslice angular H Vdet hVdet hcube hang hhom hH hH₀ hH₁
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hFM hmet hnrm hclose hlow
  exact hbound F hF hi hrank hFM hmet hnrm hclose hlow hworking

end JanetCartan.RawPrimary
