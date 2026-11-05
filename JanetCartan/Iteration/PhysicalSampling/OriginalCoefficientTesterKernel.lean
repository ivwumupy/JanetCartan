module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputHilbert.Multiplication
public import JanetCartan.Iteration.PhysicalForwardMean.NativeScalar
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarCutoffs

/-!
# One physical coefficient cutoff for the original scalar testers

The scalar sampling row really contains different physical `χstar i`. They
cannot be identified globally. The already selected coefficient cutoff is
supported where *all* of these are one. Postcompose the TESTER, not the
physical corrector or inverse, by its contractive L² multiplier. This gives
the uniform-cutoff kernel required by the mean's aggregate and individual
amplitude tests, on the original input measure, with no division or shell sum
(`new:eq:amplitude-test`, `app:ch_mean_pairs:eq:block-normal`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
namespace JanetCartan.PhysicalSampling.OriginalCoefficientTester
open RawInputHilbert PhysicalSamplingShells PhysicalMean PhysicalForwardMean
open Sampling Sampling.Realization SeparatedSampling SamplingKernelBounds CanonicalRowComparison RawInputPartition NormalComparison

theorem cutoff_bound {n : ℕ} (χ : Euclidean n → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (x : Euclidean n) : ‖(χ x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ x).1] using (hχ x).2

/-- The output restriction of the existing scalar tester. There is no new
choice of a bounded extension, phase, ψ, physical wave, or shift. -/
def restrictOutput {n : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (χ : Euclidean n → ℝ) (hc : Continuous χ) (hr : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n))) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  (boundedMultiplier ((Complex.continuous_ofReal.comp hc).aestronglyMeasurable)
    (Filter.Eventually.of_forall (cutoff_bound χ hr))).comp T

/-- One common cutoff on the existing individual or aggregate scalar operator.
The row-dependent factor `χrow` may vary arbitrarily outside `tsupport χ`;
no equality of the original cutoffs outside this set is used. -/
theorem restricted_moment_kernel {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : X → Euclidean n → ℝ) (m : X → ℝ)
    (χrow : X → Euclidean n → ℝ) (χ : Euclidean n → ℝ)
    (hc : Continuous χ) (hr : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hplateau : ∀ u x, x ∈ tsupport χ → χrow u x = 1)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun u y ↦ (χrow u y : ℂ)) x u * f u ∂μ) :
    ‖restrictOutput χ hc hr T‖ ≤ ‖T‖ ∧
      ∀ f : Lp ℂ 2 μ, restrictOutput χ hc hr T f =ᵐ[volume] fun x ↦ ∫ u,
        sampledMomentKernel φ m (fun _ y ↦ (χ y : ℂ)) x u * f u ∂μ := by
  let ha := (Complex.continuous_ofReal.comp hc).aestronglyMeasurable (μ := (volume : Measure (Euclidean n)))
  have hb : ∀ᵐ x ∂(volume : Measure (Euclidean n)), ‖(χ x : ℂ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (cutoff_bound χ hr)
  constructor
  · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul_of_nonneg_right (norm_boundedMultiplier_le ha zero_le_one hb)
      (norm_nonneg T)).trans_eq (one_mul _)
  · intro f
    filter_upwards [boundedMultiplier_coeFn ha hb (T f), hT f] with x hx hTx
    change boundedMultiplier ha hb (T f) x = _
    rw [hx,hTx,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [Function.comp_apply]
    by_cases hz : χ x = 0
    · simp only [sampledMomentKernel,hz,Complex.ofReal_zero,star_zero,mul_zero,zero_mul]
    · simp only [sampledMomentKernel,hplateau u x (subset_tsupport _ hz),Complex.ofReal_one,
        star_one,mul_one,Complex.star_def,Complex.conj_ofReal]
      ring

/-- The exact aggregate scalar action with the physical cutoff still indexed
by its actual patch. This differs from a statement already assuming one
uniform cutoff in the coordinate kernel. -/
theorem restrict_native_of_band_formula {A : Type*} [Fintype A] {n J p : ℕ} (hn : 1 ≤ n)
    (B : ℝ) (ψ : A → Point → ℝ) (w : ℝ → ℝ)
    (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (φ : A → ((Fin 3 → Fin (p + 1)) × Point) → Euclidean (n - 1) → Euclidean n → ℝ)
    (b : A → Fin J → Euclidean (n - 1) → ℝ) (χrow : A → Euclidean n → ℝ)
    (χ : Euclidean n → ℝ) (hc : Continuous χ) (hr : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hplateau : ∀ a x, x ∈ tsupport χ → χrow a x = 1)
    (hkernel : ∀ a j q x η, scalarBandKernel hn (D a) (j,q) x η =
      (b a j η : ℂ) * oscillatoryFactor 1 (φ a q η x) * (χrow a x : ℂ))
    (h : ℝ) (U : A → Lattice → Point) (L : ℕ) :
    let T := nativeScalarOperator hn B ψ w h U D L
    ‖restrictOutput χ hc hr T‖ ≤ ‖T‖ ∧
      ∀ f : Lp ℂ 2 (sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J),
        restrictOutput χ hc hr T f =ᵐ[volume] fun x ↦ ∫ u,
          sampledMomentKernel (nativeForwardScalarPhase B ψ w h U φ)
            (nativeForwardScalarMask B ψ w h U b L) (fun _ y ↦ (χ y : ℂ)) x u * f u
              ∂sampledShellMeasure (ι := SampleIndex p B ψ w h U) n J := by
  intro T
  apply restricted_moment_kernel _ _ _ (fun u x ↦ χrow u.1.1.1 x) χ hc hr
    (fun u ↦ hplateau u.1.1.1) T
  intro f
  refine (nativeScalarOperator_ae_integral hn B ψ w h U D L f).trans ?_
  apply Filter.Eventually.of_forall
  intro x
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hL : u.1.2.1.val < L
  · simp only [nativeScalarKernel,nativeForwardScalarMask,hL,ite_true,hkernel,
      sampledMomentKernel,nativeForwardScalarPhase,Complex.ofReal_mul,Complex.star_def,Complex.conj_ofReal]
    ring
  · simp only [nativeScalarKernel,nativeForwardScalarMask,hL,ite_false,sampledMomentKernel,
      Complex.ofReal_zero,zero_mul]

open PhysicalSeed PhysicalNormalInverse
variable {d : ℕ} (hn : 5 ≤ d + 1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (d + 1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean (d + 1))
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (d + 1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a) (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (userExtra : StrongExtraCaps hn)
local notation "merged" => samplingCappedExtra hn pOrder userExtra
local notation "capped" => strongCappedExtra hn merged
set_option quotPrecheck false in
local notation "selected(" f ")" => f hn εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap capped
set_option quotPrecheck false in
local notation "actual(" f ")" => f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders
  margin extendedMargin hmargin hextendedMargin cap hcap incidenceCap hincidenceCap userExtra

/-- All the original physical scalar cutoffs are exactly one on the support
of the already-selected coefficient multiplier, including its collar. -/
theorem one_on_coefficient_support (i : actual(OriginalWeights.Index)) (x : Euclidean (d+1))
    (hx : x ∈ tsupport selected(SelectedBoundary.χcoeff)) :
    actual(OriginalScalarCutoffs.χstar) i x = 1 :=
  actual(OriginalScalarCutoffs.one_on_coefficient_ball) i (ball_subset_closedBall (selected(SelectedBoundary.fact65) hx))

/-- If an individual bare producer uses its original local exterior bump,
the SAME coefficient contraction gives exactly the same common physical kernel.
This plateau alone does not prove admission of that bump to the bare factory. -/
theorem local_one_on_coefficient_support (i : actual(OriginalWeights.Index)) (x : Euclidean (d+1))
    (hx : x ∈ tsupport selected(SelectedBoundary.χcoeff)) :
    ContinuumRow.FixedCutoffs.physical (n := d+1) (selected(SelectedBoundary.ha') i) 0 x = 1 := by
  have hμ : 0 < selected(SelectedBoundary.rMeasure) := selected(SelectedBoundary.hrMeasure)
  have hi := selected(SelectedBoundary.fact60) i
  have hsub : 5*selected(SelectedBoundary.rMeasure) ≤ selected(SelectedBoundary.a') i := by linarith
  have hmem := closedBall_subset_closedBall hsub (ball_subset_closedBall (selected(SelectedBoundary.fact65) hx))
  apply interior_subset (s := {y | ContinuumRow.FixedCutoffs.physical (n := d+1) (selected(SelectedBoundary.ha') i) 0 y = 1})
  apply ContinuumRow.FixedCutoffs.physical_plateau (selected(SelectedBoundary.ha') i) (0 : Fin 3)
  simpa using hmem

end JanetCartan.PhysicalSampling.OriginalCoefficientTester
