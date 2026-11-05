module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareCurrent
public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterKernel
public import JanetCartan.Iteration.PhysicalForwardMean.SingleScalar

/-!
# The original bare row on outer labels of the very same realization

The half-open sharp annuli and the full phase come from native36. This is the
individual `hTbare` of `app:ch_mean_pairs:eq:block-fields`. The detector here
has neither a half derivative nor a sample weight. The inner/outer conversion
is multiplication by the original spatial mask, never division.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSampling.OriginalBare
open PhysicalSeed PhysicalNormalInverse PhysicalInitialization PhysicalScalarChannel
open ActualCarriers.CurrentFullPhase ProjectedStressFrame ContinuumRow CanonicalConic RawInputPartition
open PhysicalSamplingShells SeparatedSampling PhysicalMean PhysicalForwardMean

variable {d : ℕ} (hn : 5 ≤ d+1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe) (qext : BallExtension.Parameters (Euclidean (d+1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : OriginalPatchIndex hn → Euclidean (d+1)) (hk : ∀ a, k a ≠ 0)
  (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (d+1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ) (hmargin : ∀ j ∈ orders, 0 < margin j)
  (hextendedMargin : ∀ j ∈ orders, 0 < extendedMargin j) (cap : ℝ) (hcap : 0 < cap)
  (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap) (other : StrongExtraCaps hn)
local notation "E" => Euclidean (d+1)
local notation "user" => userCap hn other
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
local notation "T(" i ")" => OriginalBoundary.T hn (⟨i.1.1.1.1,i.2⟩ : OriginalPatchIndex hn)
set_option quotPrecheck false in
local notation "z₀(" i ")" => (OriginalBoundary.D hn).roots i.1.1.1.1 i.2 i.1.1.1.2
set_option quotPrecheck false in
local notation "ρ(" i ")" => originalSamplingRadius hn i.1.1 i.2 (sel(SelectedBoundary.cell) i.1.1 i.2)
set_option quotPrecheck false in
local notation "χ₀(" i ")" => FixedCutoffs.physical (n := d+1) (sel(SelectedBoundary.ha') i) 0
set_option quotPrecheck false in
local notation "ctr(" i ")" => ((0 : E), (z₀(i), (T(i)).reference.spatialPatch z₀(i)))
local notation "χ" => sel(SelectedBoundary.χcoeff)

/-- The *physical* incidence/spectator multiplier at the actual point. -/
def carrierFactor (i : Row) (z : Point) : ℝ :=
  incidenceMask z₀(i) (sel(SelectedBoundary.ha') i) (carrierSamplingEquiv.symm z).1 *
  spectatorMask z₀(i) (sel(SelectedBoundary.ha') i) (carrierSamplingEquiv.symm z).2

/-- At zero carrier multiplier the operator is zero without any geometric
claim about `z`. At nonzero multiplier the plateau-eligible native36 operator
is contracted at the actual coefficient output. The result holds for *all*
external labels on the same node and includes zero external/inner mass. -/
theorem at_outer_point (i : Row) (J : ℕ) (F : E → Euclidean (embeddingDimension (d+1)))
    (Q : {q : E → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ q (ball 0 (OriginalBoundary.R hn)) ∧
      cNorm (closedBall (0:E) (T(i)).data.localReference.stateRadius) 6 (q - fun _ ↦ cubeStress (d+1)) < (T(i)).family.threshold})
    (hQ : Q.1 = projectedStress F) (z : Point) (τ C : ℝ)
    (active : act(OriginalWeights.φ) i z ≠ 0 → bare(RowAction) F J i z τ C) :
    let φ := singleRetainedForwardPhase (J := J) (T(i)) Q ctr(i) (ρ(i)).2 τ (WithLp.toLp 2 z)
    let m := singleBareScalarMask (J := J) (originalForwardDetector (sel(SelectedBoundary.hηb) i) (sel(SelectedBoundary.hr') i))
    ∃ Tbare : Lp ℂ 2 (annularShellMeasure (n := d+1) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure E), ‖Tbare‖ ≤ Real.sqrt C ∧
      ∀ f, Tbare f =ᵐ[volume] fun x ↦ ∫ u,
        sampledMomentKernel φ (fun u ↦ bare(carrierFactor) i z * m u) (fun _ y ↦ (χ y : ℂ)) x u * f u
          ∂annularShellMeasure (n := d+1) (refinedRadius (J := J)) := by
  intro φ m
  let a := bare(carrierFactor) i z
  have hs : act(OriginalWeights.φ) i z = a^2 := rfl
  by_cases ha : a = 0
  · refine ⟨0, by simp, ?_⟩
    intro f
    simp only [← show a = bare(carrierFactor) i z from rfl,ha,zero_mul,sampledMomentKernel,
      Complex.ofReal_zero,integral_zero,zero_apply]
    exact Lp.coeFn_zero _ _ _
  · obtain ⟨Q',hQ',T₀,hT,hact⟩ := active (by rw [hs]; exact pow_ne_zero _ ha)
    obtain rfl : Q' = Q := Subtype.ext (hQ'.trans hQ.symm)
    have hgeom := act(OriginalCoefficientTester.local_one_on_coefficient_support) i
    have hr := sel(SelectedBoundary.fact63)
    have hc := (sel(SelectedBoundary.fact62)).continuous
    let S := OriginalCoefficientTester.restrictOutput χ hc hr T₀
    have h := OriginalCoefficientTester.restricted_moment_kernel _ φ m (fun _ ↦ (χ₀(i) : E → ℝ))
      χ hc hr (fun _ ↦ hgeom) T₀ (fun f ↦ by simpa only [originalBareNativeKernel_eq_sampledMomentKernel] using hact f)
    have ha₂ : |a| ≤ 1 := by
      have ha₂ := (act(OriginalWeights.patchBounds) i).le_bound z
      rw [hs] at ha₂
      exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
    refine ⟨(a:ℂ) • S, ?_, ?_⟩
    · rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg S) ha₂).trans (h.1.trans (Real.le_sqrt_of_sq_le hT))
    · intro f
      filter_upwards [Lp.coeFn_smul (a:ℂ) (S f),h.2 f] with x hx hx'
      change ((a:ℂ) • S f) x = _
      rw [hx]
      change (a:ℂ) * (S f) x = _
      rw [hx',← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [sampledMomentKernel,Complex.ofReal_mul]
      ring

end JanetCartan.PhysicalSampling.OriginalBare
