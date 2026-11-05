module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.FixedCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledMetric
public import JanetCartan.Analysis.PhysicalCutoff.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised.StageLosses

/-!
# The actual compact physical sampled primary

Paper-v2 `main:eq:primary` and `main:eq:self-off`: multiply the SAME real
quadrature sum by the fixed physical cutoff, with no periodization.  Its
Schwartz regularity and exact core jets are proved from the local smoothness
of the original wave family.  No sample, phase, or mean source is reselected.

The v2 mean producer supplies the one fixed-K family `Z₀ + W(v)`, not the old
adaptive canonical sum.  The original-data construction of that family and
its quantitative envelopes remain obligations of the primary/mean producers;
these exact construction lemmas do not assert their existence or bounds.
Consumer: `RevisedStage.increment_estimates_of_physicalSobolev_profiles`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary

open UniformStep

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The SAME physical cutoff also accepts the original buffered smooth
source domain.  Only its fixed support must lie in that domain; regularity
on the entire chart is not needed (`main:eq:mean-normal-field`). -/
def cutSchwartzOfSupport (D : LocalDomain) (f : Euclidean n → Euclidean N)
    {U : Set (Euclidean n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport (physicalCutoff (n := n) D) ⊆ U) :
    SchwartzMap (Euclidean n) (Euclidean N) :=
  ((physicalCutoff (n := n) D).hasCompactSupport.smul_right (f' := f)).toSchwartzMap
    (PrimarySourceAdmission.contDiff_cutoff_of_support_subset (physicalCutoff D).contDiff hU hf hs)

@[simp] theorem cutSchwartzOfSupport_apply (D : LocalDomain)
    (f : Euclidean n → Euclidean N) {U : Set (Euclidean n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport (physicalCutoff (n := n) D) ⊆ U) (x : Euclidean n) :
    cutSchwartzOfSupport D f hU hf hs x = physicalCutoff D x • f x := rfl

/-- Even with a buffered input chart, the actual cutoff preserves the full
core germ of the original field (`main:eq:metric-ledger`). -/
theorem cutSchwartzOfSupport_eventuallyEq (D : LocalDomain)
    (f : Euclidean n → Euclidean N) {U : Set (Euclidean n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hs : tsupport (physicalCutoff (n := n) D) ⊆ U)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    (cutSchwartzOfSupport D f hU hf hs : Euclidean n → Euclidean N) =ᶠ[𝓝 x] f := by
  obtain ⟨_, _, _, hcore, hone⟩ := physicalCutoff_properties (n := n) D
  filter_upwards [isOpen_ball.mem_nhds (hcore hx)] with y hy
  simp only [cutSchwartzOfSupport_apply, hone hy, one_smul]

/-- The actual fixed spatial cutoff of a locally smooth physical field.
This is a real Schwartz function on the original Euclidean domain, not a
periodic representative (`main:thm:step`). -/
def cutSchwartz (D : LocalDomain) (f : Euclidean n → Euclidean N)
    (hf : ContDiffOn ℝ ∞ f (D.chart n)) :
    SchwartzMap (Euclidean n) (Euclidean N) :=
  ((physicalCutoff (n := n) D).hasCompactSupport.smul_right (f' := f)).toSchwartzMap
    (contDiff_physicalCutoff_smul_of_contDiffOn D hf)

@[simp] theorem cutSchwartz_apply (D : LocalDomain)
    (f : Euclidean n → Euclidean N) (hf : ContDiffOn ℝ ∞ f (D.chart n))
    (x : Euclidean n) : cutSchwartz D f hf x = physicalCutoff D x • f x := rfl

/-- The actual compact primary of `main:eq:primary`, with its original
sample and complex wave family.  The revised stage uses `b = δ R^A` with
`A = RevisedScales.forcingExponent n`. -/
def cutSampledPrimary (D : LocalDomain) (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)) :
    SchwartzMap (Euclidean n) (Euclidean N) :=
  cutSchwartz D (sampledPrimary b μ Z) (contDiffOn_sampledPrimary b μ hZ)

@[simp] theorem cutSampledPrimary_apply (D : LocalDomain) (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)) (x : Euclidean n) :
    cutSampledPrimary D b μ Z hZ x = physicalCutoff D x • sampledPrimary b μ Z x := rfl

/-- The original fixed cutoff gives a genuine neighborhood identity, even
at the boundary of the closed core (`main:eq:metric-ledger`). -/
theorem cutSchwartz_eventuallyEq (D : LocalDomain)
    (f : Euclidean n → Euclidean N) (hf : ContDiffOn ℝ ∞ f (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    (cutSchwartz D f hf : Euclidean n → Euclidean N) =ᶠ[𝓝 x] f := by
  obtain ⟨_, _, _, hcore, hone⟩ := physicalCutoff_properties (n := n) D
  filter_upwards [isOpen_ball.mem_nhds (hcore hx)] with y hy
  simp only [cutSchwartz_apply, hone hy, one_smul]

/-- All physical core jets of the original sample are unchanged by the
fixed spatial cutoff (`main:eq:primary`). -/
theorem iteratedFDeriv_cutSampledPrimary_eq (D : LocalDomain) (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)) (j : ℕ)
    {x : Euclidean n} (hx : x ∈ D.core n) :
    iteratedFDeriv ℝ j (cutSampledPrimary D b μ Z hZ) x =
      iteratedFDeriv ℝ j (sampledPrimary b μ Z) x :=
  ((cutSchwartz_eventuallyEq D _ (contDiffOn_sampledPrimary b μ hZ) hx).iteratedFDeriv ℝ j).self_of_nhds

/-- The actual compact primary has the SAME linearized metric as its
uncut sample on the core; no strain identity is assumed (`main:eq:primary-strain`). -/
theorem linearizedMetric_cutSampledPrimary_eq (D : LocalDomain)
    (F : Euclidean n → Euclidean N) (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    linearizedMetric F (cutSampledPrimary D b μ Z hZ) x =
      linearizedMetric F (sampledPrimary b μ Z) x := by
  have hd : fderiv ℝ (cutSampledPrimary D b μ Z hZ) x =
      fderiv ℝ (sampledPrimary b μ Z) x :=
    (cutSchwartz_eventuallyEq D _ (contDiffOn_sampledPrimary b μ hZ) hx).fderiv_eq
  ext i j
  simp only [linearizedMetric, partialDeriv, hd]

/-- Exact same-family self/off splitting for the real Schwartz primary.
The self tensor is the mean producer's literal Hermitian tensor of `dZ`;
the off tensor uses the canonical full demodulated derivative amplitude.
No global smoothness of the uncut atoms is needed (`main:eq:self-off`). -/
theorem inducedMetric_cutSampledPrimary_eq_self_add_off (D : LocalDomain)
    (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {x : Euclidean n} (hx : x ∈ D.core n) :
    inducedMetric (cutSampledPrimary D b μ Z hZ) x =
      b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun y i ↦ sampledDerivative Z i y) x +
        ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ) x := by
  have hxc : x ∈ D.chart n := closedBall_subset_ball D.coreRadius_lt_chartRadius hx
  have hd (i : ι) : DifferentiableAt ℝ (Z i) x :=
    ((hZ i).contDiffAt (isOpen_ball.mem_nhds hxc)).differentiableAt (by simp)
  have he : inducedMetric (cutSampledPrimary D b μ Z hZ) x =
      inducedMetric (sampledPrimary b μ Z) x := by
    have hdcut : fderiv ℝ (cutSampledPrimary D b μ Z hZ) x =
        fderiv ℝ (sampledPrimary b μ Z) x :=
      (cutSchwartz_eventuallyEq D _ (contDiffOn_sampledPrimary b μ hZ) hx).fderiv_eq
    ext i j
    simp only [inducedMetric, partialDeriv, hdcut]
  rw [he, weightedHermitian_sampledDerivativeAmplitude μ Z θ,
    inducedMetric_eq_transpose_mul, differentialMatrix_sampledPrimary b μ hd]
  simp only [ProductSum.offSelfSource, hermitianSelfSum, CurrentMean.weightedHermitianTensor]
  abel

end JanetCartan.PhysicalPrimary
