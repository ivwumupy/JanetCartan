module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.ReferenceStrain
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Synthesis
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Plateaus
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.FixedSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMean
public import JanetCartan.Analysis.ContDiff.PositiveSquareRoot

/-!
# Geometric and scalar steps of the positive background

Checked components of `app:ch_background:prop:bg-positive` and
`app:ch_background:prop:bg-current` in `paper.tex`:

* the actual covector-raising construction and its tangent strain;
* the exact reference strain and residual when the induced metric is `I`;
* positivity, smoothness, and the square of the scalar amplitude once the
  synthesized density is smooth and bounded by `1/2`;
* a compact smooth reduced source and its normalized all-order `O(ρ)` bounds;
* the same compact source as one actual all-Sobolev L² class, with quantitative
  bounds and a constructed buffered residual for the original inverse;
* constructed source/measurement and external carrier plateaus;
* the original inverse's factor-four uncut synthesis and almost-everywhere
  cancellation on the source/exterior plateaus, from primitive row inputs.

`PositiveBackground.NormalizedSource` connects the source to the actual
projected stress and flat reference residual; `NormalizedSourceSobolev` proves
its all-order Sobolev smallness. They are downstream leaves because
SourceGeometry already imports this base module. The downstream leaves
`DensityRegularity`, `SmoothSynthesis`, and `PhysicalCancellation` construct the
smooth factor-four density and full physical tangent field, then prove reduced
cancellation on the closed physical core from primitive same-row gap,
regularity, and carrier-matching inputs. Their `with_exterior` variants retain
the supplied exterior cutoff independently of the measurement radius and
give cancellation where its open plateau meets that core. `SeedPlateaus` retains the original
seed weight, with an explicit radius containment for the actual angular mask.
`SourceInverse` applies the primitive uniform normal and raw-adjoint estimates
to the constructed compact source, yielding one smooth uncut density with
all-order `O_s(σ)` bounds. It instantiates the canonical mask estimates and
chooses one source contraction for positivity and finite low smallness.
Its `with_exterior` estimates and the corresponding covector/scalar estimates
retain that same exterior cutoff through the original inverse; the existing
fixed-radius statements remain specializations.
`SourceScalar` applies the corrected-density admission and scalar bounds to
that same constructed inverse representative. It provides the positive
initial scalar's all-order bounds and a monotone retained coefficient profile
on the distinct original image, carrier and label domains, with one cap.
`CorrectedSourceInverse` constructs that uncorrected inverse density before
fixing its corrected positive inverse. It applies the distinct-exterior
producer to the SAME representative, retaining the original density identity,
finite-low class, inverse equations and density-dependent high profile.
The uniform uncorrected and wider-density operator estimates still require
instantiation on the actual initialized row.
`InitialLabels` identifies this density with the retained ODE's original labels
and transfers its low norm without losing derivatives.
`PhysicalMean` identifies the literal transported tensor mean with the
normal square and its measured increment, using the same external weights.
The downstream `PhysicalMeanCancellation` applies canonical-mask regularity
and the full detector-projection plateau to prove physical core cancellation
for any smooth representative of the same uncorrected inverse density.
Its supplied-mask theorem accepts the exact positive angular widths returned
by the normalized adjoint construction and retains their full carrier supports;
the original conic-selection statement remains a specialization.
`WeightBuffers` fixes a measurement buffer on the entire original weight
support, and `WeightSelection` selects it jointly with the external weights
before the source scale enters. Uniform analytic estimates for the normalized
row must still be constructed with those same choices.
`RetainedSource` applies the retained mean-source theorem on that full support
with the literal squared weights, product Lebesgue measure and fixed source
cutoff. It proves source smoothness, Sobolev smallness, a positive normal lower
bound and mixed normalized field bounds on one common source interval.
`RetainedWeightBuffers` supplies its seed/current domain maps on the full weight
support from the original comparison and working-cylinder geometry.
`RetainedPhysicalSource` applies both constructions to the literal physical
mean and its exact `fixedSourceToL2` for every smaller original measurement
radius, with its admissible cap preceding the radius and current chart family.
`NormalizedMeanMatching` identifies the actual source scalar family's full
physical affine mean with the normalized carrier mean, retaining the density
and the entire external-weight support. Its compact source is exactly the
normalized seed source, including the original `-1/2` factor.
`ConstructedMeanMatching` constructs those scaled scalar flows from the retained
unit seeds. Its buffers precede the finite selection, and the same flows give
the kernel, test-integral, adjoint-integral and physical-mean identities. It
derives normal/covector smoothness and all-order Sobolev source bounds on one
positive scale interval before the varying scale.
`RetainedUnitSeed` discharges that constructor's scalar and coefficient inputs
from the original chart's characteristic formula, selected minor and Cauchy data.
`WeightedIncidence` retains the supplied seed weights while selecting the finite
incidence cover, masks and one measurement radius. The full detector support
lies in the original weight plateau, and every weight collar stays inside the
scalar-flow buffer. The final physical buffer also lies in the original
Hamilton domain; no later radius or weight is identified with these choices.
`SourceCovector` obtains all-order smallness of the same uncorrected inverse's
uncut covector and its raised domain-field correction at the flat reference.
It also applies the actual normalized tangent geometry to prove all-order
smallness of the ambient base correction and full strain error, and uniform
bounds for the full base field and strain on one source cap.
`RetainedDensityMean` applies characteristic/Hamilton footpoint matching to
identify the affine physical mean with the actual corrected positive scalar's
mean on the same retained charts.
Final instantiation of the uniform estimates and detector/weight matching on
the common normalized/history reference, the corrected row gap, and the
fixed-shift estimates remain unfinished. These conditional constructions do
not prove the full positive background proposition.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan.PositiveBackground

variable {n N : ℕ}

/-- `app:ch_background:eq:bg-current-raising`: the uncorrected residual `R₀`,
before reduction and multiplication by the source cutoff. The field `H` is the
uncorrected transported mean when this construction is assembled. -/
def referenceMeanResidual (G : Euclidean n → Euclidean N)
    (H₀ : MetricTensor n) (H : MetricField n) : MetricField n :=
  linearizedMetric G (tangentVariation G (referenceVectorField H₀)) + H

/-- `app:ch_background:prop:bg-positive`: at a flat reference immersion the
uncorrected residual is precisely `H - H₀`. The bound on this mean difference
is a separate input from the normalized-background proposition. -/
theorem referenceMeanResidual_eq_sub {G : Euclidean n → Euclidean N}
    {U : Set (Euclidean n)} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (himm : IsImmersionOn G U) (hflat : ∀ x ∈ U, inducedMetric G x = 1)
    (H₀ : MetricTensor n) (hH₀ : H₀.IsSymm) (H : MetricField n) :
    EqOn (referenceMeanResidual G H₀ H) (fun x ↦ H x - H₀) U := by
  intro x hx
  change linearizedMetric G (tangentVariation G (referenceVectorField H₀)) x + H x = _
  rw [linearizedMetric_referenceVectorField hU hG himm hflat H₀ hH₀ hx]
  exact (sub_eq_neg_add (H x) H₀).symm

/-- `app:ch_background:prop:bg-positive`: a smooth density correction bounded
in absolute value by `1/2` gives a positive smooth amplitude on the entire
carrier/initial-variable domain and exactly the prescribed density. This is the
scalar conclusion conditional on the still-needed synthesis bounds. -/
theorem amplitude_properties_of_small_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {v : E → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hv : ContDiffOn ℝ ∞ v U) (hsmall : ∀ x ∈ U, |v x| ≤ (1 / 2 : ℝ)) :
    (∀ x ∈ U, (1 / 2 : ℝ) ≤ 1 + v x) ∧
      ContDiffOn ℝ ∞ (fun x ↦ positiveDensityAmplitude σ (v x)) U ∧
      (∀ x ∈ U, 0 < positiveDensityAmplitude σ (v x)) ∧
      (∀ x ∈ U, positiveDensityAmplitude σ (v x) ^ 2 = σ ^ 2 * (1 + v x)) := by
  have hlower (x : E) (hx : x ∈ U) : (1 / 2 : ℝ) ≤ 1 + v x := by
    have h := (abs_le.mp (hsmall x hx)).1
    linarith
  have hpos (x : E) (hx : x ∈ U) : 0 < 1 + v x :=
    lt_of_lt_of_le (by norm_num) (hlower x hx)
  exact ⟨hlower, contDiffOn_positiveDensityAmplitude σ hv hpos,
    fun x hx ↦ positiveDensityAmplitude_pos hσ (hpos x hx),
    fun x hx ↦ positiveDensityAmplitude_sq (hpos x hx).le⟩

end JanetCartan.PositiveBackground
