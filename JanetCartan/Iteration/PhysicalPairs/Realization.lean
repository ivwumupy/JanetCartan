module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SourceCutoffResponse
public import JanetCartan.Analysis.PhysicalCutoff.Tail

/-!
# The real whole-space full signed-product field

The field in paper-v2 `main:prop:pairs` is the original full-source ambient
response with its original source and output cutoffs. We realize that SAME
field as a real Schwartz map. The reduced inverse and its smooth realization
are supplied by the common initializer; no quantitative output estimate is
assumed here. All complete signed sources are admitted from the final complex
family, including the plus diagonal. No sample, phase, or inverse is selected
again. The residual and physical size estimates remain separate obligations.
-/

@[expose] public noncomputable section

open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPairs

open PrimarySourceAdmission ResponseSourceExtension UniformStep

variable {n N : ℕ} {κ : Type*}
variable (F : Euclidean n → Euclidean N) (Q : Euclidean n → κ → MetricTensor n)
variable (η : Euclidean n → ℝ)
variable (T : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → κ → ℝ))
variable (Rinv : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
variable {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
variable {χ : Euclidean n → ℝ}
variable (hsolve : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
  DifferentiableAt ℝ (Rinv (AmbientResponse.correctedStressSource Q η T h)) x)
variable (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
variable (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
variable (hreg : ∀ h : compactSmoothSources (tsupport χ),
  ContDiffOn ℝ ∞ (Rinv (AmbientResponse.correctedStressSource Q η T h)) chart)

/-- The SAME ambient response on its actual smooth source domain, now valued in
real Schwartz maps (`main:prop:pairs`). Compact support and smoothness are proved
from the existing reconstruction, not asserted for arbitrary nonsmooth sources. -/
def ambientSchwartzResponse :
    compactSmoothSources (tsupport χ) →ₗ[ℝ] 𝓢(Euclidean n, Euclidean N) where
  toFun h := (hasCompactSupport_ambientExtension F Q η T Rinv
    (compactSmoothSources (tsupport χ)) Ξ hsolve h).toSchwartzMap
      (contDiff_ambientExtension F Q η T Rinv (compactSmoothSources (tsupport χ))
        Ξ hsolve h ho hF h.property.1.contDiffOn hi hrank (hreg h))
  map_add' h k := by
    apply SchwartzMap.ext
    intro x
    change ambientExtension F Q η T Rinv (compactSmoothSources (tsupport χ))
      Ξ hsolve (↑(h + k)) x = _
    exact congrFun (map_add (ambientExtension F Q η T Rinv
      (compactSmoothSources (tsupport χ)) Ξ hsolve) (h : MetricField n) k) x
  map_smul' a h := by
    apply SchwartzMap.ext
    intro x
    change ambientExtension F Q η T Rinv (compactSmoothSources (tsupport χ))
      Ξ hsolve (↑(a • h)) x = _
    exact congrFun (map_smul (ambientExtension F Q η T Rinv
      (compactSmoothSources (tsupport χ)) Ξ hsolve) a (h : MetricField n)) x

/-- Literal pointwise identity, with the original whole-source operator
unchanged (`main:prop:pairs`). -/
theorem ambientSchwartzResponse_coe (h : compactSmoothSources (tsupport χ)) :
    ⇑(ambientSchwartzResponse F Q η T Rinv Ξ hsolve ho hF hi hrank hreg h) =
      ambientExtension F Q η T Rinv (compactSmoothSources (tsupport χ)) Ξ hsolve h := rfl

/-- Exact original ambient formula with its fixed output cutoff
(`main:prop:pairs`), before any accuracy or Sobolev order. -/
theorem ambientSchwartzResponse_apply (h : compactSmoothSources (tsupport χ)) (x : Euclidean n) :
    ambientSchwartzResponse F Q η T Rinv Ξ hsolve ho hF hi hrank hreg h x =
      Ξ.toFun x • AmbientResponse.ambientResponse F Q η T Rinv h x :=
  congrFun (ambientExtension_eq_cutoff F Q η T Rinv
    (compactSmoothSources (tsupport χ)) Ξ hsolve h) x

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (b : ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
variable (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
variable {U : Set (Euclidean n)} (hU : IsOpen U)
variable (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U)
variable (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)

/-- The actual correction of the complete off-self tensor of the supplied final
family (`main:prop:pairs`). Source admission is derived internally. It retains
the original inverse, both source multipliers, and the original output cutoff. -/
def offSelfCorrection : 𝓢(Euclidean n, Euclidean N) :=
  -ambientSchwartzResponse F Q η T Rinv Ξ hsolve ho hF hi hrank hreg
    ⟨fun x ↦ χ x • ProductSum.offSelfSource b μ (sampledDerivative Z)
      (sampledDerivativeAmplitude Z θ) x,
      (sampled_offSelf_source_mem b μ hμ Z θ hU hZ hχ hc hs).1⟩

/-- The constructed real Schwartz correction is literally the original single
response on the FULL source, not a new choice for each sign (`main:prop:pairs`). -/
theorem offSelfCorrection_coe :
    ⇑(offSelfCorrection F Q η T Rinv Ξ hsolve ho hF hi hrank hreg
      b μ hμ Z θ hU hZ hχ hc hs) =
      -sourceCutoffAmbientResponse F Q η T Rinv Ξ χ hsolve
        (ProductSum.offSelfSource b μ (sampledDerivative Z) (sampledDerivativeAmplitude Z θ)) := rfl

/-- Each individual signed response is realized by the same real Schwartz map.
This does not assume any individual response norm or residual estimate
(`main:prop:pairs`). -/
def signedResponse (minus : Bool) (i j : ι) : 𝓢(Euclidean n, Euclidean N) :=
  ambientSchwartzResponse F Q η T Rinv Ξ hsolve ho hF hi hrank hreg
    ⟨fun x ↦ χ x • (if minus then
      ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j x else
      ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j x), by
      cases minus with
      | false => exact (sampled_signed_sources_mem Z θ hU hZ hχ hc hs i j).1
      | true => exact (sampled_signed_sources_mem Z θ hU hZ hχ hc hs i j).2⟩

/-- The SAME correction has the complete signed expansion in real Schwartz
space. Every plus pair, including doubled carriers, remains; only the minus
diagonal is omitted (`main:prop:pairs`, `main:eq:self-off`). -/
theorem offSelfCorrection_eq_signed :
    offSelfCorrection F Q η T Rinv Ξ hsolve ho hF hi hrank hreg
      b μ hμ Z θ hU hZ hχ hc hs =
      -ProductSum.weightedSignedSum b μ
        (signedResponse F Q η T Rinv Ξ hsolve ho hF hi hrank hreg Z θ hU hZ hχ hc hs false)
        (signedResponse F Q η T Rinv Ξ hsolve ho hF hi hrank hreg Z θ hU hZ hχ hc hs true) := by
  apply DFunLike.coe_injective
  rw [offSelfCorrection_coe]
  rw [ProductSum.solve_offSelfSource _ b μ hμ θ _ _
    (sampledDerivative_eq_phase_smul_amplitude Z θ)]
  funext x
  simp only [ProductSum.weightedSignedSum, neg_apply, smul_apply, add_apply, sum_apply,
    Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Finset.sum_apply]
  rfl

/-- Every physical Fourier-Sobolev norm of this SAME field is finite, directly
from its proved Schwartz realization (`main:prop:pairs`). -/
theorem memLp_weightedFourier_offSelfCorrection (s : ℝ) :
    MemLp (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (PhysicalCutoff.complexify (offSelfCorrection F Q η T Rinv Ξ hsolve ho hF hi hrank hreg
        b μ hμ Z θ hU hZ hχ hc hs)) ξ) 2 volume :=
  PhysicalCutoff.memLp_physicalWeightedFourier s _

end JanetCartan.PhysicalPairs
