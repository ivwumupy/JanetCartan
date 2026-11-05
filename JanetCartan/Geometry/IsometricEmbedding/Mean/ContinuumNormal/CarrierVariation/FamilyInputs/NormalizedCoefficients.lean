module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CompactSlices
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Fields
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms

/-!
# Primitive coefficient convergence of the source-normalized carrier

The normal and reduced covector are constructed from the seed canonical
normal completion, projected stress, phase covector and null amplitude.
Their identities at positive scales use the actual dilation formulas;
no output coefficient continuity is an input. All three masks are fixed.
The consumer is the primitive coefficient comparison on `CoefficientNormCharts`
in `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'.

The seed phase and null amplitude must still be instantiated by their actual
producers. These results do not identify independently selected Hamilton
charts, supply the ODE density footpoint, or prove the wider initial-density
class in the original `paper.tex`, `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open NormalizedBackground NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol LeadingWave AmbientResponse

section Pullback
variable {E Z F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Each regular normalized coefficient converges in every finite joint
space/carrier norm on its fixed compact set. This is the compact-slice lemma
applied to the literal source pullback, not an assumed coefficient-family
continuity statement. Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem tendsto_normalizedPullback_sub_cNorm
    {f : E × Z → F} {U B : Set E} {V : Set Z} {I : Set ℝ} {K : Set (E × Z)}
    (hI : IsOpen I) (hB : IsOpen B) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V))
    (hmaps : ∀ σ ∈ I, MapsTo (fun x ↦ σ • x) B U)
    (hK : IsCompact K) (hKBV : K ⊆ B ×ˢ V) {σ₀ : ℝ} (hσ₀ : σ₀ ∈ I) (m : ℕ) :
    Tendsto (fun σ ↦ cNorm K m
      ((fun p ↦ normalizedPullback f (σ, p)) -
        (fun p ↦ normalizedPullback f (σ₀, p)))) (𝓝 σ₀) (𝓝 0) := by
  have hs : ContDiffOn ℝ ∞ (normalizedPullback f) (I ×ˢ B ×ˢ V) :=
    (contDiffOn_normalizedPullback hf).mono
      (fun _ hq ↦ ⟨hmaps _ hq.1 hq.2.1, hq.2.2⟩)
  exact tendsto_cNorm_slice_sub hI (hB.prod hV) hs hK hKBV hσ₀ m
end Pullback

variable {n N : ℕ}

/-- Literal normalized primitive coefficients, with masks fixed before scale.
At positive scales `normalizedSourceCoefficients_eq_sourceDilation` identifies
them with the canonical completion of the actual dilated immersion.
Source: `app:ch_background:eq:bg-T`, `app:ch_background:eq:bg-Nsigma`. -/
def normalizedSourceCoefficients
    (F : Euclidean n → Euclidean N)
    (ξ b : Euclidean n × (ℝ × Euclidean 2) → Euclidean n)
    (measurement : Euclidean n → ℝ)
    (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (σ : ℝ) : Coefficients n N where
  measurement := measurement
  angular := angular
  high := high
  normal := fun p ↦ normalizedPullback
    (fun q ↦ principalNormal (canonicalNormalCompletion F q.1) (ξ q) (b q)) (σ, p)
  reduced := fun p ↦ (ActualCarriers.quadratic (ProjectedStressFrame.projectedStress F
    (σ • p.1)) (ξ (σ • p.1, p.2))).ofLp

/-- The primitive family is the actual scaled normal and detector, with
initial null amplitude scaled by `σ`. The zero slice uses only the regular
seed fields; no normal-rank assertion at `G₀` is made.
Source: `app:ch_background:eq:bg-Nsigma`. -/
theorem normalizedSourceCoefficients_eq_sourceDilation
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (ξ b : Euclidean n × (ℝ × Euclidean 2) → Euclidean n)
    (measurement : Euclidean n → ℝ)
    (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {σ : ℝ} (hσ : 0 < σ) (p : Euclidean n × (ℝ × Euclidean 2))
    (hrank : Set.range (normalMap F (σ • p.1)) =
      (normalSpace F (σ • p.1) : Set (Euclidean N))) :
    (normalizedSourceCoefficients F ξ b measurement angular high σ).normal p =
      principalNormal (canonicalNormalCompletion (sourceDilation F σ) p.1)
        (ξ (σ • p.1, p.2)) (sourceAmplitude b σ p) ∧
    (normalizedSourceCoefficients F ξ b measurement angular high σ).reduced p =
      (ActualCarriers.quadratic (ProjectedStressFrame.projectedStress (sourceDilation F σ) p.1)
        (ξ (σ • p.1, p.2))).ofLp := by
  constructor
  · exact (principalNormal_sourceDilation_scaled_amplitude hσ hF p.1 hrank
      (ξ (σ • p.1, p.2)) (b (σ • p.1, p.2))).symm
  · have he := funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF p.1 hrank)
    simp only [normalizedSourceCoefficients, he]

/-- The two nonconstant primitive coefficients converge on the exact fixed
`CoefficientNormCharts.field.carrier` domain. Smoothness of their output
fields is derived from the actual seed geometry. In particular `σ₀ = 0`
is allowed whenever the fixed interval contains zero.
Source: `app:ch_background:prop:bg-normalized` and `paper-v2.tex`,
`app:ch_background:prop:bg-frame`. -/
theorem tendsto_normalizedSourceCoefficients_sub_cNorm
    {F : Euclidean n → Euclidean N} {U B : Set (Euclidean n)}
    {V : Set (ℝ × Euclidean 2)} {I : Set ℝ}
    (hU : IsOpen U) (hB : IsOpen B) (hV : IsOpen V) (hI : IsOpen I)
    (hF : ContDiffOn ℝ ∞ F U) (himm : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {ξ b : Euclidean n × (ℝ × Euclidean 2) → Euclidean n}
    (hξ : ContDiffOn ℝ ∞ ξ (U ×ˢ V)) (hb : ContDiffOn ℝ ∞ b (U ×ˢ V))
    (hmaps : ∀ σ ∈ I, MapsTo (fun x ↦ σ • x) B U)
    (D : CoefficientNormCharts n) (hD : D.field.carrier ⊆ B ×ˢ V)
    (measurement : Euclidean n → ℝ)
    (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {σ₀ : ℝ} (hσ₀ : σ₀ ∈ I) (m : ℕ) :
    let a := normalizedSourceCoefficients F ξ b measurement angular high
    Tendsto (fun σ ↦ cNorm D.field.carrier m ((a σ).normal - (a σ₀).normal))
      (𝓝 σ₀) (𝓝 0) ∧
    Tendsto (fun σ ↦ cNorm D.field.carrier m ((a σ).reduced - (a σ₀).reduced))
      (𝓝 σ₀) (𝓝 0) := by
  have hν := contDiffOn_canonicalPrincipalNormal hU hF himm hrank
    (U := U ×ˢ V) (fun _ hp ↦ hp.1) hξ hb
  have hQ : ContDiffOn ℝ ∞ (fun p : Euclidean n × (ℝ × Euclidean 2) ↦
      ProjectedStressFrame.projectedStress F p.1) (U ×ˢ V) :=
    (contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF himm hrank)).comp
      contDiffOn_fst (fun _ hp ↦ hp.1)
  have hq := PiLp.contDiff_ofLp.comp_contDiffOn
    (ActualCarriers.contDiff_quadratic.comp_contDiffOn (hQ.prodMk hξ))
  exact ⟨tendsto_normalizedPullback_sub_cNorm hI hB hV hν hmaps
      (isCompact_closedBall _ _) hD hσ₀ m,
    tendsto_normalizedPullback_sub_cNorm hI hB hV hq hmaps
      (isCompact_closedBall _ _) hD hσ₀ m⟩

/-- The remaining three primitive differences vanish identically, since the
cutoffs were chosen before scale. No upper frequency cutoff is introduced.
Source: `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem normalizedSourceCoefficients_fixedMask_differences
    (F : Euclidean n → Euclidean N)
    (ξ b : Euclidean n × (ℝ × Euclidean 2) → Euclidean n)
    (measurement : Euclidean n → ℝ)
    (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (D : CoefficientNormCharts n) (σ σ₀ : ℝ) (m : ℕ) :
    let a := normalizedSourceCoefficients F ξ b measurement angular high
    cNorm D.measurement.carrier m ((a σ).measurement - (a σ₀).measurement) = 0 ∧
    cNorm D.angular.carrier m ((a σ).angular - (a σ₀).angular) = 0 ∧
    cNorm D.high.carrier m ((a σ).high - (a σ₀).high) = 0 := by
  simp [normalizedSourceCoefficients]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
