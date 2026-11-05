module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SignedSourceAdmission
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Completion

/-!
# The original source cutoff in the one sampled response

`app:ch_pairs:eq:pairs-weighted-U` applies the response to `χsrc Qoff`.
The linear map below is the existing ambient extension composed with that
fixed multiplication. It makes no new extension choice. Its signed sources
are admitted using the actual sampled derivatives, so the agreement and
regularity conclusions of the existing response apply to those same fields.

The reduced solver and its quantitative estimates remain inputs from
`both-fixed-inverse` and `both-response-transfer`. In particular this module
does not construct the uniform response estimates or `UniformHistoryCorrection`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.UniformStep

open PrimarySourceAdmission ResponseSourceExtension

variable {n N : ℕ} {κ : Type*}
variable (F : Euclidean n → Euclidean N) (Q : Euclidean n → κ → MetricTensor n)
variable (η : Euclidean n → ℝ)
variable (T : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → κ → ℝ))
variable (S : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → Euclidean n))
variable {core chart : Set (Euclidean n)} (Ξ : OutputCutoff core chart)
variable (χ : Euclidean n → ℝ)
variable (hS : ∀ h : compactSmoothSources (tsupport χ), ∀ x ∈ chart,
  DifferentiableAt ℝ (S (AmbientResponse.correctedStressSource Q η T h)) x)

/-- The SAME whole-source response, preceded by the original tensor source
cutoff in `app:ch_pairs:eq:pairs-weighted-U`. Both the source multiplier `χ`
and the output cutoff `Ξ` are fixed before signs, samples, accuracy and norm
orders. This is the map consumed by the sampled-product synthesis estimates. -/
def sourceCutoffAmbientResponse : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N) :=
  (ambientExtension F Q η T S (compactSmoothSources (tsupport χ)) Ξ hS).comp
    (LinearMap.pi fun x ↦ χ x • LinearMap.proj x)

/-- The source cutoff is applied exactly once, before the original ambient
extension (`app:ch_pairs:eq:pairs-weighted-U`). -/
theorem sourceCutoffAmbientResponse_apply (q : MetricField n) :
    sourceCutoffAmbientResponse F Q η T S Ξ χ hS q =
      ambientExtension F Q η T S (compactSmoothSources (tsupport χ)) Ξ hS
        (fun x ↦ χ x • q x) := rfl

variable {U : Set (Euclidean n)} (hU : IsOpen U)
variable (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)

include hU hχ hc hs

/-- For every source smooth on the original support chart, the masked
extension is exactly the original ambient formula with its original output
cutoff (`app:ch_response:eq:response-full-map`). Source admission is proved,
not assumed. Consumed by the cut signed-product Sobolev estimate. -/
theorem sourceCutoffAmbientResponse_eq_cutoff (q : MetricField n)
    (hq : ContDiffOn ℝ ∞ q U) :
    sourceCutoffAmbientResponse F Q η T S Ξ χ hS q =
      fun x ↦ Ξ.toFun x •
        AmbientResponse.ambientResponse F Q η T S (fun y ↦ χ y • q y) x := by
  exact ambientExtension_eq_cutoff F Q η T S (compactSmoothSources (tsupport χ))
    Ξ hS ⟨_, cutoff_mem_compactSmoothSources hχ hc hU hq hs⟩

/-- On the original response core, the full strain residual of the masked
linear map is the actual ambient residual for the cutoff source. Only the
value `χ x = 1` is used to remove the source multiplier from its leading term
(`app:ch_pairs:eq:pairs-lag-sum-error`). The response itself keeps the cutoff. -/
theorem sourceCutoffAmbientResponse_error_eq (q : MetricField n)
    (hq : ContDiffOn ℝ ∞ q U) {x : Euclidean n} (hx : x ∈ core) (hone : χ x = 1) :
    linearizedMetric F (sourceCutoffAmbientResponse F Q η T S Ξ χ hS q) x - q x =
      linearizedMetric F
        (AmbientResponse.ambientResponse F Q η T S (fun y ↦ χ y • q y)) x -
          χ x • q x := by
  rw [sourceCutoffAmbientResponse_apply,
    linearizedMetric_ambientExtension_eq F Q η T S (compactSmoothSources (tsupport χ))
      Ξ hS ⟨_, cutoff_mem_compactSmoothSources hχ hc hU hq hs⟩ hx,
    hone, one_smul]

variable (ho : IsOpen chart) (hF : ContDiffOn ℝ ∞ F chart)
variable (hi : IsImmersionOn F chart) (hrank : HasFullNormalRankOn F chart)
variable (hreg : ∀ h : compactSmoothSources (tsupport χ),
  ContDiffOn ℝ ∞ (S (AmbientResponse.correctedStressSource Q η T h)) chart)

include ho hF hi hrank hreg

/-- The original reduced solver's chart regularity gives global smoothness
of the masked ambient output (`app:ch_response:prop:response-ambient`). The
source is admitted from its local smoothness and the fixed source cutoff.
Consumed by the signed-product stage estimates, which no longer need a
separate smooth-response premise for each sampled source. -/
theorem contDiff_sourceCutoffAmbientResponse (q : MetricField n)
    (hq : ContDiffOn ℝ ∞ q U) :
    ContDiff ℝ ∞ (sourceCutoffAmbientResponse F Q η T S Ξ χ hS q) := by
  have hmem := cutoff_mem_compactSmoothSources hχ hc hU hq hs
  exact contDiff_ambientExtension F Q η T S (compactSmoothSources (tsupport χ))
    Ξ hS ⟨_, hmem⟩ ho hF hmem.1.contDiffOn hi hrank (hreg ⟨_, hmem⟩)

/-- Both complete signed sources of the actual sampled derivatives have
smooth outputs under the SAME source-cutoff response
(`app:ch_pairs:prop:pairs-lag-sum`). No regularity of a separately selected
phase extension is required. Consumed by the pair strain and Sobolev bounds. -/
theorem contDiff_sourceCutoffAmbientResponse_sampled_sources {ι : Type*}
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U) (i j : ι) :
    ContDiff ℝ ∞ (sourceCutoffAmbientResponse F Q η T S Ξ χ hS
      (ProductSum.plusSource θ (sampledDerivativeAmplitude Z θ) i j)) ∧
    ContDiff ℝ ∞ (sourceCutoffAmbientResponse F Q η T S Ξ χ hS
      (ProductSum.minusSource θ (sampledDerivativeAmplitude Z θ) i j)) := by
  obtain ⟨hp, hm⟩ := contDiffOn_sampled_signed_sources Z θ hU hZ i j
  exact ⟨contDiff_sourceCutoffAmbientResponse F Q η T S Ξ χ hS hU hχ hc hs
      ho hF hi hrank hreg _ hp,
    contDiff_sourceCutoffAmbientResponse F Q η T S Ξ χ hS hU hχ hc hs
      ho hF hi hrank hreg _ hm⟩

/-- Full tensor reconstruction for the SAME masked response
(`app:ch_response:eq:response-full-identity`). The only equation premise is
the reduced solver's original physical identity on the actual corrected
stress source. Source admission and the ambient normal equation are derived.
Consumed by `sourceCutoffAmbientResponse_error_norm_le`. -/
theorem sourceCutoffAmbientResponse_error_eq_full_residual [Fintype κ] [DecidableEq κ]
    (A : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → κ → ℝ))
    (q : MetricField n) (hq : ContDiffOn ℝ ∞ q U)
    (hsymm : ∀ x ∈ chart, (q x).IsSymm)
    (hη : ∀ x ∈ tsupport χ, η x = 1)
    (hQ : ∀ x ∈ chart, LinearIndependent ℝ (Q x))
    (hspan : ∀ x ∈ chart,
      (Submodule.span ℝ (range (Q x)) : Set (MetricTensor n)) = stressSpace F x)
    (hphysical : ∀ x ∈ chart, ∀ a,
      tensorPairing (Q x a) (symmCovariantDeriv F
        (S (AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y))) x) =
      AmbientResponse.cutoffSource η
          (AmbientResponse.stressSource Q (fun y ↦ χ y • q y)) x a +
        (A (AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y)) x a -
          AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y) x a))
    {x : Euclidean n} (hx : x ∈ core) (hone : χ x = 1) :
    let z := AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y)
    linearizedMetric F (sourceCutoffAmbientResponse F Q η T S Ξ χ hS q) x - q x =
      (2 : ℝ) • ∑ a, ∑ b, ((stressGram (Q x))⁻¹ a b *
        (A z x b - z x b)) • Q x a := by
  have hmem := cutoff_mem_compactSmoothSources hχ hc hU hq hs
  have hsupport : Function.support (fun y ↦ χ y • q y) ⊆ {y | η y = 1} := by
    intro y hy
    apply hη y
    apply subset_tsupport
    intro hyχ
    exact hy (by simp [hyχ])
  have hxchart : x ∈ chart := by
    apply Ξ.support_chart
    apply subset_tsupport
    have hxΞ : x ∈ {y | Ξ.toFun y = 1} := interior_subset (Ξ.plateau hx)
    change Ξ.toFun x = 1 at hxΞ
    simp [hxΞ]
  rw [sourceCutoffAmbientResponse_error_eq F Q η T S Ξ χ hS hU hχ hc hs q hq hx hone]
  exact AmbientResponse.ambientResponse_error_eq_full_residual Q η T A S ho hF
    hmem.1.contDiffOn (fun y hy ↦ (hsymm y hy).smul (χ y)) hsupport hi hrank
    hQ hspan (hreg ⟨_, hmem⟩) hphysical hxchart

/-- The reduced residual gives the full strain error of the original
source-cutoff response, with the SAME inverse stress Gram matrix
(`app:ch_pairs:eq:pairs-lag-sum-error`). The bound is for one complete signed
source; the sampled synthesis then incurs only `coefficientMass μ`.
The constant `Cgram` and the reduced error `ε` stay separate so their actual
producers can choose them uniformly before histories. -/
theorem sourceCutoffAmbientResponse_error_norm_le [Fintype κ] [DecidableEq κ]
    (A : (Euclidean n → κ → ℝ) →ₗ[ℝ] (Euclidean n → κ → ℝ))
    (q : MetricField n) (hq : ContDiffOn ℝ ∞ q U)
    (hsymm : ∀ x ∈ chart, (q x).IsSymm)
    (hη : ∀ x ∈ tsupport χ, η x = 1)
    (hQ : ∀ x ∈ chart, LinearIndependent ℝ (Q x))
    (hspan : ∀ x ∈ chart,
      (Submodule.span ℝ (range (Q x)) : Set (MetricTensor n)) = stressSpace F x)
    (hphysical : ∀ x ∈ chart, ∀ a,
      tensorPairing (Q x a) (symmCovariantDeriv F
        (S (AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y))) x) =
      AmbientResponse.cutoffSource η
          (AmbientResponse.stressSource Q (fun y ↦ χ y • q y)) x a +
        (A (AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y)) x a -
          AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y) x a))
    {x : Euclidean n} (hx : x ∈ core) (hone : χ x = 1)
    {Cgram ε : ℝ} (hε : 0 ≤ ε)
    (hgram : 2 * (∑ a, ∑ b, |(stressGram (Q x))⁻¹ a b| * ‖Q x a‖) ≤
      Cgram)
    (hresidual : ∀ b,
      |A (AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y)) x b -
        AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y) x b| ≤ ε) :
    ‖linearizedMetric F (sourceCutoffAmbientResponse F Q η T S Ξ χ hS q) x - q x‖ ≤
      Cgram * ε := by
  rw [sourceCutoffAmbientResponse_error_eq_full_residual F Q η T S Ξ χ hS
    hU hχ hc hs ho hF hi hrank hreg A q hq hsymm hη hQ hspan hphysical hx hone,
    norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  let z := AmbientResponse.correctedStressSource Q η T (fun y ↦ χ y • q y)
  have hnorm := CurrentMean.norm_inverseGramReconstruction_le (Q x)
    (fun b ↦ A z x b - z x b)
  rw [inverseGramReconstruction_eq_sum] at hnorm
  calc
    _ ≤ 2 * (∑ a, ∑ b,
        |(stressGram (Q x))⁻¹ a b| * |A z x b - z x b| * ‖Q x a‖) := by
      exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ ≤ 2 * (∑ a, ∑ b,
        |(stressGram (Q x))⁻¹ a b| * ε * ‖Q x a‖) := by
      gcongr with a b
      exact hresidual b
    _ = (2 * (∑ a, ∑ b,
        |(stressGram (Q x))⁻¹ a b| * ‖Q x a‖)) * ε := by
      simp only [Finset.sum_mul, mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ Cgram * ε := mul_le_mul_of_nonneg_right hgram hε

end JanetCartan.UniformStep
