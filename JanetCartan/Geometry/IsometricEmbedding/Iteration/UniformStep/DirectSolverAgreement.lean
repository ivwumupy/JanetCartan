module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SourceCutoffResponse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.AdmittedResponse

/-!
# The direct solver on the original product-source cutoff

The normalized direct constructor admits tensors through the full primary
support. The product cutoff has smaller support. The SAME correction and solve
factors remain valid on these sources, and the two ambient constructions agree
there as global fields. No equality of algebraic extensions off the admitted
source space is claimed (`app:ch_pairs:eq:pairs-weighted-U`).
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.UniformStep

open CanonicalAtomRealization CorrectedAtoms FixedDomainInverse LocalSobolev
open PrimarySourceAdmission ResponseSourceExtension AmbientResponse

variable {n N : ℕ} (F : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
    {S U W core chart : Set (Euclidean n)} (hU : IsOpen U)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
    (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
    (Zcorr solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v))
    (hW : MeasurableSet W) (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
    (Pphys : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
      Lp (Euclidean n) 2 volume)
    (hZcorr : ∀ v : smoothSource W (Euclidean n),
      Zcorr v =ᵐ[volume] SmallSupport.zeroExtend hW (Corr v))
    (hsolverAe : ∀ v : smoothSource W (Euclidean n),
      solver v =ᵐ[volume] Pphys (SmallSupport.zeroExtend hW (Corr v)))
    (χ : Euclidean n → ℝ) (hχS : tsupport χ ⊆ S)

local notation "Tresp" => directStressCorrectionFactor Q η hU hQ hη hSU Zcorr
local notation "Sresp" => directPhysicalSolveFactor Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe

include hχS in
/-- `app:ch_response:prop:response-ambient`: the normalized solver's actual
smooth realization discharges the product source's regularity input while
retaining the original, larger source-correction domain. Consumed by the
source-cutoff response in `exists_normalized_measured_direct_sampled_stage`. -/
theorem contDiff_directProductSolve (h : compactSmoothSources (tsupport χ)) :
    ContDiff ℝ ∞ (Sresp (correctedStressSource Q η Tresp h)) := by
  let hfull : compactSmoothSources S :=
    ⟨h, h.property.1, h.property.2.1, h.property.2.2.trans hχS⟩
  exact contDiff_directPhysicalSolveFactor_correctedStressSource Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe hfull

local notation "hsolved" => contDiff_directProductSolve Q η hU hQ hη hSU
  Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS

/-- The two response formulas agree on a tensor admitted by the original
product cutoff (`app:ch_pairs:eq:pairs-weighted-U`). This form applies to
the complete off-self source using `sampled_offSelf_source_mem`. -/
theorem sourceCutoffAmbientResponse_direct_eq_fixedSolver_of_mem
    (Ξ : OutputCutoff core chart) (q : MetricField n)
    (hq : (fun x ↦ χ x • q x) ∈ compactSmoothSources (tsupport χ)) :
    sourceCutoffAmbientResponse F Q η Tresp Sresp Ξ χ
      (fun h x _ ↦ (hsolved h).differentiable (by simp) x) q =
      fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun x ↦ χ x • q x) := by
  let hfull : compactSmoothSources S :=
    ⟨_, hq.1, hq.2.1, hq.2.2.trans hχS⟩
  rw [sourceCutoffAmbientResponse_apply,
    ambientExtension_eq_cutoff F Q η Tresp Sresp (compactSmoothSources (tsupport χ))
      Ξ _ ⟨_, hq⟩,
    fixedSmoothSolverAmbientExtension_eq_cutoff F Q η hU hQ hη hSU solver hsolver Ξ hfull]
  exact congrArg (fun v ↦ fun x ↦ Ξ.toFun x • completedVariation F v (hfull : MetricField n) x)
    (directPhysicalSolveFactor_correctedStressSource Q η hU hQ hη hSU
      Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe hfull)

/-- `app:ch_pairs:eq:pairs-weighted-U`: the source-cutoff ambient extension
equals the normalized constructor's original fixed solver on the literal
cutoff tensor. Admission is proved from local smoothness. The correction
factor keeps the primary-source domain; only the admitted tensor is restricted.
This equality transfers the constructed signed-source size estimates to the
unchanged stage field. -/
theorem sourceCutoffAmbientResponse_direct_eq_fixedSolver (Ξ : OutputCutoff core chart)
    {V : Set (Euclidean n)} (hV : IsOpen V)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V)
    (q : MetricField n) (hq : ContDiffOn ℝ ∞ q V) :
    sourceCutoffAmbientResponse F Q η Tresp Sresp Ξ χ
      (fun h x _ ↦ (hsolved h).differentiable (by simp) x) q =
      fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
        (fun x ↦ χ x • q x) := by
  exact sourceCutoffAmbientResponse_direct_eq_fixedSolver_of_mem F Q η hU hQ hη hSU
    Zcorr solver hsolver hW Corr Pphys hZcorr hsolverAe χ hχS Ξ q
    (cutoff_mem_compactSmoothSources hχ hχc hV hq hχV)

end JanetCartan.UniformStep
