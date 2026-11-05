module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Derivatives
public import JanetCartan.Analysis.Extension.Mollification.WeakDeriv

/-!
# Classical identification of L² coordinate derivatives

Compact tests identify the distributional derivative of a smooth L² envelope
with its classical derivative. This supplies the jet realization needed for
`app:ch_response:eq:response-graded-displacement` and
`app:ch_response:eq:response-graded-derivative`, without growth assumptions on
classical derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound

namespace JanetCartan.IsometricEmbedding.Reconstruction

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The actual distributional coordinate derivative of a smooth L² envelope is
its classical derivative almost everywhere, for
`app:ch_response:eq:response-graded-derivative`. Only the original function is
assumed to represent an L² class; no classical derivative integrability is assumed. -/
theorem coordinateDerivative_ae_eq_classical {f : E → ℂ} (hf : ContDiff ℝ ∞ f) {u v : L2}
    (hu : u =ᵐ[volume] f) {i : Fin d}
    (hv : HasEuclideanL2CoordinateDerivative i u v) :
    v =ᵐ[volume] euclideanCoordinateDerivList [i] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp v).locallyIntegrable (by norm_num))
    (contDiff_euclideanCoordinateDerivList hf [i]).continuous.locallyIntegrable
  intro ψ hψ hc
  have hcc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hcd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let test : 𝓢(E, ℂ) := hcc.toSchwartzMap hcd
  have he := congrArg (fun T : 𝓢'(E, ℂ) ↦ T test) hv
  have hd (x : E) : fderiv ℝ (fun x ↦ (ψ x : ℂ)) x =
      Complex.ofRealCLM.comp (fderiv ℝ ψ x) :=
    Complex.ofRealCLM.hasFDerivAt.comp x
      (hψ.differentiable (by simp) x).hasFDerivAt |>.fderiv
  have ht (x : E) : (LineDeriv.lineDerivOp (EuclideanSpace.basisFun (Fin d) ℝ i) test) x =
      (fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (fun x ↦ (ψ x : ℂ)) x _ = _
    rw [hd]
    simp [EuclideanSpace.basisFun_apply]
  simp only [euclideanCoordinateDerivative,
    TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, ht, neg_smul, integral_neg] at he
  change -∫ x, (fderiv ℝ ψ x (EuclideanSpace.single i 1) : ℂ) * u x =
    ∫ x, (ψ x : ℂ) * v x at he
  simp only [← Complex.real_smul] at he
  have he' : (∫ x, ψ x • v x) = -∫ x, fderiv ℝ ψ x (EuclideanSpace.single i 1) • f x := by
    rw [← he]
    congr 1
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    simp only [hx, Complex.real_smul]
  rw [he']
  exact (JanetCartan.Mollification.hasWeakFDerivOn_of_contDiff
    volume (hf.of_le (by simp)) Set.univ).2.2 ψ hψ hc (Set.subset_univ _) _ |>.symm

end JanetCartan.IsometricEmbedding.Reconstruction
