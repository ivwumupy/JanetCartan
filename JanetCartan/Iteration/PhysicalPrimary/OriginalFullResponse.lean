module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalAmbientResponse
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSolver
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponseTemplate

/-!
# The actual original-history globally uncut ambient response

Specialize the full vector solver to the original current immersion and full
projected coefficients. The fixed tensor source domain is exactly tsupport chi2;
the stress source multiplier is chi-src. The paired solver output is not cut.
The exported identity is literal equality with canonical completedVariation,
not a claimed response norm bound or an already closed strain-error estimate.
Consumers are the full physical kernel and its full derivative amplitude
(`app:ch_response:eq:response-full-map`, `main:prop:current-waves`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalFullResponse

/-- The original globally smooth full Q supplies the componentwise source
constructor on univ; no coefficient extension is reselected. -/
theorem components_smooth_univ {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiff ℝ ∞ Q) :
    ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) univ := by
  intro i
  exact (contDiff_pi.mp hQ i).contDiffOn

construct_original_full_ambient_response

end JanetCartan.PhysicalPrimary.OriginalFullResponse
