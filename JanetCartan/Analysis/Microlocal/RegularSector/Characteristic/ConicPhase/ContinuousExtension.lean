module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension.Elapsed
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Localization

/-!
# A globally continuous auxiliary for the same two-time conic phase

Localize the original two-time phase smoothly near the compact buffer and
apply the fixed radial extension. Compact support proves continuity on the
whole joint space and smoothness away from the zero spatial covector. The
extension retains exact positive degree-one homogeneity and agrees as a
joint germ with the original conic phase throughout the supported cone.
The imported elapsed-phase congruence lemmas retain both physical masks and
the original graph realization.

The parent construction supplies the compact buffer and local smoothness
from `BufferedKernel.exists_buffered_physical_pencil_kernel`. No extended
phase bound or global continuity assumption is required.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.ConicPhase
open FourierIntegral
variable {d : ℕ}

/-- Construct one globally continuous, positively homogeneous joint
auxiliary phase for the actual conic continuation of `twoTimePhase C`.
It is smooth away from zero spatial frequency and has the same joint germ
at every point whose positive radial representative lies in `K`.

The compact buffer, its inclusion and local phase smoothness are supplied
by `exists_buffered_physical_pencil_kernel`. The parent instantiates these
data; `elapsedGraph_eq_of_conic_extension` then removes the auxiliary from
the supported full graph. Source:
`app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_continuous_conicPhase_extension
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {K : Set (TwoTimePoint (Euclidean d))} (hK : IsCompact K) (hKC : K ⊆ C.target)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target) :
    ∃ G : TwoTimePoint (Euclidean d) → ℝ,
      Continuous G ∧ ContDiffOn ℝ ∞ G {q | q.2.2.2 ≠ 0} ∧
      (∀ (q : TwoTimePoint (Euclidean d)) (a : ℝ), 0 < a →
        G (q.1, (q.2.1, (q.2.2.1, a • q.2.2.2))) = a * G q) ∧
      ∀ q ∈ domain ℓ K, G =ᶠ[𝓝 q] phase ℓ C := by
  obtain ⟨F, hF, hc, _, _, he⟩ :=
    NormalComparison.exists_contDiff_localization C.open_target hK hKC hC
  exact ⟨extend ℓ F, continuous_extend_of_hasCompactSupport ℓ hF.continuous hc,
    contDiffOn_extend_off_zero ℓ hF hc,
    fun q _ ha ↦ extend_smul ℓ F q ha,
    fun q hq ↦ extend_eventuallyEq_phase ℓ C hq.1.ne' (he _ hq.2)⟩

end JanetCartan.RegularSector.Characteristic.ConicPhase
