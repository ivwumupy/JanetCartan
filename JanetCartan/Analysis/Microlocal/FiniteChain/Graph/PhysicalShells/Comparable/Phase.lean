module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.BufferedDecay
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.PhaseExtension

/-!
# Preserving the chart geometry under phase extension

The comparable physical-pair estimate for `app:ch_regular:eq:chain-tail` uses
the smooth extension only near the integration carrier and the mixed points
appearing in the chart inequalities. Agreement merely on the integration
carrier would not preserve those inequalities. The hypotheses below list all
the extra points explicitly; the parent chart construction must include them
in the compact subset of the actual phase domain used for extension.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
open FourierIntegral
variable {n : ℕ}

private theorem partial_fderiv_eq {φ ψ : Euclidean n → Euclidean n → ℝ}
    {u ξ : Euclidean n}
    (h : Function.uncurry ψ =ᶠ[𝓝 (u, ξ)] Function.uncurry φ) :
    fderiv ℝ (ψ u) ξ = fderiv ℝ (φ u) ξ ∧
      fderiv ℝ (fun v => ψ v ξ) u = fderiv ℝ (fun v => φ v ξ) u := by
  constructor
  · exact (h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt).fderiv_eq
  · exact (h.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt).fderiv_eq

/-- Preserve the forward chart, including its off-diagonal mixed evaluation
points (`app:ch_regular:eq:joint-stationary`). Consumer: the comparable-pair
estimate on a phase smooth only on its original chart domain. -/
theorem forwardChartControl_congr_phase
    {φ ψ : Euclidean n → Euclidean n → ℝ}
    {κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n}
    {I D T : Set (Euclidean n × Euclidean n)} {a b : ℝ}
    (H : ForwardChartControl φ κ I D a b)
    (heq : ∀ p ∈ T, Function.uncurry ψ =ᶠ[𝓝 p] Function.uncurry φ)
    (hD : D ⊆ T)
    (hr : ∀ q ∈ I, ((κ q).1, q.2) ∈ T)
    (hm : ∀ q ∈ I, ∀ p ∈ D, (p.1, q.2) ∈ T) :
    ForwardChartControl ψ κ I D a b := by
  have hd u ξ (h : (u, ξ) ∈ D) := partial_fderiv_eq (heq (u, ξ) (hD h))
  have hrel y η (h : (y, η) ∈ I) := partial_fderiv_eq (heq _ (hr _ h))
  have hmix y η (hi : (y, η) ∈ I) u ξ (h : (u, ξ) ∈ D) :=
    partial_fderiv_eq (heq _ (hm _ hi _ h))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u ξ h
    exact (H.differentiable u ξ h).congr_of_eventuallyEq (heq _ (hD h))
  · intro y η hi
    simpa only [ForwardRelation, (hrel y η hi).1, (hrel y η hi).2] using H.relation y η hi
  · intro y η hi u ξ h
    simpa only [(hmix y η hi u ξ h).1, (hrel y η hi).1] using H.inverse_bound y η hi u ξ h
  · intro y η hi u ξ h
    simpa only [(hmix y η hi u ξ h).1, (hd u ξ h).1] using H.covector_variation y η hi u ξ h
  · intro y η hi u ξ h
    simpa only [(hrel y η hi).2, (hd u ξ h).2] using H.base_variation y η hi u ξ h

/-- Preserve the literal reverse chart, including the mixed input-base
points (`app:ch_regular:eq:joint-stationary`). The physical weighted inverse
uses precisely this orientation. -/
theorem reverseChartControl_congr_phase
    {φ ψ : Euclidean n → Euclidean n → ℝ}
    {κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n}
    {I D T : Set (Euclidean n × Euclidean n)} {a b : ℝ}
    (H : ReverseChartControl φ κ I D a b)
    (heq : ∀ p ∈ T, Function.uncurry ψ =ᶠ[𝓝 p] Function.uncurry φ)
    (hD : D ⊆ T)
    (hr : ∀ q ∈ I, (q.1, (κ q).2) ∈ T)
    (hm : ∀ q ∈ I, ∀ p ∈ D, (q.1, p.2) ∈ T) :
    ReverseChartControl ψ κ I D a b := by
  have hd u ξ (h : (u, ξ) ∈ D) := partial_fderiv_eq (heq (u, ξ) (hD h))
  have hrel y η (h : (y, η) ∈ I) := partial_fderiv_eq (heq _ (hr _ h))
  have hmix y η (hi : (y, η) ∈ I) u ξ (h : (u, ξ) ∈ D) :=
    partial_fderiv_eq (heq _ (hm _ hi _ h))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u ξ h
    exact (H.differentiable u ξ h).congr_of_eventuallyEq (heq _ (hD h))
  · intro y η hi
    simpa only [ForwardRelation, (hrel y η hi).1, (hrel y η hi).2] using H.relation y η hi
  · intro y η hi u ξ h
    simpa only [(hmix y η hi u ξ h).2, (hrel y η hi).2] using H.inverse_bound y η hi u ξ h
  · intro y η hi u ξ h
    simpa only [(hmix y η hi u ξ h).2, (hd u ξ h).2] using H.base_variation y η hi u ξ h
  · intro y η hi u ξ h
    simpa only [(hrel y η hi).1, (hd u ξ h).1] using H.covector_variation y η hi u ξ h

/-- Agreement of the original and extended phases near a phase point gives
agreement of every joint phase jet there, for arbitrary external bases
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem jointPhase_eventuallyEq_of_phase
    (backward : Bool) {φ ψ : Euclidean n → Euclidean n → ℝ}
    (x y : Euclidean n) (p : JointVariables (Euclidean n))
    (h : Function.uncurry ψ =ᶠ[𝓝 (p.1.1, p.2.1)] Function.uncurry φ) :
    jointPhase backward ψ x y =ᶠ[𝓝 p] jointPhase backward φ x y := by
  have ht : Tendsto (fun p : JointVariables (Euclidean n) => (p.1.1, p.2.1))
      (𝓝 p) (𝓝 (p.1.1, p.2.1)) :=
    (continuous_fst.fst.prodMk continuous_snd.fst).tendsto p
  filter_upwards [h.comp_tendsto ht] with q hq
  change ψ q.1.1 q.2.1 = φ q.1.1 q.2.1 at hq
  cases backward <;> simp only [jointPhase, Bool.false_eq_true, ite_false, ite_true,
    forwardPhase, reversePhase] <;> rw [hq]

end JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
