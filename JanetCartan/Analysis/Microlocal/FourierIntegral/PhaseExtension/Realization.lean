module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension.NormalGeometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds

/-!
# Realizing the low graph from a locally smooth buffered phase

This instantiates the global phase continuity input of the source-independent
low theorem using the smooth extension construction. All operator identities
on tests refer to the original local phase. Normal geometry and normalized
inverse jets are used on the entire original averaged-gradient image.
Those primitive estimates remain explicit inputs; this is not an assertion
that the Hamilton chart or its inverse bounds have been constructed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open NormalComparison LowBounds FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual pure graph and its strong regularizations for a phase smooth
only on an open neighborhood of the closed supported chart. The auxiliary
extension is constructed, and the test and Schwartz realizations use the
original phase. Constants precede the amplitude and extension. Every shell
input is still on `bufferedNormalDomain X D S`, the full image domain.

The buffer, original inverse chart, normalized inverse/Jacobian jets and
symbol bounds remain primitive producer obligations. In particular a bound
only on a smaller common target does not instantiate `jets`. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem exists_graphL2_of_local_phase (hn : 0 < n) (R M L : ℝ)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) :
    ∃ C > 0, ∀ (X D : Set E) (O : Set (E × E))
      (S : E → E → ℝ) (A : E → E → Mat)
      (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
      (W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n))
      (a : ℝ), 0 ≤ a → IsOpen X → Convex ℝ X → IsOpen O →
      closure (X ×ˢ D) ⊆ O → ContDiffOn ℝ ∞ (Function.uncurry S) O →
      AveragedGradientChart S X D η J δ → PrimitiveNormalGeometry X D S A A η J W K →
      K ⊆ X ×ˢ (X ×ˢ D) →
      (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖)) →
      (∀ l, PrimitiveNormalShellInputs A A η J ((2 : ℝ)^l)
        (primitiveNormalReserve n) M L δ a a
        (normalDyadicShell (bufferedNormalDomain X D S) l) (V l)) →
      ∀ (hA : Continuous (Function.uncurry A)) (Kout : Set E) (hKout : IsCompact Kout)
        (hsA : ∀ x η, x ∉ Kout → A x η = 0),
      tsupport (Function.uncurry A) ⊆ X ×ˢ D →
      ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A A) →
      ∀ (P : ℝ) (k : ℕ), (∀ x η, ‖A x η‖ ≤ P * (1 + ‖η‖ ^ k)) →
      ∃ (S' : E → E → ℝ) (hS' : ContDiff ℝ ∞ (Function.uncurry S')),
        (∀ q ∈ closure (X ×ˢ D),
          Function.uncurry S' =ᶠ[𝓝 q] Function.uncurry S) ∧
        let Tj : ℕ → H →L[ℂ] H := fun j ↦ compactVectorGraph hS'.continuous
          (cutAmplitude_entry_continuous hA j)
          (cutAmplitude_entry_hasCompactSupport hKout hsA j)
        ∃ T : H →L[ℂ] H, ‖T‖ ≤ C * a ∧ ‖T.adjoint‖ ≤ C * a ∧
          (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
              (graphTestToSchwartz u) x)) ∧
          (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η) u x)) ∧
          (∀ f : H, Tendsto (fun j ↦ Tj j f) atTop (𝓝 (T f))) ∧
          (∀ f : H, Tendsto (fun j ↦ (Tj j).adjoint f) atTop (𝓝 (T.adjoint f))) ∧
          (∀ j, Tj j = T.comp (multiplier j)) ∧
          (∀ j, (Tj j).adjoint = (multiplier j).comp T.adjoint) ∧
          (∀ j (v : E → Fin r → ℂ),
            graphOperator S' (fun x _ u ↦ cutAmplitude A j x u) v =
              graphOperator S (fun x _ u ↦ cutAmplitude A j x u) v) ∧
          ∀ U : H →L[ℂ] H, (∀ u : graphTestSpace n r, U (graphTestToLp u) =ᵐ[volume]
            fun x ↦ WithLp.toLp 2 (graphOperator S (fun z _ η ↦ A z η)
              (graphTestToSchwartz u) x)) → U = T := by
  obtain ⟨C, hC, hlow⟩ := exists_graphL2_of_primitive_inputs (r := r) hn R M L hδ hF
  refine ⟨C, hC, ?_⟩
  intro X D O S A η J W K V a ha hX hcX hO hbuffer hS chart geometry hK
    hR hgrowth jets hA Kout hKout hsA hsupp hforward P k hpoly
  obtain ⟨S', hS', he'⟩ := exists_smooth_phase_extension S isClosed_closure hO hbuffer hS
  have he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D) :=
    fun _ hq ↦ (he' _ (subset_closure hq)).eq_of_nhds
  have hdom := bufferedNormalDomain_phase_congr hX hcX he
  have hcarrier (x u) (hxu : x ∉ X ∨ u ∉ D) : A x u = 0 := by
    by_contra ha
    have hp := hsupp (subset_tsupport (Function.uncurry A)
      (show (x, u) ∈ Function.support (Function.uncurry A) from ha))
    exact hxu.elim (fun hx ↦ hx hp.1) (fun hu ↦ hu hp.2)
  have hphase (x u) (ha : A x u ≠ 0) : S' x u = S x u :=
    he (hsupp (subset_tsupport (Function.uncurry A)
      (show (x, u) ∈ Function.support (Function.uncurry A) from ha)))
  have hop (v : E → Fin r → ℂ) :
      graphOperator S' (fun x _ u ↦ A x u) v = graphOperator S (fun x _ u ↦ A x u) v :=
    graphOperator_phase_congr S S' _ (fun x _ u ↦ hphase x u) v
  have hforward' : ContinuousOn (normalForwardCoordinates S') (jointNormalCarrier A A) := by
    apply hforward.congr
    intro q hq
    exact normalForwardCoordinates_phase_congr hX hcX he
      ⟨(hsupp hq.1).1, (hsupp hq.2).1, (hsupp hq.1).2⟩
  obtain ⟨T, hT, hTa, htest, hschwartz, hstrong, hadjoint, hright, hrighta, _, huniq⟩ :=
    hlow X D S' A η J W K V a ha (chart.congr_phase hX hcX he)
      (geometry.congr_phase chart hX hcX he hK) hR
      (fun x hx y hy u hu ↦ by
        rw [averagedGradient_phase_congr hX hcX he hx hy hu]
        exact hgrowth x hx y hy u hu)
      (fun l ↦ by rw [hdom]; exact jets l)
      hS'.continuous hA Kout hKout hsA hcarrier hforward' P k hpoly
  refine ⟨S', hS', he', T, hT, hTa, ?_, ?_, hstrong, hadjoint, hright, hrighta, ?_, ?_⟩
  · intro u
    simpa only [hop] using htest u
  · intro u
    simpa only [hop] using hschwartz u
  · intro j v
    apply graphOperator_phase_congr S S' _ _ v
    intro x y u hu
    apply hphase x u
    intro hz
    exact hu (by simp [cutAmplitude, hz])
  · intro U hU
    apply huniq U
    intro u
    simpa only [hop] using hU u

end JanetCartan.FourierIntegral
