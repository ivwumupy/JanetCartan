module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ResidualSmoothEnvelopes.JetBounds

/-!
# Joint smoothness of a fixed residual realization

Reduce the vector source to finitely many supported scalar tests and apply
the existing fixed-response joint regularity theorem. The consuming measured
residual constructor retains the same operator and same L² class throughout
`app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
open RetardedSobolev.Spaces FourierIntegral Pseudodifferential
open RegularSector.FiniteAssembly ResponseSmoothParameters
open FiniteChain.Graph.KernelLimits
open ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
open LocalSobolev RegularSector.FiniteAssembly.CoefficientNorms
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The same smooth linear realization is jointly smooth on each compact
observation neighborhood, from its actual all-order Sobolev estimates.
Consumer: intermediate measured words in `app:ch_regular:lem:finite-chain`. -/
theorem contDiffOn_joint_graph_realization
    {p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (c : Euclidean p ≃L[ℝ] Z)
    {X L O : Set E} (hX : IsCompact X) (hL : IsCompact L)
    (hO : IsOpen O) (hOL : O ⊆ L)
    (A : H →L[ℂ] H)
    (R : graphTestSpace (d + 1) r →ₗ[ℂ] (E → F))
    (hR : ∀ u, ContDiff ℝ ∞ (R u) ∧ R u =ᵐ[volume] A (graphTestToLp u))
    (hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ) (A (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (f : Z → graphTestSpace (d + 1) r)
    (hf : ContDiff ℝ ∞ (fun w : E × Z ↦ (f w.2).val w.1))
    (hs : ∀ a, tsupport (f a).val ⊆ X) :
    ContDiffOn ℝ ∞ (fun w : E × Z ↦ R (f w.2) w.1) (O ×ˢ univ) := by
  classical
  have hK : IsCompact (e ⁻¹' X) := e.toHomeomorph.isCompact_preimage.mpr hX
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hsource : ContDiff ℝ ∞
      (fun w : E × Euclidean p ↦ (f (c w.2)).val w.1) :=
    hf.comp (contDiff_fst.prodMk (c.contDiff.comp contDiff_snd))
  obtain ⟨tests, ht, hdecomp⟩ := exists_supported_graph_components e hX
    (fun a ↦ f (c a)) hsource (fun a ↦ hs (c a))
  let B (j : Fin r) : supportedTests (e ⁻¹' X) →ₗ[ℝ] (E → F) :=
    (R.comp (componentGraphTest e hX j)).restrictScalars ℝ
  have hcomponent (j : Fin r) : ContDiffOn ℝ ∞
      (fun w : E × Z ↦ B j (tests j (c.symm w.2)) w.1) (O ×ˢ univ) := by
    have hb (q : ℕ) : ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ u : supportedTests (e ⁻¹' X), ∀ x ∈ L,
          ‖iteratedFDeriv ℝ q (B j u) x‖ ≤ C * ‖ofTest s volume u.val‖ := by
      obtain ⟨s, C, hC, hh⟩ := smooth_graph_component_jet_bounds e he hX A R hR hA j q
      exact ⟨s, C, hC, fun u x _ ↦ hh u x⟩
    have hh := contDiffOn_joint_supportedResponse isOpen_univ hK hO hOL (B j)
      (fun u ↦ (hR (componentGraphTest e hX j u)).1) hb (tests j) (ht j).contDiffOn
    exact hh.comp
      ((c.symm.contDiff.comp contDiff_snd).prodMk contDiff_fst).contDiffOn
      (fun w hw ↦ ⟨mem_univ _, hw.1⟩)
  have hsum : ContDiffOn ℝ ∞
      (fun w : E × Z ↦ ∑ j : Fin r, B j (tests j (c.symm w.2)) w.1)
      (O ×ˢ univ) := ContDiffOn.sum fun j _ ↦ hcomponent j
  apply hsum.congr
  intro w _
  have hd : f w.2 = ∑ j : Fin r, componentGraphTest e hX j (tests j (c.symm w.2)) := by
    simpa only [c.apply_symm_apply] using hdecomp (c.symm w.2)
  rw [hd, map_sum]
  simp only [Finset.sum_apply, B, LinearMap.restrictScalars_apply, LinearMap.comp_apply]

/-- A fixed linear smooth realization of the residual maps each globally
jointly smooth compact source family to one globally jointly smooth family.
No smoothness of the output parameter dependence is assumed
(`app:ch_regular:lem:finite-chain`). -/
theorem contDiff_joint_graph_realization
    {p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (c : Euclidean p ≃L[ℝ] Z)
    {X : Set E} (hX : IsCompact X)
    (A : H →L[ℂ] H)
    (R : graphTestSpace (d + 1) r →ₗ[ℂ] (E → F))
    (hR : ∀ u, ContDiff ℝ ∞ (R u) ∧ R u =ᵐ[volume] A (graphTestToLp u))
    (hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ) (A (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (f : Z → graphTestSpace (d + 1) r)
    (hf : ContDiff ℝ ∞ (fun w : E × Z ↦ (f w.2).val w.1))
    (hs : ∀ a, tsupport (f a).val ⊆ X) :
    ContDiff ℝ ∞ (fun w : E × Z ↦ R (f w.2) w.1) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  have hh := contDiffOn_joint_graph_realization e he c hX
    (isCompact_closedBall w.1 1) isOpen_ball Metric.ball_subset_closedBall A R hR hA f hf hs
  exact (hh w ⟨Metric.mem_ball_self (by norm_num), mem_univ _⟩).contDiffAt
    ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨Metric.mem_ball_self (by norm_num), mem_univ _⟩)



end JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
