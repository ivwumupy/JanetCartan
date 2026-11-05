module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.FullOperatorRegularity
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.JointPhysicalSources
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ResidualSmoothEnvelopes.JointRegularity
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothRealization

/-!
# Joint smoothness of the same complete smooth solution

The original inverse and full solver's positive estimates construct ordinary
all-order Fourier bounds for their exact composition. Apply the existing
joint graph realization to the original compact physical source family.
Its smooth slices agree pointwise with the retained smooth solver by their
global almost-everywhere identity. Thus joint output smoothness is proved;
it is not an analytic premise of the response reconstruction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential SmallSupport RegularSector RegularSector.Realization
open RegularSector.FiniteAssembly FourierIntegral
open RegularSector.Characteristic.RetardedLocalization
open FiniteChain.Graph.KernelLimits
open ResidualSmoothEnvelopes

variable {d p : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
local notation "E" => Euclidean (d+1)
local notation "CF" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Ordinary positive estimates of the original full inverse construct joint
smoothness of the SAME smooth solution on its retained parameter domain.
The source's global joint smoothness is supplied by the original parameter
cutoff and `contDiff_original_product_physical_source_of_parameter_support`.
The slice identity and slice smoothness are the initialized smooth solver's
original clauses, with no output-parameter regularity assumption.
Consumer: `fixedSolverParameterResponse_joint_graded`'s `hg`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_full_solver_joint_solution
    (W : Set E) (hW : MeasurableSet W) {center : E} (χ₂ χ₃ : ContDiffBump center)
    (hs₂ : tsupport (χ₂ : E → ℝ) ⊆ W) (hs₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (R : LocalL2 W CF →L[ℂ] LocalL2 W CF)
    (hreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    (S : H →L[ℂ] H)
    (CI highI CS highS : ℕ → ℝ)
    (hCI : ∀ s, 0 ≤ CI s) (hhighI : ∀ s, 0 ≤ highI s)
    (hCS : ∀ s, 0 ≤ CS s) (hhighS : ∀ s, 0 ≤ highS s)
    (hInv : ∀ s (u : LocalL2 W E), MemRestrictionSobolev W s u →
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) u) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) u) ≤
          CI s * (restrictionSobolevNorm W s u + highI s * ‖u‖))
    (hS : ∀ (s : ℕ) (u : H), MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (S u) ∧
        vectorFourierSobolevNorm (s : ℝ) (S u) ≤
          CS s * (vectorFourierSobolevNorm (s : ℝ) u + highS s * ‖u‖))
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (coords : Euclidean p ≃L[ℝ] Z)
    {X : Set E} (hX : IsCompact X)
    (g : Z → E → CF) (hg : ContDiff ℝ ∞ (fun w : E × Z ↦ g w.2 w.1))
    (hs : ∀ c, tsupport (g c) ⊆ X) (hm : ∀ c, MemLp (g c) 2 volume)
    (V : Set Z) (solution : Z → E → CF)
    (hsmooth : ∀ c, c ∈ V → ContDiff ℝ ∞ (solution c))
    (hidentify : ∀ c, c ∈ V → solution c =ᵐ[volume]
      complexBumpedLocalObservation hW χ₂ χ₃ S (complexNeumannInverse R hR)
        ((hm c).toLp (g c))) :
    ContDiffOn ℝ ∞ (fun w : E × Z ↦ solution w.2 w.1) (univ ×ˢ V) := by
  let A := complexBumpedLocalObservation hW χ₂ χ₃ S (complexNeumannInverse R hR)
  have hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d+1) (d+1),
        MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) ∧
          vectorFourierSobolevNorm (s : ℝ) (A (graphTestToLp u)) ≤
            C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u) := by
    intro s
    obtain ⟨C, hC, hb⟩ := complex_full_solver_fourier_bound_of_real_positive_estimates
      W hW χ₂ χ₃ hs₂ hs₃ R hreal hR S s (CI s) (highI s) (CS s) (highS s)
      (hCI s) (hhighI s) (hCS s) (hhighS s) (hInv s) (hS s)
    exact ⟨s, C, hC, fun u ↦ hb (graphTestToLp u) (graphTest_memVectorFourierSobolev (s : ℝ) u)⟩
  have hmem (u : graphTestSpace (d+1) (d+1)) (s : ℕ) :
      MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) := by
    obtain ⟨_, _, _, h⟩ := hA s
    exact (h u).1
  obtain ⟨B, hB⟩ := exists_smooth_linear_graph_realization A hmem
  let input (c : Z) : graphTestSpace (d+1) (d+1) :=
    ⟨g c, hg.comp (contDiff_id.prodMk (contDiff_const (c := c))),
      hX.of_isClosed_subset (isClosed_tsupport _) (hs c)⟩
  have hglobal : ContDiff ℝ ∞ (fun w : E × Z ↦ B (input w.2) w.1) :=
    contDiff_joint_graph_realization e he coords hX A B hB hA input hg hs
  have hclass (c : Z) : graphTestToLp (input c) = (hm c).toLp (g c) := rfl
  have hEq (c : Z) (hc : c ∈ V) : solution c = B (input c) := by
    apply funext
    intro x
    have heq : solution c =ᵐ[volume] B (input c) :=
      (hidentify c hc).trans (by simpa only [hclass c] using (hB (input c)).2.symm)
    have heq' : solution c =ᵐ[volume.restrict univ] B (input c) := by
      simpa only [Measure.restrict_univ] using heq
    exact Measure.eqOn_open_of_ae_eq heq' isOpen_univ
      (hsmooth c hc).continuous.continuousOn (hB (input c)).1.continuous.continuousOn (mem_univ x)
  exact hglobal.contDiffOn.congr (fun w hw ↦ congrFun (hEq w.2 hw.2) w.1)


/-- The SAME full smooth solver is jointly smooth when its global physical
source already contains the actual inner recut. The source and source class
are exactly those constructed by `InitializedParameterRemainders`; no second
inner bump is inserted. Ordinary positive estimates of the original inverse
and full solver supply all graph bounds, and the original spatially smooth
representative is recovered by almost-everywhere uniqueness
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_recut_full_solver_joint_solution
    (W : Set E) (hW : MeasurableSet W) {center : E} (χ₃ : ContDiffBump center)
    (hs₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (R : LocalL2 W CF →L[ℂ] LocalL2 W CF)
    (hreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    (S : H →L[ℂ] H)
    (CI highI CS highS : ℕ → ℝ)
    (hCI : ∀ s, 0 ≤ CI s) (hhighI : ∀ s, 0 ≤ highI s)
    (hCS : ∀ s, 0 ≤ CS s) (hhighS : ∀ s, 0 ≤ highS s)
    (hInv : ∀ s (u : LocalL2 W E), MemRestrictionSobolev W s u →
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) u) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) u) ≤
          CI s * (restrictionSobolevNorm W s u + highI s * ‖u‖))
    (hS : ∀ (s : ℕ) (u : H), MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (S u) ∧
        vectorFourierSobolevNorm (s : ℝ) (S u) ≤
          CS s * (vectorFourierSobolevNorm (s : ℝ) u + highS s * ‖u‖))
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    (coords : Euclidean p ≃L[ℝ] Z)
    {X : Set E} (hX : IsCompact X)
    (g : Z → E → CF) (hg : ContDiff ℝ ∞ (fun w : E × Z ↦ g w.2 w.1))
    (hs : ∀ c, tsupport (g c) ⊆ X) (hm : ∀ c, MemLp (g c) 2 volume)
    (V : Set Z) (solution : Z → E → CF)
    (hsmooth : ∀ c, c ∈ V → ContDiff ℝ ∞ (solution c))
    (hidentify : ∀ c, c ∈ V → solution c =ᵐ[volume]
      complexLocalSolverObservation hW χ₃ S (complexNeumannInverse R hR)
        ((hm c).toLp (g c))) :
    ContDiffOn ℝ ∞ (fun w : E × Z ↦ solution w.2 w.1) (univ ×ˢ V) := by
  let A := complexLocalSolverObservation hW χ₃ S (complexNeumannInverse R hR)
  have hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d+1) (d+1),
        MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) ∧
          vectorFourierSobolevNorm (s : ℝ) (A (graphTestToLp u)) ≤
            C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u) := by
    intro s
    obtain ⟨C, hC, hb⟩ := complex_recut_full_solver_fourier_bound_of_real_positive_estimates
      W hW χ₃ hs₃ R hreal hR S s (CI s) (highI s) (CS s) (highS s)
      (hCI s) (hhighI s) (hCS s) (hhighS s) (hInv s) (hS s)
    exact ⟨s, C, hC, fun u ↦ hb (graphTestToLp u) (graphTest_memVectorFourierSobolev (s : ℝ) u)⟩
  have hmem (u : graphTestSpace (d+1) (d+1)) (s : ℕ) :
      MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) := by
    obtain ⟨_, _, _, h⟩ := hA s
    exact (h u).1
  obtain ⟨B, hB⟩ := exists_smooth_linear_graph_realization A hmem
  let input (c : Z) : graphTestSpace (d+1) (d+1) :=
    ⟨g c, hg.comp (contDiff_id.prodMk (contDiff_const (c := c))),
      hX.of_isClosed_subset (isClosed_tsupport _) (hs c)⟩
  have hglobal : ContDiff ℝ ∞ (fun w : E × Z ↦ B (input w.2) w.1) :=
    contDiff_joint_graph_realization e he coords hX A B hB hA input hg hs
  have hclass (c : Z) : graphTestToLp (input c) = (hm c).toLp (g c) := rfl
  have hEq (c : Z) (hc : c ∈ V) : solution c = B (input c) := by
    apply funext
    intro x
    have heq : solution c =ᵐ[volume] B (input c) :=
      (hidentify c hc).trans (by simpa only [hclass c] using (hB (input c)).2.symm)
    have heq' : solution c =ᵐ[volume.restrict univ] B (input c) := by
      simpa only [Measure.restrict_univ] using heq
    exact Measure.eqOn_open_of_ae_eq heq' isOpen_univ
      (hsmooth c hc).continuous.continuousOn (hB (input c)).1.continuous.continuousOn (mem_univ x)
  exact hglobal.contDiffOn.congr (fun w hw ↦ congrFun (hEq w.2 hw.2) w.1)


end JanetCartan.FixedDomainInverse
