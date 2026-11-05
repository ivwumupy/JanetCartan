module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.RealizedIdentities
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SupportedCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.LocalizedFinite

/-!
# Identifying the fixed elapsed graph with its bounded localized realization

The finite test actions and strong limits from the primitive graph producer
identify the operator constructed by `exists_buffered_elapsed_graph_fourier_bound`.
Only a smooth extension on the amplitude support is used. The original phase
need not be regular at spatial frequency zero. No additional shell majorant,
operator estimate or uncut test action is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open FourierIntegral FiniteChain.Graph KernelLimits PhysicalShells
open RegularSector.Characteristic.EvolutionIntegral
open Pseudodifferential AmplitudeBound RetardedSobolev.Spaces SobolevRealization
open EvolutionIntegratedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The two limits of the SAME finite localized graph identify the estimated
operator with `(1 - Mo) ∘ G ∘ Mi`. The phase extension agrees only where the
full amplitude is nonzero. The eventual prefix test action is obtained from
`eventually_graphShell_prefix_eq_producer`, and the strong limit is the exact
primitive graph-family output. Neither input assumes localized decay.
Consumer: `exists_buffered_elapsed_graph_fourier_bound`
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem eq_localized_of_finite_graph_realizations
    (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)
    (backward : Bool) {ρ : ℝ} (hρ : ρ ≠ 0)
    (S S' : E → E → ℝ) (hS' : ContDiff ℝ ∞ (Function.uncurry S'))
    (A : FullAmplitude (d + 1) q)
    (he : ∀ x y ξ, A x y ξ ≠ 0 → S' x ξ = S x ξ)
    (hA : ContDiff ℝ ∞ (fun p : (E × E) × E => A p.1.1 p.1.2 p.2))
    {Kb : Set (E × E)} (hKb : IsCompact Kb)
    (hAbase : ∀ x y ξ, (x, y) ∉ Kb → A x y ξ = 0)
    (mi mo : LocalizerSymbol (d + 1))
    (hi : ContDiff ℝ ∞ mi) (ho : Continuous mo)
    (his : HasCompactSupport mi) (hos : HasCompactSupport mo)
    (Mi Mo G U : H →L[ℂ] H)
    (hMi : ∀ u : H, Mi u =ᵐ[volume] fun x =>
      WithLp.toLp 2 (rightLocalizer ρ mi (fun y => (u y).ofLp) x))
    (hMo : ∀ u : H, (∀ i, Integrable (fun y => u y i)) → Mo u =ᵐ[volume]
      fun x => WithLp.toLp 2 (leftLocalizer ρ mo (fun y => (u y).ofLp) x))
    (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ᶠ N in atTop, ∀ u : graphTestSpace (d + 1) q,
      Treg N (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
        (((if backward then reverseGraphOperator else graphOperator) S
          (fun x y ξ => ((∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ) : ℂ) • A x y ξ)
          (fun y => (u.val y).ofLp)) x))
    (hlim : ∀ u, Tendsto (fun N => Treg N u) atTop (𝓝 (G u)))
    (hreg : ∀ (f : Fin q → Test d) (a : Fin q), ∀ᵐ x ∂volume,
      Tendsto (fun j : Finset ℕ × Finset ℕ =>
        leftLocalizer 1 (fun z => (∑ k ∈ j.2, outputCutoff k z.2) *
          (1 - mo (z.1, ρ⁻¹ • z.2)))
          ((if backward then reverseGraphOperator else graphOperator) S
            (fun u z ξ => ((∑ k ∈ j.1, graphCutoff k ξ) : ℂ) • A u z ξ)
            (rightLocalizer 1 (fun z => mi (z.1, ρ⁻¹ • z.2)) (physicalTestField J f))) x a)
        atTop (𝓝 (finiteL2CoordinateIsometry volume (U (physicalTestToL2 J hJ f)) a x))) :
    (1 - Mo).comp (G.comp Mi) = U := by
  let Ki := Prod.fst '' tsupport mi
  let Kη := Prod.snd '' tsupport mi
  have hiSupport (y η : E) (h : (y, η) ∉ Ki ×ˢ Kη) : mi (y, η) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact h ⟨⟨(y, η), hm, rfl⟩, ⟨(y, η), hm, rfl⟩⟩
  let c := fun j k => physicalInputCarriers
    (cutoffPairCarriers A mi Kb Ki Kη hKb (his.image continuous_fst)
      (his.image continuous_snd) hAbase hiSupport j k) hρ
  let cp (N : ℕ) : RegularizedCarriers A (fun p => mi (p.1, ρ⁻¹ • p.2))
      (fun ξ => ∑ j ∈ Finset.range N, graphCutoff j ξ)
      (LowBounds.FrequencyCutoff.physicalCutoff (2 ^ N - 1)) :=
    { RegularizedCarriers.finsetCutoffs c (Finset.range N) (Finset.range (N + 1)) with
      compact_outputCutoff := LowBounds.FrequencyCutoff.physicalCutoff_hasCompactSupport _ }
  apply eq_of_physical_test_action J hJ
  intro f a
  let v (N : ℕ) : H := (1 - Mo) (LowBounds.FrequencyCutoff.multiplier (2 ^ N - 1)
    (Treg N (Mi (physicalTestToL2 J hJ f))))
  let R (N : ℕ) (x : E) := leftLocalizer 1
    (fun z => (∑ k ∈ Finset.range (N + 1), outputCutoff k z.2) * (1 - mo (z.1, ρ⁻¹ • z.2)))
    ((if backward then reverseGraphOperator else graphOperator) S
      (fun u z ξ => ((∑ k ∈ Finset.range N, graphCutoff k ξ) : ℂ) • A u z ξ)
      (rightLocalizer 1 (fun z => mi (z.1, ρ⁻¹ • z.2)) (physicalTestField J f))) x
  have hv : Tendsto v atTop (𝓝 (((1 - Mo).comp (G.comp Mi)) (physicalTestToL2 J hJ f))) :=
    tendsto_outputMultiplier_diagonal Mo _ _ (hlim _)
  have hvR : ∀ᶠ N in atTop, v N =ᵐ[volume] fun x => WithLp.toLp 2 (R N x) := by
    filter_upwards [hreal] with N hN
    have hN' : ∀ u : graphTestSpace (d + 1) q,
        Treg N (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator) S'
            (fun x y ξ => ((∑ j ∈ Finset.range N, graphCutoff j ξ : ℝ) : ℂ) • A x y ξ)
            (fun y => (u.val y).ofLp)) x) := by
      intro u
      simpa only [ConicLimits.regularized_orientedGraph_phase_congr backward S S' A
        _ (fun x y ξ hx _ => he x y ξ hx)] using hN u
    have hfinite := bounded_finiteGraph_outputMultiplier_realization hρ mi mo hi ho hos
      Mi Mo hMi hMo backward S' A hS'.continuous (fun _ _ _ => hS'.contDiffAt) hA
      (fun ξ => ∑ j ∈ Finset.range N, graphCutoff j ξ) (2 ^ N - 1)
      (ContDiff.sum (fun j _ => contDiff_graphCutoff j)) (zero_notMem_tsupport_graphPrefix N)
      (cp N) (Treg N) hN' (physicalGraphTest J f)
    rw [← physicalTestToL2_eq_graphTestToLp J hJ f] at hfinite
    apply hfinite.trans
    apply Eventually.of_forall
    intro x
    apply congrArg (WithLp.toLp 2)
    have hcomp : leftLocalizer 1
        (fun z => LowBounds.FrequencyCutoff.physicalCutoff (2 ^ N - 1) z.2 *
          (1 - mo (z.1, ρ⁻¹ • z.2)))
        ((if backward then reverseGraphOperator else graphOperator) S'
          (fun u z ξ => ((∑ k ∈ Finset.range N, graphCutoff k ξ) : ℂ) • A u z ξ)
          (rightLocalizer 1 (fun z => mi (z.1, ρ⁻¹ • z.2)) (physicalTestField J f))) x =
        ∫ y, (regularizedJointKernel backward S' A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (fun ξ => ∑ j ∈ Finset.range N, graphCutoff j ξ)
          (LowBounds.FrequencyCutoff.physicalCutoff (2 ^ N - 1)) x y).mulVec
          (physicalTestField J f y) := by
      cases backward
      · simpa only [Bool.false_eq_true, ite_false, Complex.ofReal_sum] using
          forward_composition_eq_jointKernel S' A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (fun ξ => ∑ j ∈ Finset.range N, graphCutoff j ξ)
          (LowBounds.FrequencyCutoff.physicalCutoff (2 ^ N - 1)) hS'.continuous hA.continuous
          (hi.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
          (ho.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
          (continuous_finsetSum _ (fun j _ => (contDiff_graphCutoff j).continuous))
          (LowBounds.FrequencyCutoff.physicalCutoff_contDiff _).continuous
          (cp N) _ (contDiff_physicalTestField J f).continuous x
      · simpa only [ite_true, Complex.ofReal_sum] using
          reverse_composition_eq_jointKernel S' A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (fun ξ => ∑ j ∈ Finset.range N, graphCutoff j ξ)
          (LowBounds.FrequencyCutoff.physicalCutoff (2 ^ N - 1)) hS'.continuous hA.continuous
          (hi.continuous.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
          (ho.comp (continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)))
          (continuous_finsetSum _ (fun j _ => (contDiff_graphCutoff j).continuous))
          (LowBounds.FrequencyCutoff.physicalCutoff_contDiff _).continuous
          (cp N) _ (contDiff_physicalTestField J f).continuous x
    change (∫ y, (regularizedJointKernel backward S' A
      (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
      (fun ξ => ∑ j ∈ Finset.range N, graphCutoff j ξ)
      (LowBounds.FrequencyCutoff.physicalCutoff (2 ^ N - 1)) x y).mulVec
      (physicalTestField J f y)) = R N x
    rw [← hcomp]
    dsimp only [R]
    simp only [← Complex.ofReal_sum, outputPrefix_eq_physicalCutoff]
    rw [ConicLimits.regularized_orientedGraph_phase_congr backward S S' A
      _ (fun x y ξ hx _ => he x y ξ hx)]
  let coord := (PiLp.proj (𝕜 := ℂ) 2
    (fun _ : Fin q => Lp ℂ 2 (volume : Measure E)) a).comp (finiteL2Coordinates volume)
  have hc := (coord.continuous.tendsto _).comp hv
  obtain ⟨σ, hσ, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hc).exists_seq_tendsto_ae
  have heN : ∀ N, ∀ᵐ x ∂volume, (v N =ᵐ[volume] fun y => WithLp.toLp 2 (R N y)) →
      finiteL2CoordinateIsometry volume (v N) a x = R N x a := by
    intro N
    by_cases h : v N =ᵐ[volume] fun y => WithLp.toLp 2 (R N y)
    · exact ((finiteL2CoordinateIsometry_ae_iff volume _ _).mp h a).mono (fun _ hx _ => hx)
    · exact Eventually.of_forall (fun _ hx => (h hx).elim)
  have hdiag : Tendsto (fun N : ℕ => (Finset.range N, Finset.range (N + 1))) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_finset_range.prodMk (tendsto_finset_range.comp (tendsto_add_atTop_nat 1))
  filter_upwards [hsub, hreg f a, ae_all_iff.mpr heN] with x hx hu heNx
  have heσ := (hσ.tendsto_atTop.eventually hvR).mono (fun j hj => heNx (σ j) hj)
  exact tendsto_nhds_unique hx ((((hu.comp hdiag).comp hσ.tendsto_atTop)).congr'
    (heσ.mono (fun _ h => h.symm)))

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
