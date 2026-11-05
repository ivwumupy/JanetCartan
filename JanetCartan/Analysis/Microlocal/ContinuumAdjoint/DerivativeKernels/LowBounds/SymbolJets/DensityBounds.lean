module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.DensityBounds.Calculus
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.DensityBounds.Extension
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.DensityBounds.PrimitiveComposition
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.SymbolJets.DensityBounds.Reciprocal

/-!
# Weighted jets for the modified inverse density

For `app:ch_background:prop:bg-adjoint`, the finite primitive weighted reserve
implies uniform order-zero jets of the literal inverse density. Fixed-scale
composition retains the two half-order amplitude weights, which cancel the
reciprocal degree-one Jacobian weight in every product derivative. Buffered
extension and spectator restriction give the quantitative input to
`graphNormalAmplitudeBounds_of_densityJets`.

The constant is chosen before the arbitrary amplitude and regularizer. The
regularizer budget is explicit and fixed in the final section estimate; no
composed-amplitude, density, or operator estimate is assumed. Actual geometry
and primitive amplitude producers, and the subsequent graph-normal assembly,
remain the parent construction's obligations.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol

open ContinuumRow

variable {n : ℕ}

/-- Joint density jets for `app:ch_background:prop:bg-adjoint` follow from
primitive weighted jets: the two half-order factors cancel the reciprocal
degree-one determinant at every order. The constant is chosen before the
chart, amplitude, regularizer, and their amplitude and regularizer budgets.
The consumer is `PrimitiveJetGeometry.exists_inverseDensity_section_jet_bound`. -/
theorem exists_inverseDensity_joint_jet_bound (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C ≥ 0, ∀ {g : Chart n} {s : JetRescaling g} {ρ : ℝ}
      {L : Set (JointVariables n)} {K : Set (Euclidean 2)},
      PrimitiveJetGeometry g s N ρ B c L K →
      ∀ {X : Set (Euclidean n)} {Z : Set CarrierParameter}
        {Ω : Set (Euclidean (n - 1))}
        (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A M : ℝ),
      PrimitiveRegularity g a m →
      PrimitiveAmplitudeReserve g N ρ A X K Z Ω L a →
      PrimitiveRegularizerReserve N ρ M m →
      ∀ j ≤ N, ∀ p : JointVariables n, p.2 ∈ K →
        ‖iteratedFDeriv ℝ j (inverseDensity g a m) p‖ ≤ C * M^2 * A^2 := by
  obtain ⟨D, hD, hdjet⟩ := exists_reciprocalJacobian_jet_bound (n := n) N B hc
  let T := primitiveCompositionBound N B
  have hT : 0 ≤ T := primitiveCompositionBound_nonneg N B
  refine ⟨((2 : ℝ)^N)^4 * D * T^4, by positivity, ?_⟩
  intro g s ρ L K hg X Z Ω a m A M h ha hm j hj p hpK
  by_cases hp : p ∈ g.push '' L
  · have hpΩ := ha.buffered.image_subset hp
    have hr : 0 < ‖(g.carrier (g.pull p)).2‖ :=
      hg.threshold_pos.trans_le (hg.high_frequency p hp hpK)
    have he : inverseDensity g a m =ᶠ[𝓝 p]
        (fun q : JointVariables n ↦
          |(g.jacobian q.1.1 q.1.2.1 q.2
            (g.inverse q.1.1 q.1.2.1 q.2 q.1.2.2)).det|⁻¹ •
          ((m (g.carrier (g.pull q)) : ℂ)^2 *
            (star (a (g.carrier (g.pull q)).1 q.1.1 (g.carrier (g.pull q)).2) *
              a (g.carrier (g.pull q)).1 q.1.2.1 (g.carrier (g.pull q)).2))) := by
      filter_upwards [h.output_open.mem_nhds hpΩ] with q hq
      rw [inverseDensity_eq_indicator, indicator_of_mem hq]
      rfl
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    have hb := norm_iteratedFDeriv_weightedPair_le h.output_open
      h.reciprocalJacobian_contDiffOn h.composedRegularizer_contDiffOn
      h.composedLeftAmplitude_contDiffOn h.composedRightAmplitude_contDiffOn
      hD (mul_nonneg hT hm.budget_nonneg) (mul_nonneg hT ha.budget_nonneg) hr hpΩ
      (fun i hi ↦ hdjet hg h ha.buffered.image_subset p hp hpK i hi)
      (fun i hi ↦ hg.norm_iteratedFDeriv_composedRegularizer_le h ha.buffered hm hp hpK hi)
      (fun i hi ↦ hg.norm_iteratedFDeriv_composedLeftAmplitude_le h ha hp hpK hi)
      (fun i hi ↦ hg.norm_iteratedFDeriv_composedRightAmplitude_le h ha hp hpK hi) hj
    convert hb using 1
    ring
  · rw [iteratedFDeriv_inverseDensity_eq_zero_of_not_mem_image h ha.buffered hp,
      norm_zero]
    positivity

/-- The precise density-jet input to `graphNormalAmplitudeBounds_of_densityJets`
for `app:ch_background:prop:bg-adjoint`, including normal-frequency derivatives
through `2 * (n + 1)`. The fixed regularizer budget is absorbed into `C` before
choosing the arbitrary complex amplitude and regularizer. Geometry, amplitude,
and regularizer producers remain explicit primitive inputs. -/
theorem PrimitiveJetGeometry.exists_inverseDensity_section_jet_bound
    {g : Chart n} {s : JetRescaling g} {ρ B c : ℝ}
    {L : Set (JointVariables n)} {K : Set (Euclidean 2)}
    (hg : PrimitiveJetGeometry g s (2 * (n + 1)) ρ B c L K)
    (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (M : ℝ) :
    ∃ C ≥ 0, ∀ (a : AdjointAmplitude n) (m : CarrierVariable n → ℝ) (A : ℝ),
      PrimitiveRegularity g a m →
      PrimitiveAmplitudeReserve g (2 * (n + 1)) ρ A X K Z Ω L a →
      PrimitiveRegularizerReserve (2 * (n + 1)) ρ M m →
      ∀ j ≤ 2 * (n + 1), ∀ p : Variables n, ∀ v ∈ K,
        ‖iteratedFDeriv ℝ j (fun q ↦ inverseDensity g a m (q, v)) p‖ ≤ C * A^2 := by
  obtain ⟨C, hC, hjet⟩ :=
    exists_inverseDensity_joint_jet_bound (n := n) (2 * (n + 1)) B hg.gap_pos
  refine ⟨C * M^2, mul_nonneg hC (sq_nonneg M), ?_⟩
  intro a m A h ha hm j hj p v hv
  exact norm_iteratedFDeriv_inverseDensity_section_le h ha.buffered (by positivity)
    (fun q _ hqK ↦ hjet hg a m A M h ha hm j hj q hqK) p v hv

end JanetCartan.ContinuumAdjoint.DerivativeKernels.ModifiedNormalSymbol
