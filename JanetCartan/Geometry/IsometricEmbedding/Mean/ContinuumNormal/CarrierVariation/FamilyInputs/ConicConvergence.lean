module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CompactSlices
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ForwardJacobian

/-!
# Finite convergence on the same conic inverse domains

The joint original forward map is retained by `BufferedConic`. Its smoothness,
genuine inverse identities, augmented differential gap and literal Jacobian
gap imply the finite inverse and reciprocal-Jacobian limits. The consumer is
`NormDomains`, hence the actual same-seed construction in `SeedAssembly`.
Source: `app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-jacobian` and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol

/-- The same common inverse converges from joint regularity of its original
forward map. This is the inverse input to the two ODE-label substitutions in
`WideDensity.ConicComparison` (`app:ch_background:eq:bg-Psi`). -/
theorem tendsto_conic_inverse_sub_cNorm {n : ℕ}
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {ε : ℝ} (hε : 0 < ε)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (Ioo (-ε) ε ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-ε) ε,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) (m : ℕ) :
    Tendsto (fun σ ↦ cNorm Q m (inverseCoordinates (u σ) - inverseCoordinates (u 0)))
      (𝓝 0) (𝓝 0) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hf (σ) (hσ : σ ∈ Ioo (-ε) ε) :
      ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W :=
    hjoint.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hσ, hp⟩)
  have hnormalized := tendsto_cNorm_slice_sub isOpen_Ioo hW
    (hjoint.continuousLinearMap_comp A.symm.toContinuousLinearMap) hK hKW h0 m
  have hbase := hfamily 0 h0
  apply tendsto_inverseCoordinates_sub_cNorm hK hconv hQ hW hKW hΩ hQΩ
    (hf 0 h0) hbase.1 A hbase.2.1 hbase.2.2.1 m Y u _ hnormalized
  filter_upwards [isOpen_Ioo.mem_nhds h0] with σ hσ
  exact ⟨hf σ hσ, hfamily σ hσ⟩

/-- Common conic geometry and the smooth ORIGINAL forward family imply finite
convergence of the actual inverse, absolute determinant and reciprocal. No
inverse or Jacobian continuity is a premise. `BufferedConic` supplies every
displayed hypothesis on its literal retained source family. Source:
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem tendsto_conic_inverse_jacobian_sub_cNorm {n : ℕ}
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (c : TransportSliceCoordinates n) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (Ioo (-ε) ε ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-ε) ε,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian c (Y σ) p)) (m : ℕ) :
    Tendsto (fun σ ↦
      cNorm K m (augmentedTransportGradient (Y σ) - augmentedTransportGradient (Y 0)) +
      cNorm Q m (inverseCoordinates (u σ) - inverseCoordinates (u 0)) +
      cNorm K m (transportAbsoluteJacobian c (Y σ) - transportAbsoluteJacobian c (Y 0)) +
      cNorm K m ((fun p ↦ (transportAbsoluteJacobian c (Y σ) p)⁻¹) -
        (fun p ↦ (transportAbsoluteJacobian c (Y 0) p)⁻¹))) (𝓝 0) (𝓝 0) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hI : ∀ᶠ σ in 𝓝 (0 : ℝ), σ ∈ Ioo (-ε) ε := isOpen_Ioo.mem_nhds h0
  have hf (σ) (hσ : σ ∈ Ioo (-ε) ε) :
      ContDiffOn ℝ ∞ (augmentedTransportGradient (Y σ)) W :=
    hjoint.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨hσ, hp⟩)
  have hg (σ) (hσ : σ ∈ Ioo (-ε) ε) :
      ContDiffOn ℝ ∞ (transportAveragedGradient (Y σ)) W := (hf σ hσ).fst.snd.snd
  have hforward := tendsto_cNorm_slice_sub isOpen_Ioo hW hjoint hK hKW h0 m
  have hnormalized := tendsto_cNorm_slice_sub isOpen_Ioo hW
    (hjoint.continuousLinearMap_comp A.symm.toContinuousLinearMap) hK hKW h0 m
  have hbase := hfamily 0 h0
  have hinverse := tendsto_inverseCoordinates_sub_cNorm hK hconv hQ hW hKW hΩ hQΩ
    (hf 0 h0) hbase.1 A hbase.2.1 hbase.2.2.1 m Y u
    (hI.mono fun σ hσ ↦
      ⟨hf σ hσ, (hfamily σ hσ).1, (hfamily σ hσ).2.1,
        (hfamily σ hσ).2.2.1, (hfamily σ hσ).2.2.2.1⟩) hnormalized
  have hgrad := tendsto_cNorm_slice_sub isOpen_Ioo hW hjoint.fst.snd.snd hK hKW h0 (m + 1)
  have hslice : Tendsto (fun σ ↦ cNorm K m
      (transportSliceDifferential c (Y σ) - transportSliceDifferential c (Y 0)))
      (𝓝 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ cNorm_nonneg ..)
      (hI.mono fun σ hσ ↦
        cNorm_transportSliceDifferential_sub_le c hK hW hKW (hg σ hσ) (hg 0 h0) m)
    simpa only [augmentedTransportGradient, mul_zero] using hgrad.const_mul (((m + 1 : ℕ) : ℝ) * ‖transportDifferentialRestriction c‖)
  obtain ⟨C, _hC, hcompare⟩ := exists_transportAbsoluteJacobian_sub_le c hK hW hKW
    (hg 0 h0) hδ hbase.2.2.2.2 m
  have hjac : Tendsto (fun σ ↦
      cNorm K m (transportAbsoluteJacobian c (Y σ) - transportAbsoluteJacobian c (Y 0)) +
      cNorm K m ((fun p ↦ (transportAbsoluteJacobian c (Y σ) p)⁻¹) -
        (fun p ↦ (transportAbsoluteJacobian c (Y 0) p)⁻¹))) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..))
    · filter_upwards [isOpen_Ioo.mem_nhds h0,
        hslice.eventually (gt_mem_nhds zero_lt_one)] with σ hσ hsmall
      exact hcompare (Y σ) (hg σ hσ) (hfamily σ hσ).2.2.2.2 hsmall.le
    · simpa using hslice.const_mul C
  simpa only [add_zero, add_assoc] using (hforward.add hinverse).add hjac

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
