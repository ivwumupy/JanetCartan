module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Composition

/-!
# Fubini identification of the literal graph compositions

The operator order in `app:ch_regular:eq:joint-kernel-phase` differs from the
packed joint-variable order. The permutations below preserve product volume;
absolute integrability, already proved from primitive carriers, justifies every
iterated integration. Both orientations keep the original amplitude positions.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false

private def swapFirst (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : α × β × γ ≃ᵐ β × α × γ :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl γ)).trans
      MeasurableEquiv.prodAssoc)

private theorem preserving_swapFirst (α β γ : Type*) [MeasureSpace α] [MeasureSpace β]
    [MeasureSpace γ] [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    [SFinite (volume : Measure γ)] : MeasurePreserving (swapFirst α β γ) := by
  exact (volume_preserving_prodAssoc.symm _).trans
    ((Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)).trans
      volume_preserving_prodAssoc)

private def rotateLast (α β γ : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : α × β × γ ≃ᵐ γ × α × β :=
  MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

private theorem preserving_rotateLast (α β γ : Type*) [MeasureSpace α] [MeasureSpace β]
    [MeasureSpace γ] [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    [SFinite (volume : Measure γ)] : MeasurePreserving (rotateLast α β γ) :=
  (volume_preserving_prodAssoc.symm _).trans Measure.measurePreserving_swap

private def forwardOrder (E : Type*) [MeasurableSpace E] :
    JointVariables E ≃ᵐ E × E × E × E × E :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl E).prodCongr
      ((MeasurableEquiv.refl E).prodCongr (rotateLast E E E))).trans
    (((MeasurableEquiv.refl E).prodCongr (swapFirst E E (E × E))).trans
    ((swapFirst E E (E × E × E)).trans
      ((MeasurableEquiv.refl E).prodCongr
        ((MeasurableEquiv.refl E).prodCongr (swapFirst E E E))))))

private theorem preserving_forwardOrder (E : Type*) [MeasureSpace E]
    [SFinite (volume : Measure E)] : MeasurePreserving (forwardOrder E) :=
  volume_preserving_prodAssoc.trans
    (((MeasurePreserving.id volume).prod
      ((MeasurePreserving.id volume).prod (preserving_rotateLast E E E))).trans
    (((MeasurePreserving.id volume).prod (preserving_swapFirst E E (E × E))).trans
    ((preserving_swapFirst E E (E × E × E)).trans
      ((MeasurePreserving.id volume).prod
        ((MeasurePreserving.id volume).prod (preserving_swapFirst E E E))))))

private theorem integral_five {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Euclidean n × Euclidean n × Euclidean n × Euclidean n × Euclidean n → F)
    (hg : Integrable g) :
    (∫ p, g p) = ∫ a, ∫ b, ∫ c, ∫ d, ∫ e, g (a, b, c, d, e) := by
  rw [Measure.volume_eq_prod] at hg ⊢
  rw [integral_prod _ hg]
  apply integral_congr_ae
  filter_upwards [hg.prod_right_ae] with a ha
  rw [Measure.volume_eq_prod] at ha ⊢
  rw [integral_prod _ ha]
  apply integral_congr_ae
  filter_upwards [ha.prod_right_ae] with b hb
  rw [Measure.volume_eq_prod] at hb ⊢
  rw [integral_prod _ hb]
  apply integral_congr_ae
  filter_upwards [hb.prod_right_ae] with c hc
  rw [Measure.volume_eq_prod]
  exact integral_prod _ hc

/-- Product-volume Fubini in the literal forward operator order, used to
identify `app:ch_regular:eq:joint-kernel-phase`. -/
theorem integral_jointVariables_forwardOrder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : JointVariables (Euclidean n) → F) (hg : Integrable g) :
    (∫ p, g p) = ∫ ζ, ∫ u, ∫ ξ, ∫ z, ∫ η, g ((u, z), (ξ, η, ζ)) := by
  have hm := (preserving_forwardOrder (Euclidean n)).symm _
  rw [← hm.integral_comp' g]
  exact integral_five _ ((hm.integrable_comp_emb
    (forwardOrder (Euclidean n)).symm.measurableEmbedding).mpr hg)

/-- Product-volume Fubini in the literal reverse operator order. The two
amplitude positions are swapped in the integration order, not in the amplitude
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem integral_jointVariables_reverseOrder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : JointVariables (Euclidean n) → F) (hg : Integrable g) :
    (∫ p, g p) = ∫ ζ, ∫ z, ∫ ξ, ∫ u, ∫ η, g ((u, z), (ξ, η, ζ)) := by
  let e : JointVariables (Euclidean n) ≃ᵐ JointVariables (Euclidean n) :=
    MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)
  have hm : MeasurePreserving e := Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  rw [← hm.integral_comp' g]
  exact integral_jointVariables_forwardOrder _
    ((hm.integrable_comp_emb e.measurableEmbedding).mpr hg)


/-- The literal forward composition equals testing the full regularized joint
kernel, with all three Fourier normalizations, the complementary identity term,
and both amplitude positions (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem forward_composition_eq_jointKernel
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A mi χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    leftLocalizer 1 (fun q => χo q.2 * (1 - mo q))
      (graphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ)
        (rightLocalizer 1 mi f)) x =
      ∫ y, (regularizedJointKernel false S A mi mo χA χo x y).mulVec (f y) := by
  rw [forward_composition_iterated S A mi mo χA χo c hi f hf x,
    regularizedJointKernel_test_fubini false S A mi mo χA χo
      hS hA hi ho hg hc c f hf x]
  congr 1
  exact (integral_jointVariables_forwardOrder _
    (regularizedJointIntegrand_test_integrable false S A mi mo χA χo
      hS hA hi ho hg hc c f hf x).integral_prod_left).symm

/-- The literal reverse composition equals testing the full regularized joint
kernel, with all three Fourier normalizations, the complementary identity term,
and both amplitude positions (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem reverse_composition_eq_jointKernel
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A mi χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    leftLocalizer 1 (fun q => χo q.2 * (1 - mo q))
      (reverseGraphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ)
        (rightLocalizer 1 mi f)) x =
      ∫ y, (regularizedJointKernel true S A mi mo χA χo x y).mulVec (f y) := by
  rw [reverse_composition_iterated S A mi mo χA χo c hi f hf x,
    regularizedJointKernel_test_fubini true S A mi mo χA χo
      hS hA hi ho hg hc c f hf x]
  congr 1
  exact (integral_jointVariables_reverseOrder _
    (regularizedJointIntegrand_test_integrable true S A mi mo χA χo
      hS hA hi ho hg hc c f hf x).integral_prod_left).symm

/-- Physical-covector version of the literal forward Fubini identity. Only
the input/output symbols are normalized by `ρ`; the graph frequency stays
physical (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem forward_composition_scaled_eq_jointKernel
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A (fun q => mi (q.1, ρ⁻¹ • q.2)) χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n)
    (hρ : ρ ≠ 0) :
    leftLocalizer ρ (fun q => χo (ρ • q.2) * (1 - mo q))
      (graphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ)
        (rightLocalizer ρ mi f)) x =
      ∫ y, (regularizedJointKernel false S A
        (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2))
        χA χo x y).mulVec (f y) := by
  have hscale : Continuous (fun q : Euclidean n × Euclidean n => (q.1, ρ⁻¹ • q.2)) :=
    continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)
  have h := forward_composition_eq_jointKernel S A
    (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo
    hS hA (hi.comp hscale) (ho.comp hscale) hg hc c f hf x
  simpa only [leftLocalizer, rightLocalizer, inv_one, one_smul, smul_smul,
    mul_inv_cancel₀ hρ] using h

/-- Physical-covector version of the literal reverse Fubini identity. Only
the input/output symbols are normalized by `ρ`; the graph frequency stays
physical (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem reverse_composition_scaled_eq_jointKernel
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A (fun q => mi (q.1, ρ⁻¹ • q.2)) χA χo)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n)
    (hρ : ρ ≠ 0) :
    leftLocalizer ρ (fun q => χo (ρ • q.2) * (1 - mo q))
      (reverseGraphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ)
        (rightLocalizer ρ mi f)) x =
      ∫ y, (regularizedJointKernel true S A
        (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2))
        χA χo x y).mulVec (f y) := by
  have hscale : Continuous (fun q : Euclidean n × Euclidean n => (q.1, ρ⁻¹ • q.2)) :=
    continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)
  have h := reverse_composition_eq_jointKernel S A
    (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo
    hS hA (hi.comp hscale) (ho.comp hscale) hg hc c f hf x
  simpa only [leftLocalizer, rightLocalizer, inv_one, one_smul, smul_smul,
    mul_inv_cancel₀ hρ] using h
end JanetCartan.FiniteChain.Graph.KernelLimits
