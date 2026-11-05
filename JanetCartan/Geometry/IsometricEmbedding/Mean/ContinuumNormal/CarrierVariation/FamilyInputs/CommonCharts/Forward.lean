module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.NormalizedTransport
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.ForwardJets

/-!
# The literal source family's augmented forward map

The forward input to the common inverse construction in
`paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'. The scale, both physical
positions, incidence, spectator and frequency remain independent variables.
At zero scale we compute the map directly from the seed covector; no retained
current chart is used or identified with the source-normalized chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open NormalizedBackground.SourceGeometry ContinuumNormalReduction.TransportSymbol

variable {n : ℕ}

/-- The zero-scale transport is the adjoint of the seed covector differential.
This is the primitive frozen input to the common-domain construction, with
the original carrier labels (`new:lem:scaling`, `bg-Psi`). -/
theorem sourceTransportPosition_zero_eq_adjoint
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (ζ : (ℝ × Euclidean 2) → Euclidean (n - 1))
    {z : ℝ × Euclidean 2}
    (hκ : DifferentiableAt ℝ (fun η ↦ gradient (fun x ↦ S (x, η)) 0) (ζ z))
    (x : Euclidean n) :
    sourceTransportPosition S ζ 0 (x, z) =
      (fderiv ℝ (fun η ↦ gradient (fun x ↦ S (x, η)) 0) (ζ z)).adjoint x := by
  rw [sourceTransportPosition_zero]
  apply ext_inner_right ℝ
  intro η
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left,
    fderiv_inner_apply ℝ hκ (differentiableAt_const _)]
  simp only [fderiv_const_apply, zero_apply, inner_zero_right, zero_add]
  exact real_inner_comm _ _

/-- At scale zero the averaged gradient is independent of both physical
positions. Its data derivative is therefore computed from the actual seed
covector and the fixed carrier map, as required for the reference incidence
test in `app:ch_background:eq:bg-Psi`. -/
theorem sourceTransportAveragedGradient_zero
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (ζ : (ℝ × Euclidean 2) → Euclidean (n - 1))
    (p : InputVariables n)
    (hκ : DifferentiableAt ℝ (fun η ↦ gradient (fun x ↦ S (x, η)) 0) (ζ p.2.1)) :
    transportAveragedGradient (sourceTransportPosition S ζ 0) p =
      fderiv ℝ (fun η ↦ gradient (fun x ↦ S (x, η)) 0) (ζ p.2.1) p.2.2 := by
  let v := fderiv ℝ (fun η ↦ gradient (fun x ↦ S (x, η)) 0) (ζ p.2.1) p.2.2
  have he : (fun x ↦ inner ℝ (sourceTransportPosition S ζ 0 (x, p.2.1)) p.2.2) =
      fun x ↦ inner ℝ v x := by
    funext x
    rw [sourceTransportPosition_zero_eq_adjoint S ζ hκ,
      ContinuousLinearMap.adjoint_inner_left]
    exact real_inner_comm _ _
  have hg (x : Euclidean n) : gradient (fun y ↦ inner ℝ v y) x = v :=
    ((InnerProductSpace.toDual ℝ (Euclidean n) v).hasFDerivAt.hasGradientAt.gradient).trans
      ((InnerProductSpace.toDual ℝ (Euclidean n)).symm_apply_apply v)
  simp only [transportAveragedGradient, he, hg, intervalIntegral.integral_const,
    sub_zero, one_smul]
  rfl

private theorem augmentedTransport_family_contDiffOn
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {I : Set ℝ} {B : Set (Euclidean n)} {W : Set (ℝ × Euclidean 2)}
    {O : Set (InputVariables n)} {T : Set ℝ}
    (hI : IsOpen I) (hB : IsOpen B) (hW : IsOpen W) (hO : IsOpen O)
    (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hseg : ∀ t ∈ T, MapsTo (transportSegmentInput n t) O (B ×ˢ W))
    (hY : ContDiffOn ℝ ∞ (Function.uncurry Y) (I ×ˢ B ×ˢ W)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ O) := by
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (ℝ × Euclidean 2)) ↦
      fderiv ℝ (Y q.1) q.2) (I ×ˢ B ×ˢ W) := by
    have hs : ContDiffOn ℝ ∞ (fun q : (Euclidean n × (ℝ × Euclidean 2)) × ℝ ↦
        Y q.2 q.1) ((B ×ˢ W) ×ˢ I) :=
      hY.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq ↦ ⟨hq.2, hq.1⟩)
    exact (contDiffOn_parameterFDeriv (hB.prod hW) hI hs).comp
      (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  have hg : ContDiffOn ℝ ∞ (fun a : (ℝ × InputVariables n) × ℝ ↦
      transportSegmentGradient (Y a.1.1) a.2 a.1.2) ((I ×ˢ O) ×ˢ T) := by
    have harg : ContDiffOn ℝ ∞ (fun a : (ℝ × InputVariables n) × ℝ ↦
        (a.1.1, transportSegmentInput n a.2 a.1.2)) ((I ×ˢ O) ×ˢ T) :=
      contDiffOn_fst.fst.prodMk
        ((contDiffOn_fst.snd.fst.snd.add (contDiffOn_snd.smul
          (contDiffOn_fst.snd.fst.fst.sub contDiffOn_fst.snd.fst.snd))).prodMk
          contDiffOn_fst.snd.snd.fst)
    exact ((transportSpatialAdjoint n).contDiff.comp_contDiffOn
      (hd.comp harg (fun a ha ↦ ⟨ha.1.1, hseg a.2 ha.2 ha.1.2⟩))).clm_apply
        contDiffOn_fst.snd.snd.snd
  have havg : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      transportAveragedGradient (Y q.1) q.2) (I ×ˢ O) := by
    apply (contDiffOn_unitIntervalParameterIntegral (hI.prod hO) hT hIT hg).congr
    intro q hq
    exact transportAveragedGradient_eq_integral_segment q.2 (fun t ht ↦
      (((hY.contDiffAt ((hI.prod (hB.prod hW)).mem_nhds
        ⟨hq.1, hseg t (hIT ht) hq.2⟩)).comp _
          (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)))
  exact (contDiffOn_snd.fst.fst.prodMk
    (contDiffOn_snd.fst.snd.prodMk havg)).prodMk contDiffOn_snd.snd.fst.snd

/-- Joint smoothness of the actual source-family augmented map. The two
segment containments concern only the seed and the fixed forward domains;
inverse smoothness is a later conclusion. Consumer: the common normalized
inverse in `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem contDiffOn_sourceAugmentedTransport
    {S : Euclidean n × Euclidean (n - 1) → ℝ}
    {ζ : (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {U B : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    {W : Set (ℝ × Euclidean 2)} {O : Set (InputVariables n)} {r : ℝ}
    (hU : IsOpen U) (hB : IsOpen B) (hV : IsOpen V) (hW : IsOpen W)
    (hO : IsOpen O)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V)) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hζV : MapsTo ζ W V)
    (hseed : ∀ σ ∈ Ioo (-2 * r) (2 * r), ∀ x ∈ B, ∀ t ∈ Ioo (-1 : ℝ) 2,
      (t * σ) • x ∈ U)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hseg : ∀ t ∈ T, MapsTo (transportSegmentInput n t) O (B ×ˢ W)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (sourceTransportPosition S ζ q.1) q.2)
      (Ioo (-2 * r) (2 * r) ×ˢ O) := by
  exact augmentedTransport_family_contDiffOn isOpen_Ioo hB hW hO hT hIT hseg
    (contDiffOn_sourceTransportPosition hU hB hV hS hζ hζV hseed)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
