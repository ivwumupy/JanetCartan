module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CarrierProperties
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity

/-!
# Rank of the constructed characteristic carriers

Frozen rank supplies a positive compact adjugate gap. Joint continuity in the
frame and covector, followed by the actual Hamilton comparison, preserves this
gap for the selected carriers (`app:ch_seed:prop:seed-actual-menu`, Step 2).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Matrix.Norms.Frobenius Topology
namespace JanetCartan.ActualCarriers
open FrozenMenu CurrentFullPhase

/-- A frozen characteristic patch supplies a positive adjugate gap for nearby
frames and covectors. Both perturbations are measured in the literal shared
Euclidean/Frobenius norms (`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem exists_patch_adjugate_perturbation_radius {n : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C) :
    ∃ δ a : ℝ, 0 < δ ∧ 0 < a ∧
      ∀ (Q : Fin n → MetricTensor n) (ξ : Euclidean n) (z : Euclidean 3),
        z ∈ parameterCube P.radius → ‖Q - cubeStress n‖ < δ →
        ‖ξ - P.toFun z‖ < δ → a ≤ ‖(pencil Q ξ).adjugate‖ := by
  have hs : ContinuousOn P.toFun (parameterCube P.radius) :=
    hP.2.2.2.1.continuousOn.mono (parameterCube_subset_doubledInterior hP.1)
  have hcont : ContinuousOn (fun z ↦ ‖(cubePencil (P.toFun z)).adjugate‖)
      (parameterCube P.radius) := by
    simpa only [Function.comp_def, pencil_cubeStress] using
      (contDiff_adjugate_pencil (n := n)).continuous.norm.comp_continuousOn
      (f := fun z ↦ (cubeStress n, P.toFun z)) (continuousOn_const.prodMk hs)
  obtain ⟨a, ha, hgap⟩ := (isCompact_parameterCube P.radius).exists_forall_le'
    hcont
    (show ∀ z ∈ parameterCube P.radius, 0 < ‖(cubePencil (P.toFun z)).adjugate‖ from by
      intro z hz
      apply norm_pos_iff.mpr
      intro hzero
      have hh := (adjugate_eq_zero_iff_rank_add_two_le (by omega)
        (cubePencil (P.toFun z))).mp hzero
      have hr := (hP.2.2.2.2.1 z hz).2.2.1
      omega)
  let f : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 → ℝ :=
    fun p ↦ ‖(pencil (cubeStress n + p.1.1) (P.toFun p.2 + p.1.2)).adjugate‖
  have hev : ∀ᶠ e in 𝓝 (0 : (Fin n → MetricTensor n) × Euclidean n),
      ∀ z ∈ parameterCube P.radius, a / 2 < f (e, z) := by
    apply (isCompact_parameterCube P.radius).eventually_forall_of_forall_eventually
    intro z hz
    have hp : ContinuousAt P.toFun z := (hP.2.2.2.1.contDiffAt
      ((isOpen_parameterInterior _).mem_nhds
        (parameterCube_subset_doubledInterior hP.1 hz))).continuousAt
    have hq : ContinuousAt
        (fun p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 ↦
          cubeStress n + p.1.1) (0, z) :=
      continuousAt_const.add continuousAt_fst.fst
    have hv : ContinuousAt
        (fun p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 ↦
          P.toFun p.2 + p.1.2) (0, z) :=
      (hp.comp continuousAt_snd).add continuousAt_fst.snd
    have hpair : ContinuousAt
        (fun p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 ↦
          (cubeStress n + p.1.1, P.toFun p.2 + p.1.2)) (0, z) := hq.prodMk hv
    have hout : ContinuousAt
        (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ ‖(pencil p.1 p.2).adjugate‖)
        (cubeStress n + (0 : Fin n → MetricTensor n), P.toFun z + (0 : Euclidean n)) :=
      (contDiff_adjugate_pencil (n := n)).continuous.norm.continuousAt
    have hf : ContinuousAt f (0, z) := hout.comp
      (f := fun p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean 3 ↦
        (cubeStress n + p.1.1, P.toFun p.2 + p.1.2)) (x := (0, z)) hpair
    have hz0 : a / 2 < f (0, z) := by
      simpa only [f, Prod.fst_zero, Prod.snd_zero, add_zero, pencil_cubeStress] using
        (half_lt_self ha).trans_le (hgap z hz)
    exact hf.eventually (lt_mem_nhds hz0)
  obtain ⟨δ, hδ, hδclose⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, a / 2, hδ, half_pos ha, fun Q ξ z hz hQ hξ ↦ ?_⟩
  have he : dist (Q - cubeStress n, ξ - P.toFun z) 0 < δ := by
    simpa only [dist_eq_norm, sub_zero, Prod.norm_def] using max_lt hQ hξ
  have hh := (hδclose he z hz).le
  simpa only [f, add_sub_cancel, add_sub_cancel_left] using hh

namespace CurrentFullPhase.PatchQuantitativeFamily

/-- For the same constructed carriers, primitive frame `C⁶` closeness implies
a uniform positive adjugate gap and rank exactly `n-1`. The upper rank bound
uses their proved exact characteristic equation. The construction ball must
contain the retained frame ball, and the tested physical points lie in both
the chart and the construction domain (`app:ch_seed:prop:seed-actual-menu`,
item 1). -/
theorem exists_carrier_rank_threshold {n : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ a : ℝ, 0 < δ ∧ 0 < a ∧ ∀ Q,
      cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ ball (0 : Euclidean n) T.physicalRadius, x ∈ K →
      ∀ z ∈ parameterCube P.radius,
        a ≤ ‖(pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate‖ ∧
        (pencil (Q.1 x) (T.carrierGradient Q x z)).rank = n - 1 := by
  obtain ⟨d, a, hd, ha, hgap⟩ := exists_patch_adjugate_perturbation_radius hn hP
  obtain ⟨e, he, hcomp⟩ := T.exists_carrier_comparison_threshold hP (half_pos hd)
  refine ⟨min d e, a, lt_min hd he, ha, fun Q hclose x hx hxK z hz ↦ ?_⟩
  have hs : ∀ y ∈ K, ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) y := by
    intro y hy
    exact ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hy))).sub contDiffAt_const).of_le (by simp)
  have hQx : ‖Q.1 x - cubeStress n‖ < d := by
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hs hxK (Nat.zero_le 6)
    have hv : ‖Q.1 x - cubeStress n‖ ≤ cNorm K 6 (Q.1 - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hh
    exact hv.trans_lt (hclose.trans_le (min_le_left _ _))
  have hlocal := (cNorm_mono_set_of_contDiffAt hball hK hs).trans_lt
    (hclose.trans_le (min_le_right _ _))
  have hξ := ((hcomp Q hlocal x hx z hz).1).trans_lt (half_lt_self hd)
  have ha' := hgap (Q.1 x) (T.carrierGradient Q x z) z hz hQx hξ
  refine ⟨ha', ?_⟩
  have hne : (pencil (Q.1 x) (T.carrierGradient Q x z)).adjugate ≠ 0 :=
    norm_pos_iff.mp (ha.trans_le ha')
  have hr := (adjugate_eq_zero_iff_rank_add_two_le (by omega)
    (pencil (Q.1 x) (T.carrierGradient Q x z))).not.mp hne
  have hdet := T.carrier_characteristic Q hx (parameterCube_subset_doubledInterior hP.1 hz)
  have hle := Matrix.rank_le_card_width (pencil (Q.1 x) (T.carrierGradient Q x z))
  have hnot : (pencil (Q.1 x) (T.carrierGradient Q x z)).rank ≠ n := by
    intro heq
    have hsurj := (Matrix.mulVec_surjective_iff_rank_eq_card
      (M := pencil (Q.1 x) (T.carrierGradient Q x z))).mpr
      (by simpa only [Fintype.card_fin] using heq)
    have hunit := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero hdet
  simp only [Fintype.card_fin] at hle
  omega

end CurrentFullPhase.PatchQuantitativeFamily
end JanetCartan.ActualCarriers
