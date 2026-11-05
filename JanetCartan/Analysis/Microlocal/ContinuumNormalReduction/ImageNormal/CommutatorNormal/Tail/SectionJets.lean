module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.Kernel
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Primitive jet estimates for the exterior Bessel section

The consumer is differentiation of the literal noncompact intermediate integral
in `app:ch_background:prop:bg-frame`, Step 1. All constants below are obtained
from the positive gap and the primitive cutoff jets, before integrating.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem mul_jet_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : Set D} (hs : IsOpen s) {f g : D → ℝ}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    {p : D} (hp : p ∈ s) {N : ℕ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (bf : ∀ j ≤ N, ‖iteratedFDeriv ℝ j f p‖ ≤ B)
    (bg : ∀ j ≤ N, ‖iteratedFDeriv ℝ j g p‖ ≤ C) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q ↦ f q * g q) p‖ ≤ 2 ^ N * B * C := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn hp (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hs hp] at h
  apply h.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (bf j (by have := Finset.mem_range.mp hj; omega))
        (by positivity)) (bg (n - j) (by omega)) (norm_nonneg _) (by positivity)
    _ = 2 ^ n * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      simp
    _ ≤ _ := by gcongr; norm_num

private theorem precomp_jet_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (L : D →L[ℝ] E)
    (hL : ‖L‖ ≤ 1) (p : D) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ‖iteratedFDeriv ℝ n f (L p)‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun q ↦ f (L q)) p‖ ≤ B := by
  change ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ B
  rw [L.iteratedFDeriv_comp_right hf p (by simp)]
  apply ((iteratedFDeriv ℝ n f (L p)).norm_compContinuousLinearMap_le (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hL n) (by positivity) hB).trans_eq
    (by simp)

private def tailDifferenceMap : E × E →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E

private theorem bessel_difference_jet_bound (p : E × E) (hp : p.1 - p.2 ≠ 0) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselKernel (q.1 - q.2)) p‖ ≤
      ‖iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2)‖ * 2 ^ n := by
  let L := tailDifferenceMap (d := d)
  let s : Set E := {x | x ≠ 0}
  have hs : IsOpen s := isOpen_ne
  have hpre : IsOpen (L ⁻¹' s) := hs.preimage L.continuous
  have hmem : L p ∈ s := hp
  have he := L.iteratedFDerivWithin_comp_right contDiffOn_imageBesselKernel_offDiagonal
    hs.uniqueDiffOn hpre.uniqueDiffOn (x := p) hmem (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hpre hmem,
    iteratedFDerivWithin_of_isOpen n hs hmem] at he
  change iteratedFDeriv ℝ n (fun q : E × E ↦ imageBesselKernel (q.1 - q.2)) p = _ at he
  rw [he]
  have hL : ‖L‖ ≤ 2 := (norm_sub_le _ _).trans
    ((add_le_add (ContinuousLinearMap.norm_fst_le ℝ E E)
      (ContinuousLinearMap.norm_snd_le ℝ E E)).trans_eq (by norm_num))
  apply ((iteratedFDeriv ℝ n imageBesselKernel (p.1 - p.2)).norm_compContinuousLinearMap_le
    (fun _ ↦ L)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL n) (norm_nonneg _)

/-- Every finite collection of section jets has a quantitative bound from
primitive cutoff jets and separation. The constant `C` depends only on `d`,
`δ`, and `N`; it is chosen before either cutoff or either cutoff budget
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_imageCommutatorTailSection_primitive_jet_bound
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ β : E → ℝ),
      ContDiff ℝ ∞ χ → ContDiff ℝ ∞ β →
      (∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) →
      ∀ Bχ Bβ : ℝ, 0 ≤ Bχ → 0 ≤ Bβ →
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n χ x‖ ≤ Bχ) →
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n β x‖ ≤ Bβ) →
      ∀ n ≤ N, ∀ p, ‖iteratedFDeriv ℝ n (imageCommutatorTailSection χ β) p‖ ≤
        C * Bχ ^ 2 * (1 + Bβ) := by
  choose K hK bK using fun n ↦
    exists_imageBesselKernel_offDiagonal_jet_decay (d := d) δ hδ n 0
  simp only [pow_zero, one_mul] at bK
  let D := ∑ j ∈ Finset.range (N + 1), K j * 2 ^ j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ mul_nonneg (hK j) (by positivity)
  refine ⟨2 ^ N * (2 ^ N * (2 ^ N)) * D, by positivity, ?_⟩
  intro χ β hχ hβ hplateau Bχ Bβ hBχ hBβ bχ bβ n hn p
  by_cases hp : dist p.1 p.2 < δ
  · have he := ((imageCommutatorTailSection_eventuallyEq_zero χ β hplateau p hp).iteratedFDeriv ℝ n).eq_of_nhds
    rw [he]
    change ‖iteratedFDeriv ℝ n (fun _ : E × E ↦ (0 : ℝ)) p‖ ≤ _
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity
  · have hgap : δ ≤ ‖p.1 - p.2‖ := by simpa [dist_eq_norm] using le_of_not_gt hp
    have hne : p.1 - p.2 ≠ 0 := norm_pos_iff.mp (hδ.trans_le hgap)
    let s : Set (E × E) := {q | q.1 - q.2 ≠ 0}
    have hs : IsOpen s := isOpen_ne.preimage (continuous_fst.sub continuous_snd)
    have hps : p ∈ s := hne
    have hc : ContDiff ℝ ∞ (fun q : E × E ↦ χ q.1) := hχ.comp contDiff_fst
    have hb : ContDiff ℝ ∞ (fun q : E × E ↦ β q.2) := hβ.comp contDiff_snd
    have hkernel : ContDiffOn ℝ ∞ (fun q : E × E ↦ imageBesselKernel (q.1 - q.2)) s :=
      contDiffOn_imageBesselKernel_offDiagonal.comp
        (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ h ↦ h)
    have bc : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun q : E × E ↦ χ q.1) p‖ ≤ Bχ :=
      fun j hj ↦ precomp_jet_bound χ hχ (ContinuousLinearMap.fst ℝ E E)
        (ContinuousLinearMap.norm_fst_le ℝ E E) p j hBχ (bχ j hj _)
    have bb : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun q : E × E ↦ β q.2) p‖ ≤ Bβ :=
      fun j hj ↦ precomp_jet_bound β hβ (ContinuousLinearMap.snd ℝ E E)
        (ContinuousLinearMap.norm_snd_le ℝ E E) p j hBβ (bβ j hj _)
    have bone : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun q : E × E ↦ 1 - β q.2) p‖ ≤ 1 + Bβ := by
      intro j hj
      rw [fun_iteratedFDeriv_sub_apply contDiffAt_const (hb.contDiffAt.of_le (by simp))]
      have hconst : ‖iteratedFDeriv ℝ j (fun _ : E × E ↦ (1 : ℝ)) p‖ ≤ 1 := by
        cases j with
        | zero => simp
        | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; norm_num
      exact (norm_sub_le _ _).trans (add_le_add hconst (bb j hj))
    have bcc : ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun q : E × E ↦ χ q.1 ^ 2) p‖ ≤
        2 ^ N * Bχ * Bχ := by
      simpa only [pow_two] using mul_jet_bound hs hc.contDiffOn hc.contDiffOn hps hBχ hBχ bc bc
    have bcut := mul_jet_bound hs (hc.pow 2).contDiffOn
      (contDiff_const.sub hb).contDiffOn hps (by positivity) (by positivity) bcc bone
    have bkernel : ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (fun q : E × E ↦ imageBesselKernel (q.1 - q.2)) p‖ ≤ D := by
      intro j hj
      exact (bessel_difference_jet_bound p hne j).trans
        ((mul_le_mul_of_nonneg_right (bK j _ hgap) (by positivity)).trans
          (Finset.single_le_sum (fun k _ ↦ mul_nonneg (hK k) (by positivity))
            (Finset.mem_range.mpr (by omega))))
    have h := mul_jet_bound hs ((hc.pow 2).mul (contDiff_const.sub hb)).contDiffOn
      hkernel hps (by positivity) hD bcut bkernel n hn
    exact h.trans_eq (by ring)

/-- The primitive smooth compact cutoffs supply all finite section budgets;
this is the actual domination input for the scalar kernel integral in
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_imageCommutatorTailSection_jet_bound
    (χ β : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ p,
      ‖iteratedFDeriv ℝ n (imageCommutatorTailSection χ β) p‖ ≤ C := by
  have hex (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ B := by
    choose B hB using fun n ↦ (hfc.iteratedFDeriv n).exists_bound_of_continuous
      (hf.continuous_iteratedFDeriv (by simp))
    have hB0 n : 0 ≤ B n := (norm_nonneg _).trans (hB n 0)
    refine ⟨∑ n ∈ Finset.range (N + 1), B n, Finset.sum_nonneg (fun n _ ↦ hB0 n), ?_⟩
    intro n hn x
    exact (hB n x).trans (Finset.single_le_sum (fun j _ ↦ hB0 j)
      (Finset.mem_range.mpr (by omega)))
  obtain ⟨Bχ, hBχ, bχ⟩ := hex χ hχ hχc
  obtain ⟨Bβ, hBβ, bβ⟩ := hex β hβ hβc
  obtain ⟨C, hC, hb⟩ := exists_imageCommutatorTailSection_primitive_jet_bound (d := d) δ hδ N
  exact ⟨C * Bχ ^ 2 * (1 + Bβ), by positivity,
    hb χ β hχ hβ hplateau Bχ Bβ hBχ hBβ bχ bβ⟩

end JanetCartan.ContinuumNormalReduction.ImageNormal
