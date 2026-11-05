module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootStability
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.SymbolJets

/-!
# Scalar-symbol continuity of the constructed section roots

For `app:lem:common-hamilton-phase`, retain the transverse cylinder when
constructing the roots. This makes the differentiated implicit-equation
estimate applicable to the actual branches. The consumer is the common
root-initialized Hamilton-flow construction in `SectionFlows`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

/-- `app:lem:common-hamilton-phase`: symbol order `m + 1` controls the actual
section root at order `m` on the inner parameter ball. The tolerance also
preserves the scalar derivative gap, including when `m = 0`. No root derivative
comparison is an assumption. This is used by the constructed family below. -/
theorem exists_sectionRoot_finiteOrder_tolerance
    (H₀ : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    {D L : Set (E × E)} (hD : IsOpen D) (hL : IsCompact L) (hLD : L ⊆ D)
    (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    {s₀ : InitialData U} {r l u c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hmap : MapsTo (transverseSectionState j ν) (closedBall s₀ (2 * r) ×ˢ Icc l u) L)
    {g₀ : InitialData U → ℝ} (hg₀ : ContDiffOn ℝ ∞ g₀ (ball s₀ (2 * r)))
    (hgap : ∀ z ∈ closedBall s₀ (2 * r) ×ˢ Icc l u,
      2 * c ≤ |CharacteristicRoot.scalarDerivative (sectionEnergyEquation H₀ j ν) z|)
    (hroot₀ : ∀ s ∈ ball s₀ (2 * r), g₀ s ∈ Icc l u ∧
      H₀.h (transverseSectionState j ν (s, g₀ s)) = s.2.1)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ),
      ContDiffOn ℝ ∞ H.h D → ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc l u ∧
        H.h (transverseSectionState j ν (s, g s)) = s.2.1) →
      cNorm L (m + 1) (fun z ↦ H.h z - H₀.h z) < δ →
      cNorm (closedBall s₀ r) m (g - g₀) < ε := by
  let Q := closedBall s₀ (2 * r) ×ˢ Icc l u
  let W := transverseSectionState j ν ⁻¹' D
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hW : IsOpen W := hD.preimage (contDiff_transverseSectionState j ν).continuous
  have hQW : Q ⊆ W := fun _ hz ↦ hLD (hmap hz)
  have hf (H : HomogeneousSymbol E) (hH : ContDiffOn ℝ ∞ H.h D) :
      ContDiffOn ℝ ∞ (sectionEnergyEquation H j ν) W :=
    (hH.comp (contDiff_transverseSectionState j ν).contDiffOn
      (fun _ hz ↦ hz)).sub contDiff_fst.snd.fst.contDiffOn
  obtain ⟨d, hd, hb⟩ := CharacteristicRoot.exists_finiteOrder_root_continuity_on_closedBall
    hr hc hW hQW (hf H₀ hH₀) hg₀ hgap
    (fun s hs ↦ ⟨(hroot₀ s hs).1, sub_eq_zero.mpr (hroot₀ s hs).2⟩) m hε
  obtain ⟨B₁, hB₁, hb₁⟩ := exists_sectionEnergy_finiteOrder_bound j ν hQ 1
  obtain ⟨B, hB, hbM⟩ := exists_sectionEnergy_finiteOrder_bound j ν hQ m
  refine ⟨min (c / B₁) (d / B), lt_min (div_pos hc hB₁) (div_pos hd hB), ?_⟩
  intro H g hH hg hroot hsmall
  apply hb (sectionEnergyEquation H j ν) g (hf H hH) hg
    (fun s hs ↦ ⟨(hroot s hs).1, sub_eq_zero.mpr (hroot s hs).2⟩)
  · apply (hb₁ H H₀ D L hD (hH.of_le (by simp)) (hH₀.of_le (by simp))
      hL hLD hmap).trans
    have hn : cNorm L 1 (fun z ↦ H.h z - H₀.h z) < c / B₁ :=
      (cNorm_mono_order (by omega : 1 ≤ m + 1)).trans_lt
        (hsmall.trans_le (min_le_left _ _))
    exact ((mul_lt_mul_of_pos_left hn hB₁).trans_eq (mul_div_cancel₀ c hB₁.ne')).le
  · apply (hbM H H₀ D L hD (hH.of_le (by simp)) (hH₀.of_le (by simp))
      hL hLD hmap).trans_lt
    have hn : cNorm L m (fun z ↦ H.h z - H₀.h z) < d / B :=
      (cNorm_mono_order (Nat.le_succ m)).trans_lt (hsmall.trans_le (min_le_right _ _))
    exact (mul_lt_mul_of_pos_left hn hB).trans_eq (mul_div_cancel₀ d hB.ne')

/-- `app:lem:common-hamilton-phase`: construct actual smooth section roots on a
single cylinder and prove their finite-order symbol continuity there. The
compact normalized state set `L` is explicit and fixed before perturbation.
The open set `D'` can restrict the initial states to the inner flow ball.
Scalar uniqueness fixes the reference value and identifies every admissible
branch, so no choice of a separately constructed root is assumed compatible. -/
theorem exists_common_finiteOrder_sectionRoots
    (H₀ : HomogeneousSymbol E) {D D' L : Set (E × E)}
    (hD : IsOpen D) (hD' : IsOpen D') (hD'D : D' ⊆ D)
    (hD'L : D' ⊆ L) (hL : IsCompact L) (hLD : L ⊆ D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ D')
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ (r a δ : ℝ) (g₀ : InitialData U → ℝ),
      0 < r ∧ 0 < a ∧ 0 < δ ∧ g₀ s₀ = τ₀ ∧
      MapsTo (transverseSectionState j ν)
        (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) D' ∧
      ContDiffOn ℝ ∞ g₀ (ball s₀ (2 * r)) ∧
      (∀ s ∈ ball s₀ (2 * r), g₀ s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
        H₀.h (transverseSectionState j ν (s, g₀ s)) = s.2.1) ∧
      (∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ),
        ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ),
          ContDiffOn ℝ ∞ H.h D → ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1) →
          cNorm L (m + 1) (fun z ↦ H.h z - H₀.h z) < d →
          cNorm (closedBall s₀ r) m (g - g₀) < ε) ∧
      ∀ H : HomogeneousSymbol E, ContDiffOn ℝ ∞ H.h D →
        cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ g : InitialData U → ℝ, ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1) ∧
          (∀ s ∈ ball s₀ (2 * r), ∀ t ∈ Icc (τ₀ - a) (τ₀ + a),
            H.h (transverseSectionState j ν (s, t)) = s.2.1 ↔ g s = t) := by
  let W := transverseSectionState j ν ⁻¹' D'
  have hW : IsOpen W := hD'.preimage (contDiff_transverseSectionState j ν).continuous
  have hf (H : HomogeneousSymbol E) (hH : ContDiffOn ℝ ∞ H.h D) :
      ContDiffOn ℝ ∞ (sectionEnergyEquation H j ν) W :=
    (hH.comp (contDiff_transverseSectionState j ν).contDiffOn
      (fun _ hz ↦ hD'D hz)).sub contDiff_fst.snd.fst.contDiffOn
  have hd : CharacteristicRoot.scalarDerivative (sectionEnergyEquation H₀ j ν) (s₀, τ₀) ≠ 0 := by
    rw [scalarDerivative_sectionEnergyEquation H₀ j ν (hDH₀ (hD'D hbase))]
    exact htrans
  obtain ⟨r, a, c, e, hr, ha, hc, he, hQW, hgap, hend⟩ :=
    CharacteristicRoot.exists_simple_root_cylinder hW (hf H₀ hH₀) hbase
      (sub_eq_zero.mpr henergy) hd
  let Q := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod isCompact_Icc
  have hseg : ∀ s ∈ ball s₀ (2 * r), ∀ t ∈ Icc (τ₀ - a) (τ₀ + a), (s, t) ∈ Q :=
    fun _ hs _ ht ↦ ⟨ball_subset_closedBall hs, ht⟩
  obtain ⟨g₀, hg₀, hroot₀, hpert⟩ := CharacteristicRoot.exists_stable_roots_on_cylinder
    hQ hW hQW isOpen_ball (hf H₀ hH₀) (by linarith : τ₀ - a < τ₀ + a) hc he
    hseg hgap (fun s hs ↦ hend s (ball_subset_closedBall hs))
  have hgbase : g₀ s₀ = τ₀ := by
    have hs : s₀ ∈ ball s₀ (2 * r) := mem_ball_self (by positivity)
    apply CharacteristicRoot.scalar_root_unique_of_gap hc
      (fun t ht ↦ ((hf H₀ hH₀).contDiffAt (hW.mem_nhds (hQW (hseg _ hs t ht)))).differentiableAt
        (by simp))
      (fun t ht ↦ by linarith [hgap _ (hseg _ hs t ht)])
      (Ioo_subset_Icc_self (hroot₀ _ hs).1) ⟨by linarith, by linarith⟩ (hroot₀ _ hs).2
    exact sub_eq_zero.mpr henergy
  obtain ⟨B, hB, hb⟩ := exists_sectionEnergy_finiteOrder_bound j ν hQ 2
  refine ⟨r, a, min c (e / 2) / B, g₀, hr, ha,
    div_pos (lt_min hc (half_pos he)) hB, hgbase, hQW, hg₀,
    (fun s hs ↦ ⟨(hroot₀ s hs).1, sub_eq_zero.mp (hroot₀ s hs).2⟩), ?_, ?_⟩
  · intro m ε hε
    exact exists_sectionRoot_finiteOrder_tolerance H₀ j ν hD hL hLD hH₀ hr hc
      (fun _ hz ↦ hD'L (hQW hz)) hg₀ hgap
      (fun s hs ↦ ⟨Ioo_subset_Icc_self (hroot₀ s hs).1,
        sub_eq_zero.mp (hroot₀ s hs).2⟩) m hε
  · intro H hH hsmall
    have heq : cNorm Q 2 (sectionEnergyEquation H j ν - sectionEnergyEquation H₀ j ν) ≤
        min c (e / 2) := by
      apply (hb H H₀ D L hD (hH.of_le (by simp)) (hH₀.of_le (by simp)) hL hLD
        (fun _ hz ↦ hD'L (hQW hz))).trans
      calc
        _ ≤ B * cNorm L 3 (fun z ↦ H.h z - H₀.h z) :=
          mul_le_mul_of_nonneg_left (cNorm_mono_order (by omega)) hB.le
        _ ≤ B * (min c (e / 2) / B) := mul_le_mul_of_nonneg_left hsmall hB.le
        _ = _ := mul_div_cancel₀ _ hB.ne'
    obtain ⟨g, hg, hroot, huniq⟩ := hpert (sectionEnergyEquation H j ν) (hf H hH) heq
    refine ⟨g, hg, (fun s hs ↦ ⟨(hroot s hs).1, sub_eq_zero.mp (hroot s hs).2.1⟩), ?_⟩
    intro s hs t ht
    simpa only [sectionEnergyEquation, sub_eq_zero] using huniq s hs t ht

end JanetCartan.HamiltonPhase
