module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.Basic
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Local jets of the fixed radial continuation

The composition and multiplication in `ConicPhase.extend` cost zero derivatives.
The constant is fixed before the local phase, and uses only the normalization
map and radial factor on the compact set. The consuming construction is the
conic phase of `app:ch_regular_base:lem:characteristic-kernel`; its normalized
budgets enter `app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.ConicPhase

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed multiplication and normalization cost in the phase jets of
`app:ch_regular_base:lem:retarded-kernel`. It contains no local phase or radius. -/
def jetBoundConstant (ℓ : E →L[ℝ] ℝ) (K : Set (TwoTimePoint E)) (n : ℕ) : ℝ :=
  1 + (∑ j ∈ Finset.range (n + 1), ‖ContinuousLinearMap.mul ℝ ℝ‖ *
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
    cNorm K n (fun q ↦ ℓ q.2.2.2) *
    (compositionMultiplicity n * (1 + cNorm K n (normalize ℓ)) ^ n)

/-- Positivity of the fixed phase-jet constant, including order zero
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem jetBoundConstant_pos (ℓ : E →L[ℝ] ℝ) (K : Set (TwoTimePoint E)) (n : ℕ) :
    0 < jetBoundConstant ℓ K n := by
  unfold jetBoundConstant compositionMultiplicity
  have := cNorm_nonneg K n (fun q : TwoTimePoint E ↦ ℓ q.2.2.2)
  have := cNorm_nonneg K n (normalize ℓ)
  positivity

/-- Actual local phase jets bound the fixed conic continuation linearly at
the same order. The compact image and open smoothness domain are supplied by
the buffered chart in `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem cNorm_extend_le (ℓ : E →L[ℝ] ℝ)
    {K J U : Set (TwoTimePoint E)} (hK : IsCompact K) (hJ : IsCompact J)
    (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ q ∈ K, 0 < ℓ q.2.2.2) (hmap : MapsTo (normalize ℓ) K J)
    {F : TwoTimePoint E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (n : ℕ) :
    cNorm K n (extend ℓ F) ≤ jetBoundConstant ℓ K n * cNorm J n F := by
  have hnorm : ∀ q ∈ K, ContDiffAt ℝ n (normalize ℓ) q :=
    fun q hq ↦ (contDiffAt_normalize ℓ (hpos q hq).ne').of_le (by simp)
  have hFlocal : ∀ q ∈ J, ContDiffAt ℝ n F q :=
    fun q hq ↦ (hF.contDiffAt (hU.mem_nhds (hJU hq))).of_le (by simp)
  have hc := cNorm_comp_le_polynomial hnorm (fun q hq ↦ hFlocal _ (hmap hq))
    (fun _ hi ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hnorm hi)
    (cNorm_nonneg J n F)
    (fun i hi q hq ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ hFlocal (hmap hq) hi)
  have hKU : K ⊆ domain ℓ U := fun q hq ↦ ⟨hpos q hq, hJU (hmap hq)⟩
  have hcomp : ContDiffOn ℝ ∞ (F ∘ normalize ℓ) (domain ℓ U) := by
    intro q hq
    exact ((hF.contDiffAt (hU.mem_nhds hq.2)).comp q
      (contDiffAt_normalize ℓ hq.1.ne')).contDiffWithinAt
  have hm := FullPhaseCharts.InverseEstimates.cNorm_bilinear_le_on
    (ContinuousLinearMap.mul ℝ ℝ) hK (isOpen_domain ℓ hU) hKU
    (ℓ.contDiff.comp contDiff_snd.snd.snd).contDiffOn hcomp n
  change cNorm K n (extend ℓ F) ≤ _ at hm
  apply hm.trans
  calc
    _ ≤ (∑ j ∈ Finset.range (n + 1), ‖ContinuousLinearMap.mul ℝ ℝ‖ *
          ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
        cNorm K n (fun q ↦ ℓ q.2.2.2) *
        (compositionMultiplicity n * cNorm J n F *
          (1 + cNorm K n (normalize ℓ)) ^ n) := by
      apply mul_le_mul_of_nonneg_left hc
      exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦
        mul_nonneg (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ))
          (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _))
        (cNorm_nonneg _ _ _)
    _ ≤ jetBoundConstant ℓ K n * cNorm J n F := by
      unfold jetBoundConstant
      nlinarith [cNorm_nonneg J n F]

/-- All iterated derivatives through order `n` satisfy the same zero-loss
bound as the seminorm (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem norm_iteratedFDeriv_extend_le (ℓ : E →L[ℝ] ℝ)
    {K J U : Set (TwoTimePoint E)} (hK : IsCompact K) (hJ : IsCompact J)
    (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ q ∈ K, 0 < ℓ q.2.2.2) (hmap : MapsTo (normalize ℓ) K J)
    {F : TwoTimePoint E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {n k : ℕ} (hk : k ≤ n) {q : TwoTimePoint E} (hq : q ∈ K) :
    ‖iteratedFDeriv ℝ k (extend ℓ F) q‖ ≤ jetBoundConstant ℓ K n * cNorm J n F := by
  apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK (fun p hp ↦
    ((contDiffOn_extend ℓ hU hF).contDiffAt
      ((isOpen_domain ℓ hU).mem_nhds ⟨hpos p hp, hJU (hmap hp)⟩)).of_le
        (by simp)) hq hk).trans
  exact cNorm_extend_le ℓ hK hJ hU hJU hpos hmap hF n

/-- Choose the phase-jet constant before quantifying over the local phase.
No extended-phase budget is an input, and the derivative shift is zero
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_extend_jet_bound (ℓ : E →L[ℝ] ℝ)
    {K J U : Set (TwoTimePoint E)} (hK : IsCompact K) (hJ : IsCompact J)
    (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ q ∈ K, 0 < ℓ q.2.2.2) (hmap : MapsTo (normalize ℓ) K J) (n : ℕ) :
    ∃ A > (0 : ℝ), ∀ F : TwoTimePoint E → ℝ, ContDiffOn ℝ ∞ F U →
      cNorm K n (extend ℓ F) ≤ A * cNorm J n F ∧
      ∀ k ≤ n, ∀ q ∈ K, ‖iteratedFDeriv ℝ k (extend ℓ F) q‖ ≤ A * cNorm J n F := by
  exact ⟨jetBoundConstant ℓ K n, jetBoundConstant_pos ℓ K n, fun F hF ↦
    ⟨cNorm_extend_le ℓ hK hJ hU hJU hpos hmap hF n,
      fun _ hk _ hq ↦ norm_iteratedFDeriv_extend_le ℓ hK hJ hU hJU hpos hmap hF hk hq⟩⟩

end JanetCartan.RegularSector.Characteristic.ConicPhase
