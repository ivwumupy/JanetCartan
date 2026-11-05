module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Basic
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Averaging

/-!
# Full physical jets of the literal averaged phase coefficients

The consumer is `PhysicalMean.sampledAdjointMomentTemplate_physical_jet_le`
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). These are exact deductions from
joint primitive phase jets, with costs one for `Y` and two for the mixed
coefficient. Physical time is part of the differentiated first variable.
The actual phase profile comes from the retained full Hamilton phase, not from
an independently assumed profile for the inverse or for a successful operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace JanetCartan.PhysicalAdjointGeometry

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- The carrier/displacement substitution has a fixed norm bound, independent
of the input frequency (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_segment_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segment (X := X) (m := m) t‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change max ‖q.1‖ ‖q.2.1 + t • q.2.2‖ ≤ 2 * ‖q‖
  have hx := norm_fst_le q
  have hz := (norm_fst_le q.2).trans (norm_snd_le q)
  have hd := (norm_snd_le q.2).trans (norm_snd_le q)
  apply max_le
  · linarith [norm_nonneg q]
  · calc
      _ ≤ ‖q.2.1‖ + ‖t • q.2.2‖ := norm_add_le _ _
      _ = ‖q.2.1‖ + t * ‖q.2.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖q.2.1‖ + ‖q.2.2‖ :=
        add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) ht.2)
      _ ≤ _ := by linarith

/-- The fixed covector extraction loses precisely one joint phase derivative
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_covectorGradient_le {S : X × Euclidean m → ℝ}
    {p : X × Euclidean m} (hS : ContDiffAt ℝ ∞ S p) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (covectorGradient S) p‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) S p‖ := by
  let R := FullPhaseCharts.InverseEstimates.physicalDifferentialRestriction
    (P := X) (X := Euclidean m)
  have he : covectorGradient S =
      (InnerProductSpace.toDual ℝ (Euclidean m)).symm ∘ R ∘ fderiv ℝ S := rfl
  rw [he, (InnerProductSpace.toDual ℝ (Euclidean m)).symm.norm_iteratedFDeriv_comp_left]
  have hd := hS.fderiv_right (m := ∞) (by simp)
  calc
    _ ≤ ‖R‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ S) p‖ :=
      R.norm_iteratedFDeriv_comp_left hd (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ S) p‖ :=
      mul_le_mul_of_nonneg_right
        FullPhaseCharts.InverseEstimates.norm_physicalDifferentialRestriction_le (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- Local smoothness of the original covector gradient, retaining every
joint variable (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem contDiffOn_covectorGradient {S : X × Euclidean m → ℝ}
    {Ω : Set (X × Euclidean m)} (hΩ : IsOpen Ω) (hS : ContDiffOn ℝ ∞ S Ω) :
    ContDiffOn ℝ ∞ (covectorGradient S) Ω := by
  exact (InnerProductSpace.toDual ℝ (Euclidean m)).symm.contDiff.comp_contDiffOn
    ((hS.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_comp contDiffOn_const)

/-- Joint derivatives of the literal segment integrand cost one phase
order and only the fixed factor `2^j`, never `|η|` or a band power
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_covectorSegment_le {S : X × Euclidean m → ℝ}
    {Ω : Set (X × Euclidean m)} (hΩ : IsOpen Ω) (hS : ContDiffOn ℝ ∞ S Ω)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {q : Point X m} (hq : segment t q ∈ Ω)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w ↦ covectorGradient S (segment t w)) q‖ ≤
      2 ^ j * ‖iteratedFDeriv ℝ (j + 1) S (segment t q)‖ := by
  have hc := contDiffOn_covectorGradient hΩ hS
  have hpre := hΩ.preimage (segment (X := X) (m := m) t).continuous
  have he := (segment (X := X) (m := m) t).iteratedFDerivWithin_comp_right
    hc hΩ.uniqueDiffOn hpre.uniqueDiffOn hq (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen j hpre hq,
    iteratedFDerivWithin_of_isOpen j hΩ hq] at he
  change ‖iteratedFDeriv ℝ j (covectorGradient S ∘ segment t) q‖ ≤ _
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ (j + 1) S (segment t q)‖ * 2 ^ j := by
      apply mul_le_mul
        (norm_jet_covectorGradient_le (hS.contDiffAt (hΩ.mem_nhds hq)) j)
      · simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_segment_le ht) j
      · positivity
      · positivity
    _ = _ := mul_comm _ _

/-- Full joint jets of `Y` follow from primitive phase jets under the original
segment containment. The bound can carry any reserve profile; it is not an
inverse-coefficient premise (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_averagedCovector_le [FiniteDimensional ℝ X]
    {S : X × Euclidean m → ℝ} {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hS : ContDiffOn ℝ ∞ S Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {A : ℕ → ℝ} {k : ℕ}
    (hjet : ∀ j ≤ k + 1, ∀ p ∈ Ω, ‖iteratedFDeriv ℝ j S p‖ ≤ A j)
    {q : Point X m} (hq : q ∈ V) :
    ‖iteratedFDeriv ℝ k (averagedCovector S) q‖ ≤ 2 ^ k * A (k + 1) := by
  apply NormalComparison.norm_iteratedFDeriv_unitIntervalIntegral_le
    (H := fun w : ℝ × Point X m ↦ covectorGradient S (segment w.1 w.2))
    (B := fun j ↦ 2 ^ j * A (j + 1)) hV _ _ hq
  · intro z hz
    have hc := (contDiffOn_covectorGradient hΩ hS).contDiffAt
      (hΩ.mem_nhds (hseg z.2 hz.2 z.1 hz.1))
    have hm : ContDiffAt ℝ ∞ (fun w : ℝ × Point X m ↦
        (w.2.1, w.2.2.1 + w.1 • w.2.2.2)) z := by fun_prop
    have hh := hc.comp z hm
    simpa only [Function.comp_def, segment_apply] using hh
  · intro j hj t ht w hw
    exact (norm_jet_covectorSegment_le hΩ hS ht (hseg w hw t ht) j).trans
      (mul_le_mul_of_nonneg_left (hjet (j + 1) (by omega) _ (hseg w hw t ht))
        (by positivity))

/-- The physical injection is a contraction whenever the original transverse
section is. This does not freeze physical time (`new:lem:mean-recurrence`). -/
theorem norm_physicalInjection_le {W : Euclidean m →L[ℝ] X} (hW : ‖W‖ ≤ 1) :
    ‖physicalInjection W‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simpa [physicalInjection] using (W.le_opNorm h).trans
    (mul_le_mul_of_nonneg_right hW (norm_nonneg _))

/-- Restricting the physical differential of `Y` to the transverse section
costs exactly one further joint derivative (`new:lem:mean-recurrence`). -/
theorem norm_jet_mixedTranspose_le {W : Euclidean m →L[ℝ] X} (hW : ‖W‖ ≤ 1)
    {Y : Point X m → Euclidean m} {q : Point X m}
    (hY : ContDiffAt ℝ ∞ Y q) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (mixedTranspose W Y) q‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) Y q‖ := by
  let R : (Point X m →L[ℝ] Euclidean m) →L[ℝ] (Euclidean m →L[ℝ] Euclidean m) :=
    (ContinuousLinearMap.compL ℝ (Euclidean m) (Point X m) (Euclidean m)).flip
      (physicalInjection W)
  have hR : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro A
    change ‖A.comp (physicalInjection W)‖ ≤ 1 * ‖A‖
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left (norm_physicalInjection_le hW) (norm_nonneg A))
  have hb := R.norm_iteratedFDeriv_comp_left
    (hY.fderiv_right (m := ∞) (by simp)) (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (mixedTranspose W Y) q‖ ≤ _ at hb
  rw [norm_iteratedFDeriv_fderiv] at hb
  exact hb.trans (by simpa using (mul_le_mul_of_nonneg_right hR
    (norm_nonneg (iteratedFDeriv ℝ (j + 1) Y q))))

end JanetCartan.PhysicalAdjointGeometry
