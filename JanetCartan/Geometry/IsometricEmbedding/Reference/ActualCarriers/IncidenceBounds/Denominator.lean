module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Basic
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Local

/-!
# The incidence denominator from primitive first jets

Step 3 of `app:ch_seed:prop:seed-actual-menu`. The transverse derivative is a
fixed smooth function of the frame, phase-gradient and testing-covector values
and their transverse first derivatives. Compact frozen first-jet data with a
transverse gap therefore give a uniform perturbation radius and inverse budget.
The parent must supply the frozen gap and primitive first-jet closeness; no
incidence comparison estimate is assumed.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix Matrix.Norms.Frobenius
open Set Filter

namespace JanetCartan.ActualCarriers

/-- Primitive value and transverse derivative contraction for the denominator
in `app:ch_seed:prop:seed-actual-menu`, Step 3. -/
def incidenceTransverseCoefficient {n : ℕ}
    (j : (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) ×
      (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n)) : ℝ :=
  fderiv ℝ incidenceCoefficient j.1 j.2

/-- The denominator coefficient is smooth even when the pencil is singular
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem contDiff_incidenceTransverseCoefficient {n : ℕ} :
    ContDiff ℝ ∞ (incidenceTransverseCoefficient (n := n)) :=
  (((contDiff_incidenceCoefficient (n := n)).fderiv_right (m := ∞) (by simp)).comp contDiff_fst).clm_apply
    contDiff_snd

/-- The actual transverse derivative is computed from separate primitive first
jets by the chain rule (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem scalarDerivative_incidence_eq {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    {Q : P × ℝ → Fin n → MetricTensor n} {ξ k : P × ℝ → Euclidean n}
    {z : P × ℝ} (hQ : DifferentiableAt ℝ Q z) (hξ : DifferentiableAt ℝ ξ z)
    (hk : DifferentiableAt ℝ k z) :
    CharacteristicRoot.scalarDerivative
        (fun y ↦ fderiv ℝ (determinant (Q y)) (ξ y) (k y)) z =
      incidenceTransverseCoefficient
        (((Q z, ξ z), k z),
          ((fderiv ℝ Q z (0, 1), fderiv ℝ ξ z (0, 1)), fderiv ℝ k z (0, 1))) := by
  have h := (contDiff_incidenceCoefficient.differentiable (by simp)).differentiableAt
    |>.hasFDerivAt.comp z ((hQ.hasFDerivAt.prodMk hξ.hasFDerivAt).prodMk hk.hasFDerivAt)
  exact congrArg (fun L ↦ L (0, 1)) h.fderiv

/-- A fixed compact set of frozen primitive first jets with gap `2c` supplies
the denominator gap and inverse bound for nearby actual jets. This is the
low-order input to the implicit-root estimate in `app:ch_seed:eq:seed-phase-tame`.
The radius is independent of high frame and phase norms. -/
theorem exists_incidence_denominator_radius {n : ℕ}
    {J : Set ((((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) ×
      (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n))}
    (hJ : IsCompact J) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ j ∈ J, 2 * c ≤ |incidenceTransverseCoefficient j|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j₀ ∈ J, ∀ j, ‖j - j₀‖ < δ →
      c ≤ |incidenceTransverseCoefficient j| ∧
        |(incidenceTransverseCoefficient j)⁻¹| ≤ c⁻¹ := by
  have hev : ∀ᶠ e in 𝓝 0, ∀ j ∈ J,
      |incidenceTransverseCoefficient (j + e) - incidenceTransverseCoefficient j| < c := by
    apply hJ.eventually_forall_of_forall_eventually
    intro j _
    have hcont := (((contDiff_incidenceTransverseCoefficient (n := n)).continuous.comp
      (continuous_snd.add continuous_fst)).sub
        ((contDiff_incidenceTransverseCoefficient (n := n)).continuous.comp continuous_snd)).abs
    have hz : |incidenceTransverseCoefficient (j + 0) - incidenceTransverseCoefficient j| < c :=
      by simpa using hc
    exact (hcont.continuousAt (x := (0, j))).eventually (gt_mem_nhds hz)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro j₀ hj₀ j hj
  have he := hb (by simpa only [dist_eq_norm, sub_zero] using hj) j₀ hj₀
  rw [add_sub_cancel] at he
  have hg : c ≤ |incidenceTransverseCoefficient j| := by
    have ht := abs_sub_abs_le_abs_sub
      (incidenceTransverseCoefficient j₀) (incidenceTransverseCoefficient j)
    rw [abs_sub_comm] at ht
    linarith [hgap j₀ hj₀]
  exact ⟨hg, by rw [abs_inv]; exact (inv_le_inv₀ (hc.trans_le hg) hc).mpr hg⟩

end JanetCartan.ActualCarriers
