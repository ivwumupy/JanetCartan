module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceBounds.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Basic

/-!
# Uniform comparison of the literal incidence first jet

The determinant differential is a smooth polynomial, including at singular
pencils. Compact frozen primitive jets therefore give a uniform modulus for
the value and the *full* differential of incidence. This is the finite
dimensional step in `app:ch_seed:prop:seed-actual-menu`, Step 3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate the literal determinant incidence and its full differential on
a primitive value and derivative. The consumer is the buffered-cylinder
comparison in Step 3 of `app:ch_seed:prop:seed-actual-menu`. -/
def incidenceFirstJet
    (j : (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) ×
      (E →L[ℝ] (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n))) :
    ℝ × (E →L[ℝ] ℝ) :=
  (incidenceCoefficient j.1, (fderiv ℝ incidenceCoefficient j.1).comp j.2)

/-- Polynomial smoothness gives continuity of the full first-jet evaluation,
with no invertibility assumption (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem continuous_incidenceFirstJet :
    Continuous (incidenceFirstJet (n := n) (E := E)) := by
  exact ((contDiff_incidenceCoefficient (n := n)).continuous.comp continuous_fst).prodMk
    ((((contDiff_incidenceCoefficient (n := n)).fderiv_right (m := ∞) (by simp)).continuous.comp
      continuous_fst).clm_comp continuous_snd)

/-- A compact set of frozen primitive first jets gives one positive radius
controlling both the incidence value and its full Fréchet derivative. The
primitive jet estimates will be supplied by the selected Hamilton carriers
and the frame norm, not assumed as incidence estimates
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem exists_uniform_incidence_firstJet_radius
    {J : Set ((((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) ×
      (E →L[ℝ] (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n)))}
    (hJ : IsCompact J) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ j₀ ∈ J, ∀ (j : (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) ×
      (E →L[ℝ] (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n))),
      ‖j.1 - j₀.1‖ < δ → ‖j.2 - j₀.2‖ < δ →
      |incidenceCoefficient j.1 - incidenceCoefficient j₀.1| < ε ∧
      ‖(fderiv ℝ incidenceCoefficient j.1).comp j.2 -
        (fderiv ℝ incidenceCoefficient j₀.1).comp j₀.2‖ < ε := by
  let V := (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) ×
    (E →L[ℝ] (((Fin n → MetricTensor n) × Euclidean n) × Euclidean n))
  have hcont : Continuous (fun p : V × V ↦
      ‖incidenceFirstJet (p.2 + p.1) - incidenceFirstJet p.2‖) :=
    (((continuous_incidenceFirstJet (n := n) (E := E)).comp (continuous_snd.add continuous_fst)).sub
      ((continuous_incidenceFirstJet (n := n) (E := E)).comp continuous_snd)).norm
  have hev : ∀ᶠ e in 𝓝 (0 : V), ∀ j₀ ∈ J,
      ‖incidenceFirstJet (j₀ + e) - incidenceFirstJet j₀‖ < ε := by
    apply hJ.eventually_forall_of_forall_eventually
    intro j₀ _
    have hz : ‖incidenceFirstJet (j₀ + (0 : V)) - incidenceFirstJet j₀‖ < ε := by
      simpa using hε
    exact (hcont.continuousAt (x := (0, j₀))).eventually (gt_mem_nhds hz)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun j₀ hj₀ j hv hL ↦ ?_⟩
  have hj : dist (j - j₀) 0 < δ := by
    simpa only [dist_eq_norm, sub_zero, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      max_lt_iff] using And.intro hv hL
  have hh := hd hj j₀ hj₀
  simpa only [add_sub_cancel, incidenceFirstJet, Prod.fst_sub, Prod.snd_sub,
    Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using hh

end JanetCartan.ActualCarriers
