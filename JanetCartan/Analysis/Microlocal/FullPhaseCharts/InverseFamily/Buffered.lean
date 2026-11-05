module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseFamily.Regularity
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral

/-!
# Common buffered smooth inverse families

Assembling the two quarter gaps and the value comparison in
`app:lem:buffered-inverse-stability` with joint forward smoothness gives the
inverse family required by `app:ch_seed:prop:seed-phase-charts`.
All domains and constants are chosen before the parameterized perturbation.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Output, not input, of the common inverse construction for
`app:ch_seed:prop:seed-phase-charts`. The inverse is the explicit fiberwise
choice `phaseChartInverse`, whose parameter regularity is proved by uniqueness. -/
structure BufferedPhaseInverse (f : P → E → E) (U : Set P)
    (K D₁ D V L : Set E) (δ c : ℝ) (G : E ≃L[ℝ] E) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry (phaseChartInverse f D₁)) (U ×ˢ V)
  injective : ∀ p ∈ U, InjOn (f p) D
  lower : ∀ p ∈ U, ∀ x ∈ D, ∀ y ∈ D,
    ‖x - y‖ / 2 ≤ ‖G.symm (f p x - f p y)‖
  image_subset : ∀ p ∈ U, f p '' K ⊆ L
  inner_buffer : ∀ p ∈ U, cthickening δ (f p '' K) ⊆ V
  outer_buffer : ∀ p ∈ U, cthickening δ (closure V) ⊆ f p '' D₁
  inverse_mem : ∀ p ∈ U, ∀ v ∈ V, phaseChartInverse f D₁ p v ∈ D₁
  right_inv : ∀ p ∈ U, ∀ v ∈ V, f p (phaseChartInverse f D₁ p v) = v
  left_inv : ∀ p ∈ U, ∀ u ∈ D₁, phaseChartInverse f D₁ p (f p u) = u
  differential_bounds : ∀ p ∈ U, ∀ u ∈ D,
    Function.Bijective (fderiv ℝ (f p) u) ∧
    ‖(fderiv ℝ (f p) u).inverse‖ ≤ 2 * ‖(G.symm : E →L[ℝ] E)‖ ∧
    c ≤ |(fderiv ℝ (f p) u).det|

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- Ambient smoothness at every point of a closed parameter box contained in
the open extension, in particular at both epsilon endpoints in
`app:ch_seed:prop:seed-phase-charts`. The subset hypothesis is explicit. -/
theorem BufferedPhaseInverse.contDiffAt_on_box
    {f : P → E → E} {U Q : Set P} {K D₁ D V L : Set E} {δ c : ℝ}
    {G : E ≃L[ℝ] E} (h : BufferedPhaseInverse f U K D₁ D V L δ c G)
    (hU : IsOpen U) (hV : IsOpen V) (hQ : Q ⊆ U)
    {p : P} (hp : p ∈ Q) {v : E} (hv : v ∈ V) :
    ContDiffAt ℝ ∞ (Function.uncurry (phaseChartInverse f D₁)) (p, v) :=
  h.smooth.contDiffAt ((hU.prod hV).mem_nhds ⟨hQ hp, hv⟩)

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- Uniqueness on the entire outer data chart, even when a candidate was chosen
on a different inner domain (`app:ch_seed:prop:seed-phase-charts`). -/
theorem BufferedPhaseInverse.inverse_eq_of_apply_eq
    {f : P → E → E} {U : Set P} {K D₁ D V L : Set E} {δ c : ℝ}
    {G : E ≃L[ℝ] E} (h : BufferedPhaseInverse f U K D₁ D V L δ c G)
    (h₁D : D₁ ⊆ D) {p : P} (hp : p ∈ U) {u v : E}
    (hu : u ∈ D) (hv : v ∈ V) (he : f p u = v) :
    phaseChartInverse f D₁ p v = u :=
  h.injective p hp (h₁D (h.inverse_mem p hp v hv)) hu
    ((h.right_inv p hp v hv).trans he.symm)

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- Smoothness on a literal closed epsilon interval, with an explicit open
interval extension and an open neighborhood of the remaining parameter box.
This supplies valid endpoint regularity in `app:ch_seed:prop:seed-phase-charts`.
For the full chart `Q` contains `(spectator,x,x')`; for the transverse chart it
contains `(spectator,t,z₁,y,y')`. -/
theorem BufferedPhaseInverse.contDiffAt_closed_epsilon_box
    {f : (ℝ × P) → E → E} {I : Set ℝ} {U Q : Set P}
    {K D₁ D V L : Set E} {δ c εstar : ℝ} {G : E ≃L[ℝ] E}
    (h : BufferedPhaseInverse f (I ×ˢ U) K D₁ D V L δ c G)
    (hI : IsOpen I) (hU : IsOpen U) (hV : IsOpen V)
    (hinterval : Icc 0 εstar ⊆ I) (hQ : Q ⊆ U)
    {ε : ℝ} (hε : ε ∈ Icc 0 εstar) {p : P} (hp : p ∈ Q)
    {v : E} (hv : v ∈ V) :
    ContDiffAt ℝ ∞ (Function.uncurry (phaseChartInverse f D₁)) ((ε, p), v) :=
  h.contDiffAt_on_box (hI.prod hU) hV (prod_mono hinterval hQ) ⟨hε, hp⟩ hv

omit [CompleteSpace P] [FiniteDimensional ℝ E] in
/-- The first epsilon derivative of the constructed inverse is itself jointly
smooth on the same fixed open boxes (`app:ch_seed:prop:seed-phase-charts`).
`I` may contain the closed interval `[0, epsilon_*]`; no division by epsilon
or one-sided extension is involved. Quantitative tame bounds are separate. -/
theorem BufferedPhaseInverse.contDiffOn_epsilon_deriv
    {f : (ℝ × P) → E → E} {I : Set ℝ} {U : Set P}
    {K D₁ D V L : Set E} {δ c : ℝ} {G : E ≃L[ℝ] E}
    (h : BufferedPhaseInverse f (I ×ˢ U) K D₁ D V L δ c G)
    (hI : IsOpen I) (hU : IsOpen U) (hV : IsOpen V) :
    ContDiffOn ℝ ∞ (fun q : (ℝ × P) × E ↦
      deriv (fun ε ↦ phaseChartInverse f D₁ (ε, q.1.2) q.2) q.1.1)
      ((I ×ˢ U) ×ˢ V) := by
  have hs : ContDiffOn ℝ ∞ (fun q : ℝ × (P × E) ↦
      phaseChartInverse f D₁ (q.1, q.2.1) q.2.2) (I ×ˢ U ×ˢ V) :=
    h.smooth.comp ((contDiffOn_fst.prodMk contDiffOn_snd.fst).prodMk
      contDiffOn_snd.snd) (fun _ hq ↦ ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩)
  have hd : ContDiffOn ℝ ∞ (fun q : ℝ × (P × E) ↦
      deriv (fun ε ↦ phaseChartInverse f D₁ (ε, q.2.1) q.2.2) q.1)
      (I ×ˢ U ×ˢ V) :=
    (contDiffOn_parameterFDeriv hI (hU.prod hV) hs).clm_apply contDiffOn_const
  exact hd.comp (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
    (fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A fixed compact subset contains every buffered inner image. This upgrades
fiberwise compactness to the common compact containment asserted in
`app:ch_seed:prop:seed-phase-charts`. -/
theorem exists_compact_buffer_core {V : Set E} (hV : IsCompact (closure V))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : Set E, IsCompact L ∧ L ⊆ V ∧
      ∀ A : Set E, cthickening δ A ⊆ V → A ⊆ L := by
  let L := closure V \ thickening δ Vᶜ
  refine ⟨L, hV.diff isOpen_thickening, ?_, ?_⟩
  · intro x hx
    by_contra hn
    exact hx.2 (self_subset_thickening hδ Vᶜ hn)
  · intro A hA x hx
    refine ⟨subset_closure (hA (self_subset_cthickening A hx)), ?_⟩
    intro hn
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hn
    exact hy (hA (mem_cthickening_of_dist_le y x δ A hx (by simpa [dist_comm] using hxy.le)))

/-- Construct the common smooth inverse from the literal two quarter gaps,
the value comparison on `K = closure D₀`, and joint forward smoothness.
The open set `U` contains all closed physical, spectator and epsilon boxes;
the open set `O` contains the entire convex data box `D`. This is the
conditional inverse-family part of `app:ch_seed:prop:seed-phase-charts`.
The constants, target, and compact image core depend only on frozen geometry.
No inverse map, inverse smoothness, or local equivalence is an input. -/
theorem exists_common_smooth_phase_inverses
    {K D₁ D : Set E} (hK : IsCompact K) (hD₁ : IsOpen D₁)
    (hK₁ : K ⊆ D₁) (h₁D : D₁ ⊆ D) (hD : Convex ℝ D)
    (G : E ≃L[ℝ] E) {f₀ : E → E}
    (hf₀ : ∀ x ∈ D, DifferentiableAt ℝ f₀ x)
    (hgap₀ : ∀ x ∈ D, ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ f₀ x) -
      ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ∃ c > 0, ∃ δ > 0, ∃ V L : Set E,
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ (f : P → E → E) (U : Set P) (O : Set E),
        IsOpen U → IsOpen O → D ⊆ O →
        ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ O) →
        (∀ p ∈ U, ∀ x ∈ D, ‖(G.symm : E →L[ℝ] E).comp
          (fderiv ℝ (f p) x - fderiv ℝ f₀ x)‖ ≤ 1 / 4) →
        (∀ p ∈ U, ∀ x ∈ K, ‖f p x - f₀ x‖ ≤ δ) →
        BufferedPhaseInverse f U K D₁ D V L δ c G := by
  obtain ⟨c, hc, δ, hδ, V, hV, hVc, hs⟩ :=
    common_buffered_domains_with_normalized_jacobian_bounds hK hD₁ hK₁ h₁D hD G hf₀ hgap₀
  obtain ⟨L, hLc, hLV, hL⟩ := exists_compact_buffer_core hVc hδ
  refine ⟨c, hc, δ, hδ, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro f U O hU hO hDO hf hgap hvalue
  have hdiff : ∀ p ∈ U, ∀ x ∈ D, DifferentiableAt ℝ (f p) x := by
    intro p hp x hx
    exact ((hf.contDiffAt ((hU.prod hO).mem_nhds ⟨hp, hDO hx⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hout p hp := hs (f p) (hdiff p hp) (hgap p hp) (hvalue p hp)
  have himage : ∀ p ∈ U, V ⊆ f p '' D₁ := by
    intro p hp v hv
    exact (hout p hp).2.2.2.2.1 (self_subset_cthickening (closure V) (subset_closure hv))
  refine ⟨?_, fun p hp ↦ (hout p hp).1, fun p hp ↦ (hout p hp).2.1,
    fun p hp ↦ hL _ (hout p hp).2.2.2.1,
    fun p hp ↦ (hout p hp).2.2.2.1, fun p hp ↦ (hout p hp).2.2.2.2.1,
    fun p hp v hv ↦ (phaseChartInverse_spec (himage p hp hv)).1,
    fun p hp v hv ↦ (phaseChartInverse_spec (himage p hp hv)).2,
    fun p hp u hu ↦ phaseChartInverse_apply ((hout p hp).1.mono h₁D) hu,
    fun p hp ↦ (hout p hp).2.2.2.2.2⟩
  exact contDiffOn_phaseChartInverse hU hD₁ hV
    (hf.mono (prod_mono Subset.rfl (h₁D.trans hDO)))
    (fun p hp ↦ (hout p hp).1.mono h₁D) himage
    (fun p hp u hu ↦ ((hout p hp).2.2.2.2.2 u (h₁D hu)).1)

end JanetCartan.FullPhaseCharts
