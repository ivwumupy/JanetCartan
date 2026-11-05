module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.Localizers
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.SummedSupport

/-!
# Fixed cutoff budgets and physical carriers for elapsed localization

The constructed smooth compact masks supply the exact input/output derivative
grades used by the primitive graph theorem, with zero fixed offset. A single
physical cutoff covers both literal orientations of the elapsed amplitude,
including the identity contribution to the complementary localizer.
All choices precede the scale, elapsed time and accuracy parameters.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.KernelLimits

variable {d : ℕ}

private theorem exists_compact_derivative_profile
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ H : ℕ → ℝ, (∀ k, 0 ≤ H k) ∧ ∀ k p, ‖iteratedFDeriv ℝ k f p‖ ≤ H k := by
  have hb k := (hc.iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous
    ((hf.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).continuous)
  choose H hH using hb
  exact ⟨fun k => max 0 (H k), fun k => le_max_left _ _,
    fun k p => (hH k p).trans (le_max_right _ _)⟩

/-- Construct the two precise mask profiles consumed by
`exists_graph_factor_sobolev_bound_of_primitive_grades`. The input symbol
retains its source base and is complexified isometrically; the output symbol
retains its physical position. The profiles are fixed before `L` and the
derivative order, and both mask offsets can be zero
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsed_localizer_grades
    {mi mo : LocalizerSymbol (d + 1)}
    {Ki Ii Ko Oo : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hi : IsBufferedLocalizer mi Ki Ii) (ho : IsBufferedLocalizer mo Ko Oo) :
    ∃ Di Do : ℕ → ℝ, (∀ k, 0 ≤ Di k) ∧ (∀ k, 0 ≤ Do k) ∧
      (∀ (L : ℝ), 1 ≤ L → ∀ y k (p : JointVariables (Euclidean (d + 1))),
        ‖iteratedFDeriv ℝ k (fun v : JointVariables (Euclidean (d + 1)) =>
          (mi (y, v.2.2.1) : ℂ)) p‖ ≤ Di k * L ^ k) ∧
      ∀ (L : ℝ), 1 ≤ L → ∀ x ζ k,
        ‖iteratedFDeriv ℝ k (fun v => mo (v, ζ)) x‖ ≤ Do k * L ^ k := by
  have hic : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ mi) :=
    Complex.ofRealCLM.contDiff.comp hi.smooth
  have his : HasCompactSupport (Complex.ofRealCLM ∘ mi) := hi.compactSupport.comp_left rfl
  obtain ⟨Di, hDi, hbi⟩ := exists_compact_derivative_profile hic his
  obtain ⟨Do, hDo, hbo⟩ := exists_compact_derivative_profile ho.smooth ho.compactSupport
  refine ⟨Di, Do, hDi, hDo, ?_, ?_⟩
  · intro L hL y k p
    let π : JointVariables (Euclidean (d + 1)) →L[ℝ]
        Euclidean (d + 1) × Euclidean (d + 1) :=
      (0 : JointVariables (Euclidean (d + 1)) →L[ℝ] Euclidean (d + 1)).prod
        ((ContinuousLinearMap.fst ℝ _ _).comp
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
    have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by
      intro v
      change ‖((0 : Euclidean (d + 1)), v.2.2.1)‖ ≤ 1 * ‖v‖
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), one_mul] using
        ((norm_fst_le v.2.2).trans (norm_snd_le v.2)).trans (norm_snd_le v))
    have hb := norm_iteratedFDeriv_preAffine_le π (y, 0) isOpen_univ
      hic.contDiffOn (mem_univ _) k (x := p)
    have hb' := hb.trans ((mul_le_mul_of_nonneg_right (hbi k _)
      (pow_nonneg (norm_nonneg _) _)).trans
      (mul_le_of_le_one_right (hDi k) (pow_le_one₀ (norm_nonneg _) hπ)))
    have hscale : Di k ≤ Di k * L ^ k :=
      le_mul_of_one_le_right (hDi k) (one_le_pow₀ hL)
    simpa only [π, ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk_add_mk, zero_add, add_zero,
      Function.comp_apply, Complex.ofRealCLM_apply] using hb'.trans hscale
  · intro L hL x ζ k
    let π := ContinuousLinearMap.inl ℝ (Euclidean (d + 1)) (Euclidean (d + 1))
    have hπ : ‖π‖ ≤ 1 := π.opNorm_le_bound zero_le_one (by
      intro v
      simp [π, Prod.norm_def])
    have hb := norm_iteratedFDeriv_preAffine_le π (0, ζ) isOpen_univ
      ho.smooth.contDiffOn (mem_univ _) k (x := x)
    have hb' := hb.trans ((mul_le_mul_of_nonneg_right (hbo k _)
      (pow_nonneg (norm_nonneg _) _)).trans
      (mul_le_of_le_one_right (hDo k) (pow_le_one₀ (norm_nonneg _) hπ)))
    have hscale : Do k ≤ Do k * L ^ k :=
      le_mul_of_one_le_right (hDo k) (one_le_pow₀ hL)
    simpa only [π, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
      using hb'.trans hscale

/-- Both physical masks give a compact two-position amplitude carrier,
uniformly in elapsed time and in the original symbol and multiplier. Neither
position is discarded in the reverse orientation
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem elapsedAmplitude_eq_zero_off_physical_carrier
    {q : ℕ} (b : TwoTimeAmplitude d q) (χout χsource β : Euclidean (d + 1) → ℂ)
    (r : ℝ) (u z ξ : Euclidean (d + 1))
    (hz : (u, z) ∉ tsupport χout ×ˢ tsupport χsource) :
    elapsedAmplitude b χout χsource β r u z ξ = 0 := by
  by_cases hu : u ∈ tsupport χout
  · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
      (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport (fun hs => hz ⟨hu, hs⟩))))
  · exact elapsedAmplitude_eq_zero_of_mask b χout χsource β r u z ξ
      (Or.inl (image_eq_zero_of_notMem_tsupport hu))

/-- Construct one physical output cutoff for both orientations and all
elapsed times. Its plateau includes the physical support of the original
amplitude and the left localizer, so the identity contribution of `1 - mo`
is retained. These are exactly `hKb`, `ht`, `hmt`, and `hplateau` of the
primitive graph Sobolev theorem (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsed_physical_output_cutoff
    {χout χsource : Euclidean (d + 1) → ℂ}
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource)
    {mo : LocalizerSymbol (d + 1)}
    {Ko Oo : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hmo : IsBufferedLocalizer mo Ko Oo) :
    IsCompact (tsupport χout ×ˢ tsupport χsource) ∧
    ∃ (t : Set (Euclidean (d + 1))) (ψ : Euclidean (d + 1) → ℝ),
      IsCompact t ∧ (∀ x ∉ t, ∀ ξ, mo (x, ξ) = 0) ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, ψ x ∈ Icc (0 : ℝ) 1) ∧
      ∀ backward x, x ∈ leakageOutputCarrier backward
        (tsupport χout ×ˢ tsupport χsource) t → ψ x = 1 := by
  let t := Prod.fst '' tsupport mo
  have ht : IsCompact t := hmo.compactSupport.image continuous_fst
  have hb := hout.prod hsource
  let R := leakageOutputCarrier false (tsupport χout ×ˢ tsupport χsource) t ∪
    leakageOutputCarrier true (tsupport χout ×ˢ tsupport χsource) t
  have hR : IsCompact R := (isCompact_leakageOutputCarrier false hb ht).union
    (isCompact_leakageOutputCarrier true hb ht)
  obtain ⟨ψ, hψ, hrange, hsψ, _, hplateau⟩ :=
    CompatibleResponse.exists_compact_family_cutoff hR isOpen_univ (subset_univ R)
  refine ⟨hb, t, ψ, ht, ?_, hψ, hsψ, hrange, ?_⟩
  · intro x hx ξ
    exact image_eq_zero_of_notMem_tsupport (fun hp => hx ⟨(x, ξ), hp, rfl⟩)
  · intro backward x hx
    apply interior_subset (hplateau ?_)
    cases backward
    · exact Or.inl hx
    · exact Or.inr hx

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
