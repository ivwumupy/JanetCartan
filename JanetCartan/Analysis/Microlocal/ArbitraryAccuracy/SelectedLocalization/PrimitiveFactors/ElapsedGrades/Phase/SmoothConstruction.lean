module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Profiles
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.ContinuousExtension

/-!
# A smooth auxiliary for the actual selected conic phase

The local phase is compactly localized before radial extension. A fixed
small-frequency cutoff removes the singularity at zero. Joint germs, including
after positive frequency normalization, agree with the original phase above
the cutoff. Consumer: `CompleteFactor.hphaseGerm` and its auxiliary smoothness
input (`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ}

/-- Construct a globally smooth two-time phase from the actual local chart.
The compact buffer and local smoothness come from
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`; the fixed
positive lower frequency bound is geometric. The auxiliary is not asserted
to be homogeneous at zero. Its normalized joint germs are the original conic
phase on every retained carrier above `δ`, uniformly for `ρ ≥ 1`
(`app:ch_regular:eq:high-phase`). -/
theorem exists_smooth_truncated_conicPhase
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {J : Set (TwoTimePoint (Euclidean d))} (hJ : IsCompact J) (hJC : J ⊆ C.target)
    (hC : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ψ : TwoTimePhase d,
      ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ) ∧
      (∀ w : SymbolBudgets.TwoTimePoint d,
        budgetCoordinates w ∈ domain ℓ J → δ < ‖w.2‖ →
        SymbolBudgets.jointPhase Ψ =ᶠ[𝓝 w]
          SymbolBudgets.jointPhase (curriedExtend ℓ (twoTimePhase C))) ∧
      ∀ ρ : ℝ, 1 ≤ ρ → ∀ w : SymbolBudgets.TwoTimePoint d,
        budgetCoordinates w ∈ domain ℓ J → δ < ‖w.2‖ →
        SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) =ᶠ[𝓝 w]
          SymbolBudgets.jointPhase (curriedExtend ℓ (twoTimePhase C)) := by
  obtain ⟨F, hF, hcF, _, _, heF⟩ :=
    NormalComparison.exists_contDiff_localization C.open_target hJ hJC hC
  let χ : ContDiffBump (0 : Euclidean d) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let G : TwoTimePoint (Euclidean d) → ℝ :=
    fun q ↦ (1 - χ q.2.2.2) * extend ℓ F q
  have hG : ContDiff ℝ ∞ G := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q.2.2.2 = 0
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hn : ∀ᶠ v : TwoTimePoint (Euclidean d) in 𝓝 q, ‖v.2.2.2‖ < δ / 2 :=
        (isOpen_lt continuous_snd.snd.snd.norm continuous_const).mem_nhds
          (by simpa [hq] using half_pos hδ)
      filter_upwards [hn] with v hv
      have hvχ : χ v.2.2.2 = 1 := χ.one_of_mem_closedBall (by
        simpa only [mem_closedBall, dist_zero_right] using hv.le)
      simp [G, hvχ]
    · exact (contDiffAt_const.sub (χ.contDiff.contDiffAt.comp q contDiffAt_snd.snd.snd)).mul
        (contDiffAt_extend_of_hasCompactSupport ℓ hF hcF hq)
  let Ψ : TwoTimePhase d := fun t s y η ↦ G (t, (s, (y, η)))
  have he : ∀ w : SymbolBudgets.TwoTimePoint d,
      budgetCoordinates w ∈ domain ℓ J → δ < ‖w.2‖ →
      SymbolBudgets.jointPhase Ψ =ᶠ[𝓝 w]
        SymbolBudgets.jointPhase (curriedExtend ℓ (twoTimePhase C)) := by
    intro w hw hδw
    have hf := (extend_eventuallyEq_phase ℓ C hw.1.ne' (heF _ hw.2)).comp_tendsto
      (budgetCoordinates.continuous.tendsto w)
    have hn : ∀ᶠ v : SymbolBudgets.TwoTimePoint d in 𝓝 w, δ < ‖v.2‖ :=
      (isOpen_lt continuous_const continuous_snd.norm).mem_nhds hδw
    filter_upwards [hf, hn] with v hv hnv
    have hvχ : χ v.2 = 0 := χ.zero_of_le_dist (by
      simpa only [dist_zero_right] using hnv.le)
    change (1 - χ v.2) * extend ℓ F (budgetCoordinates v) = _
    rw [hvχ, sub_zero, one_mul]
    exact hv
  refine ⟨Ψ, hG.comp budgetCoordinates.contDiff, he, ?_⟩
  intro ρ hρ w hw hδw
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hscaled : budgetCoordinates (w.1, ρ • w.2) ∈ domain ℓ J :=
    mem_domain_smul ℓ hw hρpos
  have hn : δ < ‖ρ • w.2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos]
    exact hδw.trans_le (le_mul_of_one_le_left (norm_nonneg _) hρ)
  have ht : Continuous (fun v : SymbolBudgets.TwoTimePoint d ↦ (v.1, ρ • v.2)) :=
    continuous_fst.prodMk (continuous_snd.const_smul ρ)
  have hh := (he _ hscaled hn).comp_tendsto (ht.tendsto w)
  have heq := normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) hρpos
  filter_upwards [hh] with v hv
  calc
    SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) v =
        SymbolBudgets.jointPhase (SymbolBudgets.normalizedTwoTimePhase ρ
          (curriedExtend ℓ (twoTimePhase C))) v := congrArg (fun a ↦ ρ⁻¹ * a) hv
    _ = _ := by rw [heq]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
