module

public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.ParameterFamily

/-!
# Smooth extensions used only for local transport

Auxiliary compact localizations for the derivative identity in
`app:ch_osc:prop:osc-normal`. The given data are never required to be smooth
or supported outside their original parameter and spatial domains.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison

/-- Localize a smooth function near a compact subset of its open domain.
Used for the phase and velocity in `app:ch_osc:prop:osc-normal`. -/
theorem exists_contDiff_localization
    {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {U S : Set P} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    {f : P → Q} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ f' : P → Q, ContDiff ℝ ∞ f' ∧ HasCompactSupport f' ∧
      tsupport f' ⊆ U ∧ (∀ p, f p = 0 → f' p = 0) ∧
      ∀ p ∈ S, f' =ᶠ[𝓝 p] f := by
  obtain ⟨V, hV, hSV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hS hU hSU
  obtain ⟨W, hW, hVW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨θ, hθ, _, hsθ, heθ⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  have ht : tsupport θ ⊆ U := by simpa only [tsupport, hsθ] using hWU
  refine ⟨fun p ↦ θ p • f p, ?_, ?_, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ tsupport θ
    · exact hθ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (ht hp)))
    · apply (contDiffAt_const (c := (0 : Q))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
      simp [hq]
  · apply HasCompactSupport.of_support_subset_isCompact hWc
    intro p hp
    apply subset_closure
    rw [← hsθ]
    by_contra hn
    exact hp (by simp [Function.notMem_support.mp hn])
  · exact (tsupport_smul_subset_left θ f).trans ht
  · intro p hp
    simp [hp]
  · intro p hp
    filter_upwards [hV.mem_nhds (hSV hp)] with q hq
    rw [(heθ q).mp (subset_closure hq), one_smul]
end JanetCartan.NormalComparison
