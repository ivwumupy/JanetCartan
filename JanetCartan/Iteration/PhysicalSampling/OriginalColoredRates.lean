module

public import JanetCartan.Iteration.PhysicalSampling.OriginalRates
public import JanetCartan.Iteration.PhysicalInitialization.OriginalColoredProtectionApplication

/-!
# Actual fine-ceiling rates of the one retained original colored packet

Instantiate the original fine-threshold producer with the literal task68
`Rcolor (i,color)` and its proved lower bound one. No radial labels, protection
directions, phases or samples are selected again. The coarse parameter reaches
the event threshold; the current physical coefficient scale fits both the
revised fine ceiling and the inverse of every actual rate. Consumers: the
original measured/scalar finite-family continuations on one actual history
(`app:ch_waves:thm:sampling`, `app:rem:exhaustive-signed-pairs`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalSampling.OriginalColoredRates
open PhysicalSeed PhysicalNormalInverse RawInputPartition

variable {m : ℕ} (hn : 5 ≤ m + 1) (pOrder : ℕ)
  (εframe : ℝ) (hεframe : 0 < εframe)
  (qext : BallExtension.Parameters (Euclidean (m + 1)))
  (hqcenter : qext.center = 0) (hqradius : qext.radius = OriginalBoundary.b hn)
  (k : (a : Fin (OriginalBoundary.D hn).chartCount) ×
    Fin ((OriginalBoundary.D hn).patchCount a) → Euclidean (m + 1))
  (hk : ∀ a, k a ≠ 0) (hkD : ∀ a, k a ∈ (OriginalBoundary.D hn).domain a.1)
  (p : BallExtension.Parameters (Euclidean (m + 1))) (orders : Finset ℕ)
  (margin extendedMargin : ℕ → ℝ)
  (hmargin : ∀ a ∈ orders, 0 < margin a)
  (hextendedMargin : ∀ a ∈ orders, 0 < extendedMargin a)
  (cap : ℝ) (hcap : 0 < cap) (incidenceCap : ℝ) (hincidenceCap : 0 < incidenceCap)
  (userExtra : StrongExtraCaps hn)

set_option quotPrecheck false in
local notation "actual(" f ")" =>
  f hn pOrder εframe hεframe qext hqcenter hqradius k hk hkD p orders margin extendedMargin
    hmargin hextendedMargin cap hcap incidenceCap hincidenceCap userExtra

/-- There is no radial lower-bound premise: these are exactly the retained
original colored rates, at every fine shell on every reached original history
(`app:ch_waves:thm:sampling`). -/
theorem exists_fine_threshold (eventThreshold : ℝ) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ Rinit ≥ S, ∀ stage : ℕ,
      let T := historyScale Rinit growthExponent stage
      let Λ := T ^ fineExponent
      let lam := T ^ carrierExponent
      let rate := fun (i : actual(OriginalWeights.Index)) (c : Fin 3 → Fin (pOrder + 1)) ↦
        (actual(PhysicalInitialization.OriginalColoredProtectionApplication.Rcolor) (i, c) * lam)⁻¹
      let L := currentCoefficientScale Rinit stage
      eventThreshold ≤ T ∧ 1 ≤ Λ ∧ 0 < lam ∧ 1 ≤ L ∧ L ≤ Λ ∧
        ∀ i c, 0 < rate i c ∧ rate i c ≤ 1 ∧ L ≤ (rate i c)⁻¹ ∧
          ∀ j : Fin (cutoffCount Λ), rate i c * (2 : ℝ) ^ j.val ≤ actual(OriginalMargins.ε) := by
  obtain ⟨S, hS, hstages⟩ := actual(OriginalRates.exists_fine_threshold)
    (show (0 : ℝ) < 1 from zero_lt_one) eventThreshold
  refine ⟨S, hS, ?_⟩
  intro Rinit hR stage T Λ lam rate L
  have hRone : 1 ≤ Rinit := (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR)
  obtain ⟨hevent, hfine, hlam, _hbuffer, hscale⟩ := hstages Rinit hR stage
  let R := fun (i : actual(OriginalWeights.Index)) (c : Fin 3 → Fin (pOrder + 1)) ↦
    actual(PhysicalInitialization.OriginalColoredProtectionApplication.Rcolor) (i, c)
  have hrad : ∀ i c, 1 ≤ R i c := fun i c ↦
    actual(PhysicalInitialization.OriginalColoredProtectionApplication.radial_ge_one) (i, c)
  have hL := OriginalRates.current_scale_bounds_for_radial_rate hRone (le_refl (1 : ℝ)) stage
  refine ⟨hevent, hfine, hlam, hL.1, hL.2.1, ?_⟩
  intro i c
  obtain ⟨hτ, hτone, hband⟩ := hscale R hrad i c
  exact ⟨hτ, hτone,
    (OriginalRates.current_scale_bounds_for_radial_rate hRone (hrad i c) stage).2.2, hband⟩

end JanetCartan.PhysicalSampling.OriginalColoredRates
