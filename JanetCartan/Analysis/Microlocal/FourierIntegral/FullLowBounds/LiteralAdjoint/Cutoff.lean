module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Distributional

/-!
# A fixed frequency mask avoiding the origin

The regularizations used by the full low-bound construction can be made to
avoid zero as required by the reverse part of `SobolevBounds.IntegerBounds`.
Every amplitude supported in the fixed closed frequency carrier is preserved.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.FullLowBounds
open LowBounds.FrequencyCutoff
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- A fixed smooth mask is one on the closed frequency carrier and zero near
zero. Consumer: the cutoff sequence for `exists_adjoint_integer_sobolev_constant`,
from `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem exists_frequencyMask {F₀ : Set E} (hF₀ : IsClosed F₀) (hzero : (0 : E) ∉ F₀) :
    ∃ m : E → ℂ, ContDiff ℝ ∞ m ∧ (∀ η ∈ F₀, m η = 1) ∧
      (0 : E) ∉ tsupport m ∧ (∀ η, star (m η) = m η) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF₀.isOpen_compl 0 hzero
  let b : ContDiffBump (0 : E) := ⟨ε / 2, ε, by positivity, by linarith⟩
  let m : E → ℂ := fun η ↦ 1 - (b η : ℂ)
  refine ⟨m, contDiff_const.sub (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_, ?_, ?_⟩
  · intro η hη
    have hdist : ε ≤ dist η 0 := by
      by_contra h
      exact hball (by simpa only [Metric.mem_ball] using lt_of_not_ge h) hη
    simp [m, b.zero_of_le_dist hdist]
  · rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [b.eventuallyEq_one] with η hη
    simp [m, hη]
  · intro η
    simp [m]

/-- Multiplying the existing physical cutoff by the fixed mask supplies smooth
compact support excluding zero, while preserving every full amplitude supported
in `F₀`. The very same sequence works for all modified amplitudes in the reverse
integer Sobolev theorem (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem exists_compatiblePhysicalCutoff {F₀ : Set E}
    (hF₀ : IsClosed F₀) (hzero : (0 : E) ∉ F₀) :
    ∃ χ : ℕ → E → ℂ,
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧
      (∀ j, HasCompactSupport (χ j)) ∧
      (∀ j, (0 : E) ∉ tsupport (χ j)) ∧
      (∀ j η, star (χ j η) = χ j η) ∧
      (∀ (A : FullAmplitude n r), (∀ x y η, η ∉ F₀ → A x y η = 0) →
        ∀ j, frequencyCutFullAmplitude (χ j) A =
          frequencyCutFullAmplitude (complexPhysicalCutoff j) A) := by
  obtain ⟨m, hm, hmone, hmzero, hmstar⟩ := exists_frequencyMask hF₀ hzero
  refine ⟨fun j η ↦ complexPhysicalCutoff j η * m η,
    fun j ↦ (complexPhysicalCutoff_contDiff j).mul hm,
    fun j ↦ (complexPhysicalCutoff_hasCompactSupport j).mul_right, ?_, ?_, ?_⟩
  · intro j
    rw [notMem_tsupport_iff_eventuallyEq] at hmzero ⊢
    filter_upwards [hmzero] with η hη
    simp [hη]
  · intro j η
    simp [hmstar, complexPhysicalCutoff]
  · intro A hA j
    funext x y η
    by_cases hη : η ∈ F₀
    · simp [frequencyCutFullAmplitude, hmone η hη]
    · simp [frequencyCutFullAmplitude, hA x y η hη]

end JanetCartan.FourierIntegral.FullLowBounds
