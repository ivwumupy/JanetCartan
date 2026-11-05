module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Phase

/-!
# One joint smooth localization of the exact trade directions

The localizer is chosen once on `(physical position, carrier, displacement)`;
it is not chosen separately at every input frequency. The original coefficient
and every ambient derivative are preserved near the same compact support.
This is the regularity interface of
`PhysicalMean.sampledAdjointMomentExpansion_realizes` and
`PhysicalMean.sampledAdjointMomentTemplate_physical_jet_le`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.PhysicalAdjointGeometry

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {m : ℕ}

/-- A single global smooth family realizes the actual local inverse-transpose
and exact phase identity on the prescribed original compact set. Its primitive
unit input is proved for the current Hamilton phase in `ActualGeometry`; no
separately chosen frequency extension occurs
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem exists_joint_trade_extension
    (W : Euclidean m →L[ℝ] X) {Y : Point X m → Euclidean m}
    {V K : Set (Point X m)} (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hY : ContDiffOn ℝ ∞ Y V) (hu : ∀ q ∈ V, IsUnit (mixedTranspose W Y q)) :
    ∃ Y' : Point X m → Euclidean m, ∃ L : Point X m → Euclidean m →L[ℝ] X,
      ContDiff ℝ ∞ Y' ∧ ContDiff ℝ ∞ L ∧
      (∀ q ∈ K, Y' =ᶠ[𝓝 q] Y) ∧
      (∀ q ∈ K, L =ᶠ[𝓝 q] tradeDirection W Y) ∧
      ∀ q ∈ K, ∀ h η : Euclidean m,
        fderiv ℝ (fun x ↦ inner ℝ (Y' (x, q.2)) η) q.1 (L q h) = inner ℝ h η := by
  have hC := contDiffOn_mixedTranspose hV hY W
  have hi : ContDiffOn ℝ ∞ (fun q ↦ Ring.inverse (mixedTranspose W Y q)) V :=
    contDiffOn_ringInverse_units.comp hC hu
  obtain ⟨Y', hY', _, _, _, heY⟩ := NormalComparison.exists_contDiff_localization hV hK hKV hY
  obtain ⟨J, hJ, _, _, _, heJ⟩ := NormalComparison.exists_contDiff_localization hV hK hKV hi
  let L : Point X m → Euclidean m →L[ℝ] X := fun q ↦ W.comp (J q)
  have hL : ContDiff ℝ ∞ L := contDiff_const.clm_comp hJ
  have heL : ∀ q ∈ K, L =ᶠ[𝓝 q] tradeDirection W Y := by
    intro q hq
    filter_upwards [heJ q hq] with p hp
    simp only [L, tradeDirection, hp]
  refine ⟨Y', L, hY', hL, heY, heL, ?_⟩
  intro q hq h η
  have hCeq : mixedTranspose W Y' q = mixedTranspose W Y q := by
    unfold mixedTranspose
    rw [(heY q hq).fderiv_eq]
  have hu' : IsUnit (mixedTranspose W Y' q) := hCeq ▸ hu q (hKV hq)
  have hLeq : L q = tradeDirection W Y' q := by
    rw [(heL q hq).eq_of_nhds]
    simp only [tradeDirection, hCeq]
  rw [hLeq]
  exact fderiv_phase_tradeDirection W (hY'.differentiable (by simp) q) hu' h η

omit [FiniteDimensional ℝ X] in
/-- Substitution of the same sample carrier and literal displacement produces
one globally smooth joint frequency/physical family. This is stronger than
separate pointwise smooth extensions and supplies the measurable-family
premise of the mean14 fixed-template expansion
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem contDiff_sampled_trade_family
    {L : Point X m → Euclidean m →L[ℝ] X} (hL : ContDiff ℝ ∞ L)
    (ζ : Euclidean m) (τ : ℝ) :
    ContDiff ℝ ∞ (fun q : Euclidean m × X ↦ L (q.2, ζ, τ • q.1)) := by
  apply hL.comp
  fun_prop

end JanetCartan.PhysicalAdjointGeometry
