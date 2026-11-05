module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.LocalChart
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.PrimitiveInverse

/-!
# Compact coefficient and frequency buffers for the same algebraic root

The original joint root data construct the exact smoothness and primitive
bounds consumed by `AlgebraicSymbols.exists_conicAlgebraicSymbols_supported_budgets`.
The open margins lie inside the retained joint root buffer. Source:
`app:ch_regular_base:eq:complement-inverse` and `complement-symbol`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicChart
open ActualCarriers RootFamily FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

/-- Positive compact product buffers with open margins, joint root smoothness,
and the exact original-pencil bounds required by `AlgebraicSymbols`.
The input is the proved output of `exists_localChart_with_algebraic_data`;
no inverse or completion estimate is used (`complement-inverse`). -/
theorem exists_compact_root_buffers (c : LocalChart Ω x RQ A₀ ξ M)
    (hc : RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
      c.minorGap c.transportGap) :
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
      a < c.coefficientRadius ∧ b < min c.coefficientRadius c.rootRadius ∧
      let KA := closedBall A₀ a
      let Kη := closedBall (coordinateSplit c.index ξ).2 b
      IsCompact KA ∧ IsCompact Kη ∧
      KA ⊆ ball A₀ c.coefficientRadius ∧
      Kη ⊆ ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) ∧
      (∀ p ∈ ball A₀ c.coefficientRadius ×ˢ
          ball (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius),
        ContDiffAt ℝ ∞ c.root p) ∧
      ∃ bound > (0 : ℝ), ∀ p ∈ KA ×ˢ Kη,
        ‖coefficientRootPencil (coordinateSplit c.index) c.root p‖ ≤ bound ∧
        ‖pencil p.1 ((coordinateSplit c.index).symm (1, 0))‖ ≤ bound ∧
        (coefficientRootPencil (coordinateSplit c.index) c.root p).det = 0 ∧
        c.minorGap ≤ |(coefficientRootPencil (coordinateSplit c.index) c.root p).adjugate c.row c.col| ∧
        c.transportGap ≤ |minorTransportCoefficient
          (coefficientRootPencil (coordinateSplit c.index) c.root p)
          (pencil p.1 ((coordinateSplit c.index).symm (1, 0))) c.row c.col| := by
  let a := c.coefficientRadius / 2
  let b := min c.coefficientRadius c.rootRadius / 2
  have ha : 0 < a := half_pos c.coefficientRadius_pos
  have hb : 0 < b := half_pos (lt_min c.coefficientRadius_pos c.rootRadius_pos)
  have ha' : a < c.coefficientRadius := half_lt_self c.coefficientRadius_pos
  have hb' : b < min c.coefficientRadius c.rootRadius :=
    half_lt_self (lt_min c.coefficientRadius_pos c.rootRadius_pos)
  let K := closedBall A₀ a ×ˢ closedBall (coordinateSplit c.index ξ).2 b
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hsub : K ⊆ closedBall A₀ c.coefficientRadius ×ˢ
      closedBall (coordinateSplit c.index ξ).2 (min c.coefficientRadius c.rootRadius) :=
    prod_mono (closedBall_subset_closedBall ha'.le) (closedBall_subset_closedBall hb'.le)
  have hH : ContinuousOn c.root K := fun p hp ↦
    (hc.2 p (hsub hp)).1.continuousAt.continuousWithinAt
  have hP : ContinuousOn (coefficientRootPencil (coordinateSplit c.index) c.root) K :=
    contDiff_pencil.continuous.comp_continuousOn
      (continuousOn_fst.prodMk ((coordinateSplit c.index).symm.continuous.comp_continuousOn
        (hH.prodMk continuousOn_snd)))
  have hA : Continuous (fun p : Coeff × Euclidean d ↦
      pencil p.1 ((coordinateSplit c.index).symm (1, 0))) :=
    contDiff_pencil.continuous.comp (continuous_fst.prodMk continuous_const)
  obtain ⟨P, hPbound⟩ := (hK.image_of_continuousOn hP).isBounded.exists_norm_le
  obtain ⟨A, hAbound⟩ := (hK.image hA).isBounded.exists_norm_le
  refine ⟨a, ha, b, hb, ha', hb', isCompact_closedBall _ _, isCompact_closedBall _ _,
    closedBall_subset_ball ha', closedBall_subset_ball hb', ?_,
    1 + |P| + |A|, by positivity, ?_⟩
  · intro p hp
    exact (hc.2 p ⟨ball_subset_closedBall hp.1, ball_subset_closedBall hp.2⟩).1
  · intro p hp
    refine ⟨(hPbound _ (mem_image_of_mem _ hp)).trans ?_,
      (hAbound _ (mem_image_of_mem _ hp)).trans ?_, (hc.2 p (hsub hp)).2⟩
    · linarith [le_abs_self P, abs_nonneg A]
    · linarith [le_abs_self A, abs_nonneg P]

end JanetCartan.RegularSector.Characteristic.AlgebraicChart
