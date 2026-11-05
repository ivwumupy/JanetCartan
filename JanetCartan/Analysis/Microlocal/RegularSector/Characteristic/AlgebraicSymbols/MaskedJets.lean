module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.SupportedSymbols
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.AlgebraicBudget

/-!
# Both physical masks and the exact PDO coordinate derivatives

This transfers physical seminorm estimates to the existing paired-position
PDO API. It retains the physical covector `2πξ` and every mask derivative.
Its physical input is produced for the literal algebraic symbol by
`exists_conicAlgebraicSymbol_weighted_cNorm_bounds`. The residual still needs
the corresponding physical-action estimate before this transfer is applied.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open PdoRealization NormalComparison AmplitudeBound FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ

private theorem norm_jet_smul_le_uniform
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    {f : F → ℂ} {g : F → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (z : F) {m k : ℕ} (hk : k ≤ m) {A B : ℝ} (hA : 0 ≤ A)
    (ha : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f z‖ ≤ A)
    (hb : ∀ j ≤ m, ‖iteratedFDeriv ℝ j g z‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f y • g y) z‖ ≤ 2 ^ m * A * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  apply (norm_iteratedFDeriv_smul_le hf hg z (n := k) (by simp)).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha j (hjk.trans hk)) (Nat.cast_nonneg _))
        (hb _ ((Nat.sub_le k j).trans hk)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = 2 ^ k * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk) hA) hB

private theorem norm_jet_comp_linear_le
    {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : F →L[ℝ] G) {f : G → H} (hf : ContDiff ℝ ∞ f)
    (z : F) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ L) z‖ ≤ ‖iteratedFDeriv ℝ k f (L z)‖ * ‖L‖ ^ k := by
  rw [L.iteratedFDeriv_comp_right hf z (by simp)]
  simpa using (iteratedFDeriv ℝ k f (L z)).norm_compContinuousLinearMap_le (fun _ ↦ L)

/-- Fixed smooth masks have one constant for the exact weighted coordinate
derivatives, without loss of physical derivative order. The input seminorm
is on the original physical ball containing the output mask. It is an
intermediate estimate, produced for the algebraic symbol by
`exists_conicAlgebraicSymbol_weighted_cNorm_bounds`; no PDO bound is assumed.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_maskedPhysicalPDOCycleSymbol_derivative_constant
    (x : E) (R : ℝ) (χout χsource : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (hcarrier : tsupport χout ⊆ closedBall x R) (m : ℕ) :
    ∃ C > 0, ∀ c : E → E → CMat,
      ContDiff ℝ ∞ (Function.uncurry c) → ∀ D : ℝ, 0 ≤ D →
      (∀ η, (1 + ‖η‖) * cNorm (closedBall x R) m (fun y ↦ c y η) ≤ D) →
      ∀ ξ is, is.length ≤ m → ∀ z,
        (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤ C * D := by
  obtain ⟨Ao, hAo, hjo⟩ := hco.exists_bound_iteratedFDeriv ho m
  obtain ⟨As, hAs, hjs⟩ := hcs.exists_bound_iteratedFDeriv hs m
  let L := normalLeftPosition (d + 1)
  let S := normalRightPosition (d + 1)
  let Lo := max 1 ‖L‖ ^ m
  let Ls := max 1 ‖S‖ ^ m
  have hLo : 0 < Lo := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  have hLs : 0 < Ls := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  have hpL k (hk : k ≤ m) : ‖L‖ ^ k ≤ Lo :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  have hpS k (hk : k ≤ m) : ‖S‖ ^ k ≤ Ls :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  let F : P → ℂ := fun z ↦ χout (L z) * χsource (S z)
  have hF : ContDiff ℝ ∞ F := (ho.comp L.contDiff).mul (hs.comp S.contDiff)
  let J := 2 ^ m * (Ao * Lo) * (As * Ls)
  have hJ : 0 ≤ J := mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hAo hLo.le))
    (mul_nonneg hAs hLs.le)
  have hjF z k (hk : k ≤ m) : ‖iteratedFDeriv ℝ k F z‖ ≤ J := by
    exact norm_jet_smul_le_uniform (ho.comp L.contDiff) (hs.comp S.contDiff) z hk
      (mul_nonneg hAo hLo.le)
      (fun j hj ↦ (norm_jet_comp_linear_le L ho z j).trans
        (mul_le_mul (hjo j hj _) (hpL j hj) (by positivity) hAo))
      (fun j hj ↦ (norm_jet_comp_linear_le S hs z j).trans
        (mul_le_mul (hjs j hj _) (hpS j hj) (by positivity) hAs))
  let C := 1 + 2 ^ m * J * Lo
  have hC : 0 < C := by
    have := mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ m) hJ) hLo.le
    dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro c hc D hD hbudget ξ is his z
  have hslice (η : E) : ContDiff ℝ ∞ (fun y ↦ c y η) :=
    hc.comp (contDiff_id.prodMk contDiff_const)
  have hpair : ContDiff ℝ ∞ (maskedPhysicalPDOCycleSymbol χout χsource c ξ) :=
    (contDiff_maskedPhysicalPDOCycleSymbol ho hs hc).comp (contDiff_const.prodMk contDiff_id)
  have he : maskedPhysicalPDOCycleSymbol χout χsource c ξ =
      fun z ↦ F z • c (L z) ((2 * Real.pi) • ξ) := rfl
  by_cases hz : L z ∈ tsupport χout
  · let η := (2 * Real.pi) • ξ
    have hjc k (hk : k ≤ m) :
        ‖iteratedFDeriv ℝ k ((fun y ↦ c y η) ∘ L) z‖ ≤
          cNorm (closedBall x R) m (fun y ↦ c y η) * Lo := by
      exact (norm_jet_comp_linear_le L (hslice η) z k).trans
        (mul_le_mul (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x R)
          (fun _ _ ↦ (hslice η).contDiffAt.of_le (by simp)) (hcarrier hz) hk)
          (hpL k hk) (by positivity) (cNorm_nonneg _ _ _))
    have hj := norm_jet_smul_le_uniform hF ((hslice η).comp L.contDiff) z his hJ
      (hjF z) hjc
    have hcoord := norm_matrixAmplitudeCoordinateDerivList_le_jet hpair is z
    rw [he] at hcoord
    have hfreq : 1 + ‖ξ‖ ≤ 1 + ‖η‖ := by
      dsimp [η]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith [Real.one_le_pi_div_two, norm_nonneg ξ]
    have hwt : (1 + ‖ξ‖) * cNorm (closedBall x R) m (fun y ↦ c y η) ≤ D :=
      (mul_le_mul_of_nonneg_right hfreq (cNorm_nonneg _ _ _)).trans (hbudget η)
    calc
      _ ≤ (1 + ‖ξ‖) * (2 ^ m * J *
          (cNorm (closedBall x R) m (fun y ↦ c y η) * Lo)) :=
        mul_le_mul_of_nonneg_left (hcoord.trans hj) (by positivity)
      _ = (2 ^ m * J * Lo) *
          ((1 + ‖ξ‖) * cNorm (closedBall x R) m (fun y ↦ c y η)) := by ring
      _ ≤ (2 ^ m * J * Lo) * D :=
        mul_le_mul_of_nonneg_left hwt (mul_nonneg (mul_nonneg (by positivity) hJ) hLo.le)
      _ ≤ C * D := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hD
  · have hz0 := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto L.continuous.continuousAt
    have he0 : maskedPhysicalPDOCycleSymbol χout χsource c ξ =ᶠ[𝓝 z] (fun _ ↦ 0) := by
      filter_upwards [hz0] with w hw
      change χout (L w) = 0 at hw
      rw [he]
      simp [F, hw]
    have hj0 := (he0.iteratedFDeriv (𝕜 := ℝ) is.length).eq_of_nhds
    have hcoord := norm_matrixAmplitudeCoordinateDerivList_le_jet hpair is z
    rw [hj0] at hcoord
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] at hcoord
    exact (mul_le_mul_of_nonneg_left hcoord (by positivity)).trans
      (by simpa using mul_nonneg hC.le hD)

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
