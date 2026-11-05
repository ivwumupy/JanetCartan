module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.SmoothSupport

/-!
# Fixed physical masks and the exact PDO position derivatives

Convert a local physical `cNorm` into the global paired-position derivative
budget of `PdoRealization.IntegerBounds`. The masks are fixed before the
symbol, and only their costs are absorbed. This is used for the source and
upper endpoint in `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral.SymbolBudgets NormalComparison AmplitudeBound PdoRealization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Complex scalar homogeneity of the local Frobenius budget. The scalar is
the fixed-frequency value of the original multiplier; no frequency factor
is differentiated in the PDO position budget (`energy-complete-residual`). -/
theorem cNorm_complex_smul_on_open {K U : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → Mat} (hf : ContDiffOn ℝ ∞ f U) (a : ℂ) (m : ℕ) :
    cNorm K m (fun x ↦ a • f x) = ‖a‖ * cNorm K m f := by
  unfold cNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have himage : (fun x ↦ ‖iteratedFDeriv ℝ j (fun y ↦ a • f y) x‖) '' K =
      (fun b : ℝ ↦ ‖a‖ • b) '' ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' K) := by
    rw [Set.image_image]
    apply Set.image_congr
    intro x hx
    simp only [iteratedFDeriv_const_smul_apply'
      ((hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp)), norm_smul, smul_eq_mul]
  rw [himage, Set.image_smul, Real.sSup_smul_of_nonneg (norm_nonneg a), smul_eq_mul]

private theorem contDiff_maskedMatrix {U : Set E} (hU : IsOpen U)
    {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    {f : E → Mat} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x ↦ χ x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hχU hx)))
  · apply (contDiffAt_const (c := (0 : Mat))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change χ y = 0 at hy
    simp only [hy, zero_smul]

private theorem maskedMatrix_jet_le {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχK : tsupport χ ⊆ K) {f : E → Mat} (hf : ContDiffOn ℝ ∞ f U)
    {m k : ℕ} (hk : k ≤ m) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y ↦ χ y • f y) x‖ ≤
      ((m + 1 : ℝ) * 2 ^ m * cNorm K m χ) * cNorm K m f := by
  by_cases hx : x ∈ K
  · have hg := contDiff_maskedMatrix hU hχ (hχK.trans hKU) hf
    exact (norm_iteratedFDeriv_le_cNorm hK (hg.of_le (by simp)) hx hk).trans
      (cNorm_smul_on_open_le hK hU hKU hχ.contDiffOn hf m)
  · have hz : iteratedFDeriv ℝ k (fun y ↦ χ y • f y) x = 0 := by
      by_contra hn
      exact hx (hχK (tsupport_smul_subset_left χ f
        (support_iteratedFDeriv_subset k hn)))
    rw [hz, norm_zero]
    have := cNorm_nonneg K m χ
    have := cNorm_nonneg K m f
    positivity

private theorem linear_pullback_jet_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : X →L[ℝ] Y) {f : Y → Z} (hf : ContDiff ℝ ∞ f)
    {m k : ℕ} {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ B)
    (hk : k ≤ m) (x : X) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (L y)) x‖ ≤ B * max 1 ‖L‖ ^ m := by
  have h := norm_iteratedFDeriv_preAffine_le (x := x) L 0 isOpen_univ hf.contDiffOn (mem_univ _) k
  simp only [add_zero] at h
  apply h.trans
  exact mul_le_mul (hb k hk _) ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k).trans
    (pow_le_pow_right₀ (le_max_left _ _) hk)) (by positivity) hB

/-- Fixed masks convert the original local matrix jets into the literal
paired-position PDO derivatives, at every order. The constant precedes the
varying symbol and its smoothness neighborhood. Consumer: indices one and
two of `CompleteResidual.directPDOSymbols` in `energy-complete-residual`. -/
theorem exists_masked_position_derivative_constant
    {K : Set E} (hK : IsCompact K) (χout χsource : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hso : tsupport χout ⊆ K) (hcs : HasCompactSupport χsource) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (U : Set E), IsOpen U → K ⊆ U →
      ∀ f : E → Mat, ContDiffOn ℝ ∞ f U →
      ∀ is : List (Fin (2 * (d + 1))), is.length ≤ m → ∀ z : P,
        ‖matrixAmplitudeCoordinateDerivList is
          (fun p ↦ (χout (splitPhysicalPositions p).1 * χsource (splitPhysicalPositions p).2) •
            f (splitPhysicalPositions p).1) z‖ ≤ D * cNorm K m f := by
  obtain ⟨S, hS, hbS⟩ := hcs.exists_bound_iteratedFDeriv hs m
  let L := normalLeftPosition (d + 1)
  let R := normalRightPosition (d + 1)
  let B := (m + 1 : ℝ) * 2 ^ m * cNorm K m χout
  let D := 2 ^ m * (S * max 1 ‖R‖ ^ m) * (B * max 1 ‖L‖ ^ m)
  have hB : 0 ≤ B := by
    have := cNorm_nonneg K m χout
    dsimp [B]
    positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + D, by linarith, ?_⟩
  intro U hU hKU f hf is hi z
  have hcf := cNorm_nonneg K m f
  let g : E → Mat := fun x ↦ χout x • f x
  have hg : ContDiff ℝ ∞ g := contDiff_maskedMatrix hU ho (hso.trans hKU) hf
  have hgb j (hj : j ≤ m) x : ‖iteratedFDeriv ℝ j g x‖ ≤ B * cNorm K m f :=
    maskedMatrix_jet_le hK hU hKU ho hso hf hj x
  have hr : ContDiff ℝ ∞ (fun p ↦ χsource (R p)) := hs.comp R.contDiff
  have hl : ContDiff ℝ ∞ (fun p ↦ g (L p)) := hg.comp L.contDiff
  have he : (fun p ↦ (χout (splitPhysicalPositions p).1 * χsource (splitPhysicalPositions p).2) •
      f (splitPhysicalPositions p).1) = (fun p ↦ χsource (R p) • g (L p)) := by
    funext p
    change (χout (L p) * χsource (R p)) • f (L p) = _
    simp only [g, smul_smul, mul_comm]
  rw [he]
  apply (norm_matrixAmplitudeCoordinateDerivList_le_jet (hr.smul hl) is z).trans
  have hj := norm_iteratedFDeriv_smul_le hr hl z (n := is.length) (by simp)
  apply hj.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (is.length + 1), (is.length.choose i : ℝ) *
        (S * max 1 ‖R‖ ^ m) * (B * cNorm K m f * max 1 ‖L‖ ^ m) := by
      apply Finset.sum_le_sum
      intro i hi'
      have hik : i ≤ is.length := Nat.le_of_lt_succ (Finset.mem_range.mp hi')
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (linear_pullback_jet_le R hs hS hbS (hik.trans hi) z) (Nat.cast_nonneg _))
        (linear_pullback_jet_le L hg (mul_nonneg hB (cNorm_nonneg _ _ _)) hgb
          ((Nat.sub_le _ _).trans hi) z) (norm_nonneg _) (by positivity)
    _ = 2 ^ is.length * (S * max 1 ‖R‖ ^ m) *
        (B * cNorm K m f * max 1 ‖L‖ ^ m) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast
    _ ≤ 2 ^ m * (S * max 1 ‖R‖ ^ m) * (B * cNorm K m f * max 1 ‖L‖ ^ m) := by
      gcongr
      norm_num
    _ = D * cNorm K m f := by dsimp [D]; ring
    _ ≤ (1 + D) * cNorm K m f := by nlinarith [cNorm_nonneg K m f]

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
