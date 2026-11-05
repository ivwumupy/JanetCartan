module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FiniteProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Accuracy
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.SobolevScale
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction

/-!
# Initial-source accuracy with a finite derivative reserve

The original scale gap absorbs the losses in the PROVED bounded-operator
estimate. Constants precede the varying phase, amplitude, source frequency,
localizer and physical restriction domain. This supplies the initial source
input of `finiteChain_observation_rapidDecayAt`, separately from residual-word
leakage and terminal protection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization Pseudodifferential LocalSobolev
open ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic.RetardedLocalization

variable {d r : ℕ}
local notation "n" => (d + 1 : ℕ)
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Arbitrary prescribed accuracy for the ACTUAL initial identity-minus-right
localizer in the existing restriction Sobolev scale. The integration order
and constant precede every varying source and proof mask. The sole geometric
premise is the original source graph plateau; no tail is assumed
(`app:ch_regular:eq:source-tail`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_initialSource_restriction_accuracy_constant_finite
    (K : Set E) (hK : IsCompact K) (δ G : ℝ) (hδ : 0 < δ)
    (P D C : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hD : ∀ j, 0 ≤ D j)
    (hC : ∀ j, 0 ≤ C j) (b s : ℕ) {σ : ℝ} (hσ : 0 < σ) (Q : ℝ) :
    ∃ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀
    (m : LocalizerSymbol n) (_hm : ContDiff ℝ ∞ m) (_hmc : HasCompactSupport m)
    (φ : E → ℝ) (a : E → V)
    {U : Set E} (_hU : IsOpen U) (_hKU : K ⊆ U)
    (_hφ : ContDiffOn ℝ ∞ φ U) (_ha : ContDiffOn ℝ ∞ a U) (_hs : tsupport a ⊆ K)
    {S : Set (E × E)} {A L ρ : ℝ} (_hA : 0 ≤ A)
    (_hL : 1 ≤ L) (_hρ : 1 ≤ ρ) (_hscale : L ≤ ρ ^ (1 - σ))
    (_hgraph : ∀ y ∈ tsupport a, (y, gradient φ y) ∈ S)
    (_hplateau : cthickening δ S ⊆ interior {p | m p = 1})
    (_hupper : ∀ y ∈ U, ‖fderiv ℝ φ y‖ ≤ G)
    (_hmjet : ∀ j, j ≤ q → ∀ p, ‖iteratedFDeriv ℝ j m p‖ ≤ D j)
    (_hp : ∀ y ∈ tsupport a, ∀ j, 1 ≤ j → j ≤ q →
      ‖iteratedFDeriv ℝ (j + 1) φ y‖ ≤ P j * L ^ j)
    (_hajet : ∀ y ∈ tsupport a, ∀ j, j ≤ q →
      ‖iteratedFDeriv ℝ j a y‖ ≤ C j * ((A * L ^ b) * L ^ j))
    (M : H →L[ℂ] H)
    (_hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (u : H) (_hu : u =ᵐ[volume] fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y)
    (W : Set E) (hW : MeasurableSet W),
    restrictL2 W (u - M u) ∈ (restrictionSobolevScale W V hW).level s ∧
      (restrictionSobolevScale W V hW).gradeNorm s (restrictL2 W (u - M u)) ≤
        B * A * ρ ^ (-Q) := by
  let c : ℝ := (s : ℝ) + (n : ℝ) / 2
  obtain ⟨k, _, hk⟩ := exists_finite_neumann_order hσ c Q b
  let q := k + (s + n + 1)
  have hq : (s : ℝ) + (n : ℝ) / 2 < q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) d]
  have horder : c + (b : ℝ) - σ * q ≤ -Q := by
    have hkq : (k : ℝ) ≤ q := by exact_mod_cast (Nat.le_add_right k (s+n+1))
    nlinarith [mul_le_mul_of_nonneg_left hkq hσ.le]
  obtain ⟨J, hJ, hcompare⟩ := exists_restrictionScale_fourier_comparison n r s
  let B := (r : ℝ) * sourceLocalizationKernelConstant K δ G P D C q *
    Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * (s : ℝ))))
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (sourceLocalizationKernelConstant_nonneg K δ G P D C hD hC q)) (Real.sqrt_nonneg _)
  refine ⟨q, J * B, mul_nonneg hJ.le hB, ?_⟩
  intro m hm hmc φ a U hU hKU hφ ha hs S A L ρ hA hL hρ hscale
    hgraph hplateau hupper hmjet hp hajet M hM u hu W hW
  obtain ⟨hmem, hbound⟩ := bounded_initialSource_defect_sobolev_bound_finite
    m hm hmc φ a hU hK hKU hφ ha hs hδ hA hL hρ b hgraph hplateau hupper
    P D C hP hD hC q hmjet hp hajet M hM u hu (Nat.cast_nonneg s) hq
  obtain ⟨hv, hnorm⟩ := hcompare W hW (u - M u) (restrictL2 W (u - M u)) hmem
    (restrictL2_coeFn W (u - M u)).symm
  refine ⟨hv, hnorm.trans ?_⟩
  have hdecay : ρ ^ c * L ^ b * (L / ρ) ^ q ≤ ρ ^ (-Q) :=
    (finite_neumann_scale_bound hρ (zero_le_one.trans hL) hσ.le hscale b q).trans
      (Real.rpow_le_rpow_of_exponent_le hρ horder)
  calc
    J * vectorFourierSobolevNorm (s : ℝ) (u - M u) ≤
        J * (B * (A * L ^ b) * (ρ ^ c * (L / ρ) ^ q)) :=
      mul_le_mul_of_nonneg_left hbound hJ.le
    _ = (J * B) * A * (ρ ^ c * L ^ b * (L / ρ) ^ q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (mul_nonneg (mul_nonneg hJ.le hB) hA)


end JanetCartan.InitialSourceLocalization
