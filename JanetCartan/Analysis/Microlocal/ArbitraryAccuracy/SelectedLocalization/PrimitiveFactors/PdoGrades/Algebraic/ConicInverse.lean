module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.JointInverse

/-!
# Order minus one for the joint coefficient inverse

The covector dilation is inside the differentiated function. Thus the bounds
include normalized covariable derivatives, rather than just physical slices.
The compact carrier and its complement certificate are fixed before dilation.
Consumer: the inverse factor in the selected branch-three joint PDO grade,
`app:ch_regular:eq:high-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.Characteristic ActualCarriers
open RegularSector.Characteristic.AlgebraicSymbols
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.RootFamily
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

/-- The SAME conic inverse, before coefficient substitution, with its
degree-minus-one factor explicit (`app:ch_regular_base:eq:complement-inverse`). -/
def coefficientConicBminus (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ) (p : Coeff × E) : CMat :=
  (ℓ (spatialPart p.2))⁻¹ • coefficientBminus i r c H (p.1, normalizeCovector ℓ p.2)

/-- Exact identification with the selected inverse at the original field;
no independently constructed inverse is identified with it
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem conicBminus_fieldRoot_eq_coefficientConicBminus
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ) (Q : E → Coeff) (y ξ : E) :
    conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ =
      coefficientConicBminus ℓ i r c H (Q (physicalCoordinates i y), ξ) := rfl

private theorem spatialPart_smul (ρ : ℝ) (ξ : E) :
    spatialPart (ρ • ξ) = ρ • spatialPart ξ :=
  congrArg Prod.snd ((coordinateSplit 0).map_smul ρ ξ)

private theorem normalizeCovector_smul (ℓ : Euclidean d →L[ℝ] ℝ)
    {ρ : ℝ} (hρ : ρ ≠ 0) (ξ : E) :
    normalizeCovector ℓ (ρ • ξ) = normalizeCovector ℓ ξ := by
  simp only [normalizeCovector, spatialPart_smul, map_smul, smul_eq_mul,
    _root_.mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hρ, mul_one]

/-- Exact homogeneity of the literal conic coefficient inverse, including
off-root time frequencies (`app:ch_regular:eq:high-amplitude`). -/
theorem coefficientConicBminus_smul
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (A : Coeff) (ξ : E) :
    coefficientConicBminus ℓ i r c H (A, ρ • ξ) =
      ρ⁻¹ • coefficientConicBminus ℓ i r c H (A, ξ) := by
  simp only [coefficientConicBminus, spatialPart_smul, map_smul, smul_eq_mul,
    normalizeCovector_smul ℓ hρ, _root_.mul_inv_rev, smul_smul]
  rw [mul_comm]

/-- All mixed coefficient/covector derivatives retain order minus one under
normalization. This is an equality of derivative norms of the actual dilated
function, not an estimate of a frozen frequency slice
(`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_coefficientConicBminus_rescale
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (k : ℕ) (p : Coeff × E)
    (hs : ContDiffAt ℝ ∞ (coefficientConicBminus ℓ i r c H) p) :
    ‖iteratedFDeriv ℝ k (fun v : Coeff × E ↦
      coefficientConicBminus ℓ i r c H (v.1, ρ • v.2)) p‖ =
        ρ⁻¹ * ‖iteratedFDeriv ℝ k (coefficientConicBminus ℓ i r c H) p‖ := by
  have he : (fun v : Coeff × E ↦ coefficientConicBminus ℓ i r c H (v.1, ρ • v.2)) =
      ρ⁻¹ • coefficientConicBminus ℓ i r c H :=
    funext fun v ↦ coefficientConicBminus_smul ℓ i r c H hρ.ne' v.1 v.2
  rw [he, iteratedFDeriv_const_smul_apply (hs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]

/-- On a fixed compact set of coefficients and normalized directions, the
primitive root and actual complement-domain certificates give a joint profile
for every normalized dilation, with exact order minus one. The root germ is
supplied by the retained `RootBuffer`; complement membership is produced by
the retained spectral collar and its completion-domain certificate. No inverse
or joint-symbol estimate is a hypothesis. The constants precede the varying
field, scale, frequency and accuracy (`app:ch_regular:eq:high-amplitude`). -/
theorem exists_coefficientConicBminus_joint_bounds
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (H : Coeff × Euclidean d → ℝ)
    {S : Set (Coeff × E)} (hS : IsCompact S)
    (hpos : ∀ p ∈ S, ℓ (spatialPart p.2) ≠ 0)
    (hH : ∀ p ∈ S, ContDiffAt ℝ ∞ H
      (p.1, spatialPart (normalizeCovector ℓ p.2)))
    (hdomain : ∀ p ∈ S,
      ((coefficientRootPencil (coordinateSplit i) H
          (p.1, spatialPart (normalizeCovector ℓ p.2)),
        pencil p.1 ((coordinateSplit i).symm (1, 0))),
          normalizeCovector ℓ p.2 0 - H (p.1, spatialPart (normalizeCovector ℓ p.2))) ∈
        minorComplementDomain r c) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ p ∈ S, ContDiffAt ℝ ∞ (coefficientConicBminus ℓ i r c H) p) ∧
      ∀ (ρ : ℝ), 0 < ρ → ∀ k p, p ∈ S →
        ‖iteratedFDeriv ℝ k (fun v : Coeff × E ↦
          coefficientConicBminus ℓ i r c H (v.1, ρ • v.2)) p‖ ≤ ρ⁻¹ * C k := by
  have hs p (hp : p ∈ S) : ContDiffAt ℝ ∞ (coefficientConicBminus ℓ i r c H) p := by
    have hn := (contDiffAt_normalizeCovector ℓ (hpos p hp)).comp p contDiffAt_snd
    have hbase := contDiffAt_coefficientBminus i r c H
      (p := (p.1, normalizeCovector ℓ p.2)) (hH p hp) (hdomain p hp)
    have hb := hbase.comp p (contDiffAt_fst.prodMk hn)
    exact (((ℓ.contDiff.comp ((coordinateSplit 0).contDiff.comp contDiff_snd).snd).contDiffAt).inv
      (hpos p hp)).smul hb
  let C := fun k ↦ 1 + cNorm S k (coefficientConicBminus ℓ i r c H)
  have hC k : 0 < C k := by
    dsimp [C]
    linarith [cNorm_nonneg S k (coefficientConicBminus ℓ i r c H)]
  refine ⟨C, hC, hs, ?_⟩
  intro ρ hρ k p hp
  rw [norm_iteratedFDeriv_coefficientConicBminus_rescale ℓ i r c H hρ k p (hs p hp)]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hρ).le
  exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS
    (fun p hp ↦ (hs p hp).of_le (show (k : ℕ∞ω) ≤ ∞ by simp)) hp le_rfl).trans
      (le_add_of_nonneg_left zero_le_one)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
