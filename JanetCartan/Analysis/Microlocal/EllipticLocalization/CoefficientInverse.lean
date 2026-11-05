module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.Symbol
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.FirstJetProfile

/-!
# The full pencil inverse before coefficient substitution

These are the coefficient functions of the actual global elliptic symbols,
including the complete physical action on the first jet. They supply the
mixed position/covector grades in `app:ch_regular:eq:high-amplitude`; no
characteristic chart or complement inverse is substituted for the full pencil.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open ActualCarriers FiniteMasks.ActualFamily EllipticComplement
open Characteristic.AlgebraicSymbols CharacteristicTransport.CompleteResidual FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "Jet" => Coeff × ((E →L[ℝ] Coeff) × Mat)

/-- The literal full pencil inverse in coefficient/covector variables,
before the original angular and radial masks (`sec:energy-construction`). -/
def coefficientEllipticInverse (p : Coeff × E) : CMat :=
  ((pencil p.1 p.2)⁻¹).map Complex.ofReal

/-- The complete physical action as a function of the original first
coefficient jet and full `B` (`app:ch_regular_base:eq:energy-complete-residual`). -/
def coefficientEllipticPhysicalAction (v : Jet × E) : CMat :=
  (∑ a, (pencil v.1.1 (EuclideanSpace.single a 1)).map Complex.ofReal *
    fderiv ℝ coefficientEllipticInverse (v.1.1, v.2)
      (v.1.2.1 (EuclideanSpace.single a 1), 0)) +
    v.1.2.2.map Complex.ofReal * coefficientEllipticInverse (v.1.1, v.2)

/-- The actual inverse is jointly smooth wherever the full determinant is
nonzero (`app:ch_regular:eq:high-amplitude`). -/
theorem contDiffAt_coefficientEllipticInverse {p : Coeff × E}
    (hp : determinant p.1 p.2 ≠ 0) : ContDiffAt ℝ ∞ coefficientEllipticInverse p :=
  contDiff_matrix_map_ofReal.contDiffAt.comp p
    ((contDiffAt_matrix_inv ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hp))).comp p contDiff_pencil.contDiffAt)

/-- Smoothness of the whole physical action follows from the full inverse,
including coefficient directions and the potential (`energy-complete-residual`). -/
theorem contDiffAt_coefficientEllipticPhysicalAction {v : Jet × E}
    (hv : determinant v.1.1 v.2 ≠ 0) : ContDiffAt ℝ ∞ coefficientEllipticPhysicalAction v := by
  have hG := contDiffAt_coefficientEllipticInverse (p := (v.1.1, v.2)) hv
  have hπ : ContDiffAt ℝ ∞ (fun v : Jet × E ↦ (v.1.1, v.2)) v :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have hg := hG.comp v hπ
  have hd := (hG.fderiv_right (m := ∞) (by simp)).comp v hπ
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro a _
    exact (contDiff_matrix_map_ofReal.contDiffAt.comp v
      (contDiff_pencil.contDiffAt.comp v (contDiffAt_fst.fst.prodMk contDiffAt_const))).mul
      (hd.clm_apply ((contDiffAt_fst.snd.fst.clm_apply contDiffAt_const).prodMk contDiffAt_const))
  · exact (contDiff_matrix_map_ofReal.contDiffAt.comp v contDiffAt_fst.snd.snd).mul hg

/-- Positive covector dilation of the literal full inverse has exact degree
minus one, including at singular pencils where the nonsingular inverse is
zero (`app:ch_regular_base:sec:energy-construction`). -/
theorem coefficientEllipticInverse_smul (A : Coeff) (ξ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    coefficientEllipticInverse (A, ρ • ξ) = ρ⁻¹ • coefficientEllipticInverse (A, ξ) := by
  have he : (pencil A (ρ • ξ))⁻¹ = ρ⁻¹ • (pencil A ξ)⁻¹ := by
    rw [show pencil A (ρ • ξ) = ρ • pencil A ξ from (pencilContinuousLinearMap A).map_smul _ _]
    by_cases hu : IsUnit (pencil A ξ).det
    · let := invertibleOfNonzero hρ.ne'
      rw [Matrix.inv_smul _ _ hu, invOf_eq_inv]
    · have hz := not_ne_iff.mp (fun h ↦ hu (isUnit_iff_ne_zero.mpr h))
      have hn : ¬IsUnit (ρ • pencil A ξ).det := by simp [hz]
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hn, Matrix.nonsing_inv_apply_not_isUnit _ hu, smul_zero]
  simp only [coefficientEllipticInverse, he,
    Matrix.map_smul Complex.ofReal ρ⁻¹ (fun a ↦ by simp [Complex.real_smul])]

variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The whole normalized inverse on the original input plateau, with its
exact radial/angular multiplier and degree-minus-one factor. This identity
also holds in the low collar (`app:ch_regular:eq:high-amplitude`). -/
theorem ellipticInverseSymbol_normalized_eq (threshold : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (Q : E → Coeff) (y ξ : E) (hy : f.inputMask y = 1) :
    ellipticInverseSymbol f hK threshold Q y (ρ • ξ) =
      ρ⁻¹ • ((ellipticSourceMask f hK threshold (ρ • ξ) : ℂ) •
        coefficientEllipticInverse (Q y, ξ)) := by
  change (f.inputMask y : ℂ) • (ellipticSourceMask f hK threshold (ρ • ξ) : ℂ) •
    coefficientEllipticInverse (Q y, ρ • ξ) = _
  rw [hy, Complex.ofReal_one, one_smul, coefficientEllipticInverse_smul _ _ hρ, smul_comm]

/-- The complete residual on the original input plateau is the same
multiplier times the physical action of the full inverse, with degree minus
one exposed before joint differentiation (`energy-complete-residual`). -/
theorem ellipticResidualSymbol_normalized_eq (threshold : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (Q : E → Coeff) (B : E → Mat) (y ξ : E)
    (hy : y ∈ interior {y | f.inputMask y = 1})
    (hQ : DifferentiableAt ℝ Q y)
    (hG : DifferentiableAt ℝ coefficientEllipticInverse (Q y, ξ)) :
    ellipticResidualSymbol f hK threshold Q B y (ρ • ξ) =
      ρ⁻¹ • ((ellipticSourceMask f hK threshold (ρ • ξ) : ℂ) •
        coefficientEllipticPhysicalAction ((Q y, (fderiv ℝ Q y, B y)), ξ)) := by
  let β : ℂ := (ellipticSourceMask f hK threshold (ρ • ξ) : ℂ)
  have hin := hQ.hasFDerivAt.prodMk (hasFDerivAt_const ξ y)
  have hd := hG.hasFDerivAt.comp y hin
  have he : (fun z ↦ ellipticInverseSymbol f hK threshold Q z (ρ • ξ)) =ᶠ[𝓝 y]
      fun z ↦ ρ⁻¹ • (β • coefficientEllipticInverse (Q z, ξ)) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact ellipticInverseSymbol_normalized_eq f hK threshold hρ Q z ξ
      (interior_subset (s := {y | f.inputMask y = 1}) hz)
  have hder : HasFDerivAt (fun z ↦ ρ⁻¹ • (β • coefficientEllipticInverse (Q z, ξ)))
      (ρ⁻¹ • (β • ((fderiv ℝ coefficientEllipticInverse (Q y, ξ)).comp
        ((fderiv ℝ Q y).prod 0)))) y :=
    (hd.const_smul β).const_smul ρ⁻¹
  have heder := (hder.congr_of_eventuallyEq he).fderiv
  simp only [ellipticResidualSymbol, physicalSymbolApply, partialDeriv, heder,
    he.eq_of_nhds, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, _root_.zero_apply, Matrix.mul_smul,
    coefficientEllipticPhysicalAction, smul_add, Finset.smul_sum, β]

/-- Joint germ identity for the inverse and its full residual at the same
output point. Smoothness comes from the original field and full determinant
gap, with no symbol-grade input (`app:ch_regular:eq:high-amplitude`). -/
theorem ellipticSymbols_normalized_eventuallyEq (threshold : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (Q : E → Coeff) (B : E → Mat) (v : E × E)
    (hv : v.1 ∈ interior {y | f.inputMask y = 1})
    (hQ : ContDiffAt ℝ ∞ Q v.1)
    (hG : ContDiffAt ℝ ∞ coefficientEllipticInverse (Q v.1, v.2)) (residual : Bool) :
    (fun w : E × E ↦ (if residual then ellipticResidualSymbol f hK threshold Q B
      else ellipticInverseSymbol f hK threshold Q) w.1 (ρ • w.2)) =ᶠ[𝓝 v]
      fun w ↦ ρ⁻¹ • ((ellipticSourceMask f hK threshold (ρ • w.2) : ℂ) •
        (if residual then coefficientEllipticPhysicalAction
          ((Q w.1, (fderiv ℝ Q w.1, B w.1)), w.2)
        else coefficientEllipticInverse (Q w.1, w.2))) := by
  have hF : ContinuousAt (fun w : E × E ↦ (Q w.1, w.2)) v :=
    (hQ.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [continuous_fst.continuousAt.eventually (isOpen_interior.mem_nhds hv),
    continuous_fst.continuousAt.eventually ((hQ.of_le (m := (1 : ℕ∞ω)) (by simp)).eventually (by simp)),
    hF.eventually ((hG.of_le (m := (1 : ℕ∞ω)) (by simp)).eventually (by simp))] with w hw hqw hgw
  cases residual
  · exact ellipticInverseSymbol_normalized_eq f hK threshold hρ Q w.1 w.2
      (interior_subset (s := {y | f.inputMask y = 1}) hw)
  · exact ellipticResidualSymbol_normalized_eq f hK threshold hρ Q B w.1 w.2 hw
      hqw.differentiableAt_one hgw.differentiableAt_one

end JanetCartan.RegularSector.EllipticLocalization
