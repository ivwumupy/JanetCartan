module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.AngularMask
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.SupportedSymbols

/-!
# The supported global pencil inverse

The physical input cutoff also supplies an extension in the left variable:
it is identically one on a neighborhood of the entire output support. No
coefficient outside the original physical neighborhood needs to be smooth.
The symbol differentiated in the residual includes this extension, with the
original zeroth order coefficient. Source: `app:ch_regular_base:sec:energy-construction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open ActualCarriers FiniteMasks.ActualFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
local notation "H" => SpacetimeL2 d (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- Exact radial determinant gap everywhere on the closed complementary
source support, even off the protected compact (`sec:energy-construction`). -/
theorem determinant_gap_on_ellipticSourceMask {L : ℝ} (hL : 0 < L)
    {A : Coeff} (hA : A ∈ closedBall A₀ f.coefficientRadius) {ξ : E}
    (hξ : ξ ∈ tsupport (ellipticSourceMask f hK L)) :
    f.determinantGap / 2 * ‖ξ‖ ^ (d + 1) < |determinant A ξ| := by
  obtain ⟨hr, hdir⟩ := ellipticSourceMask_support f hK hL hξ
  have hg := (ellipticAngularMask_spec f hK).2.2.2.2 A hA _ hdir
  have hp : 0 < ‖ξ‖ := (mul_pos zero_lt_two hL).trans_le hr
  have he : determinant A ξ = ‖ξ‖ ^ (d+1) * determinant A (NormedSpace.normalize ξ) := by
    conv_lhs => rw [← NormedSpace.norm_smul_normalize ξ]
    exact determinant_smul _ _ _
  rw [he, abs_mul, abs_of_nonneg (pow_nonneg hp.le _), mul_comm (f.determinantGap / 2)]
  exact mul_lt_mul_of_pos_left hg (pow_pos hp _)

/-- The actual inverse matrix times the collared elliptic source. Its
extension in the physical variable uses a mask already on a proved plateau
at the output (`app:ch_regular_base:sec:energy-construction`). -/
def ellipticInverseSymbol (L : ℝ) (Q : E → Coeff) (y ξ : E) : CMat :=
  (f.inputMask y : ℂ) • (ellipticSourceMask f hK L ξ : ℂ) • ((pencil (Q y) ξ)⁻¹).map Complex.ofReal

/-- The full differentiated symbol, before the common scalar `1/i`.
No derivative of the supported symbol or potential term has been removed
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def ellipticResidualSymbol (L : ℝ) (Q : E → Coeff) (B : E → Mat) : E → E → CMat :=
  physicalSymbolApply (fun y a ↦ (pencil (Q y) (EuclideanSpace.single a 1)).map Complex.ofReal)
    (fun y ↦ (B y).map Complex.ofReal) (ellipticInverseSymbol f hK L Q)

/-- The source matrix is scalar in the original row and column indices
(`app:ch_regular_base:sec:energy-construction`). -/
def ellipticSourceSymbol (L : ℝ) (_y ξ : E) : CMat :=
  (ellipticSourceMask f hK L ξ : ℂ) • (1 : CMat)

/-- On the whole doubled physical ball the auxiliary extension factor is one
as a germ. In particular it does not alter the parametrix or its physical
derivatives at any output point (`sec:energy-construction`). -/
theorem ellipticInverseSymbol_eq_near (L : ℝ) (Q : E → Coeff)
    {y : E} (hy : y ∈ closedBall x (2 * f.physicalRadius)) (ξ : E) :
    (fun z ↦ ellipticInverseSymbol f hK L Q z ξ) =ᶠ[𝓝 y]
      (fun z ↦ (ellipticSourceMask f hK L ξ : ℂ) • ((pencil (Q z) ξ)⁻¹).map Complex.ofReal) := by
  filter_upwards [isOpen_interior.mem_nhds (f.inputMask_plateau hy)] with z hz
  have he : f.inputMask z = 1 := interior_subset (s := {z | f.inputMask z = 1}) hz
  simp only [ellipticInverseSymbol, he, Complex.ofReal_one, one_smul]

/-- The added source is exactly the principal action of the actual inverse,
including at zero and both radial shoulders. It uses no characteristic
projection or pairing normalization (`sector-theorem-identity`). -/
theorem principalMatrix_mul_ellipticInverseSymbol {L : ℝ} (hL : 0 < L)
    (Q : E → Coeff) (hQ : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    {y : E} (hy : y ∈ closedBall x (2 * f.physicalRadius)) (ξ : E) :
    (∑ a, (ξ a : ℂ) • (pencil (Q y) (EuclideanSpace.single a 1)).map Complex.ofReal) *
      ellipticInverseSymbol f hK L Q y ξ = ellipticSourceSymbol f hK L y ξ := by
  have hid : (∑ a, (ξ a : ℂ) • (pencil (Q y) (EuclideanSpace.single a 1)).map Complex.ofReal)
      = (pencil (Q y) ξ).map Complex.ofReal := by
    simpa [coefficient, physicalCoordinates] using principalMatrix_eq 0 Q y ξ
  rw [hid, (ellipticInverseSymbol_eq_near f hK L Q hy ξ).eq_of_nhds, ellipticSourceSymbol,
    Matrix.mul_smul]
  by_cases hz : ellipticSourceMask f hK L ξ = 0
  · simp only [hz, Complex.ofReal_zero, zero_smul]
  have hyΩ := f.physicalBall_subset (closedBall_subset_closedBall
    (by linarith [f.physicalRadius_pos] : 2*f.physicalRadius ≤ 4*f.physicalRadius) hy)
  have hg := determinant_gap_on_ellipticSourceMask f hK hL (hQ hyΩ) (subset_tsupport _ hz)
  have hu : IsUnit (pencil (Q y) ξ).det := isUnit_iff_ne_zero.mpr (abs_pos.mp
    ((mul_nonneg (half_pos f.determinantGap_pos).le (pow_nonneg (norm_nonneg _) _)).trans_lt hg))
  have he := congrArg Complex.ofRealHom.mapMatrix ((pencil (Q y) ξ).mul_nonsing_inv hu)
  exact congrArg ((ellipticSourceMask f hK L ξ : ℂ) • ·) (by
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply,
      show (⇑Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal from funext Complex.ofRealHom_eq_coe] using he)

/-- Global joint smoothness of the actual complementary inverse, obtained
from ellipticity only where the two masks can be active. This is the symbol
needed by the canonical PDO calculus (`sec:energy-construction`). -/
theorem contDiff_ellipticInverseSymbol (hΩ : IsOpen Ω) {L : ℝ} (hL : 0 < L)
    (Q : E → Coeff) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius)) :
    ContDiff ℝ ∞ (Function.uncurry (ellipticInverseSymbol f hK L Q)) := by
  apply contDiff_iff_contDiffAt.mpr
  rintro p
  by_cases hy : p.1 ∈ tsupport f.inputMask
  · by_cases hξ : p.2 ∈ tsupport (ellipticSourceMask f hK L)
    · have hyΩ := f.physicalBall_subset (ball_subset_closedBall ((ball_subset_ball
        (by linarith [f.physicalRadius_pos] : 3*f.physicalRadius ≤ 4*f.physicalRadius))
          (f.inputMask_support hy)))
      have hg := determinant_gap_on_ellipticSourceMask f hK hL (hmap hyΩ) hξ
      have hn : (pencil (Q p.1) p.2).det ≠ 0 := abs_pos.mp
        ((mul_nonneg (half_pos f.determinantGap_pos).le (pow_nonneg (norm_nonneg _) _)).trans_lt hg)
      have hh := contDiff_pencil.contDiffAt.comp p
        (((hQ.contDiffAt (hΩ.mem_nhds hyΩ)).comp p contDiffAt_fst).prodMk contDiffAt_snd)
      have hinv := (contDiffAt_matrix_inv (N := ∞) ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr hn))).comp p hh
      exact ((Complex.ofRealCLM.contDiff.comp (f.inputMask_smooth.comp contDiff_fst)).contDiffAt).smul
        (((Complex.ofRealCLM.contDiff.comp ((ellipticSourceMask_properties f hK L).1.comp
          contDiff_snd)).contDiffAt).smul (contDiff_matrix_map_ofReal.contDiffAt.comp p hinv))
    · apply (contDiffAt_const (c := (0 : CMat))).congr_of_eventuallyEq
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hξ).comp_tendsto
        (continuous_snd.continuousAt (x := p))] with z hz
      change ellipticSourceMask f hK L z.2 = 0 at hz
      change ellipticInverseSymbol f hK L Q z.1 z.2 = 0
      simp only [ellipticInverseSymbol, hz, Complex.ofReal_zero, zero_smul, smul_zero]
  · apply (contDiffAt_const (c := (0 : CMat))).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto
      (continuous_fst.continuousAt (x := p))] with z hz
    change f.inputMask z.1 = 0 at hz
    change ellipticInverseSymbol f hK L Q z.1 z.2 = 0
    simp only [ellipticInverseSymbol, hz, Complex.ofReal_zero, zero_smul]

/-- Global joint smoothness of the differentiated complementary inverse,
including the zeroth order coefficient (`energy-complete-residual`). -/
theorem contDiff_ellipticResidualSymbol (hΩ : IsOpen Ω) {L : ℝ} (hL : 0 < L)
    (Q : E → Coeff) (B : E → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius)) :
    ContDiff ℝ ∞ (Function.uncurry (ellipticResidualSymbol f hK L Q B)) := by
  apply contDiff_physicalSymbolApply_on_carrier (isClosed_tsupport f.inputMask) hΩ
    ((f.inputMask_support.trans (ball_subset_ball (by linarith [f.physicalRadius_pos] :
      3*f.physicalRadius ≤ 4*f.physicalRadius))).trans (ball_subset_closedBall.trans
        f.physicalBall_subset))
  · exact contDiffOn_pi.mpr fun _ ↦ contDiff_matrix_map_ofReal.comp_contDiffOn
      (contDiff_pencil.comp_contDiffOn (hQ.prodMk contDiffOn_const))
  · exact contDiff_matrix_map_ofReal.comp_contDiffOn hB
  · exact contDiff_ellipticInverseSymbol f hK hΩ hL Q hQ hmap
  · intro y hy ξ
    simp only [ellipticInverseSymbol, image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero,
      zero_smul]

/-- The three original-coordinate elliptic PDOs: the solver, its principal
source and its differentiated remainder use both original physical masks,
the same collared symbol, and no real pairing (`sec:energy-construction`). -/
def ellipticSolver (L : ℝ) (Q : E → Coeff) : H →L[ℂ] H :=
  (1 / Complex.I) • maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ))
    (fun z ↦ (f.inputMask z : ℂ)) (ellipticInverseSymbol f hK L Q)

/-- The principal elliptic source, with the original input and output masks
(`app:ch_regular_base:sec:energy-construction`). -/
def ellipticSourcePDO (L : ℝ) : H →L[ℂ] H :=
  maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ))
    (ellipticSourceSymbol f hK L)

/-- The full order-minus-one elliptic residual measured where the outer
cutoff is one (`app:ch_regular_base:sec:energy-construction`). -/
def ellipticResidual (L : ℝ) (Q : E → Coeff) (B : E → Mat) : H →L[ℂ] H :=
  (1 / Complex.I) • maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ))
    (fun z ↦ (f.inputMask z : ℂ)) (ellipticResidualSymbol f hK L Q B)

end JanetCartan.RegularSector.EllipticComplement
