module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.AlgebraicExtension
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.PairedCoordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Diagonal

/-!
# Smoothness and fixed support of the literal source and endpoint PDOs

The symbols in `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`, retain both physical
masks and the conversion `ξ_phys = 2π ξ`. Local smoothness of the original
physical coefficient suffices: the output mask supplies a zero germ outside
its chart. No replacement coefficient or replacement amplitude is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets PdoRealization
open NormalComparison AmplitudeBound
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Smooth physical masks turn local joint smoothness of the SAME symbol into
global joint smoothness in the exact cycle coordinates. Consumer: the source
and endpoint `GraphNormalAmplitudeBounds` in `energy-complete-residual`. -/
theorem contDiff_maskedPhysicalPDOCycleSymbol
    {U : Set E} (hU : IsOpen U) (χout χsource : E → ℂ)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hsupp : tsupport χout ⊆ U) (c : E → E → Mat)
    (hc : ContDiffOn ℝ ∞ (Function.uncurry c) (U ×ˢ univ)) :
    ContDiff ℝ ∞ (Function.uncurry (maskedPhysicalPDOCycleSymbol χout χsource c)) := by
  let l : E × P → E := fun p ↦ normalLeftPosition (d + 1) p.2
  let r : E × P → E := fun p ↦ normalRightPosition (d + 1) p.2
  let ν : E × P → E := fun p ↦ (2 * Real.pi) • p.1
  have hl : ContDiff ℝ ∞ l := (normalLeftPosition (d + 1)).contDiff.comp contDiff_snd
  have hr : ContDiff ℝ ∞ r := (normalRightPosition (d + 1)).contDiff.comp contDiff_snd
  have hν : ContDiff ℝ ∞ ν := contDiff_fst.const_smul _
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : l p ∈ tsupport χout
  · exact ((ho.comp hl).contDiffAt.mul (hs.comp hr).contDiffAt).smul
      ((hc.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hsupp hp, mem_univ _⟩)).comp p
        (hl.prodMk hν).contDiffAt)
  · apply (contDiffAt_const (c := (0 : Mat))).congr_of_eventuallyEq
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto hl.continuous.continuousAt
    filter_upwards [hz] with z hz
    change χout (l z) = 0 at hz
    change (χout (l z) * χsource (r z)) • c (l z) (ν z) = 0
    rw [hz, zero_mul, zero_smul]

/-- The source PDO has global joint smoothness for the literal normalized
source datum from `ResidualCoordinates.conicSourceSymbol`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_sourcePDOCycleSymbol
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (β χout χsource : E → ℂ) (hβ : ContDiff ℝ ∞ β)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource) :
    ContDiff ℝ ∞ (Function.uncurry (maskedPhysicalPDOCycleSymbol χout χsource
      (fun x ξ ↦ (ResidualCoordinates.conicSourceSymbol ℓ ρ σ x (spatialPart ξ) * β ξ) •
        (1 : Mat)))) := by
  apply contDiff_maskedPhysicalPDOCycleSymbol isOpen_univ χout χsource ho hs (subset_univ _) _
  have hσ' := ResidualCoordinates.contDiff_conicSourceSymbol ℓ ρ hρ hsρ σ hσ
  exact (((hσ'.comp (contDiff_fst.prodMk (spatialProjection.contDiff.comp contDiff_snd))).mul
    (hβ.comp contDiff_snd)).smul contDiff_const).contDiffOn

/-- The literal upper-endpoint symbol is globally jointly smooth after the
physical masks. The original coefficient is only required to be smooth on
the output-mask chart; BOTH time slots of `W₁` are pulled back to `x 0`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_endpointPDOCycleSymbol
    {U : Set E} (hU : IsOpen U) (A : E → Fin (d + 1) → Mat)
    (hA : ContDiffOn ℝ ∞ (fun x ↦ A x 0) U)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    (β χout χsource : E → ℂ) (hβ : ContDiff ℝ ∞ β)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hsupp : tsupport χout ⊆ U) :
    ContDiff ℝ ∞ (Function.uncurry (maskedPhysicalPDOCycleSymbol χout χsource
      (fun x ξ ↦ β ξ • (A x 0 * W (x 0) (x 0) (spatialPart x) (spatialPart ξ))))) := by
  apply contDiff_maskedPhysicalPDOCycleSymbol hU χout χsource ho hs hsupp _
  have hw : ContDiff ℝ ∞ (fun p : E × E ↦
      W (p.1 0) (p.1 0) (spatialPart p.1) (spatialPart p.2)) :=
    hW.comp (((diagonalLinear.contDiff.comp contDiff_fst).fst).prodMk
      (spatialProjection.contDiff.comp contDiff_snd))
  exact (hβ.comp contDiff_snd).contDiffOn.smul
    ((hA.comp contDiffOn_fst (fun _ hp ↦ hp.1)).mul hw.contDiffOn)

/-- Both original masks provide ONE frequency-independent paired-position
support box for every literal PDO symbol. Consumer: the source and endpoint
normal-amplitude bounds in `energy-complete-residual`. -/
theorem maskedPhysicalPDOCycleSymbol_supportedInCenteredBox
    (χout χsource : E → ℂ) (c : E → E → Mat) {R : ℝ}
    (ho : ∀ x ∈ tsupport χout, ‖x‖ ≤ R)
    (hs : ∀ x ∈ tsupport χsource, ‖x‖ ≤ R) (ξ : E) (i j : Fin q) :
    SupportedInCenteredBox R (fun z ↦ maskedPhysicalPDOCycleSymbol χout χsource c ξ z i j) := by
  apply pairedNormalAmplitude_supportedInCenteredBox
    (S := tsupport χout ∪ tsupport χsource)
    (f := fun p : E × E × E ↦ (χout p.1 * χsource p.2.1) • c p.1 p.2.2)
    (fun x hx ↦ hx.elim (ho x) (hs x))
  intro p hp
  have hout : χout p.1 ≠ 0 := by
    intro hz
    apply hp
    simp only [hz, zero_mul, zero_smul]
  have hsource : χsource p.2.1 ≠ 0 := by
    intro hz
    apply hp
    simp only [hz, mul_zero, zero_smul]
  exact ⟨Or.inl (subset_tsupport χout hout), Or.inr (subset_tsupport χsource hsource)⟩

/-- Compact physical masks choose a single positive support box BEFORE any
varying symbol or frequency. Thus the support premises of the source and
endpoint estimates are produced by the fixed masks themselves.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_maskedPhysicalPDOCycleSymbol_support_box
    (χout χsource : E → ℂ) (ho : HasCompactSupport χout) (hs : HasCompactSupport χsource) :
    ∃ R > (0 : ℝ), (∀ x ∈ tsupport χout, ‖x‖ ≤ R) ∧
      (∀ x ∈ tsupport χsource, ‖x‖ ≤ R) ∧
      ∀ c : E → E → Mat, ∀ ξ i j,
        SupportedInCenteredBox R (fun z ↦ maskedPhysicalPDOCycleSymbol χout χsource c ξ z i j) := by
  obtain ⟨R, hR, hbound⟩ := (ho.union hs).isBounded.exists_pos_norm_le
  have hout x (hx : x ∈ tsupport χout) : ‖x‖ ≤ R := hbound x (Or.inl hx)
  have hsource x (hx : x ∈ tsupport χsource) : ‖x‖ ≤ R := hbound x (Or.inr hx)
  exact ⟨R, hR, hout, hsource, fun c ↦
    maskedPhysicalPDOCycleSymbol_supportedInCenteredBox χout χsource c hout hsource⟩

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
