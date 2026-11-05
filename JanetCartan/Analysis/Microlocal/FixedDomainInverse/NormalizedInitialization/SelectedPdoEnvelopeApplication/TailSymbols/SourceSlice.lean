module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.CoordinateJets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Regularizations
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Coordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback

/-!
# Recover the actual masked symbol from its retained cycle certificate

Fix a source position where the original input mask is one. Undo only the
physical frequency conversion `ξphys=2πξ`. The resulting slice is exactly the
output-masked symbol, and the affine physical map has a fixed derivative cost.
Consumer: the full-frequency complementary PDO estimate in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
open ArbitraryAccuracy.SelectedLocalization FourierIntegral Pseudodifferential AmplitudeBound
open RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "P" => Euclidean (2*(d+1))
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Fixed dimensional constants convert the retained complete cycle-symbol
certificate into global physical jets of the SAME output-masked symbol.
Joint smoothness follows from the actual normal certificate. The frequency
parameter remains arbitrary; no annular restriction is introduced
(`app:ch_regular_base:eq:actual-normal-amplitude`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_cycle_source_slice_constants :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (χout χsource : E → ℂ) (z₀ : E), χsource z₀ = 1 →
      ∀ (σ : E → E → Mat) (R N : ℝ),
        GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource σ) R N →
      ∀ (D : ℕ → ℝ), (∀ j, 0 ≤ D j) →
        (∀ j ξ is, is.length ≤ j → ∀ z,
          ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol χout χsource σ ξ) z‖ ≤ D j) →
        ContDiff ℝ ∞ (Function.uncurry (fun y ξ ↦ χout y • σ y ξ)) ∧
        ∀ j ξ y, ‖iteratedFDeriv ℝ j (fun z ↦ χout z • σ z ξ) y‖ ≤ C j * D j := by
  let Pleft : E →L[ℝ] P := (pairedPositionCLM (d := d+1)).comp
    (ContinuousLinearMap.inl ℝ E E)
  let C := fun j ↦ (2*(d+1) : ℝ)^j * ‖Pleft‖^j
  refine ⟨C, fun j ↦ mul_nonneg (pow_nonneg (by positivity) j)
    (pow_nonneg (norm_nonneg _) j), ?_⟩
  intro χout χsource z₀ hz σ R N hnormal D hD hcoords
  let A : FullAmplitude (d+1) q := fun y z ξ ↦ (χout y * χsource z) • σ y ξ
  have hA := contDiff_fullAmplitude_of_cycleSymbol A hnormal
  have hsmooth : ContDiff ℝ ∞ (Function.uncurry (fun y ξ ↦ χout y • σ y ξ)) := by
    have hh := hA.comp ((contDiff_fst.prodMk (contDiff_const (c := z₀))).prodMk contDiff_snd)
    change ContDiff ℝ ∞ (fun v : E × E ↦ χout v.1 • σ v.1 v.2)
    simpa only [A, Function.comp_def, hz, mul_one] using hh
  refine ⟨hsmooth, ?_⟩
  intro j ξ y
  let ξcycle := (2*Real.pi)⁻¹ • ξ
  let b := maskedPhysicalPDOCycleSymbol χout χsource σ ξcycle
  have hb : ContDiff ℝ ∞ b := hnormal.smooth.comp
    ((contDiff_const (c := ξcycle)).prodMk contDiff_id)
  have hpair (z : E) : Pleft z + pairedPosition 0 z₀ = pairedPosition z z₀ := by
    have hm := (pairedPositionCLM (d := d+1)).map_add (z, 0) (0, z₀)
    change pairedPosition (z+0) (0+z₀) = pairedPosition z 0 + pairedPosition 0 z₀ at hm
    change pairedPosition z 0 + pairedPosition 0 z₀ = pairedPosition z z₀
    simpa only [add_zero, zero_add] using hm.symm
  have he : (fun z ↦ χout z • σ z ξ) = fun z ↦ b (Pleft z + pairedPosition 0 z₀) := by
    funext z
    rw [hpair]
    simp only [b, ξcycle, maskedPhysicalPDOCycleSymbol_pairedPosition,
      smul_inv_smul₀ (by positivity : (2*Real.pi : ℝ) ≠ 0), hz, mul_one]
  rw [he]
  apply (norm_iteratedFDeriv_preAffine_le Pleft (pairedPosition 0 z₀)
    isOpen_univ hb.contDiffOn (mem_univ _) j).trans
  have hjet := norm_iteratedFDeriv_le_coordinate_certificate hb j (hD j)
    (fun is his z ↦ hcoords j ξcycle is his.le z) (Pleft y + pairedPosition 0 z₀)
  exact (mul_le_mul_of_nonneg_right hjet (pow_nonneg (norm_nonneg _) j)).trans_eq
    (by dsimp [C]; push_cast; ring)

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication.TailSymbols
