module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Geometry
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Amplitude

/-!
# Profiles of the original source times the complementary right symbol

The common proof-mask derivatives are fixed before the varying source and
slow scale. The Leibniz convolution below preserves the original amplitude
budget and its single fixed slow-scale loss. Its consumer is the initial
source Fourier estimate in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Retarded.KernelDecay
open JanetCartan.Localization

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
local notation "E" => Euclidean n

private theorem complex_source_slice_jet_le
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (k : ℕ) (y η : E) :
    ‖iteratedFDeriv ℝ k (fun z ↦ (m (z, η) : ℂ)) y‖ ≤
      ‖iteratedFDeriv ℝ k m (y, η)‖ := by
  have hs : ContDiff ℝ ∞ (fun z ↦ m (z, η)) :=
    hm.comp (contDiff_id.prodMk contDiff_const)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘ (fun z ↦ m (z, η))) y‖ ≤ _
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hs.contDiffAt (by simp)]
  exact (norm_iteratedFDeriv_symbol_slice_le
    (hm.comp (contDiff_snd.prodMk contDiff_fst)) k η y).trans_eq
      ((LinearIsometryEquiv.prodComm ℝ E E).norm_iteratedFDeriv_comp_right m (η, y) k)

/-- The actual complementary source amplitude is smooth on the original
phase domain (`app:ch_regular:eq:source-tail`). -/
theorem contDiffOn_complementarySourceAmplitude
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (a : E → F)
    {U : Set E} (ha : ContDiffOn ℝ ∞ a U) (η : E) :
    ContDiffOn ℝ ∞ (complementarySourceAmplitude m a η) U :=
  (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
    (hm.comp (contDiff_id.prodMk contDiff_const)))).contDiffOn.smul ha

/-- Primitive joint mask jets and original amplitude jets bound their
literal product. The offset `b` is unchanged for every integration order,
and constants depend only on the two fixed profiles
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:source-tail`). -/
theorem norm_iteratedFDeriv_complementarySourceAmplitude_le
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (a : E → F)
    {U : Set E} (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ U) (D C : ℕ → ℝ)
    (hD : ∀ k, 0 ≤ D k) (hmjet : ∀ k p, ‖iteratedFDeriv ℝ k m p‖ ≤ D k)
    {A L : ℝ} (hL : 1 ≤ L) (b : ℕ) (η y : E)
    (hajet : ∀ k, ‖iteratedFDeriv ℝ k a y‖ ≤ C k * ((A * L ^ b) * L ^ k))
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (complementarySourceAmplitude m a η) y‖ ≤
      derivativeConvolution (fun j ↦ 1 + D j) C k * ((A * L ^ b) * L ^ k) := by
  have hms : ContDiff ℝ ∞ (fun z ↦ (m (z, η) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hm.comp (contDiff_id.prodMk contDiff_const))
  have hslice j : ‖iteratedFDeriv ℝ j (fun z ↦ (m (z, η) : ℂ)) y‖ ≤
      1 * D j * L ^ (j + 0) := by
    simpa only [one_mul, add_zero] using
      ((complex_source_slice_jet_le m hm j y η).trans (hmjet j (y, η))).trans
        (le_mul_of_one_le_right (hD j) (one_le_pow₀ hL))
  have hcomplement j := norm_iteratedFDeriv_one_sub_le_grades hms le_rfl hL 0 y hslice j
  have haglobal := contDiff_of_contDiffOn_support_neighborhood hU ha hs
  have h := norm_iteratedFDeriv_smul_le_amplitude_grades
    (f := fun z ↦ 1 - (m (z, η) : ℂ)) (C := fun j ↦ 1 + D j)
    (B := C) (S := A * L ^ b) (L := L) (contDiff_const.sub hms) haglobal
    (fun j ↦ by linarith [hD j]) (zero_le_one.trans hL) 0 0 y
    (fun j ↦ by simpa only [one_mul] using hcomplement j)
    (fun j ↦ by simpa only [add_zero, mul_assoc, mul_left_comm, mul_comm] using hajet j) k
  change ‖iteratedFDeriv ℝ k (fun z ↦ (1 - (m (z, η) : ℂ)) • a z) y‖ ≤ _
  simpa only [add_zero, mul_assoc, mul_left_comm, mul_comm] using h

end JanetCartan.InitialSourceLocalization
