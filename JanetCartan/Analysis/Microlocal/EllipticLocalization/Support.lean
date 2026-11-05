module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.Symbol
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal

/-!
# Literal carriers of the global elliptic factors

The inverse, full differentiated residual and source keep the original physical
masks and the same closed frequency support. These are the carrier inputs to
the diagonal localization estimate in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement
open ArbitraryAccuracy.ResidualLocalization CharacteristicTransport.CompleteResidual
open FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The original physical supports are fixed and compact before coefficients,
frequency and accuracy are varied (`app:ch_regular:lem:finite-chain`). -/
theorem elliptic_physical_carrier :
    IsCompact (tsupport (fun y ↦ (f.outputMask y : ℂ)) ×ˢ
      tsupport (fun y ↦ (f.inputMask y : ℂ))) ∧
    tsupport (fun y ↦ (f.outputMask y : ℂ)) ⊆ closedBall x (2*f.physicalRadius) ∧
    tsupport (fun y ↦ (f.inputMask y : ℂ)) ⊆ closedBall x (3*f.physicalRadius) := by
  exact ⟨(f.outputMask_compact.comp_left Complex.ofReal_zero).prod
    (f.inputMask_compact.comp_left Complex.ofReal_zero),
    (tsupport_comp_subset Complex.ofReal_zero f.outputMask).trans
      (f.outputMask_support.trans ball_subset_closedBall),
    (tsupport_comp_subset Complex.ofReal_zero f.inputMask).trans
      (f.inputMask_support.trans ball_subset_closedBall)⟩

/-- Every zero of the actual source multiplier is a zero of all three
symbols, including the differentiated physical extension and full `B` term.
Consumer: zero germs in the comparable grade (`energy-complete-residual`). -/
theorem ellipticSymbols_zero_of_sourceMask_zero (threshold : ℝ)
    (Q : E → Coeff) (B : E → Mat) {ξ : E}
    (hz : ellipticSourceMask f hK threshold ξ = 0) :
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)), ∀ y, s y ξ = 0 := by
  have hi : (fun y ↦ ellipticInverseSymbol f hK threshold Q y ξ) = 0 := by
    funext y
    simp only [ellipticInverseSymbol, hz, Complex.ofReal_zero, zero_smul, smul_zero,
      Pi.zero_apply]
  intro s hs y
  simp only [mem_insert_iff, mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact congrFun hi y
  · simp [ellipticResidualSymbol, physicalSymbolApply, hi, partialDeriv]
    rw [show ellipticInverseSymbol f hK threshold Q y ξ = 0 from congrFun hi y,
      Matrix.mul_zero]
  · simp [ellipticSourceSymbol, hz]

/-- All three literal symbols vanish off the same closed source support.
In particular the full `B` term and the differentiated extension have no
extra frequency support (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem ellipticSymbols_zero_off_frequency_support (threshold : ℝ)
    (Q : E → Coeff) (B : E → Mat) {ξ : E}
    (hξ : ξ ∉ tsupport (ellipticSourceMask f hK threshold)) :
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)), ∀ y, s y ξ = 0 :=
  ellipticSymbols_zero_of_sourceMask_zero f hK threshold Q B
    (image_eq_zero_of_notMem_tsupport hξ)

/-- The closed elliptic carrier avoids zero at the original `2*threshold`
collar; both literal orientations retain this carrier and the original
physical masks (`app:ch_regular:eq:chain-tail`). -/
theorem elliptic_masked_amplitude_support
    (χout : E → ℂ) {threshold : ℝ} (ht : 0 < threshold)
    (Q : E → Coeff) (B : E → Mat) :
    let F := tsupport (ellipticSourceMask f hK threshold)
    IsClosed F ∧ (0 : E) ∉ F ∧
    (∀ ξ ∈ F, 2*threshold ≤ ‖ξ‖) ∧
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)), ∀ backward y z ξ,
      ((y, z) ∉ tsupport χout ×ˢ
        tsupport (fun z ↦ (f.inputMask z : ℂ)) ∨ ξ ∉ F) →
      orientedMaskedPDOAmplitude backward χout
        (fun z ↦ (f.inputMask z : ℂ)) s y z ξ = 0 := by
  intro F
  refine ⟨isClosed_tsupport _, ?_, fun ξ hξ ↦ (ellipticSourceMask_support f hK ht hξ).1, ?_⟩
  · intro h
    have hh := (ellipticSourceMask_support f hK ht h).1
    simp only [norm_zero] at hh
    linarith
  · intro s hs backward y z ξ h
    have hz : (χout y * (f.inputMask z : ℂ)) • s y ξ = 0 := by
      rcases h with h | h
      · by_cases hy : y ∈ tsupport χout
        · have hz := image_eq_zero_of_notMem_tsupport (fun hz ↦ h ⟨hy, hz⟩)
          simp only [hz, mul_zero, zero_smul]
        · have hy := image_eq_zero_of_notMem_tsupport hy
          simp only [hy, zero_mul, zero_smul]
      · rw [ellipticSymbols_zero_off_frequency_support f hK threshold Q B h s hs y, smul_zero]
    simp only [orientedMaskedPDOAmplitude, hz, Matrix.conjTranspose_zero, ite_self]

/-- The closed elliptic carrier avoids zero at the original `2*threshold`
collar; both literal orientations retain this carrier and the original
physical masks (`app:ch_regular:eq:chain-tail`). -/
theorem elliptic_oriented_amplitude_support {threshold : ℝ} (ht : 0 < threshold)
    (Q : E → Coeff) (B : E → Mat) :
    let F := tsupport (ellipticSourceMask f hK threshold)
    IsClosed F ∧ (0 : E) ∉ F ∧
    (∀ ξ ∈ F, 2*threshold ≤ ‖ξ‖) ∧
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)), ∀ backward y z ξ,
      ((y, z) ∉ tsupport (fun y ↦ (f.outputMask y : ℂ)) ×ˢ
        tsupport (fun z ↦ (f.inputMask z : ℂ)) ∨ ξ ∉ F) →
      orientedMaskedPDOAmplitude backward (fun y ↦ (f.outputMask y : ℂ))
        (fun z ↦ (f.inputMask z : ℂ)) s y z ξ = 0 := by
  exact elliptic_masked_amplitude_support f hK
    (fun y ↦ (f.outputMask y : ℂ)) ht Q B

end JanetCartan.RegularSector.EllipticLocalization
