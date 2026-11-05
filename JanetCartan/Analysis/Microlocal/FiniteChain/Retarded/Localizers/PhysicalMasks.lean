module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Grades
import Mathlib.Tactic.FunProp

/-!
# Physical supports of retarded masks

The normalized masks in `app:ch_regular:lem:finite-chain` give compact smooth
physical masks and positive radial annuli at frequency `ρ > 0`. The physical
base is unchanged. Covector reflection preserves the same annular endpoints.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial homogeneity of the joint covector size
(`app:ch_regular:lem:finite-chain`). -/
theorem frequencySize_smul (r τ : ℝ) (η : E) :
    frequencySize (r * τ) (r • η) = |r| * frequencySize τ η := by
  rw [frequencySize_eq_norm, frequencySize_eq_norm]
  change ‖r • WithLp.toLp 2 (τ, η)‖ = _
  rw [norm_smul, Real.norm_eq_abs]

/-- Positive frequency normalization is a homeomorphism of phase space
(`app:ch_regular:lem:finite-chain`). -/
def normalizeMaskCovectorHomeomorph {ρ : ℝ} (hρ : 0 < ρ) :
    CanonicalPhase E ≃ₜ CanonicalPhase E where
  toFun := normalizeMaskCovector ρ
  invFun := fun p => (p.1, ρ • p.2)
  left_inv := by intro p; simp [smul_smul, hρ.ne']
  right_inv := by intro p; simp [smul_smul, hρ.ne']
  continuous_toFun := (normalizeMaskCovector ρ).continuous
  continuous_invFun := by fun_prop

/-- The entire physical support, including shoulders, is the rescaled
normalized support (`app:ch_regular:lem:finite-chain`). -/
theorem tsupport_physicalMask (m : CanonicalPhase E → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (physicalMask ρ m) = normalizeMaskCovector ρ ⁻¹' tsupport m :=
  tsupport_comp_eq_preimage m (normalizeMaskCovectorHomeomorph hρ)

/-- Physical rescaling preserves smooth buffered masks and compact support
(`app:ch_regular:lem:finite-chain`). -/
theorem IsBufferedMask.physical {m : CanonicalPhase E → ℝ}
    {K O : Set (CanonicalPhase E)} (hm : IsBufferedMask m K O)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IsBufferedMask (physicalMask ρ m) (normalizeMaskCovector ρ ⁻¹' K)
      (normalizeMaskCovector ρ ⁻¹' O) := by
  refine ⟨contDiff_physicalMask hm.smooth ρ, fun p => hm.range _, ?_, ?_, ?_⟩
  · change IsCompact (tsupport (physicalMask ρ m))
    rw [tsupport_physicalMask m hρ]
    exact (normalizeMaskCovectorHomeomorph hρ).isCompact_preimage.mpr hm.compactSupport
  · rw [tsupport_physicalMask m hρ]
    exact preimage_mono hm.support_subset
  · have hp := preimage_mono (f := normalizeMaskCovectorHomeomorph hρ) hm.plateau
    rw [(normalizeMaskCovectorHomeomorph hρ).preimage_interior] at hp
    exact hp

/-- The normalized annulus becomes an annulus with endpoints proportional to
the physical frequency (`app:ch_regular:lem:finite-chain`). -/
theorem mem_phaseAnnulus_normalizeMaskCovector {ρ : ℝ} (hρ : 0 < ρ)
    (a b : ℝ) (p : CanonicalPhase E) :
    normalizeMaskCovector ρ p ∈ phaseAnnulus a b ↔
      p ∈ phaseAnnulus (ρ * a) (ρ * b) := by
  change (a < frequencySize (ρ⁻¹ * p.2.1) (ρ⁻¹ • p.2.2) ∧
    frequencySize (ρ⁻¹ * p.2.1) (ρ⁻¹ • p.2.2) < b) ↔ _
  rw [frequencySize_smul, abs_of_pos (inv_pos.mpr hρ),
    lt_inv_mul_iff₀ hρ, inv_mul_lt_iff₀ hρ]
  rfl

/-- Both signed physical masks have the same strictly positive annular
endpoints (`app:ch_regular:lem:finite-chain`). This applies to every member
of the constructed annular input/output families, with unchanged base support. -/
theorem physicalMask_annular_support {m : CanonicalPhase E → ℝ}
    {a b ρ : ℝ} (ha : 0 < a) (hab : a < b) (hρ : 0 < ρ)
    (hm : tsupport m ⊆ phaseAnnulus a b) (negative : Bool) :
    0 < ρ * a ∧ ρ * a < ρ * b ∧
      tsupport (physicalMask ρ (if negative then signedMask m else m)) ⊆
        phaseAnnulus (ρ * a) (ρ * b) := by
  refine ⟨mul_pos hρ ha, mul_lt_mul_of_pos_left hab hρ, ?_⟩
  intro p hp
  apply (mem_phaseAnnulus_normalizeMaskCovector hρ a b p).mp
  rw [tsupport_physicalMask _ hρ] at hp
  cases negative
  · exact hm hp
  · simp only [↓reduceIte, tsupport_signedMask] at hp
    have h := hm hp
    simpa only [phaseAnnulus, mem_ofPred_eq, frequencySize_reflectCovector] using h

end JanetCartan.FiniteChain.Retarded
