module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Levels

/-!
# Invertible weighted Fourier analysis on physical carrier levels

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
weighted Fourier analysis identifies the actual finite-energy domain with L².
Its inverse is constructed by division by the full physical weight followed by
inverse Fourier. This supplies completeness of the separately normed Hilbert levels.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CarrierSobolev
open ContinuumRow RawCutoffBounds

variable {n : ℕ}

/-- Weighted Fourier analysis of an actual physical Sobolev class
(`app:ch_background:prop:bg-adjoint`). -/
def physicalSobolevAnalysis (s : ℕ) : physicalSobolevLevel n s →ₗ[ℂ] CarrierL2 n where
  toFun f := f.property.toLp (fun ξ ↦ initialWeight s ξ • initialFourier n f.val ξ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f + g).property.coeFn_toLp, f.property.coeFn_toLp,
      g.property.coeFn_toLp, Lp.coeFn_add
        (f.property.toLp _) (g.property.toLp _),
      Lp.coeFn_add (initialFourier n f.val) (initialFourier n g.val)] with ξ hfg hf hg ha hF
    rw [hfg, ha]
    simp only [Submodule.coe_add, map_add, hF, Pi.add_apply, smul_add, hf, hg]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(c • f).property.coeFn_toLp, f.property.coeFn_toLp,
      Lp.coeFn_smul c (f.property.toLp _),
      Lp.coeFn_smul c (initialFourier n f.val)] with ξ hcf hf hc hF
    rw [hcf, hc]
    simp only [Submodule.coe_smul, map_smul, hF, Pi.smul_apply, smul_comm c, hf]

/-- Almost-everywhere formula for weighted analysis
(`app:ch_background:prop:bg-adjoint`). -/
theorem physicalSobolevAnalysis_coeFn (s : ℕ) (f : physicalSobolevLevel n s) :
    physicalSobolevAnalysis s f =ᵐ[carrierMeasure n]
      fun ξ ↦ initialWeight s ξ • initialFourier n f.val ξ :=
  f.property.coeFn_toLp

/-- Analysis has exactly the prescribed full Fourier norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_physicalSobolevAnalysis (s : ℕ) (f : physicalSobolevLevel n s) :
    ‖physicalSobolevAnalysis s f‖ = physicalSobolevNorm s f.val :=
  Lp.norm_toLp _ f.property

/-- Weighted analysis is faithful to the underlying physical L² class
(`app:ch_background:prop:bg-adjoint`). -/
theorem physicalSobolevAnalysis_injective (s : ℕ) :
    Function.Injective (physicalSobolevAnalysis (n := n) s) := by
  intro f g h
  have hz : physicalSobolevAnalysis s (f - g) = 0 := by rw [map_sub, h, sub_self]
  have hn := norm_le_physicalSobolevNorm (f - g).property
  rw [← norm_physicalSobolevAnalysis, hz, norm_zero] at hn
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))))

/-- Division by the physical weight sends every L² class to L², since the
weight is at least one (`app:ch_background:prop:bg-inverse`). -/
theorem memLp_inverseInitialWeight (s : ℕ) (g : CarrierL2 n) :
    MemLp (fun ξ ↦ (initialWeight s ξ)⁻¹ • g ξ) 2 (carrierMeasure n) := by
  apply (Lp.memLp g).mono
    ((measurable_initialWeight s).inv.aestronglyMeasurable.smul
      (Lp.memLp g).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖(initialWeight s ξ)⁻¹ • g ξ‖ ≤ ‖g ξ‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (initialWeight_pos s ξ))]
  have hw : 1 ≤ initialWeight s ξ := by
    simpa using initialWeight_mono (Nat.zero_le s) ξ
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hw)

/-- The inverse-weight Fourier datum, defined for every L² input
(`app:ch_background:prop:bg-inverse`). -/
def inverseWeightedInitial (s : ℕ) (g : CarrierL2 n) : CarrierL2 n :=
  (memLp_inverseInitialWeight s g).toLp (fun ξ ↦ (initialWeight s ξ)⁻¹ • g ξ)

/-- Formula for the inverse-weight datum (`app:ch_background:prop:bg-inverse`). -/
theorem inverseWeightedInitial_coeFn (s : ℕ) (g : CarrierL2 n) :
    inverseWeightedInitial s g =ᵐ[carrierMeasure n]
      fun ξ ↦ (initialWeight s ξ)⁻¹ • g ξ :=
  (memLp_inverseInitialWeight s g).coeFn_toLp

/-- Cancellation of the positive weight constructs finite energy for the
inverse Fourier datum (`app:ch_background:prop:bg-inverse`). -/
theorem memPhysicalSobolev_inverseWeightedInitial (s : ℕ) (g : CarrierL2 n) :
    MemPhysicalSobolev s ((initialFourier n).symm (inverseWeightedInitial s g)) := by
  unfold MemPhysicalSobolev CarrierWeightedMem
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply (Lp.memLp g).ae_eq
  filter_upwards [inverseWeightedInitial_coeFn s g] with ξ hξ
  rw [hξ, smul_smul, mul_inv_cancel₀ (initialWeight_pos s ξ).ne', one_smul]

/-- Explicit synthesis: divide by the full weight and take inverse Fourier.
It takes values in the actual domain (`app:ch_background:prop:bg-inverse`). -/
def physicalSobolevSynthesis (s : ℕ) (g : CarrierL2 n) : physicalSobolevLevel n s :=
  ⟨(initialFourier n).symm (inverseWeightedInitial s g),
    memPhysicalSobolev_inverseWeightedInitial s g⟩

/-- Weighted analysis of the constructed synthesis recovers every L² datum
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem physicalSobolevAnalysis_synthesis (s : ℕ) (g : CarrierL2 n) :
    physicalSobolevAnalysis s (physicalSobolevSynthesis s g) = g := by
  apply Lp.ext
  filter_upwards [physicalSobolevAnalysis_coeFn s (physicalSobolevSynthesis s g),
    inverseWeightedInitial_coeFn s g] with ξ ha hi
  change _ = initialWeight s ξ •
    initialFourier n ((initialFourier n).symm (inverseWeightedInitial s g)) ξ at ha
  rw [LinearIsometryEquiv.apply_symm_apply, hi, smul_smul,
    mul_inv_cancel₀ (initialWeight_pos s ξ).ne', one_smul] at ha
  exact ha

/-- Synthesis recovers the original physical class
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem physicalSobolevSynthesis_analysis (s : ℕ) (f : physicalSobolevLevel n s) :
    physicalSobolevSynthesis s (physicalSobolevAnalysis s f) = f :=
  physicalSobolevAnalysis_injective s (physicalSobolevAnalysis_synthesis s _)

/-- The actual weighted Fourier equivalence, with its explicit inverse;
the Sobolev topology will be induced from it (`app:ch_background:prop:bg-inverse`). -/
def physicalSobolevAnalysisEquiv (s : ℕ) : physicalSobolevLevel n s ≃ₗ[ℂ] CarrierL2 n where
  toLinearMap := physicalSobolevAnalysis s
  invFun := physicalSobolevSynthesis s
  left_inv := physicalSobolevSynthesis_analysis s
  right_inv := physicalSobolevAnalysis_synthesis s

end JanetCartan.CarrierSobolev
