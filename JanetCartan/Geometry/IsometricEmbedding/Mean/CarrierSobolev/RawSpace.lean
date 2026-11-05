module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives
public import JanetCartan.Analysis.Operator.GradedInverse.Scale

/-!
# The full Sobolev scale on raw carrier data

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
raw `(z,η)` data have the full physical Sobolev norm after the actual partial
unitary radian inverse transform. The complete Hilbert levels are parametrized
by their physical realizations; their injection into raw L² is the inverse
partial transform. No estimate for the geometric adjoint is assumed here.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.CarrierSobolev
open ContinuumRow

variable {n : ℕ}

/-- Full raw input membership in `app:ch_background:prop:bg-adjoint`, including
all mixed physical `z,y` derivatives before any physical cutoff. -/
def MemRawSobolev (s : ℕ) (f : CarrierL2 n) : Prop :=
  MemPhysicalSobolev s (partialUnitaryInverse n f)

/-- The full raw norm for `app:ch_background:eq:bg-r-inverse`. As for the
physical norm, analytic uses require finite-energy membership. -/
def rawSobolevNorm (s : ℕ) (f : CarrierL2 n) : ℝ :=
  physicalSobolevNorm s (partialUnitaryInverse n f)

/-- Actual raw input domains, pulled back by the constructed unitary transform
(`app:ch_background:prop:bg-adjoint`). -/
def rawSobolevLevel (n s : ℕ) : Submodule ℂ (CarrierL2 n) :=
  (physicalSobolevLevel n s).comap (partialUnitaryInverse n).toLinearEquiv.toLinearMap

/-- Membership means full physical regularity (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem mem_rawSobolevLevel (s : ℕ) (f : CarrierL2 n) :
    f ∈ rawSobolevLevel n s ↔ MemRawSobolev s f := Iff.rfl

/-- Raw level zero is exactly the published carrier L² domain
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem rawSobolevLevel_zero (n : ℕ) : rawSobolevLevel n 0 = ⊤ := by
  simp [rawSobolevLevel]

/-- The unitary convention preserves the original zeroth norm
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem rawSobolevNorm_zero (f : CarrierL2 n) : rawSobolevNorm 0 f = ‖f‖ := by
  simp [rawSobolevNorm]

/-- Higher raw orders include in lower orders (`app:ch_background:prop:bg-adjoint`). -/
theorem MemRawSobolev.mono {s t : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev t f) (hst : s ≤ t) : MemRawSobolev s f :=
  MemPhysicalSobolev.mono hf hst

/-- The full raw norm is monotone on its actual domain
(`app:ch_background:prop:bg-adjoint`). -/
theorem rawSobolevNorm_mono {s t : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev t f) (hst : s ≤ t) : rawSobolevNorm s f ≤ rawSobolevNorm t f :=
  physicalSobolevNorm_mono hf hst

/-- All mixed physical weak derivatives characterize raw membership exactly,
with no analytic premise (`app:ch_background:prop:bg-adjoint`). -/
theorem memRawSobolev_iff_exists_derivatives (s : ℕ) (f : CarrierL2 n) :
    MemRawSobolev s f ↔ ∃ v : CarrierL2DerivativeFamily n s,
      HasCarrierL2Derivatives s (partialUnitaryInverse n f) v :=
  memPhysicalSobolev_iff_exists_carrierL2Derivatives s _

/-- The raw norm controls, and is controlled by, all mixed physical derivatives
(`app:ch_background:eq:bg-r-inverse`). The derivatives are constructed. -/
theorem MemRawSobolev.exists_derivatives_norm_bounds {s : ℕ} {f : CarrierL2 n}
    (hf : MemRawSobolev s f) :
    ∃ v : CarrierL2DerivativeFamily n s,
      HasCarrierL2Derivatives s (partialUnitaryInverse n f) v ∧
      v (.empty (3 + (n - 1)) s) = partialUnitaryInverse n f ∧
      rawSobolevNorm s f ≤ (4 * Real.pi) ^ s * carrierL2DerivativeNormSum v ∧
      carrierL2DerivativeNormSum v ≤
        (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s * rawSobolevNorm s f :=
  MemPhysicalSobolev.exists_carrierL2Derivatives_norm_bounds hf

/-- Complete carrier Hilbert levels, parametrized by physical realization.
`toRawL2` below gives their faithful raw-data injection. This is the carrier
summand of `X^s` in `app:ch_background:prop:bg-adjoint`. -/
abbrev RawSobolevSpace (n s : ℕ) := PhysicalSobolevSpace n s

/-- Retain both complex quadratures as a real Hilbert space when assembling
the real row input (`app:ch_background:defn:bg-row`). -/
instance rawSobolevRealInnerProductSpace (n s : ℕ) : InnerProductSpace ℝ (RawSobolevSpace n s) :=
  InnerProductSpace.rclikeToReal ℂ _

namespace RawSobolevSpace

/-- The raw `(z,η)` datum represented by a full Sobolev element
(`app:ch_background:prop:bg-adjoint`). -/
def toRawL2 (s : ℕ) : RawSobolevSpace n s →L[ℂ] CarrierL2 n :=
  (partialUnitaryInverse n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (PhysicalSobolevSpace.toL2 s)

/-- Partial unitary synthesis recovers the physical realization
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem partialUnitaryInverse_toRawL2 (s : ℕ) (u : RawSobolevSpace n s) :
    partialUnitaryInverse n (toRawL2 s u) = PhysicalSobolevSpace.toL2 s u :=
  (partialUnitaryInverse n).apply_symm_apply _

/-- Raw injection is faithful (`app:ch_background:prop:bg-adjoint`). -/
theorem toRawL2_injective (s : ℕ) : Function.Injective (toRawL2 (n := n) s) :=
  (partialUnitaryInverse n).symm.injective.comp (PhysicalSobolevSpace.toL2_injective s)

/-- Every element has finite full raw norm (`app:ch_background:prop:bg-adjoint`). -/
theorem toRawL2_mem (s : ℕ) (u : RawSobolevSpace n s) : MemRawSobolev s (toRawL2 s u) := by
  unfold MemRawSobolev
  rw [partialUnitaryInverse_toRawL2]
  exact PhysicalSobolevSpace.toL2_mem s u

/-- The complete Hilbert norm is precisely the full raw Sobolev norm
(`app:ch_background:eq:bg-r-inverse`). -/
theorem norm_eq (s : ℕ) (u : RawSobolevSpace n s) : ‖u‖ = rawSobolevNorm s (toRawL2 s u) := by
  rw [rawSobolevNorm, partialUnitaryInverse_toRawL2, PhysicalSobolevSpace.norm_eq]

/-- The raw L² injection is contractive (`app:ch_background:prop:bg-inverse`). -/
theorem norm_toRawL2_le (s : ℕ) (u : RawSobolevSpace n s) : ‖toRawL2 s u‖ ≤ ‖u‖ := by
  change ‖(partialUnitaryInverse n).symm (PhysicalSobolevSpace.toL2 s u)‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  exact PhysicalSobolevSpace.norm_toL2_le s u

/-- Construct a level element from raw finite-energy data
(`app:ch_background:prop:bg-adjoint`). -/
def ofRawL2 (s : ℕ) (f : CarrierL2 n) (hf : MemRawSobolev s f) : RawSobolevSpace n s :=
  PhysicalSobolevSpace.ofL2 s (partialUnitaryInverse n f) hf

/-- Reconstruction preserves the raw datum (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toRawL2_ofRawL2 (s : ℕ) (f : CarrierL2 n) (hf : MemRawSobolev s f) :
    toRawL2 s (ofRawL2 s f hf) = f := (partialUnitaryInverse n).symm_apply_apply f

/-- The injection has exactly the finite-energy domain as its range
(`app:ch_background:prop:bg-adjoint`). -/
theorem range_toRawL2 (s : ℕ) :
    Set.range (toRawL2 (n := n) s) = (rawSobolevLevel n s : Set (CarrierL2 n)) := by
  ext f
  exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ toRawL2_mem s u,
    fun hf ↦ ⟨ofRawL2 s f hf, toRawL2_ofRawL2 s f hf⟩⟩

/-- Compatible inclusion of higher raw Sobolev levels
(`app:ch_background:prop:bg-inverse`). -/
abbrev inclusion {s t : ℕ} (hst : s ≤ t) : RawSobolevSpace n t →L[ℂ] RawSobolevSpace n s :=
  PhysicalSobolevSpace.inclusion hst

/-- Inclusions preserve the literal raw datum (`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem toRawL2_inclusion {s t : ℕ} (hst : s ≤ t) (u : RawSobolevSpace n t) :
    toRawL2 s (inclusion hst u) = toRawL2 t u := rfl

/-- The original raw carrier L² is exactly level zero, with no normalization
loss (`app:ch_background:prop:bg-inverse`). -/
def zeroEquivL2 : RawSobolevSpace n 0 ≃ₗᵢ[ℂ] CarrierL2 n :=
  PhysicalSobolevSpace.zeroEquivL2.trans (partialUnitaryInverse n).symm

/-- Compact smooth physical tests, transported back to raw data, are dense
in the full raw norm (`app:ch_background:prop:bg-adjoint`). -/
theorem denseRange_compactSmooth (s : ℕ) :
    DenseRange (fun φ : carrierInitialTestSpace n ↦
      (PhysicalSobolevSpace.compactSmooth s φ.val φ.property.1 φ.property.2 :
        RawSobolevSpace n s)) := PhysicalSobolevSpace.denseRange_compactSmooth s

/-- Every raw level has dense image in the literal carrier L² space
(`app:ch_background:prop:bg-inverse`). -/
theorem denseRange_toRawL2 (s : ℕ) : DenseRange (toRawL2 (n := n) s) :=
  (partialUnitaryInverse n).symm.surjective.denseRange.comp
    (PhysicalSobolevSpace.denseRange_toL2 s) (partialUnitaryInverse n).symm.continuous

end RawSobolevSpace

/-- Weighted analysis of the actual raw subspace, used to supply its scale
seminorm (`app:ch_background:prop:bg-inverse`). -/
def rawSobolevAnalysis (s : ℕ) : rawSobolevLevel n s →ₗ[ℂ] CarrierL2 n where
  toFun f := physicalSobolevAnalysis s ⟨partialUnitaryInverse n f, f.property⟩
  map_add' f g := by
    rw [← map_add]
    congr 1
    exact Subtype.ext ((partialUnitaryInverse n).map_add f.val g.val)
  map_smul' c f := by
    change _ = c • physicalSobolevAnalysis s _
    rw [← map_smul]
    congr 1
    exact Subtype.ext ((partialUnitaryInverse n).map_smul c f.val)

/-- Weighted raw analysis has the full mixed physical norm
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_rawSobolevAnalysis (s : ℕ) (f : rawSobolevLevel n s) :
    ‖rawSobolevAnalysis s f‖ = rawSobolevNorm s f.val :=
  norm_physicalSobolevAnalysis s _

/-- The actual raw carrier scale for the inverse bootstrap interface
(`app:ch_background:prop:bg-inverse`). -/
def rawSobolevScale (n : ℕ) : GradedScale (CarrierL2 n) where
  level s := (rawSobolevLevel n s).restrictScalars ℝ
  level_zero := by simp
  antitone_level := fun _ _ h _ hf ↦ MemRawSobolev.mono hf h
  seminorm s := (normSeminorm ℝ (CarrierL2 n)).comp
    (((rawSobolevAnalysis s).comp
      ((rawSobolevLevel n s).restrictScalarsEquiv ℝ).toLinearMap).restrictScalars ℝ)
  seminorm_zero f := by
    change ‖rawSobolevAnalysis 0 ⟨f.val, f.property⟩‖ = ‖f.val‖
    rw [norm_rawSobolevAnalysis, rawSobolevNorm_zero]
  monotone_seminorm {s t} h f := by
    change ‖rawSobolevAnalysis s ⟨f.val, MemRawSobolev.mono f.property h⟩‖ ≤
      ‖rawSobolevAnalysis t ⟨f.val, f.property⟩‖
    simp only [norm_rawSobolevAnalysis]
    exact rawSobolevNorm_mono f.property h

/-- On its finite-energy domain the scale norm is exactly the raw norm
(`app:ch_background:eq:bg-r-inverse`). -/
theorem rawSobolevScale_gradeNorm {s : ℕ} {f : CarrierL2 n} (hf : MemRawSobolev s f) :
    (rawSobolevScale n).gradeNorm s f = rawSobolevNorm s f := by
  rw [(rawSobolevScale n).gradeNorm_eq (show f ∈ (rawSobolevScale n).level s from hf)]
  exact norm_rawSobolevAnalysis s ⟨f, hf⟩

end JanetCartan.CarrierSobolev
