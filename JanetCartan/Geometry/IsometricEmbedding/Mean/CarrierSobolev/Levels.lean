module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Weights

/-!
# Linear domains of the full initial Fourier Sobolev norms

The domains in `app:ch_background:prop:bg-adjoint` are actual subspaces of
physical `(z,y)` L² classes. The level-zero and inclusion identifications below
are unconditional. The Sobolev Hilbert norm must still be supplied separately;
the subtype's inherited L² norm is not the higher-order Sobolev norm.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CarrierSobolev
open ContinuumRow RawCutoffBounds

variable {n : ℕ}

/-- Zero has finite full initial energy
(`app:ch_background:prop:bg-adjoint`). -/
theorem memPhysicalSobolev_zero_function (s : ℕ) :
    MemPhysicalSobolev s (0 : CarrierL2 n) := by
  unfold MemPhysicalSobolev CarrierWeightedMem
  simp only [map_zero]
  apply (memLp_congr_ae ?_).mpr (MemLp.zero (ε := ℂ))
  filter_upwards [Lp.coeFn_zero ℂ 2 (carrierMeasure n)] with ξ hξ
  change initialWeight s ξ • (0 : CarrierL2 n) ξ = (0 : ℂ)
  rw [hξ]
  simp

/-- Addition preserves the full initial energy domain
(`app:ch_background:prop:bg-adjoint`). -/
theorem MemPhysicalSobolev.add {s : ℕ} {f g : CarrierL2 n}
    (hf : MemPhysicalSobolev s f) (hg : MemPhysicalSobolev s g) :
    MemPhysicalSobolev s (f + g) := by
  unfold MemPhysicalSobolev CarrierWeightedMem at *
  apply (memLp_congr_ae ?_).mpr (hf.add hg)
  filter_upwards [Lp.coeFn_add (initialFourier n f) (initialFourier n g)] with ξ hξ
  simp only [map_add, hξ, Pi.add_apply, smul_add]

/-- Complex scalar multiplication preserves the full initial energy domain
(`app:ch_background:prop:bg-adjoint`). -/
theorem MemPhysicalSobolev.smul {s : ℕ} {f : CarrierL2 n}
    (hf : MemPhysicalSobolev s f) (c : ℂ) : MemPhysicalSobolev s (c • f) := by
  unfold MemPhysicalSobolev CarrierWeightedMem at *
  apply (memLp_congr_ae ?_).mpr (hf.const_smul c)
  filter_upwards [Lp.coeFn_smul c (initialFourier n f)] with ξ hξ
  simp only [map_smul, hξ, Pi.smul_apply, smul_comm c]

/-- Concrete full physical Sobolev domains as subspaces of the published L²
space (`app:ch_background:prop:bg-adjoint`). This declaration supplies the
linear domain only, not the higher-order Hilbert topology. -/
def physicalSobolevLevel (n s : ℕ) : Submodule ℂ (CarrierL2 n) where
  carrier := {f | MemPhysicalSobolev s f}
  zero_mem' := memPhysicalSobolev_zero_function s
  add_mem' := MemPhysicalSobolev.add
  smul_mem' c _ hf := hf.smul c

/-- The physical Fourier-energy domain at zero is all of the original carrier
L² space (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem physicalSobolevLevel_zero (n : ℕ) : physicalSobolevLevel n 0 = ⊤ := by
  ext f
  simp [physicalSobolevLevel]

/-- All level inclusions use the same underlying L² class
(`app:ch_background:prop:bg-adjoint`). -/
theorem antitone_physicalSobolevLevel (n : ℕ) : Antitone (physicalSobolevLevel n) := by
  intro s t hst f hf
  exact hf.mono hst

end JanetCartan.CarrierSobolev
