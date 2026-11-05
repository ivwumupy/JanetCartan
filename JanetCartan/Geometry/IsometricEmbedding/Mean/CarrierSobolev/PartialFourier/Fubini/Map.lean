module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Fubini.Slices

/-!
# The carrier Fubini isometry

The section map and its linear isometry structure, for the partial Fourier
realization in `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Fubini

/-- The iterated L² class of the sections of a carrier L² function
(`app:ch_background:prop:bg-adjoint`). -/
def toIterated {n : ℕ} (f : CarrierL2 n) : IteratedCarrierL2 n :=
  (memLp_slice (Lp.stronglyMeasurable f) (Lp.memLp f)).toLp _

/-- Outer representative of the Fubini map (`app:ch_background:prop:bg-adjoint`). -/
theorem toIterated_coeFn {n : ℕ} (f : CarrierL2 n) :
    toIterated f =ᵐ[volume.prod volume] slice f :=
  (memLp_slice (Lp.stronglyMeasurable f) (Lp.memLp f)).coeFn_toLp

/-- Nested representative formula, avoiding any joint-evaluation assumption
(`app:ch_background:prop:bg-adjoint`). -/
theorem toIterated_coeFn_coeFn {n : ℕ} (f : CarrierL2 n) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      (toIterated f) z =ᵐ[volume] fun η => f (z, η) := by
  filter_upwards [toIterated_coeFn f, memLp_slice_ae (Lp.memLp f)] with z hz hm
  rw [hz]
  exact slice_coeFn hm

/-- Fubini's squared norm identity (`app:ch_background:prop:bg-adjoint`). -/
theorem toIterated_norm_sq {n : ℕ} (f : CarrierL2 n) :
    ‖toIterated f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [norm_sq, norm_sq]
  change (∫ z, ‖toIterated f z‖ ^ 2 ∂volume.prod volume) =
    ∫ p, ‖f p‖ ^ 2 ∂(volume.prod volume).prod volume
  rw [integral_prod _ ((Lp.memLp f).integrable_norm_pow (by decide : 2 ≠ 0))]
  apply integral_congr_ae
  filter_upwards [toIterated_coeFn f, memLp_slice_ae (Lp.memLp f)] with z hz hm
  rw [hz, slice_norm_sq hm]

/-- The carrier section map preserves the L² norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem toIterated_norm {n : ℕ} (f : CarrierL2 n) : ‖toIterated f‖ = ‖f‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (toIterated_norm_sq f)

/-- Additivity of the actual section map (`app:ch_background:prop:bg-adjoint`). -/
theorem toIterated_add {n : ℕ} (f g : CarrierL2 n) :
    toIterated (f + g) = toIterated f + toIterated g := by
  apply Lp.ext
  filter_upwards [toIterated_coeFn_coeFn (f + g), toIterated_coeFn_coeFn f,
    toIterated_coeFn_coeFn g, Lp.coeFn_add (toIterated f) (toIterated g),
    ae_ae_of_ae_prod (Lp.coeFn_add f g)] with z hfg hf hg hz ha
  rw [hz]
  apply Lp.ext
  filter_upwards [hfg, hf, hg, ha, Lp.coeFn_add ((toIterated f) z) ((toIterated g) z)]
    with η hfg hf hg ha hz
  simp only [hfg, ha, hz, Pi.add_apply, hf, hg]

/-- Complex linearity of the section map (`app:ch_background:prop:bg-adjoint`). -/
theorem toIterated_smul {n : ℕ} (c : ℂ) (f : CarrierL2 n) :
    toIterated (c • f) = c • toIterated f := by
  apply Lp.ext
  filter_upwards [toIterated_coeFn_coeFn (c • f), toIterated_coeFn_coeFn f,
    Lp.coeFn_smul c (toIterated f), ae_ae_of_ae_prod (Lp.coeFn_smul c f)] with z hcf hf hz ha
  rw [hz]
  apply Lp.ext
  filter_upwards [hcf, hf, ha, Lp.coeFn_smul c ((toIterated f) z)] with η hcf hf ha hz
  simp only [hcf, ha, hz, Pi.smul_apply, hf]

/-- The genuine carrier section isometry. Surjectivity is proved separately
before constructing the equivalence (`app:ch_background:prop:bg-adjoint`). -/
def linearIsometry (n : ℕ) : CarrierL2 n →ₗᵢ[ℂ] IteratedCarrierL2 n where
  toFun := toIterated
  map_add' := toIterated_add
  map_smul' := toIterated_smul
  norm_map' := toIterated_norm

end Fubini
end JanetCartan.CarrierSobolev
