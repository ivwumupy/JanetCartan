module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Analysis

/-!
# Complete complex Hilbert levels for the physical carrier input

The separate type below carries the full physical Sobolev norm, not the
submodule's inherited L² norm. Weighted Fourier analysis and its constructed
inverse prove completeness. These levels are consumed by the construction of
`X^s` in `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

namespace JanetCartan.CarrierSobolev
open ContinuumRow

/-- The actual physical finite-energy domain with its own Sobolev topology,
supplied below (`app:ch_background:prop:bg-adjoint`). -/
def PhysicalSobolevSpace (n s : ℕ) : Type := physicalSobolevLevel n s

namespace PhysicalSobolevSpace

variable {n : ℕ}

instance (s : ℕ) : AddCommGroup (PhysicalSobolevSpace n s) :=
  inferInstanceAs (AddCommGroup (physicalSobolevLevel n s))

instance (s : ℕ) : Module ℂ (PhysicalSobolevSpace n s) :=
  inferInstanceAs (Module ℂ (physicalSobolevLevel n s))

/-- Forget only the Sobolev topology (`app:ch_background:prop:bg-adjoint`). -/
def toLevel (s : ℕ) : PhysicalSobolevSpace n s ≃ₗ[ℂ] physicalSobolevLevel n s :=
  LinearEquiv.refl ℂ _

/-- Weighted Fourier analysis on the separate Sobolev type
(`app:ch_background:prop:bg-adjoint`). -/
def analysis (s : ℕ) : PhysicalSobolevSpace n s ≃ₗ[ℂ] CarrierL2 n :=
  (toLevel s).trans (physicalSobolevAnalysisEquiv s)

instance (s : ℕ) : NormedAddCommGroup (PhysicalSobolevSpace n s) :=
  NormedAddCommGroup.induced _ _ (analysis s) (analysis s).injective

instance (s : ℕ) : NormedSpace ℂ (PhysicalSobolevSpace n s) :=
  NormedSpace.induced ℂ _ _ (analysis s)

instance (s : ℕ) : InnerProductSpace ℂ (PhysicalSobolevSpace n s) :=
  InnerProductSpace.induced (analysis s)

/-- Surjective isometric weighted Fourier analysis, with the explicit inverse
constructed in `physicalSobolevSynthesis` (`app:ch_background:prop:bg-inverse`). -/
def analysisIsometry (s : ℕ) : PhysicalSobolevSpace n s ≃ₗᵢ[ℂ] CarrierL2 n where
  toLinearEquiv := analysis s
  norm_map' _ := rfl

/-- Completeness follows from the constructed equivalence onto L²
(`app:ch_background:prop:bg-inverse`). -/
instance completeSpace (s : ℕ) : CompleteSpace (PhysicalSobolevSpace n s) :=
  (analysisIsometry s).toIsometryEquiv.completeSpace

/-- Faithful continuous inclusion into the original physical L² space
(`app:ch_background:prop:bg-adjoint`). -/
def toL2 (s : ℕ) : PhysicalSobolevSpace n s →L[ℂ] CarrierL2 n :=
  ((physicalSobolevLevel n s).subtype.comp (toLevel s).toLinearMap).mkContinuous 1
    (by
      intro f
      rw [one_mul]
      change ‖(toLevel s f).val‖ ≤ ‖physicalSobolevAnalysis s (toLevel s f)‖
      rw [norm_physicalSobolevAnalysis]
      exact norm_le_physicalSobolevNorm (toLevel s f).property)

/-- Inclusion retains precisely the original physical class
(`app:ch_background:prop:bg-adjoint`). -/
theorem toL2_apply (s : ℕ) (f : PhysicalSobolevSpace n s) :
    toL2 s f = (toLevel s f).val := rfl

/-- Inclusion is faithful (`app:ch_background:prop:bg-adjoint`). -/
theorem toL2_injective (s : ℕ) : Function.Injective (toL2 (n := n) s) :=
  Subtype.val_injective

/-- Every included element has finite full physical Fourier energy
(`app:ch_background:prop:bg-adjoint`). -/
theorem toL2_mem (s : ℕ) (f : PhysicalSobolevSpace n s) :
    MemPhysicalSobolev s (toL2 s f) := (toLevel s f).property

/-- The norm is exactly the specified physical Fourier norm
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_eq (s : ℕ) (f : PhysicalSobolevSpace n s) :
    ‖f‖ = physicalSobolevNorm s (toL2 s f) :=
  norm_physicalSobolevAnalysis s (toLevel s f)

/-- The L² inclusion is a contraction (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_toL2_le (s : ℕ) (f : PhysicalSobolevSpace n s) : ‖toL2 s f‖ ≤ ‖f‖ := by
  rw [norm_eq]
  exact norm_le_physicalSobolevNorm (toL2_mem s f)

/-- Regard a physical L² class of finite energy as a Sobolev element
(`app:ch_background:prop:bg-adjoint`). -/
def ofL2 (s : ℕ) (f : CarrierL2 n) (hf : MemPhysicalSobolev s f) :
    PhysicalSobolevSpace n s := (toLevel s).symm ⟨f, hf⟩

/-- The realization keeps the physical L² class (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toL2_ofL2 (s : ℕ) (f : CarrierL2 n) (hf : MemPhysicalSobolev s f) :
    toL2 s (ofL2 s f hf) = f := rfl

/-- Reconstruction from the physical class (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem ofL2_toL2 (s : ℕ) (f : PhysicalSobolevSpace n s) :
    ofL2 s (toL2 s f) (toL2_mem s f) = f := rfl

/-- The Sobolev level is exactly the image in physical L²
(`app:ch_background:prop:bg-adjoint`). -/
theorem range_toL2 (s : ℕ) :
    Set.range (toL2 (n := n) s) = (physicalSobolevLevel n s : Set (CarrierL2 n)) := by
  ext f
  exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ toL2_mem s g, fun hf ↦ ⟨ofL2 s f hf, rfl⟩⟩

/-- The algebraic inclusion between actual physical domains
(`app:ch_background:prop:bg-adjoint`). -/
def inclusionLinear {s t : ℕ} (h : s ≤ t) :
    PhysicalSobolevSpace n t →ₗ[ℂ] PhysicalSobolevSpace n s :=
  (toLevel s).symm.toLinearMap.comp
    ((Submodule.inclusion (antitone_physicalSobolevLevel n h)).comp (toLevel t).toLinearMap)

/-- All higher physical Sobolev levels include contractively into lower ones
(`app:ch_background:prop:bg-adjoint`). -/
def inclusion {s t : ℕ} (h : s ≤ t) :
    PhysicalSobolevSpace n t →L[ℂ] PhysicalSobolevSpace n s :=
  (inclusionLinear h).mkContinuous 1 (by
    intro f
    rw [one_mul, norm_eq, norm_eq]
    exact physicalSobolevNorm_mono (toL2_mem t f) h)

/-- Level inclusions preserve the physical class
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toL2_inclusion {s t : ℕ} (h : s ≤ t) (f : PhysicalSobolevSpace n t) :
    toL2 s (inclusion h f) = toL2 t f := rfl

/-- Level inclusions have norm at most one (`app:ch_background:prop:bg-adjoint`). -/
theorem norm_inclusion_le {s t : ℕ} (h : s ≤ t) (f : PhysicalSobolevSpace n t) :
    ‖inclusion h f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq, toL2_inclusion]
  exact physicalSobolevNorm_mono (toL2_mem t f) h

/-- Inclusion into the same level is the identity
(`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem inclusion_refl (s : ℕ) (f : PhysicalSobolevSpace n s) :
    inclusion (le_refl s) f = f := rfl

/-- All level inclusions are compatible (`app:ch_background:prop:bg-adjoint`). -/
theorem inclusion_trans {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t)
    (f : PhysicalSobolevSpace n t) :
    inclusion hrs (inclusion hst f) = inclusion (hrs.trans hst) f := rfl

/-- Level zero is isometrically the original physical L² space, via the
underlying class itself (`app:ch_background:prop:bg-inverse`). -/
def zeroEquivL2 : PhysicalSobolevSpace n 0 ≃ₗᵢ[ℂ] CarrierL2 n where
  toFun := toL2 0
  invFun f := ofL2 0 f (memPhysicalSobolev_zero f)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := (toL2 0).map_add
  map_smul' := (toL2 0).map_smul
  norm_map' f := by
    change ‖toL2 0 f‖ = ‖f‖
    rw [norm_eq, physicalSobolevNorm_zero]

end PhysicalSobolevSpace
end JanetCartan.CarrierSobolev
