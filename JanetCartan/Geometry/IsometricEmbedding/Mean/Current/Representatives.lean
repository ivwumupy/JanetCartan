module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.SmoothOutput
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Smooth representatives of the complete mean output

For `main:eq:full-recursion`, the residual lives on the whole auxiliary torus.
The exterior summand is retained here. The smooth space is the singleton case
of the shared family space, so all existing Sobolev seminorms apply to it.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CurrentMean

open ContinuumRow AuxiliaryRawBand

/-- The smooth full-output sources of `main:eq:prepared-residual` and
`main:eq:full-recursion`. No inverse regularity is built into this space. -/
abbrev SmoothResidual (n : ℕ) := SmoothPeriodicFamily n Unit (Euclidean n)

/-- The original real torus L² realization (`main:eq:full-recursion`). -/
def smoothResidualToL2 (n : ℕ) : SmoothResidual n →ₗ[ℝ] OutputL2 n :=
  SmoothPeriodicFamily.componentL2 ()

/-- Equality of smooth full-output sources is detected by their original L²
classes (`main:eq:prepared-residual`). -/
theorem smoothResidualToL2_injective (n : ℕ) :
    Function.Injective (smoothResidualToL2 n) := by
  intro f g h
  have hae : (fun x ↦ f.val x ()) =ᵐ[volume] (fun x ↦ g.val x ()) :=
    (SmoothPeriodicFamily.componentL2_coe_ae () f).symm.trans
      (h ▸ SmoothPeriodicFamily.componentL2_coe_ae () g)
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae
    (SmoothPeriodicFamily.smooth f ()).1 (SmoothPeriodicFamily.smooth g ()).1
  apply Subtype.ext
  funext x u
  cases u
  exact congrFun heq x

/-- The complete smooth representative belongs to every level of the
original periodic Sobolev scale (`main:lem:mean-recurrence`). -/
theorem smoothResidualToL2_mem {n : ℕ} (f : SmoothResidual n) (s : ℕ) :
    smoothResidualToL2 n f ∈ (periodicSobolevScale n (Euclidean n)).level s :=
  (SmoothPeriodicFamily.smooth f ()).toLp_mem_periodicSobolevLevel s
    (SmoothPeriodicFamily.memLp f ())

/-- The high norm of the L² recurrence and the Fourier norm of its SAME
smooth representative agree exactly. This is the connection from
`RecurrenceTail.run_residual_gradeNorm_le` to the precision upgrade
(`main:lem:mean-recurrence`). -/
theorem smoothResidualToL2_gradeNorm {n : ℕ} (f : SmoothResidual n) (s : ℕ) :
    (periodicSobolevScale n (Euclidean n)).gradeNorm s (smoothResidualToL2 n f) =
      periodicSobolevNorm s (fun x ↦ f.val x ()) :=
  (SmoothPeriodicFamily.smooth f ()).gradeNorm_toLp s
    (SmoothPeriodicFamily.memLp f ())

/-- Smooth sources supported in a fixed set, for the preparation domain in
`app:ch_mean_pairs:prop:mean-coarse`. Support is a condition on the actual
representative; no Sobolev estimate or inverse identity is assumed. -/
def supportedSmoothResidual (n : ℕ) (S : Set (Torus n)) :
    Submodule ℝ (SmoothResidual n) where
  carrier := {f | ∀ x, x ∉ S → f.val x () = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    change f.val x () + g.val x () = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' c f hf := by intro x hx; change c • f.val x () = 0; rw [hf x hx, smul_zero]

/-- Pass from an L² identity on a common open plateau to pointwise equality
before restricting to the physical closed core (`main:eq:mean-equation`). -/
theorem smoothResidual_eqOn_core_of_ae {n : ℕ} (f : SmoothResidual n)
    {g : Torus n → Euclidean n} {U D : Set (Torus n)}
    (hU : IsOpen U) (hD : D ⊆ U) (hg : ContinuousOn g U)
    (hae : (smoothResidualToL2 n f : Torus n → Euclidean n) =ᵐ[volume.restrict U] g) :
    Set.EqOn (fun x ↦ f.val x ()) g D := by
  have hr : (smoothResidualToL2 n f : Torus n → Euclidean n) =ᵐ[volume.restrict U]
      (fun x ↦ f.val x ()) :=
    ae_restrict_of_ae (SmoothPeriodicFamily.componentL2_coe_ae () f)
  exact (MeasureTheory.Measure.eqOn_open_of_ae_eq (hr.symm.trans hae) hU
    (SmoothPeriodicFamily.smooth f ()).1.continuousOn hg).mono hD

section Auxiliary

variable {n : ℕ}
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))

/-- The SAME smooth image-plus-exterior output for a canonical update
(`main:eq:full-recursion`). Only the original L² inverse is used. -/
def cutAuxiliaryRepresentative (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (K : ℝ) (e : OutputL2 n) : SmoothResidual n :=
  ⟨fun x _ ↦ smoothAuxiliaryOutput c χmeas χsrc ψ K
      ((imageChannel c χmeas χsrc).adjoint (Q₀ e)) (exteriorChannel ψ (Q₀ e)) x,
    fun _ ↦ isSmoothPeriodic_smoothAuxiliaryOutput c hc χmeas χsrc ψ hm hs hψ K _ _⟩

/-- This representative realizes the original complete cut auxiliary normal,
with its original raw cutoff and fixed `Q₀` (`main:eq:canonical-identity`). -/
theorem cutAuxiliaryRepresentative_toL2 (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    {K : ℝ} (hK : 1 ≤ K) (e : OutputL2 n) :
    smoothResidualToL2 n (cutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ Q₀ K e) =
      cutAuxiliaryNormal c χmeas χsrc ψ hK (Q₀ e) := by
  apply Lp.ext
  exact (SmoothPeriodicFamily.componentL2_coe_ae () _).trans
    (auxiliaryOutput_coeFn c χmeas χsrc ψ hs K _ _).symm

/-- The actual smooth complete-output update is linear, proved using its L²
realization and uniqueness of continuous representatives. This makes no false
L²-to-Cʳ claim for the uncut density synthesis (`main:eq:full-recursion`). -/
def cutAuxiliaryCorrection (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    {K : ℝ} (hK : 1 ≤ K) : OutputL2 n →ₗ[ℝ] SmoothResidual n where
  toFun := cutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ Q₀ K
  map_add' e f := by
    apply smoothResidualToL2_injective n
    simp only [map_add, cutAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ Q₀ hK]
  map_smul' a e := by
    apply smoothResidualToL2_injective n
    simp only [map_smul, RingHom.id_apply,
      cutAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ Q₀ hK]

end Auxiliary
end JanetCartan.CurrentMean
