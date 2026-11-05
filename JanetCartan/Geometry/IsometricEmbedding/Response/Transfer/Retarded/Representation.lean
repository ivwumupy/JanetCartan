module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.Basic
public import JanetCartan.Analysis.Sobolev.Local.Scale.Graded
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.Integrability
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Euclidean representatives of the supported retarded fields

For the norm adapter in `app:ch_response:eq:fixed-factor-transfer`, use the first
Euclidean coordinate as time and the remaining coordinates as the transverse
variable. The coordinate map preserves Lebesgue measure. Smooth test fields
therefore give concrete local L² classes in the project's actual restriction
Sobolev scale, with membership at every grade proved from classical weak jets.
No norm comparison is assumed or asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer

open RetardedSobolev.Spaces LocalSobolev

/-- Time followed by transverse coordinates, for the representation adapter of
`app:ch_response:eq:fixed-factor-transfer`. This is a coordinate equivalence,
not an isometry between the product max norm and the Euclidean norm. -/
def retardedCoordinates (d : ℕ) : Euclidean (d + 1) ≃L[ℝ] ℝ × (Fin d → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x ↦ (x 0, fun i ↦ x i.succ)
      invFun := fun p ↦ WithLp.toLp 2 (Fin.cons p.1 p.2)
      left_inv := by
        intro x
        exact congrArg (WithLp.toLp 2) (Fin.cons_self_tail (WithLp.ofLp x))
      right_inv := by intro p; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }

/-- Exact coordinate evaluation, with physical coordinates unchanged
(`app:ch_response:eq:fixed-factor-transfer`). -/
@[simp] theorem retardedCoordinates_apply {d : ℕ} (x : Euclidean (d + 1)) :
    retardedCoordinates d x = (x 0, fun i ↦ x i.succ) := rfl

/-- The retarded coordinate conversion preserves actual Lebesgue measure
(`app:ch_response:thm:response-literal-transfer`). -/
theorem measurePreserving_retardedCoordinates (d : ℕ) :
    MeasurePreserving (retardedCoordinates d) := by
  convert (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) 0).comp
    (PiLp.volume_preserving_ofLp (Fin (d + 1))) using 1
  rfl

/-- The same supported smooth field expressed on the shared Euclidean space
(`app:ch_response:eq:fixed-factor-transfer`). -/
def retardedTestFunction {d : ℕ} (f : Test d) : Euclidean (d + 1) → ℂ :=
  f.val ∘ retardedCoordinates d

/-- Coordinate conversion preserves smoothness
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem contDiff_retardedTestFunction {d : ℕ} (f : Test d) :
    ContDiff ℝ ∞ (retardedTestFunction f) :=
  f.property.1.comp (retardedCoordinates d).contDiff

/-- Coordinate conversion preserves compact support
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem hasCompactSupport_retardedTestFunction {d : ℕ} (f : Test d) :
    HasCompactSupport (retardedTestFunction f) :=
  f.property.2.comp_homeomorph (retardedCoordinates d).toHomeomorph

/-- L² integrability of the actual Euclidean representative
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem memLp_retardedTestFunction {d : ℕ} (f : Test d) :
    MemLp (retardedTestFunction f) 2 volume :=
  (contDiff_retardedTestFunction f).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_retardedTestFunction f)

/-- The actual L² class of a retarded test field, in the local scale on the
whole Euclidean chart (`app:ch_response:eq:fixed-factor-transfer`). -/
def retardedTestToLocalL2 {d : ℕ} (f : Test d) :
    LocalL2 (univ : Set (Euclidean (d + 1))) ℂ :=
  ((memLp_retardedTestFunction f).restrict univ).toLp (retardedTestFunction f)

/-- The local L² realization has the stated smooth representative
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retardedTestToLocalL2_ae {d : ℕ} (f : Test d) :
    (retardedTestToLocalL2 f : Euclidean (d + 1) → ℂ) =ᵐ[volume.restrict univ]
      retardedTestFunction f :=
  ((memLp_retardedTestFunction f).restrict univ).coeFn_toLp

/-- Every supported smooth formula belongs to every grade of the actual local
Sobolev scale. The extension is the formula itself, with its classical weak
jets (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retardedTestToLocalL2_mem {d : ℕ} (f : Test d) (s : ℕ) :
    MemRestrictionSobolev univ s (retardedTestToLocalL2 f) := by
  refine ⟨{
    toFun := retardedTestFunction f
    jet := fun j ↦ iteratedFDeriv ℝ j (retardedTestFunction f)
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume
      ((contDiff_retardedTestFunction f).of_le (by simp)) univ
    memLp_fun := memLp_retardedTestFunction f
    memLp_jet := fun j _ ↦ memLp_iteratedFDeriv_of_contDiff_hasCompactSupport
      (contDiff_retardedTestFunction f) (hasCompactSupport_retardedTestFunction f) j
    restrict_eq := (retardedTestToLocalL2_ae f).symm }⟩

end JanetCartan.ResponseTransfer
