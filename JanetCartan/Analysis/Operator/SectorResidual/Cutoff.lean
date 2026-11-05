module

public import Mathlib.Algebra.Module.LinearMap.Defs

import Mathlib.Tactic.Abel

/-!
# The buffered integration identity

The operator algebra behind `app:ch_regular_base:eq:DJ-identity` in `paper.tex`.
The primitive identity is required only after the input cutoff. Differentiation
of the output cutoff contributes a commutator, retained until the nesting
identities remove it. The maps may act on spaces of smooth functions; no
boundedness of the differentiation operator is required.
-/

@[expose] public section

namespace JanetCartan.SectorResidual

variable {𝕜 C X Y : Type*} [Ring 𝕜]
  [AddCommGroup C] [Module 𝕜 C] [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup Y] [Module 𝕜 Y]

/-- The buffered integral `χout P χin` in `app:ch_osc:setup:osc-retarded`.
For the complex normalization, `P` includes the factor `i`. -/
def bufferedIntegral (P χin χout : C →ₗ[𝕜] C) : C →ₗ[𝕜] C :=
  χout.comp (P.comp χin)

/-- The exact output-cutoff commutator `[Dt, χout]` used in
`app:ch_regular_base:eq:DJ-identity`. -/
def cutoffCommutator (Dt χout : C →ₗ[𝕜] C) : C →ₗ[𝕜] C :=
  Dt.comp χout - χout.comp Dt

/-- Differentiating the buffered integral retains the output-cutoff commutator.
The fundamental theorem is assumed only on cut off inputs, as required in
`app:ch_regular_base:eq:DJ-identity`, not as a global identity for the primitive. -/
theorem derivative_bufferedIntegral (Dt P χin χout : C →ₗ[𝕜] C)
    (hprimitive : Dt.comp (P.comp χin) = χin) :
    Dt.comp (bufferedIntegral P χin χout) =
      χout.comp χin + (cutoffCommutator Dt χout).comp (P.comp χin) := by
  ext x
  have h := LinearMap.congr_fun hprimitive x
  simp only [LinearMap.comp_apply] at h
  simp only [bufferedIntegral, cutoffCommutator, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply]
  rw [h]
  abel

/-- The two nesting identities remove the cutoff product, but leave the
integration-cutoff commutator in `app:ch_regular_base:eq:DJ-identity`.
The left map `T` may already include a measurement cutoff. -/
theorem sandwich_derivative_bufferedIntegral (T : C →ₗ[𝕜] X) (V : Y →ₗ[𝕜] C)
    (Dt P χin χout : C →ₗ[𝕜] C)
    (hprimitive : Dt.comp (P.comp χin) = χin)
    (hinput : χin.comp V = V) (houtput : T.comp χout = T) :
    T.comp ((Dt.comp (bufferedIntegral P χin χout)).comp V) =
      T.comp V +
        T.comp ((cutoffCommutator Dt χout).comp ((P.comp χin).comp V)) := by
  rw [derivative_bufferedIntegral Dt P χin χout hprimitive]
  ext x
  have hin := LinearMap.congr_fun hinput x
  have hout := LinearMap.congr_fun houtput (V x)
  simp only [LinearMap.comp_apply] at hin hout
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  rw [hin, hout]

/-- The sandwiched identity `T Dt J V = T V` of
`app:ch_regular_base:eq:DJ-identity` follows from all three nesting identities.
This does not assert `Dt J = I` on the whole canonical space. -/
theorem sandwich_derivative_bufferedIntegral_of_nested
    (T : C →ₗ[𝕜] X) (V : Y →ₗ[𝕜] C) (Dt P χin χout : C →ₗ[𝕜] C)
    (hprimitive : Dt.comp (P.comp χin) = χin)
    (hinput : χin.comp V = V) (houtput : T.comp χout = T)
    (hcommutator : T.comp (cutoffCommutator Dt χout) = 0) :
    T.comp ((Dt.comp (bufferedIntegral P χin χout)).comp V) = T.comp V := by
  rw [sandwich_derivative_bufferedIntegral T V Dt P χin χout
    hprimitive hinput houtput, ← LinearMap.comp_assoc, hcommutator]
  simp

end JanetCartan.SectorResidual
