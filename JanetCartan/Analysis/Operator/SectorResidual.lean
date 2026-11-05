module

public import JanetCartan.Analysis.Operator.SectorResidual.Cutoff
public import Mathlib.Algebra.Module.Submodule.LinearMap

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-!
# Exact residual of a finite sector construction

This is the operator ledger of `app:ch_regular_base:eq:finite-conjugation`
and `app:ch_regular_base:eq:complete-residual` in `paper.tex`. All factors are
actual linear maps, with composition in the displayed order. The physical
source and solution spaces may differ, as may the canonical spaces of the
individual sectors. No continuity or analytic estimates are asserted here.

The conjugation and source-cut inverse identities are inputs. The general
formula retains the integration defect. For buffered integrals we derive its
cutoff commutator explicitly; it disappears only under the stated nesting
identities. In particular, no global identity `Dt J = I` is assumed.
The factor `F` can be the full sum of graph, target and source commutators
`E + C + S` in the manuscript; none of its terms is dropped.
-/

@[expose] public section

open scoped BigOperators

namespace JanetCartan.SectorResidual

variable {𝕜 X Y : Type*} [Ring 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]

/-- The error in the sandwiched integration identity of
`app:ch_regular_base:eq:DJ-identity`. It includes all cutoff defects. -/
def integrationDefect {C : Type*} [AddCommGroup C] [Module 𝕜 C]
    (T : C →ₗ[𝕜] X) (Dt J : C →ₗ[𝕜] C) (V : X →ₗ[𝕜] C) : X →ₗ[𝕜] X :=
  T.comp ((Dt.comp J).comp V) - T.comp V

/-- Under input/output nesting, the integration defect is exactly the
output-cutoff commutator from `app:ch_regular_base:eq:DJ-identity`. -/
theorem integrationDefect_bufferedIntegral
    {C : Type*} [AddCommGroup C] [Module 𝕜 C]
    (T : C →ₗ[𝕜] X) (V : X →ₗ[𝕜] C) (Dt P χin χout : C →ₗ[𝕜] C)
    (hprimitive : Dt.comp (P.comp χin) = χin)
    (hinput : χin.comp V = V) (houtput : T.comp χout = T) :
    integrationDefect T Dt (bufferedIntegral P χin χout) V =
      T.comp ((cutoffCommutator Dt χout).comp ((P.comp χin).comp V)) := by
  rw [integrationDefect, sandwich_derivative_bufferedIntegral T V Dt P χin χout
    hprimitive hinput houtput, add_sub_cancel_left]

/-- The local exact product of `app:ch_regular_base:eq:local-exact-product`,
with the integration defect retained before imposing cutoff nesting. -/
theorem local_residual_with_integration_defect
    {C : Type*} [AddCommGroup C] [Module 𝕜 C]
    (L : Y →ₗ[𝕜] X) (Ttilde : C →ₗ[𝕜] Y) (T F : C →ₗ[𝕜] X)
    (Dt J : C →ₗ[𝕜] C) (V : X →ₗ[𝕜] C) (E0 : X →ₗ[𝕜] X)
    (hconjugation : L.comp Ttilde - T.comp Dt = F)
    (hinverse : T.comp V = LinearMap.id - E0) :
    LinearMap.id - L.comp (Ttilde.comp (J.comp V)) =
      E0 - F.comp (J.comp V) - integrationDefect T Dt J V := by
  ext x
  have hconj := LinearMap.congr_fun hconjugation (J (V x))
  have hinv := LinearMap.congr_fun hinverse x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply] at hconj hinv
  simp only [integrationDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply]
  rw [eq_add_of_sub_eq hconj, hinv]
  abel

variable {ι : Type*} {C : ι → Type*}
  [∀ j, AddCommGroup (C j)] [∀ j, Module 𝕜 (C j)]

/-- The finite actual solver `Q_N` of `app:ch_regular_base:eq:QN-definition`.
Every sector includes its source partition operator on the right. -/
def sectorParametrix (s : Finset ι) (Ttilde : ∀ j, C j →ₗ[𝕜] Y)
    (J : ∀ j, C j →ₗ[𝕜] C j) (V : ∀ j, X →ₗ[𝕜] C j)
    (A : ι → X →ₗ[𝕜] X) : X →ₗ[𝕜] Y :=
  ∑ j ∈ s, (Ttilde j).comp ((J j).comp ((V j).comp (A j)))

/-- The complete physical residual of
`app:ch_regular_base:eq:scalar-residual-definition`. -/
def sectorResidual (AGamma : X →ₗ[𝕜] X) (L : Y →ₗ[𝕜] X)
    (Q : X →ₗ[𝕜] Y) : X →ₗ[𝕜] X := AGamma - L.comp Q

/-- The exact finite residual ledger, before suppressing any integration-cutoff
term in `app:ch_regular_base:eq:complete-residual`. Only the genuine conjugation,
inverse and partition identities are assumed. -/
theorem complete_residual_with_integration_defect
    (s : Finset ι) (L : Y →ₗ[𝕜] X)
    (Ttilde : ∀ j, C j →ₗ[𝕜] Y) (T F : ∀ j, C j →ₗ[𝕜] X)
    (Dt J : ∀ j, C j →ₗ[𝕜] C j) (V : ∀ j, X →ₗ[𝕜] C j)
    (A E0 : ι → X →ₗ[𝕜] X) (AGamma Epart : X →ₗ[𝕜] X)
    (hconjugation : ∀ j ∈ s, L.comp (Ttilde j) - (T j).comp (Dt j) = F j)
    (hinverse : ∀ j ∈ s, (T j).comp (V j) = LinearMap.id - E0 j)
    (hpartition : AGamma = Epart + ∑ j ∈ s, A j) :
    sectorResidual AGamma L (sectorParametrix s Ttilde J V A) =
      Epart + ∑ j ∈ s,
        (E0 j - (F j).comp ((J j).comp (V j)) -
          integrationDefect (T j) (Dt j) (J j) (V j)).comp (A j) := by
  ext x
  simp only [sectorResidual, sectorParametrix, hpartition, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact LinearMap.congr_fun
    (local_residual_with_integration_defect L (Ttilde j) (T j) (F j)
      (Dt j) (J j) (V j) (E0 j) (hconjugation j hj) (hinverse j hj)) (A j x)

/-- The manuscript's complete residual follows from its exact sandwiched
`app:ch_regular_base:eq:DJ-identity`. This hypothesis concerns `T Dt J V`,
and does not strengthen the buffered identity to `Dt J = I`. -/
theorem complete_residual_of_sandwiched_derivative
    (s : Finset ι) (L : Y →ₗ[𝕜] X)
    (Ttilde : ∀ j, C j →ₗ[𝕜] Y) (T F : ∀ j, C j →ₗ[𝕜] X)
    (Dt J : ∀ j, C j →ₗ[𝕜] C j) (V : ∀ j, X →ₗ[𝕜] C j)
    (A E0 : ι → X →ₗ[𝕜] X) (AGamma Epart : X →ₗ[𝕜] X)
    (hconjugation : ∀ j ∈ s, L.comp (Ttilde j) - (T j).comp (Dt j) = F j)
    (hinverse : ∀ j ∈ s, (T j).comp (V j) = LinearMap.id - E0 j)
    (hpartition : AGamma = Epart + ∑ j ∈ s, A j)
    (hderivative : ∀ j ∈ s,
      (T j).comp (((Dt j).comp (J j)).comp (V j)) = (T j).comp (V j)) :
    sectorResidual AGamma L (sectorParametrix s Ttilde J V A) =
      Epart + ∑ j ∈ s, (E0 j - (F j).comp ((J j).comp (V j))).comp (A j) := by
  rw [complete_residual_with_integration_defect s L Ttilde T F Dt J V A E0 AGamma Epart
    hconjugation hinverse hpartition]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [integrationDefect, hderivative j hj, sub_self, sub_zero]

/-- The complete finite ledger with the integration-cutoff commutator retained.
In `app:ch_regular_base:eq:complete-residual` this is the additional negative
term `T [Dt, χout] P χin V A` until commutator vanishing has been proved.
Only the input/output nesting and the cut off primitive identity are used. -/
theorem complete_residual_with_cutoff_commutator
    (s : Finset ι) (L : Y →ₗ[𝕜] X)
    (Ttilde : ∀ j, C j →ₗ[𝕜] Y) (T F : ∀ j, C j →ₗ[𝕜] X)
    (Dt P χin χout : ∀ j, C j →ₗ[𝕜] C j) (V : ∀ j, X →ₗ[𝕜] C j)
    (A E0 : ι → X →ₗ[𝕜] X) (AGamma Epart : X →ₗ[𝕜] X)
    (hconjugation : ∀ j ∈ s, L.comp (Ttilde j) - (T j).comp (Dt j) = F j)
    (hinverse : ∀ j ∈ s, (T j).comp (V j) = LinearMap.id - E0 j)
    (hpartition : AGamma = Epart + ∑ j ∈ s, A j)
    (hprimitive : ∀ j ∈ s, (Dt j).comp ((P j).comp (χin j)) = χin j)
    (hinput : ∀ j ∈ s, (χin j).comp (V j) = V j)
    (houtput : ∀ j ∈ s, (T j).comp (χout j) = T j) :
    sectorResidual AGamma L
        (sectorParametrix s Ttilde (fun j ↦ bufferedIntegral (P j) (χin j) (χout j)) V A) =
      Epart + ∑ j ∈ s,
        (E0 j - (F j).comp ((bufferedIntegral (P j) (χin j) (χout j)).comp (V j)) -
          (T j).comp ((cutoffCommutator (Dt j) (χout j)).comp
            (((P j).comp (χin j)).comp (V j)))).comp (A j) := by
  rw [complete_residual_with_integration_defect s L Ttilde T F Dt _ V A E0 AGamma Epart
    hconjugation hinverse hpartition]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [integrationDefect_bufferedIntegral (T j) (V j) (Dt j) (P j) (χin j) (χout j)
    (hprimitive j hj) (hinput j hj) (houtput j hj)]

/-- `app:ch_regular_base:eq:complete-residual` derived from the genuine factor
identities and all three cutoff nesting identities. In particular, the
sandwiched derivative identity is proved, rather than assumed globally for `J`.
Analytic construction of these factors and their estimates remains an input. -/
theorem complete_residual_of_nested_cutoffs
    (s : Finset ι) (L : Y →ₗ[𝕜] X)
    (Ttilde : ∀ j, C j →ₗ[𝕜] Y) (T F : ∀ j, C j →ₗ[𝕜] X)
    (Dt P χin χout : ∀ j, C j →ₗ[𝕜] C j) (V : ∀ j, X →ₗ[𝕜] C j)
    (A E0 : ι → X →ₗ[𝕜] X) (AGamma Epart : X →ₗ[𝕜] X)
    (hconjugation : ∀ j ∈ s, L.comp (Ttilde j) - (T j).comp (Dt j) = F j)
    (hinverse : ∀ j ∈ s, (T j).comp (V j) = LinearMap.id - E0 j)
    (hpartition : AGamma = Epart + ∑ j ∈ s, A j)
    (hprimitive : ∀ j ∈ s, (Dt j).comp ((P j).comp (χin j)) = χin j)
    (hinput : ∀ j ∈ s, (χin j).comp (V j) = V j)
    (houtput : ∀ j ∈ s, (T j).comp (χout j) = T j)
    (hcommutator : ∀ j ∈ s, (T j).comp (cutoffCommutator (Dt j) (χout j)) = 0) :
    sectorResidual AGamma L
        (sectorParametrix s Ttilde (fun j ↦ bufferedIntegral (P j) (χin j) (χout j)) V A) =
      Epart + ∑ j ∈ s,
        (E0 j - (F j).comp ((bufferedIntegral (P j) (χin j) (χout j)).comp (V j))).comp
          (A j) := by
  apply complete_residual_of_sandwiched_derivative s L Ttilde T F Dt _ V A E0 AGamma Epart
    hconjugation hinverse hpartition
  intro j hj
  exact sandwich_derivative_bufferedIntegral_of_nested (T j) (V j)
    (Dt j) (P j) (χin j) (χout j)
    (hprimitive j hj) (hinput j hj) (houtput j hj) (hcommutator j hj)

/-- The measured version of `app:ch_regular_base:eq:complete-residual` when
output nesting and commutator vanishing hold only after a measurement map `M`.
This proves only the measured identity, without asserting global cancellation
at a physical cutoff transition. All full conjugation errors remain in `F`. -/
theorem measured_complete_residual_of_nested_cutoffs
    {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z]
    (M : X →ₗ[𝕜] Z) (s : Finset ι) (L : Y →ₗ[𝕜] X)
    (Ttilde : ∀ j, C j →ₗ[𝕜] Y) (T F : ∀ j, C j →ₗ[𝕜] X)
    (Dt P χin χout : ∀ j, C j →ₗ[𝕜] C j) (V : ∀ j, X →ₗ[𝕜] C j)
    (A E0 : ι → X →ₗ[𝕜] X) (AGamma Epart : X →ₗ[𝕜] X)
    (hconjugation : ∀ j ∈ s, L.comp (Ttilde j) - (T j).comp (Dt j) = F j)
    (hinverse : ∀ j ∈ s, (T j).comp (V j) = LinearMap.id - E0 j)
    (hpartition : AGamma = Epart + ∑ j ∈ s, A j)
    (hprimitive : ∀ j ∈ s, (Dt j).comp ((P j).comp (χin j)) = χin j)
    (hinput : ∀ j ∈ s, (χin j).comp (V j) = V j)
    (houtput : ∀ j ∈ s, (M.comp (T j)).comp (χout j) = M.comp (T j))
    (hcommutator : ∀ j ∈ s,
      (M.comp (T j)).comp (cutoffCommutator (Dt j) (χout j)) = 0) :
    M.comp (sectorResidual AGamma L
        (sectorParametrix s Ttilde (fun j ↦ bufferedIntegral (P j) (χin j) (χout j)) V A)) =
      M.comp (Epart + ∑ j ∈ s,
        (E0 j - (F j).comp ((bufferedIntegral (P j) (χin j) (χout j)).comp (V j))).comp
          (A j)) := by
  have hdefect : ∀ j ∈ s, M.comp (integrationDefect (T j) (Dt j)
      (bufferedIntegral (P j) (χin j) (χout j)) (V j)) = 0 := by
    intro j hj
    have h := sandwich_derivative_bufferedIntegral_of_nested (M.comp (T j)) (V j)
      (Dt j) (P j) (χin j) (χout j)
      (hprimitive j hj) (hinput j hj) (houtput j hj) (hcommutator j hj)
    ext x
    simp only [integrationDefect, LinearMap.comp_apply, LinearMap.sub_apply,
      map_sub, LinearMap.zero_apply]
    exact sub_eq_zero.mpr (LinearMap.congr_fun h x)
  rw [complete_residual_with_integration_defect s L Ttilde T F Dt _ V A E0 AGamma Epart
    hconjugation hinverse hpartition]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, map_add, map_sum, map_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hz := LinearMap.congr_fun (hdefect j hj) (A j x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, sub_zero]

end JanetCartan.SectorResidual
