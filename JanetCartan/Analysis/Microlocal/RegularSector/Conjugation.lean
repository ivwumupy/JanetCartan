module

public import JanetCartan.Analysis.Operator.SectorResidual
public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Complex.Basic

import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.Abel

/-!
# Conjugate sectors and real normalization

Algebraic assembly for `app:ch_regular_base:prop:complete-residual` and
`app:ch_regular_base:thm:sector`. The negative sector is constructed from the
entire positive-sector factors, retaining their order and the minus sign in
`𝒥₋ = -conj 𝒥₊`. The resulting finite sum is anti-real, so multiplication by
`-i` preserves real inputs. The residual has the manuscript's plus convention.

These are identities for supplied complex-linear factors. This module does not
construct the phase charts, graph operators, cutoff partition, or characteristic
integral, and asserts no analytic estimates. For function spaces, `star` is
pointwise complex conjugation; the abstract formulation also applies to supported
function spaces whenever the same real structure is provided.
-/

@[expose] public section

open scoped BigOperators

namespace JanetCartan.RegularSector

variable {E F G : Type*}
  [AddCommGroup E] [Module ℂ E] [StarAddMonoid E] [StarModule ℂ E]
  [AddCommGroup F] [Module ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [AddCommGroup G] [Module ℂ G] [StarAddMonoid G] [StarModule ℂ G]

/-- Conjugation on both sides of a complex-linear factor, as in
`app:ch_regular_base:eq:signed-graph-factor`. -/
def conjugateOperator (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F where
  toFun x := star (T (star x))
  map_add' x y := by simp
  map_smul' z x := by simp

/-- Pointwise form of the whole-factor conjugation in
`app:ch_regular_base:eq:signed-coordinate-inverse`. -/
@[simp] theorem conjugateOperator_apply (T : E →ₗ[ℂ] F) (x : E) :
    conjugateOperator T x = star (T (star x)) := rfl

/-- Conjugating the whole sector twice restores it
(`app:ch_regular_base:eq:signed-graph-factor`). -/
@[simp] theorem conjugateOperator_conjugateOperator (T : E →ₗ[ℂ] F) :
    conjugateOperator (conjugateOperator T) = T := by ext x; simp

/-- Conjugation preserves finite error sums
(`app:ch_regular_base:eq:finite-conjugation`). -/
@[simp] theorem conjugateOperator_add (T U : E →ₗ[ℂ] F) :
    conjugateOperator (T + U) = conjugateOperator T + conjugateOperator U := by ext x; simp

/-- The sign in conjugate partners is preserved
(`app:ch_regular_base:eq:signed-canonical-integral`). -/
@[simp] theorem conjugateOperator_neg (T : E →ₗ[ℂ] F) :
    conjugateOperator (-T) = -conjugateOperator T := by ext x; simp

/-- Conjugation preserves the residual difference
(`app:ch_regular_base:eq:scalar-residual-definition`). -/
@[simp] theorem conjugateOperator_sub (T U : E →ₗ[ℂ] F) :
    conjugateOperator (T - U) = conjugateOperator T - conjugateOperator U := by ext x; simp

/-- Complex scalar coefficients are conjugated, as required for the factor `i`
in `app:ch_regular_base:eq:signed-canonical-integral`. -/
@[simp] theorem conjugateOperator_smul (z : ℂ) (T : E →ₗ[ℂ] F) :
    conjugateOperator (z • T) = star z • conjugateOperator T := by ext x; simp

/-- Whole-factor conjugation preserves composition order
(`app:ch_regular_base:eq:signed-coordinate-inverse`). -/
@[simp] theorem conjugateOperator_comp (T : F →ₗ[ℂ] G) (U : E →ₗ[ℂ] F) :
    conjugateOperator (T.comp U) = (conjugateOperator T).comp (conjugateOperator U) := by ext x; simp

/-- Conjugation commutes with the finite sector sum
(`app:ch_regular_base:eq:QN-definition`). -/
@[simp] theorem conjugateOperator_sum {ι : Type*} (s : Finset ι) (T : ι → E →ₗ[ℂ] F) :
    conjugateOperator (∑ j ∈ s, T j) = ∑ j ∈ s, conjugateOperator (T j) := by
  ext x
  simp [LinearMap.sum_apply]

variable {ι : Type*} {C : ι → Type*}
  [∀ j, AddCommGroup (C j)] [∀ j, Module ℂ (C j)]
  [∀ j, StarAddMonoid (C j)] [∀ j, StarModule ℂ (C j)]

/-- The explicitly conjugated partner factors produce `Q₋ = -conj Q₊`
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem partner_parametrix (s : Finset ι) (Ttilde : ∀ j, C j →ₗ[ℂ] F)
    (J : ∀ j, C j →ₗ[ℂ] C j) (V : ∀ j, E →ₗ[ℂ] C j)
    (A : ι → E →ₗ[ℂ] E) :
    SectorResidual.sectorParametrix s (fun j ↦ conjugateOperator (Ttilde j))
      (fun j ↦ -conjugateOperator (J j)) (fun j ↦ conjugateOperator (V j))
      (fun j ↦ conjugateOperator (A j)) =
        -conjugateOperator (SectorResidual.sectorParametrix s Ttilde J V A) := by
  ext x
  simp [SectorResidual.sectorParametrix, LinearMap.sum_apply]

/-- The finite sum with both complete conjugate sectors, using the existing
`sectorParametrix` definition (`app:ch_regular_base:eq:QN-definition`).
The input `J` represents the complex integral `𝒥`, including its factor `i`. -/
def pairedParametrix (s : Finset ι) (Ttilde : ∀ j, C j →ₗ[ℂ] F)
    (J : ∀ j, C j →ₗ[ℂ] C j) (V : ∀ j, E →ₗ[ℂ] C j)
    (A : ι → E →ₗ[ℂ] E) : E →ₗ[ℂ] F :=
    SectorResidual.sectorParametrix s Ttilde J V A +
    SectorResidual.sectorParametrix s (fun j ↦ conjugateOperator (Ttilde j))
      (fun j ↦ -conjugateOperator (J j)) (fun j ↦ conjugateOperator (V j))
      (fun j ↦ conjugateOperator (A j))

/-- The full paired finite construction is anti-real
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem conjugateOperator_pairedParametrix (s : Finset ι) (Ttilde : ∀ j, C j →ₗ[ℂ] F)
    (J : ∀ j, C j →ₗ[ℂ] C j) (V : ∀ j, E →ₗ[ℂ] C j)
    (A : ι → E →ₗ[ℂ] E) :
    conjugateOperator (pairedParametrix s Ttilde J V A) = -pairedParametrix s Ttilde J V A := by
  simp only [pairedParametrix, partner_parametrix, conjugateOperator_add,
    conjugateOperator_neg, conjugateOperator_conjugateOperator]
  abel

/-- The scalar normalization `Q_N / i = -i Q_N` in
`app:ch_regular_base:eq:real-sector-normalization`, before the output cutoff. -/
def physicalNormalization (Q : E →ₗ[ℂ] F) : E →ₗ[ℂ] F := -Complex.I • Q

/-- An anti-real parametrix becomes real after division by `i`
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem conjugateOperator_physicalNormalization (Q : E →ₗ[ℂ] F)
    (hQ : conjugateOperator Q = -Q) :
    conjugateOperator (physicalNormalization Q) = physicalNormalization Q := by
  simp [physicalNormalization, hQ]

/-- The normalized operator sends conjugation-fixed inputs to conjugation-fixed
outputs (`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem physicalNormalization_real (Q : E →ₗ[ℂ] F)
    (hQ : conjugateOperator Q = -Q) {x : E} (hx : star x = x) :
    star (physicalNormalization Q x) = physicalNormalization Q x := by
  have h := LinearMap.congr_fun (conjugateOperator_physicalNormalization Q hQ) x
  simpa [hx] using h

/-- The constructed paired sum gives real outputs after normalization, with no
additional reality premise on the supplied sector factors
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem pairedParametrix_physicalNormalization_real
    (s : Finset ι) (Ttilde : ∀ j, C j →ₗ[ℂ] F)
    (J : ∀ j, C j →ₗ[ℂ] C j) (V : ∀ j, E →ₗ[ℂ] C j)
    (A : ι → E →ₗ[ℂ] E) {x : E} (hx : star x = x) :
    star (physicalNormalization (pairedParametrix s Ttilde J V A) x) =
      physicalNormalization (pairedParametrix s Ttilde J V A) x :=
  physicalNormalization_real _ (conjugateOperator_pairedParametrix s Ttilde J V A) hx

/-- For a real characteristic integral `J`, both partner sectors use the same
complex integral `iJ` (`app:ch_regular_base:eq:signed-canonical-integral`).
Reality of the actual retarded integral remains an analytic construction input. -/
theorem negative_conjugateOperator_smul_I (J : E →ₗ[ℂ] F)
    (hJ : conjugateOperator J = J) :
    -conjugateOperator (Complex.I • J) = Complex.I • J := by
  simp [hJ]

/-- The full residual is real when the angular partition is real and both
`L = P/i` and `Q` are anti-real
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem conjugateOperator_residual (A : E →ₗ[ℂ] E) (L : F →ₗ[ℂ] E)
    (Q : E →ₗ[ℂ] F) (hA : conjugateOperator A = A) (hL : conjugateOperator L = -L)
    (hQ : conjugateOperator Q = -Q) :
    conjugateOperator (SectorResidual.sectorResidual A L Q) =
      SectorResidual.sectorResidual A L Q := by
  simp [SectorResidual.sectorResidual, hA, hL, hQ]

omit [StarAddMonoid E] [StarModule ℂ E] [StarAddMonoid F] [StarModule ℂ F] in
/-- The exact sign conversion `P S = AΓ + R`, with `R = -ℰ`
(`app:ch_regular_base:eq:two-residual-conventions`). This algebraic identity
holds before the extra output cutoff; restricting to its plateau is separate. -/
theorem physicalNormalization_identity (A : E →ₗ[ℂ] E)
    (L : F →ₗ[ℂ] E) (Q : E →ₗ[ℂ] F) :
    (Complex.I • L).comp (physicalNormalization Q) =
      A + -SectorResidual.sectorResidual A L Q := by
  ext x
  simp [physicalNormalization, SectorResidual.sectorResidual, smul_smul]

end JanetCartan.RegularSector
