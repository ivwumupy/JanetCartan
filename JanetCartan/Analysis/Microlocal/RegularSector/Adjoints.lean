module

public import JanetCartan.Analysis.Operator.SectorResidual
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Literal adjoints of the finite sector products

The bounded lift of the existing `SectorResidual.sectorParametrix` and exact
adjoint formulas for `app:ch_regular_base:prop:complete-residual`. Each adjoint
reverses the full displayed product. Source and measurement cutoffs exchange
roles. The error factor includes all source, target, angular and low-frequency
terms supplied by the analytic construction.

The hypotheses that these factors are bounded on the stated Hilbert spaces are
inputs. These formulas do not establish Sobolev gains, supported/restriction
space identifications, or the analytic graph and characteristic-integral bounds.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.RegularSector

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type*} {C : ι → Type*}
  [∀ j, NormedAddCommGroup (C j)] [∀ j, InnerProductSpace 𝕜 (C j)]

/-- The continuous-linear lift of `app:ch_regular_base:eq:QN-definition`,
for factors already proved bounded on their respective Hilbert spaces. -/
def boundedParametrix (s : Finset ι) (Ttilde : ∀ j, C j →L[𝕜] F)
    (J : ∀ j, C j →L[𝕜] C j) (V : ∀ j, E →L[𝕜] C j)
    (A : ι → E →L[𝕜] E) : E →L[𝕜] F :=
  ∑ j ∈ s, (Ttilde j) ∘L (J j) ∘L (V j) ∘L (A j)

/-- Compatibility with the shared finite construction
(`app:ch_regular_base:eq:QN-definition`); no second algebraic solver is assumed. -/
theorem boundedParametrix_toLinearMap (s : Finset ι) (Ttilde : ∀ j, C j →L[𝕜] F)
    (J : ∀ j, C j →L[𝕜] C j) (V : ∀ j, E →L[𝕜] C j)
    (A : ι → E →L[𝕜] E) :
    (boundedParametrix s Ttilde J V A).toLinearMap =
      SectorResidual.sectorParametrix s (fun j ↦ (Ttilde j).toLinearMap)
        (fun j ↦ (J j).toLinearMap) (fun j ↦ (V j).toLinearMap)
        (fun j ↦ (A j).toLinearMap) := by
  ext x
  simp [boundedParametrix, SectorResidual.sectorParametrix, LinearMap.sum_apply]

variable [CompleteSpace E] [CompleteSpace F] [∀ j, CompleteSpace (C j)]

/-- The literal adjoint of the full finite solution operator
(`app:ch_regular_base:prop:complete-residual`). -/
theorem boundedParametrix_adjoint (s : Finset ι) (Ttilde : ∀ j, C j →L[𝕜] F)
    (J : ∀ j, C j →L[𝕜] C j) (V : ∀ j, E →L[𝕜] C j)
    (A : ι → E →L[𝕜] E) :
    (boundedParametrix s Ttilde J V A).adjoint =
      ∑ j ∈ s, (A j).adjoint ∘L (V j).adjoint ∘L (J j).adjoint ∘L
        (Ttilde j).adjoint := by
  simp [boundedParametrix, ContinuousLinearMap.comp_assoc]

variable (s : Finset ι) (Epart : E →L[𝕜] E)
    (E0 A : ι → E →L[𝕜] E) (Ferror : ∀ j, C j →L[𝕜] E)
    (J : ∀ j, C j →L[𝕜] C j) (V : ∀ j, E →L[𝕜] C j)

omit [CompleteSpace F] in
/-- The adjoint of the complete residual ledger, including the low-frequency
partition term (`app:ch_regular_base:eq:adjoint-integrated-term`).
The factor `Ferror` is the full conjugation error, not just its graph component. -/
theorem completeResidual_adjoint :
    (Epart + ∑ j ∈ s, (E0 j - Ferror j ∘L J j ∘L V j) ∘L A j).adjoint =
      Epart.adjoint + ∑ j ∈ s,
        (A j).adjoint ∘L ((E0 j).adjoint -
          (V j).adjoint ∘L (J j).adjoint ∘L (Ferror j).adjoint) := by
  simp [ContinuousLinearMap.comp_assoc]

omit [CompleteSpace F] in
/-- Source and measurement cutoffs exchange roles under literal adjunction
(`app:ch_regular_base:eq:measured-adjoint`). Self-adjointness of both supplied
cutoff maps is explicit; the finite residual keeps every factor in reverse order. -/
theorem measuredResidual_adjoint (χin χmeas : E →L[𝕜] E)
    (hin : χin.adjoint = χin) (hmeas : χmeas.adjoint = χmeas) :
    (χmeas ∘L
      (Epart + ∑ j ∈ s, (E0 j - Ferror j ∘L J j ∘L V j) ∘L A j) ∘L χin).adjoint =
      χin ∘L (Epart.adjoint + ∑ j ∈ s,
        (A j).adjoint ∘L ((E0 j).adjoint -
          (V j).adjoint ∘L (J j).adjoint ∘L (Ferror j).adjoint)) ∘L χmeas := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    completeResidual_adjoint, hin, hmeas, ContinuousLinearMap.comp_assoc]

end JanetCartan.RegularSector
