module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Local
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Reversed supported/restriction duality

Negative integer spaces in `app:ch_osc:prop:osc-retarded-tube` are defined as
continuous duals of the reversed positive spaces. The transpose bound is abstract;
identifying it with a literal integral requires the displayed smooth L² pairing.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.RetardedSobolev.Spaces

/-- The negative ambient space is the continuous dual of the positive completion
(`app:ch_osc:prop:osc-retarded-tube`). -/
abbrev NegativeAmbient (d m : ℕ) :=
  StrongDual ℂ (Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))

/-- Negative supported space: the dual of the positive restriction space
(`app:ch_osc:prop:osc-retarded-tube`). -/
abbrev NegativeSupported {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :=
  StrongDual ℂ (Restriction m U)

/-- Negative restriction space: the dual of the positive supported space
(`app:ch_osc:prop:osc-retarded-tube`). -/
abbrev NegativeRestriction {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :=
  StrongDual ℂ (Supported m U)

instance (d m : ℕ) : NormedAddCommGroup (NegativeAmbient d m) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance (d m : ℕ) : NormedSpace ℂ (NegativeAmbient d m) :=
  ContinuousLinearMap.toNormedSpace

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    NormedAddCommGroup (NegativeSupported m U) := ContinuousLinearMap.toNormedAddCommGroup

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    NormedSpace ℂ (NegativeSupported m U) := ContinuousLinearMap.toNormedSpace

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    NormedAddCommGroup (NegativeRestriction m U) := ContinuousLinearMap.toNormedAddCommGroup

instance {d : ℕ} (m : ℕ) (U : Set (ℝ × (Fin d → ℝ))) :
    NormedSpace ℂ (NegativeRestriction m U) := ContinuousLinearMap.toNormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The continuous transpose reverses a bounded map
(`app:ch_osc:prop:osc-retarded-tube`). -/
def boundedTranspose (A : E →L[ℂ] F) : StrongDual ℂ F →L[ℂ] StrongDual ℂ E :=
  (ContinuousLinearMap.compL ℂ E F ℂ).flip A

/-- Exact transpose evaluation (`app:ch_osc:eq:retarded-literal-adjoint`). -/
@[simp] theorem boundedTranspose_apply (A : E →L[ℂ] F) (v : StrongDual ℂ F) (u : E) :
    boundedTranspose A v u = v (A u) := rfl

/-- The transpose has at most the same operator norm
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem norm_boundedTranspose_le (A : E →L[ℂ] F) : ‖boundedTranspose A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (v.opNorm_comp_le A).trans_eq (mul_comm _ _)

/-- Quantitative bounded-transpose theorem
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem boundedTranspose_bound (A : E →L[ℂ] F) {C : ℝ} (hA : ‖A‖ ≤ C)
    (v : StrongDual ℂ F) : ‖boundedTranspose A v‖ ≤ C * ‖v‖ :=
  (boundedTranspose A).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right ((norm_boundedTranspose_le A).trans hA) (norm_nonneg _))

/-- A positive supported-to-restriction map transposes to the reversed negative
supported-to-restriction pair (`app:ch_osc:prop:osc-retarded-tube`). -/
def supportedRestrictionTranspose {d e m n : ℕ}
    {U : Set (ℝ × (Fin d → ℝ))} {V : Set (ℝ × (Fin e → ℝ))}
    (A : Supported m U →L[ℂ] Restriction n V) :
    NegativeSupported n V →L[ℂ] NegativeRestriction m U := boundedTranspose A

/-- A positive restriction-to-supported map transposes to the reversed negative
restriction-to-supported pair (`app:ch_osc:prop:osc-retarded-tube`). -/
def restrictionSupportedTranspose {d e m n : ℕ}
    {U : Set (ℝ × (Fin d → ℝ))} {V : Set (ℝ × (Fin e → ℝ))}
    (A : Restriction m U →L[ℂ] Supported n V) :
    NegativeRestriction n V →L[ℂ] NegativeSupported m U := boundedTranspose A

/-- The literal smooth L² pairing, conjugate-linear in its first argument
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
def smoothPairing {d : ℕ} (g f : Test d) : ℂ :=
  ∫ p : (Fin d → ℝ) × ℝ, star (g.val (p.2, p.1)) * f.val (p.2, p.1)

/-- Identification with a literal adjoint requires the exact L² pairing on dense
smooth tests (`app:ch_osc:eq:retarded-literal-adjoint`). Test families may be
supported tests or restrictions. All comparison maps and the classical adjoint
identity remain explicit premises; no concrete retarded bound is assumed here. -/
theorem boundedTranspose_eq_of_smooth_pairing {d e : ℕ} {X Y : Type*}
    (fieldX : X → Test d) (fieldY : Y → Test e)
    (includeX : X → E) (includeY : Y → F) (hdense : DenseRange includeX)
    (T : X → Y) (S : Y → X) (A : E →L[ℂ] F)
    (hA : ∀ f, A (includeX f) = includeY (T f))
    (pairX : X → StrongDual ℂ E) (pairY : Y → StrongDual ℂ F)
    (hpairX : ∀ g f, pairX g (includeX f) = smoothPairing (fieldX g) (fieldX f))
    (hpairY : ∀ g f, pairY g (includeY f) = smoothPairing (fieldY g) (fieldY f))
    (hadjoint : ∀ f g,
      smoothPairing (fieldY g) (fieldY (T f)) = smoothPairing (fieldX (S g)) (fieldX f))
    (g : Y) : boundedTranspose A (pairY g) = pairX (S g) := by
  apply DFunLike.coe_injective
  apply hdense.equalizer (boundedTranspose A (pairY g)).continuous (pairX (S g)).continuous
  funext f
  simp only [Function.comp_apply, boundedTranspose_apply, hA, hpairX, hpairY, hadjoint]

end JanetCartan.RetardedSobolev.Spaces
