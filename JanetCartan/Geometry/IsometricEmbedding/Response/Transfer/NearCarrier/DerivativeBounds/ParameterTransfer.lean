module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.SobolevAssembly
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Literal parameter derivative input

The one-parameter counterpart of `HasSpatialAmplitudeTransfer` for
`app:ch_response:eq:direct-envelope-profile`. The phase contribution transfers
to spatial derivatives of the datum; varying the datum supplies a separate
parameter derivative. This interface asserts actual derivatives, with no
modified-amplitude or Sobolev estimate in its premises.

The parameter-dependent realization `T t` represents demodulation and evaluation
of the joint full amplitude. The original operator and frequency are held fixed
in this identity. The actual construction must prove the identity for that
realization; arbitrary differentiable changes of the original operator are not
licensed by this interface. The open parameter domain can contain any prescribed
compact box. No global parameter extension or torus identification is required.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d m : ℕ} {X E ι Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Exact one-parameter analytic input for
`app:ch_response:eq:direct-envelope-profile`. `v i` is the full-amplitude
parameter direction; `qs i` includes all source divergence terms. The bilinear
maps `B i j` retain signs and matrix order. `df` and `pf` must be actual spatial
and parameter derivatives of the datum. The identity is local on `U` and is
required only at points with all those derivatives. `P` records supports and
phase sectors, not a norm conclusion. The geometry and finite FIO calculus
must supply this input for the fixed original operator. -/
def HasParameterAmplitudeTransfer
    (U : Set Y) (w : Fin m → Y)
    (v : Fin m → X) (qs : Fin m → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin m → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin m → Fin d → ι)
    (a : ι → X → E) (T : Y → (X → E) → L2 →L[ℂ] L2)
    (P : (X → E) → Prop) : Prop :=
  ∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
    ∀ (f : Y → L2) (df : Fin d → Y → L2) (pf : Y → L2) (i : Fin m)
      (t : Y), t ∈ U →
      (∀ j, HasEuclideanL2CoordinateDerivative j (f t) (df j t)) →
      HasLineDerivAt ℝ f (pf t) t (w i) →
      HasLineDerivAt ℝ (fun u => T u (b.evaluate a) (f u))
        (T t ((b.divergenceTransfer (v i) (qs i)).evaluate a) (f t) +
          ∑ j, T t ((b.coefficientProduct (B i j) (idx i j)).evaluate a) (df j t) +
          T t (b.evaluate a) (pf t)) t (w i)

/-- The actual directional derivative of the demodulated family in
`app:ch_response:eq:direct-envelope-profile`, retaining the derivative of its
datum. This extracts an equality from the explicit one-derivative input;
higher derivative identities are not presumed. -/
theorem HasParameterAmplitudeTransfer.lineDeriv_eq
    {U : Set Y} {w : Fin m → Y}
    {v : Fin m → X} {qs : Fin m → List (X × ι × (E →L[ℝ] E →L[ℝ] E))}
    {B : Fin m → Fin d → E →L[ℝ] E →L[ℝ] E} {idx : Fin m → Fin d → ι}
    {a : ι → X → E} {T : Y → (X → E) → L2 →L[ℂ] L2}
    {P : (X → E) → Prop}
    (h : HasParameterAmplitudeTransfer U w v qs B idx a T P)
    (b : AmplitudeExpression X E ι) (hb : P (b.evaluate a))
    (f : Y → L2) (df : Fin d → Y → L2) (pf : Y → L2) (i : Fin m)
    (t : Y) (ht : t ∈ U)
    (hdf : ∀ j, HasEuclideanL2CoordinateDerivative j (f t) (df j t))
    (hpf : HasLineDerivAt ℝ f (pf t) t (w i)) :
    lineDeriv ℝ (fun u => T u (b.evaluate a) (f u)) t (w i) =
      T t ((b.divergenceTransfer (v i) (qs i)).evaluate a) (f t) +
        ∑ j, T t ((b.coefficientProduct (B i j) (idx i j)).evaluate a) (df j t) +
        T t (b.evaluate a) (pf t) :=
  (h b hb f df pf i t ht hdf hpf).lineDeriv

end JanetCartan.IsometricEmbedding.Response.NearCarrier
