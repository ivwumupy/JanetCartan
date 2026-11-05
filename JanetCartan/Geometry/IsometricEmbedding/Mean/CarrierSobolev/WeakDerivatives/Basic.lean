module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Levels
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives

/-!
# Actual mixed weak derivatives of carrier L² classes

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
we use Mathlib's tempered-distribution derivative after the explicit ordered
Euclidean coordinate identification. The coordinate formulas in `Coordinates`
identify these with all three carrier directions and all transverse directions.
Each entry of a derivative family is an L² class for the literal product measure.
The predicate contains only distributional derivative identities.

The bridge to `MemPhysicalSobolev` still requires commuting the full Fourier
transform with the coordinate identification and comparing the two weights.
The results here reuse the established Euclidean theorem without asserting that
this remaining bridge has been proved.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap LineDeriv

namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

variable {n s : ℕ}

/-- All ordered coordinate words of length at most `s`, including the empty
word, for `app:ch_background:prop:bg-adjoint`. The coordinate list has length
`3 + (n - 1)`, including all the carrier directions. -/
abbrev CarrierDerivativeIndex (n s : ℕ) := EuclideanDerivativeIndex (3 + (n - 1)) s

/-- Actual mixed derivative representatives on `(ds dv) dy` for
`app:ch_background:prop:bg-adjoint`. -/
abbrev CarrierL2DerivativeFamily (n s : ℕ) := CarrierDerivativeIndex n s → CarrierL2 n

/-- A weak coordinate derivative in the full physical coordinate list,
for `app:ch_background:prop:bg-adjoint`. This is equality of distributions,
not a Fourier moment assumption. -/
def HasCarrierL2CoordinateDerivative (i : Fin (3 + (n - 1))) (f g : CarrierL2 n) : Prop :=
  HasEuclideanL2CoordinateDerivative i (flatInitialL2Equiv n f) (flatInitialL2Equiv n g)

/-- Distributional compatibility of all mixed derivatives through order `s`,
for `app:ch_background:prop:bg-adjoint`. Every family entry is a literal carrier
L² class; the zero-order entry is the original input. -/
def HasCarrierL2Derivatives (s : ℕ) (f : CarrierL2 n)
    (v : CarrierL2DerivativeFamily n s) : Prop :=
  HasEuclideanL2Derivatives s (flatInitialL2Equiv n f) (fun w => flatInitialL2Equiv n (v w))

/-- Sum of the physical L² norms of all mixed derivatives, for the norm
comparison required by `app:ch_background:prop:bg-adjoint`. -/
def carrierL2DerivativeNormSum (v : CarrierL2DerivativeFamily n s) : ℝ := ∑ w, ‖v w‖

/-- Weak derivatives are unique as classes on the literal carrier product
measure, for `app:ch_background:prop:bg-adjoint`. -/
theorem HasCarrierL2CoordinateDerivative.unique {i : Fin (3 + (n - 1))}
    {f g h : CarrierL2 n} (hg : HasCarrierL2CoordinateDerivative i f g)
    (hh : HasCarrierL2CoordinateDerivative i f h) : g = h :=
  (flatInitialL2Equiv n).injective (HasEuclideanL2CoordinateDerivative.unique hg hh)

/-- The distributional definition gives integration by parts against every
Schwartz test, in particular every compact smooth test. This spells out the
weak derivative meaning used in `app:ch_background:prop:bg-adjoint`. -/
theorem hasCarrierL2CoordinateDerivative_iff_test
    (i : Fin (3 + (n - 1))) (f g : CarrierL2 n) :
    HasCarrierL2CoordinateDerivative i f g ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin (3 + (n - 1))), ℂ),
        (∫ x, φ x • flatInitialL2Equiv n g x) =
          -(∫ x, (∂_{EuclideanSpace.basisFun (Fin (3 + (n - 1))) ℝ i} φ) x •
            flatInitialL2Equiv n f x) := by
  constructor
  · intro h φ
    have he := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin (3 + (n - 1))), ℂ) => T φ) h
    simpa only [euclideanCoordinateDerivative, TemperedDistribution.lineDerivOp_apply_apply,
      Lp.toTemperedDistribution_apply, neg_apply, neg_smul, integral_neg] using he.symm
  · intro h
    change euclideanCoordinateDerivative i (flatInitialL2Equiv n f) = _
    ext φ
    simpa only [euclideanCoordinateDerivative, TemperedDistribution.lineDerivOp_apply_apply,
      Lp.toTemperedDistribution_apply, neg_apply, neg_smul, integral_neg] using (h φ).symm

/-- The derivative family includes the original physical class at order zero,
for `app:ch_background:prop:bg-adjoint`. -/
theorem HasCarrierL2Derivatives.root {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) : v (.empty (3 + (n - 1)) s) = f :=
  (flatInitialL2Equiv n).injective (HasEuclideanL2Derivatives.root h)

/-- Order zero is exactly equality with the physical input, for
`app:ch_background:prop:bg-adjoint`. -/
theorem hasCarrierL2Derivatives_zero_iff (f : CarrierL2 n)
    (v : CarrierL2DerivativeFamily n 0) : HasCarrierL2Derivatives 0 f v ↔ v () = f :=
  (flatInitialL2Equiv n).injective.eq_iff

/-- The branches are actual coordinate weak derivatives, each with its own
mixed derivatives through the remaining order. This is the full recursion
required in `app:ch_background:prop:bg-adjoint`. -/
theorem hasCarrierL2Derivatives_succ_iff (f : CarrierL2 n)
    (v : CarrierL2DerivativeFamily n (s + 1)) :
    HasCarrierL2Derivatives (s + 1) f v ↔ v none = f ∧
      ∀ i : Fin (3 + (n - 1)),
        HasCarrierL2CoordinateDerivative i f (v (some (i, .empty (3 + (n - 1)) s))) ∧
        HasCarrierL2Derivatives s (v (some (i, .empty (3 + (n - 1)) s)))
          (fun w => v (some (i, w))) := by
  simp only [HasCarrierL2Derivatives, HasEuclideanL2Derivatives,
    HasCarrierL2CoordinateDerivative, (flatInitialL2Equiv n).injective.eq_iff]

/-- Truncating the mixed derivative budget preserves actual derivative
identities, for `app:ch_background:prop:bg-adjoint`. -/
theorem HasCarrierL2Derivatives.truncate {f : CarrierL2 n}
    {v : CarrierL2DerivativeFamily n (s + 1)} (h : HasCarrierL2Derivatives (s + 1) f v) :
    HasCarrierL2Derivatives s f (fun w => v w.raise) :=
  HasEuclideanL2Derivatives.truncate h

/-- Every entry is the indicated iterated distributional derivative, for
`app:ch_background:prop:bg-adjoint`. -/
theorem HasCarrierL2Derivatives.toTemperedDistribution
    {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) (w : CarrierDerivativeIndex n s) :
    euclideanIteratedCoordinateDerivative w
        (flatInitialL2Equiv n f : 𝓢'(EuclideanSpace ℝ (Fin (3 + (n - 1))), ℂ)) =
      (flatInitialL2Equiv n (v w) : 𝓢'(EuclideanSpace ℝ (Fin (3 + (n - 1))), ℂ)) :=
  HasEuclideanL2Derivatives.toTemperedDistribution h w

/-- The finite derivative aggregate has exactly the Euclidean normalization,
for `app:ch_background:prop:bg-adjoint`. -/
theorem carrierL2DerivativeNormSum_eq_euclidean (v : CarrierL2DerivativeFamily n s) :
    carrierL2DerivativeNormSum v =
      euclideanL2DerivativeNormSum (fun w => flatInitialL2Equiv n (v w)) := by
  simp [carrierL2DerivativeNormSum, euclideanL2DerivativeNormSum_eq_sum]

/-- Nonnegativity of the actual finite derivative norm aggregate, for
`app:ch_background:prop:bg-adjoint`. -/
theorem carrierL2DerivativeNormSum_nonneg (v : CarrierL2DerivativeFamily n s) :
    0 ≤ carrierL2DerivativeNormSum v :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- Existence of every mixed weak derivative is exactly Euclidean Sobolev
membership after the explicit coordinate identification, for
`app:ch_background:prop:bg-adjoint`. Identifying this membership with the
published physical Fourier weight is a separate bridge. -/
theorem exists_carrierL2Derivatives_iff_memFourierSobolev (f : CarrierL2 n) :
    (∃ v : CarrierL2DerivativeFamily n s, HasCarrierL2Derivatives s f v) ↔
      MemFourierSobolev (s : ℝ) (flatInitialL2Equiv n f) := by
  constructor
  · rintro ⟨v, hv⟩
    exact HasEuclideanL2Derivatives.memFourierSobolev hv
  · intro h
    obtain ⟨v, hv⟩ := h.exists_integerDerivatives
    refine ⟨fun w => (flatInitialL2Equiv n).symm (v w), ?_⟩
    simpa only [HasCarrierL2Derivatives, LinearIsometryEquiv.apply_symm_apply] using hv

/-- The actual mixed derivative norms bound the standard Euclidean Fourier
norm in the physical coordinate chart, for `app:ch_background:prop:bg-adjoint`.
The extra comparison with `physicalSobolevNorm` is not assumed here. -/
theorem HasCarrierL2Derivatives.flatFourierSobolevNorm_le
    {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) :
    fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) ≤
      (2 : ℝ) ^ s * carrierL2DerivativeNormSum v := by
  rw [carrierL2DerivativeNormSum_eq_euclidean]
  exact HasEuclideanL2Derivatives.fourierSobolevNorm_le h

/-- The standard Euclidean Fourier norm controls all actual mixed derivative
norms, with an explicit dimension constant, for
`app:ch_background:prop:bg-adjoint`. -/
theorem HasCarrierL2Derivatives.normSum_le_flatFourierSobolevNorm
    {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) :
    carrierL2DerivativeNormSum v ≤
      (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s *
        fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) := by
  rw [carrierL2DerivativeNormSum_eq_euclidean]
  exact HasEuclideanL2Derivatives.normSum_le_fourierSobolevNorm h

end JanetCartan.CarrierSobolev
