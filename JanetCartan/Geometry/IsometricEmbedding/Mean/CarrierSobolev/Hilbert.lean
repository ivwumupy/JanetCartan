module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Density

/-!
# Physical carrier Sobolev Hilbert spaces

For `app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`,
the actual physical finite-energy levels carry their full Fourier Hilbert norm,
with faithful L² injections, compatible contractive level inclusions, and the
isometric identification at order zero. Completeness is proved by constructing
the inverse weighted Fourier map on all of L². Actual compactly supported smooth
functions of all physical `(z,y)` variables belong to every level and are dense
in its full Sobolev norm, including the physical `2π` derivative factor.

The compatibility results below supply dense level inclusions for the parent
construction of the paper's input scale `X^s`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.CarrierSobolev.PhysicalSobolevSpace
open ContinuumRow

variable {n : ℕ}

/-- The same physical compact smooth function realizes compatibly at every
Sobolev order in the input scale of `app:ch_background:prop:bg-adjoint`. -/
@[simp] theorem inclusion_compactSmooth {s t : ℕ} (hst : s ≤ t)
    (φ : CarrierVariable n → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    inclusion hst (compactSmooth t φ hφ hc) = compactSmooth s φ hφ hc := rfl

/-- Higher physical levels are dense in lower ones, because every compact smooth
physical function belongs to every level (`app:ch_background:prop:bg-adjoint`).
This supplies the dense inclusions for the carrier part of `X^s`. -/
theorem denseRange_inclusion {s t : ℕ} (hst : s ≤ t) :
    DenseRange (inclusion (n := n) hst) := by
  apply (denseRange_compactSmooth (n := n) s).mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨compactSmooth t φ.val φ.property.1 φ.property.2,
    inclusion_compactSmooth hst φ.val φ.property.1 φ.property.2⟩

/-- Every physical Sobolev level has dense image in the original L² space,
as required for the carrier input scale in `app:ch_background:prop:bg-inverse`. -/
theorem denseRange_toL2 (s : ℕ) : DenseRange (toL2 (n := n) s) :=
  (zeroEquivL2 (n := n)).surjective.denseRange.comp
    (denseRange_inclusion (Nat.zero_le s)) (zeroEquivL2 (n := n)).continuous

end JanetCartan.CarrierSobolev.PhysicalSobolevSpace
