module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives.FourierTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeakDerivatives.WeightComparison

/-!
# Full mixed weak derivatives of physical carrier data

The weak derivative predicates and finite families use the literal initial
product-measure L² classes and all `3 + (n - 1)` physical directions from
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`.
The full initial Fourier transform commutes with the Euclidean identification,
so physical finite energy is equivalent to existence of these actual weak
derivatives, with no additional transport premise. The imported multiplier
identities retain the physical `2π i` factor in every coordinate.

Writing `A` for the sum of the L² norms of all ordered derivatives through
order `s`, we prove `physicalSobolevNorm s f ≤ (4π)^s A` and
`A ≤ (1 + 2π (3 + (n - 1)))^s physicalSobolevNorm s f`. This supplies the
mixed-derivative characterization needed to construct the carrier summands
of `X^s` in `app:ch_background:eq:bg-r-inverse`.
-/

@[expose] public noncomputable section

namespace JanetCartan.CarrierSobolev
open ContinuumRow Pseudodifferential

variable {n s : ℕ}

/-- The physical finite-energy predicate equals standard Euclidean Sobolev
membership in the full initial coordinate chart. Fourier transport is proved,
not assumed, for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`. -/
theorem memPhysicalSobolev_iff_memFourierSobolev (s : ℕ) (f : CarrierL2 n) :
    MemPhysicalSobolev s f ↔ MemFourierSobolev (s : ℝ) (flatInitialL2Equiv n f) :=
  memPhysicalSobolev_iff_memFourierSobolev_of_fourierTransport s f
    (flatInitialL2Equiv_initialFourier n f)

/-- The Euclidean Fourier norm is bounded by the full physical norm, under
finite energy, for the carrier summands of `app:ch_background:eq:bg-r-inverse`. -/
theorem fourierSobolevNorm_le_physicalSobolevNorm (s : ℕ) (f : CarrierL2 n)
    (hf : MemPhysicalSobolev s f) :
    fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) ≤ physicalSobolevNorm s f :=
  fourierSobolevNorm_le_physicalSobolevNorm_of_fourierTransport s f
    (flatInitialL2Equiv_initialFourier n f) hf

/-- The unit-period Fourier convention costs at most `(2π)^s` when comparing
the full physical norm with the Euclidean Bessel norm, for
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-inverse`. -/
theorem physicalSobolevNorm_le_mul_fourierSobolevNorm (s : ℕ) (f : CarrierL2 n)
    (hf : MemPhysicalSobolev s f) :
    physicalSobolevNorm s f ≤
      (2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) :=
  physicalSobolevNorm_le_mul_fourierSobolevNorm_of_fourierTransport s f
    (flatInitialL2Equiv_initialFourier n f) hf

/-- Physical carrier Sobolev membership is equivalent to existence of all
mixed weak coordinate derivatives through order `s` as literal product-measure
L² classes, for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:prop:bg-inverse`. The derivative predicate contains only
distributional identities, and retains all `3 + (n - 1)` directions. -/
theorem memPhysicalSobolev_iff_exists_carrierL2Derivatives (s : ℕ) (f : CarrierL2 n) :
    MemPhysicalSobolev s f ↔
      ∃ v : CarrierL2DerivativeFamily n s, HasCarrierL2Derivatives s f v :=
  (memPhysicalSobolev_iff_memFourierSobolev s f).trans
    (exists_carrierL2Derivatives_iff_memFourierSobolev f).symm

/-- Full physical finite energy constructs every mixed weak derivative needed
by `app:ch_background:prop:bg-adjoint`, as classes on the original measure. -/
theorem MemPhysicalSobolev.exists_carrierL2Derivatives {f : CarrierL2 n}
    (hf : MemPhysicalSobolev s f) :
    ∃ v : CarrierL2DerivativeFamily n s, HasCarrierL2Derivatives s f v :=
  (memPhysicalSobolev_iff_exists_carrierL2Derivatives s f).mp hf

/-- All actual mixed L² derivatives imply full physical finite energy;
membership is a conclusion for `app:ch_background:prop:bg-adjoint`. -/
theorem HasCarrierL2Derivatives.memPhysicalSobolev
    {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) : MemPhysicalSobolev s f :=
  (memPhysicalSobolev_iff_exists_carrierL2Derivatives s f).mpr ⟨v, h⟩

/-- The actual mixed derivative norms bound the physical Sobolev norm with an
explicit order constant, for `app:ch_background:eq:bg-r-inverse`. Finite energy
follows from the distributional identities and is not an extra hypothesis. -/
theorem HasCarrierL2Derivatives.physicalSobolevNorm_le
    {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) :
    physicalSobolevNorm s f ≤ (4 * Real.pi) ^ s * carrierL2DerivativeNormSum v := by
  calc
    _ ≤ (2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) (flatInitialL2Equiv n f) :=
      physicalSobolevNorm_le_mul_fourierSobolevNorm s f h.memPhysicalSobolev
    _ ≤ (2 * Real.pi) ^ s * ((2 : ℝ) ^ s * carrierL2DerivativeNormSum v) :=
      mul_le_mul_of_nonneg_left h.flatFourierSobolevNorm_le (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; congr 2; ring

/-- The physical Sobolev norm controls the finite sum of every actual mixed
derivative norm, for `app:ch_background:prop:bg-adjoint`. The constant depends
only on the order and full initial dimension. -/
theorem HasCarrierL2Derivatives.normSum_le_physicalSobolevNorm
    {f : CarrierL2 n} {v : CarrierL2DerivativeFamily n s}
    (h : HasCarrierL2Derivatives s f v) :
    carrierL2DerivativeNormSum v ≤
      (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s * physicalSobolevNorm s f :=
  h.normSum_le_flatFourierSobolevNorm.trans (mul_le_mul_of_nonneg_left
    (fourierSobolevNorm_le_physicalSobolevNorm s f h.memPhysicalSobolev) (by positivity))

/-- Both constants in the physical mixed-derivative comparison are strictly
positive at every order, including zero, for `app:ch_background:eq:bg-r-inverse`. -/
theorem physicalDerivative_norm_constants_pos (n s : ℕ) :
    0 < (4 * Real.pi) ^ s ∧ 0 < (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s := by
  constructor <;> positivity

/-- Quantitative characterization for the carrier summands of `X^s` in
`app:ch_background:eq:bg-r-inverse` and `app:ch_background:eq:bg-density-adjoint`:
physical membership constructs actual mixed derivatives, the empty derivative
is the original class, and their finite norm sum is comparable in both
directions with the physical norm. No Fourier transport premise remains. -/
theorem MemPhysicalSobolev.exists_carrierL2Derivatives_norm_bounds {f : CarrierL2 n}
    (hf : MemPhysicalSobolev s f) :
    ∃ v : CarrierL2DerivativeFamily n s,
      HasCarrierL2Derivatives s f v ∧ v (.empty (3 + (n - 1)) s) = f ∧
      physicalSobolevNorm s f ≤ (4 * Real.pi) ^ s * carrierL2DerivativeNormSum v ∧
      carrierL2DerivativeNormSum v ≤
        (1 + 2 * Real.pi * (3 + (n - 1) : ℕ)) ^ s * physicalSobolevNorm s f := by
  obtain ⟨v, hv⟩ := hf.exists_carrierL2Derivatives
  exact ⟨v, hv, hv.root, hv.physicalSobolevNorm_le, hv.normSum_le_physicalSobolevNorm⟩

end JanetCartan.CarrierSobolev
