module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Coefficients
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Extension

/-!
# Weak derivative characterization of consecutive Sobolev levels

The distributional induction in `app:ch_background:prop:bg-inverse` uses the
equivalence between one additional Fourier Sobolev order and coordinate weak
derivatives in the preceding order. Existence comes from smooth density and
completeness; the converse comes from the physical Fourier symbols.
-/

@[expose] public noncomputable section

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- One more Sobolev order is equivalent to membership in the preceding order
and existence of all coordinate weak derivatives in that order
(`app:ch_background:prop:bg-inverse`). -/
theorem mem_periodicSobolevLevel_succ_iff (s : ℕ) (u : PeriodicL2 n F) :
    u ∈ periodicSobolevLevel n F (s + 1) ↔
      u ∈ periodicSobolevLevel n F s ∧
        ∀ i : Fin n, ∃ v : PeriodicL2 n F,
          v ∈ periodicSobolevLevel n F s ∧ HasPeriodicWeakDerivative i u v := by
  constructor
  · exact exists_periodicWeakDerivatives_of_mem_succ s u
  · rintro ⟨hu, hv⟩
    choose v hv hd using hv
    exact mem_periodicSobolevLevel_succ_of_weakDerivatives hu hv hd

/-- At order one the preceding-level condition is automatic by Parseval
(`app:ch_background:prop:bg-inverse`). -/
theorem mem_periodicSobolevLevel_one_iff_weakDerivatives (u : PeriodicL2 n F) :
    u ∈ periodicSobolevLevel n F 1 ↔
      ∀ i : Fin n, ∃ v : PeriodicL2 n F, HasPeriodicWeakDerivative i u v := by
  simp only [mem_periodicSobolevLevel_succ_iff,
    periodicSobolevLevel_zero, Submodule.mem_top, true_and]

/-- A weak derivative of an `H^(s+1)` field automatically belongs to `H^s`:
uniqueness identifies it with the derivative constructed by completion
(`app:ch_background:prop:bg-inverse`). -/
theorem HasPeriodicWeakDerivative.mem_periodicSobolevLevel {s : ℕ} {i : Fin n}
    {u v : PeriodicL2 n F} (h : HasPeriodicWeakDerivative i u v)
    (hu : u ∈ periodicSobolevLevel n F (s + 1)) :
    v ∈ periodicSobolevLevel n F s := by
  obtain ⟨w, hw, hd⟩ := (exists_periodicWeakDerivatives_of_mem_succ s u hu).2 i
  rwa [h.unique hd]

namespace PeriodicSobolevSpace

/-- The completed derivative has exactly the unit-torus `2π` Fourier symbol
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem periodicFourierCoeff_coordinateDerivative (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n F (s + 1)) (k : Fin n → ℤ) :
    periodicFourierCoeff (toL2 s (coordinateDerivative s i u)) k =
      (-(2 * Real.pi * (k i : ℝ)) • (periodicFourierCoeff (toL2 (s + 1) u) k).2,
        (2 * Real.pi * (k i : ℝ)) • (periodicFourierCoeff (toL2 (s + 1) u) k).1) :=
  (hasPeriodicWeakDerivative_coordinateDerivative s i u).periodicFourierCoeff_eq k

end PeriodicSobolevSpace
end JanetCartan
