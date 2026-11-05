module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient.Translation

/-!
# Difference-quotient identities on the actual periodic L² space

The algebra needed to estimate `E δₕ v` in `app:ch_background:prop:bg-inverse`.
These identities do not require an H¹ assumption on `v`. The uniform bound for
the divided conjugation operator must still be established from the full PDO
amplitude and its primitive bounds.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual divided conjugation difference, with the positive-shift convention
of `periodicL2Translation` (`app:ch_background:prop:bg-inverse`). -/
def periodicConjugationDifference (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
    (i : Fin n) (h : ℝ) : PeriodicL2 n F →L[ℝ] PeriodicL2 n F :=
  h⁻¹ • ((periodicL2Translation (periodicCoordinateShift i h)).toContinuousLinearMap.comp
    (E.comp (periodicL2Translation (-periodicCoordinateShift i h)).toContinuousLinearMap) - E)

/-- Factoring the commutator leaves a translation on the input. This is why the
PDO amplitude must translate both physical positions
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicL2DifferenceQuotient_commutator
    (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F) (i : Fin n) (h : ℝ)
    (v : PeriodicL2 n F) :
    periodicL2DifferenceQuotient i h (E v) - E (periodicL2DifferenceQuotient i h v) =
      periodicConjugationDifference E i h (periodicL2Translation (periodicCoordinateShift i h) v) := by
  have hinv : periodicL2Translation (-periodicCoordinateShift i h)
      (periodicL2Translation (periodicCoordinateShift i h) v) = v := by
    rw [← periodicL2Translation_add, neg_add_cancel, periodicL2Translation_zero]
  change h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h) (E v) - E v) -
    E (h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h) v - v)) =
      h⁻¹ • (periodicL2Translation (periodicCoordinateShift i h)
        (E (periodicL2Translation (-periodicCoordinateShift i h)
          (periodicL2Translation (periodicCoordinateShift i h) v))) -
        E (periodicL2Translation (periodicCoordinateShift i h) v))
  rw [hinv, map_smul, map_sub]
  module

/-- The identity used before applying the coercive L² estimate in
`app:ch_background:prop:bg-inverse`. No derivative of the unknown inverse output
is taken. -/
theorem periodic_operator_differenceQuotient_eq
    (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F) (i : Fin n) (h : ℝ)
    (v : PeriodicL2 n F) :
    E (periodicL2DifferenceQuotient i h v) =
      periodicL2DifferenceQuotient i h (E v) -
        periodicConjugationDifference E i h (periodicL2Translation (periodicCoordinateShift i h) v) := by
  rw [← periodicL2DifferenceQuotient_commutator]
  abel

/-- The exact norm inequality to which the PDO estimate is applied in
`app:ch_background:prop:bg-inverse`. This alone makes no uniform-in-step claim. -/
theorem norm_periodic_operator_differenceQuotient_le
    (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F) (i : Fin n) (h : ℝ)
    (v : PeriodicL2 n F) :
    ‖E (periodicL2DifferenceQuotient i h v)‖ ≤
      ‖periodicL2DifferenceQuotient i h (E v)‖ + ‖periodicConjugationDifference E i h‖ * ‖v‖ := by
  rw [periodic_operator_differenceQuotient_eq]
  have hb := (periodicConjugationDifference E i h).le_opNorm
    (periodicL2Translation (periodicCoordinateShift i h) v)
  rw [norm_periodicL2Translation] at hb
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) hb)

end JanetCartan.ContinuumCommutator
