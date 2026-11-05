module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.BesselAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Operators

/-!
# Ordered derivatives commute with the constant image factors

The ordered operators used in the inverse bootstrap commute with the literal
`J` and `Dᵢ J` factors on every Sobolev datum. These identities supply the
constant-factor branches in `app:ch_background:eq:bg-commutator`.
-/

public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open ContinuumRow PeriodicSobolevSpace

variable {n : ℕ}

private theorem reverseDerivativeToL2_besselSobolev (s : ℕ) (is : List (Fin n))
    (h : is.length ≤ s) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    Exterior.reverseDerivativeToL2 s is h (besselSobolev s u) =
      periodicBesselInverse (Exterior.reverseDerivativeToL2 s is h u) := by
  induction s generalizing is with
  | zero =>
    have he : is = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst is
    exact toL2_besselSobolev 0 u
  | succ s ih =>
    cases is with
    | nil => exact toL2_besselSobolev (s + 1) u
    | cons i is =>
      simp only [Exterior.reverseDerivativeToL2, ContinuousLinearMap.comp_apply,
        coordinateDerivative_besselSobolev, ih]

private theorem reverseDerivativeToL2_derivativeBesselSobolev (s : ℕ) (j : Fin n)
    (is : List (Fin n)) (h : is.length ≤ s)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    Exterior.reverseDerivativeToL2 s is h (derivativeBesselSobolev s j u) =
      derivativeBessel j (Exterior.reverseDerivativeToL2 s is h u) := by
  induction s generalizing is with
  | zero =>
    have he : is = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst is
    exact toL2_derivativeBesselSobolev 0 j u
  | succ s ih =>
    cases is with
    | nil => exact toL2_derivativeBesselSobolev (s + 1) j u
    | cons i is =>
      simp only [Exterior.reverseDerivativeToL2, ContinuousLinearMap.comp_apply,
        coordinateDerivative_derivativeBesselSobolev, ih]

/-- Every ordered lower derivative commutes with the same Bessel inverse
(`app:ch_background:eq:bg-commutator`). -/
theorem derivativeToL2_besselSobolev (s : ℕ) (is : List (Fin n))
    (h : is.length ≤ s) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    Exterior.derivativeToL2 s is h (besselSobolev s u) =
      periodicBesselInverse (Exterior.derivativeToL2 s is h u) :=
  reverseDerivativeToL2_besselSobolev s is.reverse (by simpa using h) u

/-- Every ordered lower derivative commutes with the actual `Dⱼ J` factor
(`app:ch_background:eq:bg-commutator`). -/
theorem derivativeToL2_derivativeBesselSobolev (s : ℕ) (j : Fin n)
    (is : List (Fin n)) (h : is.length ≤ s)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    Exterior.derivativeToL2 s is h (derivativeBesselSobolev s j u) =
      derivativeBessel j (Exterior.derivativeToL2 s is h u) :=
  reverseDerivativeToL2_derivativeBesselSobolev s j is.reverse (by simpa using h) u

/-- Negating the constructed Sobolev action gives the actual L² adjoint
of `Dⱼ J` at every order (`app:ch_background:eq:bg-commutator`). -/
theorem toL2_neg_derivativeBesselSobolev (s : ℕ) (j : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (-derivativeBesselSobolev s j u) = (derivativeBessel j).adjoint (toL2 s u) := by
  rw [map_neg, toL2_derivativeBesselSobolev, derivativeBessel_adjoint, neg_apply]

/-- Ordered derivatives also commute with the literal adjoint factors in
the second half of the normal (`app:ch_background:eq:bg-commutator`). -/
theorem derivativeToL2_neg_derivativeBesselSobolev (s : ℕ) (j : Fin n)
    (is : List (Fin n)) (h : is.length ≤ s)
    (u : PeriodicSobolevSpace n (Euclidean n) s) :
    Exterior.derivativeToL2 s is h (-derivativeBesselSobolev s j u) =
      (derivativeBessel j).adjoint (Exterior.derivativeToL2 s is h u) := by
  rw [map_neg, derivativeToL2_derivativeBesselSobolev, derivativeBessel_adjoint, neg_apply]

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
