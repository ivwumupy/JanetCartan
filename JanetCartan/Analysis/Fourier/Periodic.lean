module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Periodic fields and Fourier conventions

Shared conventions for the analytic constructions of paper.tex. We use the unit torus;
its physical frequencies are 2π times integer vectors. Real Fourier coefficients are
stored as a pair of real vectors, avoiding a choice of complexification of the codomain.

These are definitions on smooth functions, not a replacement for completed Sobolev spaces.
Statements using the real-valued Fourier sum must establish its summability.
-/

@[expose] public noncomputable section

open scoped ContDiff
open MeasureTheory

namespace JanetCartan

/-- The fixed auxiliary torus. -/
abbrev Torus (n : ℕ) := UnitAddTorus (Fin n)

/-- The quotient from coordinate space to the auxiliary torus. -/
def torusQuotient {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Torus n :=
  fun i ↦ (x i : AddCircle (1 : ℝ))

/-- A periodic Euclidean lift. -/
def periodicLift {n : ℕ} {F : Type*} (f : Torus n → F) :
    EuclideanSpace ℝ (Fin n) → F :=
  f ∘ torusQuotient

/-- A closed fundamental cell, centered so the physical chart lies in its interior. -/
def fundamentalCell (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 1 / 2}

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness of a periodic field, with continuity on the quotient explicit. -/
def IsSmoothPeriodic (f : Torus n → F) : Prop :=
  Continuous f ∧ ContDiff ℝ ∞ (periodicLift f)

/-- The L² norm for the normalized Haar measure of the unit torus. -/
def periodicL2Norm (f : Torus n → F) : ℝ :=
  Real.sqrt (∫ x : Torus n, ‖f x‖ ^ 2)

/-- Real and imaginary parts of the normalized Fourier coefficient. -/
def periodicFourierCoeff (f : Torus n → F) (k : Fin n → ℤ) : F × F :=
  (∫ x : Torus n, (UnitAddTorus.mFourier (-k) x).re • f x,
   ∫ x : Torus n, (UnitAddTorus.mFourier (-k) x).im • f x)

/-- Physical frequency in the unit-period convention. -/
def frequencyNorm (k : Fin n → ℤ) : ℝ :=
  2 * Real.pi * ‖(WithLp.toLp 2 (fun i ↦ (k i : ℝ)) : EuclideanSpace ℝ (Fin n))‖

/-- Exact Fourier support below a given physical frequency. -/
def HasFourierSupport (L : ℝ) (f : Torus n → F) : Prop :=
  ∀ k : Fin n → ℤ, L < frequencyNorm k → periodicFourierCoeff f k = 0

/-- Fourier Sobolev size for smooth fields; use only when the series is summable.

For a Hilbert codomain this is the Bessel-potential norm on the unit torus.
-/
def periodicSobolevNorm (s : ℝ) (f : Torus n → F) : ℝ :=
  Real.sqrt (∑' k : Fin n → ℤ,
    (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2))

end JanetCartan
