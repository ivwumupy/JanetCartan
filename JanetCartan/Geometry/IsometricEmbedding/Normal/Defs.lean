module

public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# Tangential and normal variations

The coordinate connection is that of the induced metric, as in Section 2.
These definitions do not require a separate choice of normal frame.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius
open Set

namespace JanetCartan

/-- The Christoffel coefficients of the induced metric. -/
def christoffel {n N : ℕ} (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (inducedMetric F x)⁻¹ k l *
    (partialDeriv (fun y ↦ inducedMetric F y j l) x i +
      partialDeriv (fun y ↦ inducedMetric F y i l) x j -
      partialDeriv (fun y ↦ inducedMetric F y i j) x l)

/-- The symmetrized covariant derivative of a covector field for the induced metric. -/
def symmCovariantDeriv {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) : MetricField n :=
  fun x i j ↦
    (partialDeriv (fun y ↦ u y j) x i + partialDeriv (fun y ↦ u y i) x j) / 2 -
      ∑ k, christoffel F x i j k * u x k

/-- Raising a covector with the induced metric and applying dF. -/
def tangentLift {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) : Euclidean n → Euclidean N :=
  fun x ↦ ∑ i, ∑ j, ((inducedMetric F x)⁻¹ i j * u x j) • partialDeriv F x i

/-- Pairing an ambient field with the second fundamental form. -/
def normalPairing {n N : ℕ} (F w : Euclidean n → Euclidean N) : MetricField n :=
  fun x i j ↦ inner ℝ (w x) (secondFundamentalForm F x i j)

end JanetCartan
