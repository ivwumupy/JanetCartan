module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.InitialTrade
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Derivatives

/-!
# Concrete recursion for differentiated adjoint amplitudes

Shared definitions for the independent iteration and symbol-bound deductions in
`app:ch_background:prop:bg-adjoint`. The recursion uses the amplitudes of the
proved one-step trades, rather than storing a claimed expansion or bound in a
record. Its relation to iterated derivatives and its quantitative bounds are
separate proof obligations. The initial derivative is physical η multiplication.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow

variable {n : ℕ}

/-- A full scalar amplitude, retaining all carrier, measurement and frequency
variables of `app:ch_background:eq:bg-T`. Vector amplitudes are handled entrywise. -/
abbrev AdjointAmplitude (n : ℕ) :=
  CarrierParameter → Euclidean n → Euclidean (n - 1) → ℂ

/-- Initial or carrier directional differentiation in
`app:ch_background:prop:bg-adjoint`; initial differentiation is in physical `y`. -/
inductive InitialCarrierDerivative (n : ℕ) where
  | initial (direction : Euclidean (n - 1))
  | carrier (direction : CarrierParameter)

/-- The Fourier-side action of a physical derivative in
`app:ch_background:prop:bg-adjoint`. In particular `initial` is multiplication
by `i⟪h,η⟫`, never an η derivative. -/
def applyInitialCarrierDerivative (d : InitialCarrierDerivative n)
    (f : CarrierVariable n → ℂ) (u : CarrierVariable n) : ℂ :=
  match d with
  | .initial h => (Complex.I * (inner ℝ h u.2 : ℂ)) * f u
  | .carrier h => fderiv ℝ (fun z ↦ f (z, u.2)) u.1 h

/-- One term of the actual finite expansion in
`app:ch_background:prop:bg-adjoint`. These fields contain only the constructed
amplitude and the ordered physical derivatives of the datum, not estimates. -/
structure AdjointDerivativeTerm (n : ℕ) where
  amplitude : AdjointAmplitude n
  dataDerivatives : List (Fin n)

/-- The chart integral represented by an expansion term, using the shared
ordered Euclidean coordinate derivatives (`app:ch_background:prop:bg-adjoint`). -/
def AdjointDerivativeTerm.realize (t : AdjointDerivativeTerm n)
    (Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ)
    (v : Euclidean n → ℂ) (u : CarrierVariable n) : ℂ :=
  chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ t.amplitude u.1 x u.2)
    (AmplitudeBound.euclideanCoordinateDerivList t.dataDerivatives v)

/-- The branch leaving the datum derivative count unchanged, for
`app:ch_background:prop:bg-adjoint`. `L z x h` is the measurement direction
transposing `⟪h,η⟫`, and `V z x h` transposes the carrier phase derivative. -/
def zeroBranchAmplitude
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (a : AdjointAmplitude n) : AdjointAmplitude n :=
  fun z x η ↦ match d with
  | .initial h => initialZeroAmplitude (fun y ↦ a z y η) (fun y ↦ L z y h) x
  | .carrier h => carrierZeroAmplitude (fun y ↦ fderiv ℝ (fun w ↦ a w y η) z h)
      (fun y ↦ a z y η) (fun y ↦ V z y h) x

/-- The branch adding one measurement derivative to the datum, for
`app:ch_background:prop:bg-adjoint`. -/
def firstBranchAmplitude
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (a : AdjointAmplitude n) (j : Fin n) :
    AdjointAmplitude n :=
  fun z x η ↦ match d with
  | .initial h => initialFirstAmplitude (fun y ↦ a z y η) (fun y ↦ L z y h) j x
  | .carrier h => carrierFirstAmplitude (fun y ↦ a z y η) (fun y ↦ V z y h) j x

/-- The concrete `n+1` terms obtained by one derivative trade, for
`app:ch_background:prop:bg-adjoint`. -/
def differentiateAdjointTerm
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (t : AdjointDerivativeTerm n) :
    List (AdjointDerivativeTerm n) :=
  ⟨zeroBranchAmplitude L V d t.amplitude, t.dataDerivatives⟩ ::
    List.ofFn (fun j : Fin n ↦
      ⟨firstBranchAmplitude L V d t.amplitude j, j :: t.dataDerivatives⟩)

/-- Recursively constructed amplitudes for every ordered initial/carrier
derivative word in `app:ch_background:prop:bg-adjoint`. The leftmost derivative
acts last, matching `euclideanCoordinateDerivList`. -/
def adjointDerivativeExpansion
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n) :
    List (InitialCarrierDerivative n) → AdjointAmplitude n → List (AdjointDerivativeTerm n)
  | [], a => [⟨a, []⟩]
  | d :: ds, a => (adjointDerivativeExpansion L V ds a).flatMap
      (differentiateAdjointTerm L V d)

/-- One trade adds at most one derivative to the datum, directly from the
constructed branches (`app:ch_background:prop:bg-adjoint`). -/
theorem dataDerivatives_length_le_one_step
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (t q : AdjointDerivativeTerm n)
    (hq : q ∈ differentiateAdjointTerm L V d t) :
    q.dataDerivatives.length ≤ t.dataDerivatives.length + 1 := by
  simp only [differentiateAdjointTerm, List.mem_cons, List.mem_ofFn] at hq
  rcases hq with rfl | ⟨j, rfl⟩ <;> simp

/-- Every constructed term after `s` derivatives has at most `s` derivatives
on the datum (`app:ch_background:prop:bg-adjoint`). No expansion identity or
operator estimate is a premise of this combinatorial statement. -/
theorem dataDerivatives_length_le_expansion
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    t.dataDerivatives.length ≤ ds.length := by
  induction ds generalizing t with
  | nil =>
      simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
      subst t
      simp
  | cons d ds ih =>
      obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
      exact (dataDerivatives_length_le_one_step L V d q t ht).trans
        (Nat.add_le_add_right (ih q hq) 1)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
