module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Basic
public import JanetCartan.Analysis.Fourier.Periodic.Deriv

/-!
# Exact derivative bounds under compact-amplitude periodization

For `app:ch_osc:lem:osc-amplitude`, periodization preserves each physical
coordinate derivative bound with the same constant. The local comparison also
applies to the full iterated Fréchet derivatives on the closed cell.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ContDiff

namespace JanetCartan.AmplitudeBound

variable {n : ℕ}

/-- Ordered Euclidean coordinate derivatives for the physical amplitude in
`app:ch_osc:lem:osc-amplitude`, using the same order as `periodicCoordinateDerivList`. -/
def euclideanCoordinateDerivList :
    List (Fin n) → (EuclideanSpace ℝ (Fin n) → ℂ) → EuclideanSpace ℝ (Fin n) → ℂ
  | [], f => f
  | i :: is, f => fun x ↦ fderiv ℝ (euclideanCoordinateDerivList is f) x
      (EuclideanSpace.single i 1)

/-- All ordered derivatives of a smooth physical amplitude are smooth
(`app:ch_osc:lem:osc-amplitude`). -/
theorem contDiff_euclideanCoordinateDerivList {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : ContDiff ℝ ∞ f) (is : List (Fin n)) :
    ContDiff ℝ ∞ (euclideanCoordinateDerivList is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- Local agreement of amplitudes implies local agreement of every ordered
physical derivative (`app:ch_osc:lem:osc-amplitude`). -/
theorem euclideanCoordinateDerivList_eventuallyEq
    {f g : EuclideanSpace ℝ (Fin n) → ℂ} {x : EuclideanSpace ℝ (Fin n)}
    (h : f =ᶠ[𝓝 x] g) (is : List (Fin n)) :
    euclideanCoordinateDerivList is f =ᶠ[𝓝 x] euclideanCoordinateDerivList is g := by
  induction is with
  | nil => exact h
  | cons i is ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun y hy ↦
      congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ ↦ L (EuclideanSpace.single i 1)) hy

/-- The ordered torus derivatives lift to the ordered physical derivatives
(`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_coordinateDerivList_eq {f : Torus n → ℂ}
    (hf : IsSmoothPeriodic f) (is : List (Fin n)) :
    periodicLift (periodicCoordinateDerivList is f) =
      euclideanCoordinateDerivList is (periodicLift f) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [periodicCoordinateDerivList, periodicLift_coordinateDeriv (hf.coordinateDerivList is).2,
      ih]
    rfl

/-- Every ordered derivative agrees with the original amplitude's derivative
throughout the closed cell (`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_coordinateDerivList_amplitudePeriodization_eq {r : ℝ}
    (hr : r < 1 / 2) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : SupportedInCenteredBox r f) (hf : ContDiff ℝ ∞ f)
    (is : List (Fin n)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ fundamentalCell n) :
    periodicLift (periodicCoordinateDerivList is (amplitudePeriodization f)) x =
      euclideanCoordinateDerivList is f x := by
  rw [periodicLift_coordinateDerivList_eq (isSmoothPeriodic_amplitudePeriodization hr hs hf)]
  exact (euclideanCoordinateDerivList_eventuallyEq
    (periodicLift_amplitudePeriodization_eventuallyEq hr hs hx) is).self_of_nhds

/-- Differentiation commutes with compact-amplitude periodization
(`app:ch_osc:lem:osc-amplitude`). -/
theorem coordinateDerivList_amplitudePeriodization {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    (hf : ContDiff ℝ ∞ f) (is : List (Fin n)) :
    periodicCoordinateDerivList is (amplitudePeriodization f) =
      amplitudePeriodization (euclideanCoordinateDerivList is f) := by
  funext z
  have h := periodicLift_coordinateDerivList_amplitudePeriodization_eq hr hs hf is
    (centeredTorusRepresentative_mem z)
  simpa only [periodicLift, Function.comp_apply, torusQuotient_centeredTorusRepresentative,
    amplitudePeriodization] using h

/-- A bound on any mixed coordinate derivative transfers without loss of the
constant (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_coordinateDerivList_amplitudePeriodization_le {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    (hf : ContDiff ℝ ∞ f) (is : List (Fin n)) {A : ℝ}
    (hA : ∀ x, ‖euclideanCoordinateDerivList is f x‖ ≤ A) (z : Torus n) :
    ‖periodicCoordinateDerivList is (amplitudePeriodization f) z‖ ≤ A := by
  rw [coordinateDerivList_amplitudePeriodization hr hs hf]
  exact norm_amplitudePeriodization_le hA z

/-- Uniform pure derivative bounds through any specified finite order are
preserved for the entire parameter family (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_pureDeriv_amplitudePeriodization_le {X : Type*} {r : ℝ} (hr : r < 1 / 2)
    {b : X → EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ))
    (N : ℕ) (A : ℕ → ℝ)
    (hA : ∀ ξ k, k ≤ N → ∀ i x,
      ‖euclideanCoordinateDerivList (List.replicate k i) (b ξ) x‖ ≤ A k) :
    ∀ ξ k, k ≤ N → ∀ i z,
      ‖periodicCoordinateDerivList (List.replicate k i) (amplitudePeriodization (b ξ)) z‖ ≤
        A k := by
  intro ξ k hk i z
  exact norm_coordinateDerivList_amplitudePeriodization_le hr (hs ξ) (hb ξ)
    (List.replicate k i) (hA ξ k hk i) z

/-- The full iterated Fréchet derivatives agree on the closed cell, even without
a smoothness assumption, by local equality (`app:ch_osc:lem:osc-amplitude`). -/
theorem iteratedFDeriv_periodicLift_amplitudePeriodization_eq {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f) (k : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ fundamentalCell n) :
    iteratedFDeriv ℝ k (periodicLift (amplitudePeriodization f)) x =
      iteratedFDeriv ℝ k f x :=
  ((periodicLift_amplitudePeriodization_eventuallyEq hr hs hx).iteratedFDeriv ℝ k).self_of_nhds

/-- Full Fréchet derivative bounds also transfer globally with their original
constant (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_iteratedFDeriv_amplitudePeriodization_le {r : ℝ} (hr : r < 1 / 2)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hs : SupportedInCenteredBox r f)
    (k : ℕ) {A : ℝ} (hA : ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (periodicLift (amplitudePeriodization f)) x‖ ≤ A := by
  apply norm_iteratedFDeriv_periodicLift_le
  intro y hy
  rw [iteratedFDeriv_periodicLift_amplitudePeriodization_eq hr hs k hy]
  exact hA y

end JanetCartan.AmplitudeBound
