module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.Compatibility
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder

/-!
# Smooth representatives of all-order local Sobolev classes

For `H^∞` in `app:not:fourier`, restriction-space membership at every integer
order gives a smooth representative on the open domain. At each finite order
we apply `Smooth.FiniteOrder` to that order's whole-space weak extension, then
use `Smooth.Compatibility` to obtain a single representative. No common
extension at all orders is required. The dimension-zero case needs no
regularity assumption: every function on the zero-dimensional Euclidean space
is constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.LocalSobolev

section ZeroDimension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The dimension-zero case of the smooth-representative assertion in
`app:not:fourier`, used in `app:ch_regular:thm:exact-correction`. In this
dimension every local L² class has a constant, hence smooth, representative. -/
theorem exists_contDiffOn_infty_ae_eq_dimension_zero
    (U : Set (EuclideanSpace ℝ (Fin 0))) (u : LocalL2 U F) :
    ∃ f : EuclideanSpace ℝ (Fin 0) → F,
      ContDiffOn ℝ ∞ f U ∧ f =ᵐ[volume.restrict U] u := by
  refine ⟨fun _ ↦ u 0, contDiffOn_const, Filter.Eventually.of_forall ?_⟩
  intro x
  exact congrArg u (Subsingleton.elim 0 x)

end ZeroDimension

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The local `H^∞` regularity assertion in `app:not:fourier`, used for
smoothness in `app:ch_regular:thm:exact-correction`. Membership at every
integer order yields one smooth representative on the open domain, even
when the whole-space weak extensions differ between orders. -/
theorem exists_contDiffOn_infty_ae_eq_of_memRestrictionSobolev
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (u : LocalL2 U F)
    (hu : ∀ s : ℕ, MemRestrictionSobolev U s u) :
    ∃ f : EuclideanSpace ℝ (Fin n) → F,
      ContDiffOn ℝ ∞ f U ∧ f =ᵐ[volume.restrict U] u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact exists_contDiffOn_infty_ae_eq_dimension_zero U u
  · apply exists_contDiffOn_infty_ae_eq_of_finiteOrderRepresentatives hU u
    intro k
    obtain ⟨e⟩ := hu (k + n + 1)
    obtain ⟨f, hf, hfe⟩ := FiniteOrder.exists_contDiff_ae_eq_of_weakJet hn
      e.weakJet e.memLp_fun e.memLp_jet
    have hfeU : f =ᵐ[volume.restrict U] e.toFun := ae_restrict_of_ae hfe
    exact ⟨f, hf.contDiffOn, hfeU.trans e.restrict_eq⟩

/-- On a local ball of positive radius, the intersection of the integer
restriction Sobolev spaces has smooth representatives (`app:not:fourier`),
as used in `app:ch_regular:thm:exact-correction`. This includes dimension zero. -/
theorem exists_contDiffOn_infty_ae_eq_ball_of_memRestrictionSobolev
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (_hR : 0 < R)
    (u : LocalL2 (Metric.ball c R) F)
    (hu : ∀ s : ℕ, MemRestrictionSobolev (Metric.ball c R) s u) :
    ∃ f : EuclideanSpace ℝ (Fin n) → F,
      ContDiffOn ℝ ∞ f (Metric.ball c R) ∧
        f =ᵐ[volume.restrict (Metric.ball c R)] u :=
  exists_contDiffOn_infty_ae_eq_of_memRestrictionSobolev Metric.isOpen_ball u hu

end JanetCartan.LocalSobolev
