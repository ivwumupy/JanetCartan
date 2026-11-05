module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.PeriodicExtension.Operator
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.PeriodicExtension.Transfer

/-!
# The commutator identity on all periodic Sobolev inputs

For `app:ch_background:eq:bg-commutator`, the meaning of `T D^is u` is the
independent first-order transfer extension composed with the actual lower weak
derivatives. Smooth density then proves the distributional commutator identity.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
open JanetCartan.AmplitudeBound
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.Pseudodifferential.DifferentialChart
open PeriodicSobolevSpace PeriodicExtension
variable {d : ℕ}
variable (hd : 0 < d) (r : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (M : ℝ)
  (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)

/-- The meaning of `T D^(i::is) u` for Sobolev data, constructed independently
of the highest-order commutator. Only the first-order amplitude budget is used
(`app:ch_background:eq:bg-commutator`). -/
def torusOnOrderedDerivative (n : ℕ) (i : Fin d) (is : List (Fin d)) (hlen : is.length ≤ n) :
    PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicSobolevNegativeOne d ℂ :=
  (torusOnCoordinateDerivative hd r b hb hs M hM i).comp
    (ContinuumCommutator.Exterior.derivativeToL2 n is hlen)

/-- On smooth fields the independent distribution is the literal operator on
the ordered derivative (`app:ch_background:eq:bg-commutator`). -/
theorem torusOnOrderedDerivative_ofSmooth (hr : r < 1 / 2)
    (n : ℕ) (i : Fin d) (is : List (Fin d)) (hlen : is.length ≤ n)
    (f : Torus d → ℂ) (hf : IsSmoothPeriodic f) :
    torusOnOrderedDerivative hd r b hb hs M hM n i is hlen (ofSmooth n f hf) =
      PeriodicSobolevNegativeOne.ofL2
        (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
          (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (i :: is) f)
            (hf.coordinateDerivList (i :: is))))) := by
  simp only [torusOnOrderedDerivative, ContinuousLinearMap.comp_apply,
    ContinuumCommutator.Exterior.derivativeToL2_ofSmooth]
  exact torusOnCoordinateDerivative_ofSmooth hd r b hb hs M hM hr i _
    (hf.coordinateDerivList is)

/-- Smooth density uniquely determines the ordered distributional extension
(`app:ch_background:eq:bg-commutator`). -/
theorem torusOnOrderedDerivative_unique (hr : r < 1 / 2)
    (n : ℕ) (i : Fin d) (is : List (Fin d)) (hlen : is.length ≤ n)
    (S : PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicSobolevNegativeOne d ℂ)
    (hS : ∀ (f : Torus d → ℂ) (hf : IsSmoothPeriodic f),
      S (ofSmooth n f hf) = PeriodicSobolevNegativeOne.ofL2
        (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
          (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (i :: is) f)
            (hf.coordinateDerivList (i :: is)))))) :
    S = torusOnOrderedDerivative hd r b hb hs M hM n i is hlen := by
  apply DFunLike.coe_injective
  apply (denseRange_ofSmooth n).equalizer S.continuous
    (torusOnOrderedDerivative hd r b hb hs M hM n i is hlen).continuous
  funext f
  exact (hS f.val f.property).trans
    (torusOnOrderedDerivative_ofSmooth hd r b hb hs M hM hr n i is hlen f.val f.property).symm

/-- Distributional commutator identity against every smooth periodic test on
every Hⁿ input. The second term is the independently defined `T D^(i::is) u`,
not an expression defined using the desired commutator
(`app:ch_background:eq:bg-commutator`). -/
theorem torusSobolevCommutator_distribution (hr : r < 1 / 2) (n : ℕ) (H : ℝ)
    (i : Fin d) (is : List (Fin d)) (hlen : (i :: is).length = n + 1)
    (hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + (i :: is).length) H)
    (u : PeriodicSobolevSpace d ℂ n) (φ : Torus d → ℂ) (hφ : IsSmoothPeriodic φ) :
    let T := torusL2Operator hd r b hb hs M
      (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
    (-1 : ℝ) ^ (i :: is).length *
        (∫ x, inner ℝ (T (toL2 n u) x) (periodicCoordinateDerivList (i :: is).reverse φ x)) -
      torusOnOrderedDerivative hd r b hb hs M hM n i is (by have hh := hlen; simp only [List.length_cons] at hh; omega) u (ofSmooth 1 φ hφ) =
      ∫ x, inner ℝ (torusSobolevCommutator hd r hr n M b hb hs H hM
        (i :: is) hlen hH u x) (φ x) := by
  let T := torusL2Operator hd r b hb hs M
    (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
  let S := torusSobolevCommutator hd r hr n M b hb hs H hM (i :: is) hlen hH
  let Q := torusOnOrderedDerivative hd r b hb hs M hM n i is (by have hh := hlen; simp only [List.length_cons] at hh; omega)
  have he : (fun v : PeriodicSobolevSpace d ℂ n ↦
      (-1 : ℝ) ^ (i :: is).length *
        ⟪T (toL2 n v), toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (i :: is).reverse φ)
          (hφ.coordinateDerivList _))⟫ - Q v (ofSmooth 1 φ hφ)) =
      (fun v ↦ ⟪S v, toL2 0 (ofSmooth 0 φ hφ)⟫) := by
    apply (denseRange_ofSmooth n).equalizer (by fun_prop) (by fun_prop)
    funext f
    have hw := torusSobolevCommutator_ofSmooth hd r hr n M b hb hs H hM
      (i :: is) hlen hH f.val f.property
    have hw' := (weakDerivativeList_iff_inner (i :: is) _ _).mp hw ⟨φ, hφ⟩
    simp only [smoothDerivative_apply, smoothRealization, LinearMap.coe_mk, AddHom.coe_mk,
      inner_add_left] at hw'
    dsimp only [Function.comp_apply, Q]
    rw [torusOnOrderedDerivative_ofSmooth hd r b hb hs M hM hr,
      PeriodicSobolevNegativeOne.ofL2_apply]
    have htest : toL2 1 (ofSmooth 1 φ hφ) = toL2 0 (ofSmooth 0 φ hφ) := rfl
    rw [htest]
    dsimp only [T, S]
    linarith
  have h := congrFun he u
  simpa only [inner_periodicL2_ofSmooth, T, S, Q] using h

end JanetCartan.Pseudodifferential.DifferentialChart
