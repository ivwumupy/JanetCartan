module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Operators
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Distribution
public import JanetCartan.Analysis.Operator.CoerciveInverse

/-!
# Higher weak derivatives of the same coercive inverse

The H⁻¹ uniqueness argument of `app:ch_background:prop:bg-inverse` on the
existing periodic Fourier Sobolev scale. Bounded H¹ restrictions of `E` and
its single L² inverse are inputs from first-order regularity. A continuous
commutator with the literal smooth weak identity supplies the differential
input. Neither the highest weak derivative nor higher inverse regularity is
assumed. The actual normal representation must supply that commutator.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.HigherRegularity

open PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The existing ordered derivative operator really represents the iterated
weak derivative on every Sobolev datum (`app:ch_background:eq:bg-commutator`). -/
theorem hasWeakDerivativeList_derivativeToL2 (s : ℕ) (is : List (Fin n))
    (hlen : is.length ≤ s) (u : PeriodicSobolevSpace n F s) :
    HasPeriodicWeakDerivativeList is (toL2 s u) (Exterior.derivativeToL2 s is hlen u) := by
  intro φ hφ
  have he :
      (fun v : PeriodicSobolevSpace n F s ↦
        ⟪Exterior.derivativeToL2 s is hlen v, toL2 0 (ofSmooth 0 φ hφ)⟫) =
      (fun v ↦ (-1 : ℝ) ^ is.length *
        ⟪toL2 s v, toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse φ)
          (hφ.coordinateDerivList _))⟫) := by
    apply (denseRange_ofSmooth s).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, Exterior.derivativeToL2_ofSmooth,
      inner_periodicL2_ofSmooth]
    exact f.property.hasPeriodicWeakDerivativeList is s 0 φ hφ
  simpa only [inner_periodicL2_ofSmooth] using congrFun he u

/-- Lower ordered derivatives have operator bound one in the fixed Fourier
normalization (`app:ch_background:eq:bg-commutator`). -/
theorem norm_derivativeToL2_le (s : ℕ) (is : List (Fin n)) (hlen : is.length ≤ s)
    (u : PeriodicSobolevSpace n F s) : ‖Exterior.derivativeToL2 s is hlen u‖ ≤ ‖u‖ := by
  have hr : ∀ (s : ℕ) (js : List (Fin n)) (h : js.length ≤ s)
      (u : PeriodicSobolevSpace n F s), ‖Exterior.reverseDerivativeToL2 s js h u‖ ≤ ‖u‖ := by
    intro s
    induction s with
    | zero =>
      intro js h u
      have hj : js = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst js
      exact norm_toL2_le 0 u
    | succ s ih =>
      intro js h u
      cases js with
      | nil => exact norm_toL2_le (s + 1) u
      | cons j js =>
        exact (ih js (by simpa using h) (coordinateDerivative s j u)).trans
          (norm_coordinateDerivative_le s j u)
  exact hr s is.reverse (by simpa using hlen) u

/-- The top derivative of an Hˢ field as an H⁻¹ functional: first take the
existing lower derivative, then the negative-order coordinate derivative.
This definition does not use a commutator (`app:ch_background:prop:bg-inverse`). -/
def negativeOrderedDerivative (s : ℕ) (i : Fin n) (is : List (Fin n))
    (hlen : is.length ≤ s) :
    PeriodicSobolevSpace n F s →L[ℝ] PeriodicSobolevNegativeOne n F :=
  (PeriodicSobolevNegativeOne.coordinateDerivative i).comp
    (Exterior.derivativeToL2 s is hlen)

/-- The constructed negative-order derivative has the literal distributional
test formula, without assuming an L² top derivative
(`app:ch_background:prop:bg-inverse`). -/
theorem negativeOrderedDerivative_apply_smooth (s : ℕ) (i : Fin n)
    (is : List (Fin n)) (hlen : is.length ≤ s) (u : PeriodicSobolevSpace n F s)
    (φ : Torus n → F) (hφ : IsSmoothPeriodic φ) :
    negativeOrderedDerivative s i is hlen u (ofSmooth 1 φ hφ) =
      (-1 : ℝ) ^ (i :: is).length *
        (∫ x, ⟪toL2 s u x, periodicCoordinateDerivList (i :: is).reverse φ x⟫) := by
  rw [negativeOrderedDerivative, ContinuousLinearMap.comp_apply,
    PeriodicSobolevNegativeOne.coordinateDerivative_ofSmooth,
    hasWeakDerivativeList_derivativeToL2 s is hlen u _ (hφ.coordinateDeriv i)]
  simp only [List.length_cons, List.reverse_cons, periodicCoordinateDerivList_append,
    periodicCoordinateDerivList, pow_succ]
  ring

/-- L² representability of the independently defined H⁻¹ top derivative is
exactly the existing weak-jet relation (`app:ch_background:prop:bg-inverse`). -/
theorem negativeOrderedDerivative_eq_ofL2_iff (s : ℕ) (i : Fin n)
    (is : List (Fin n)) (hlen : is.length ≤ s) (u : PeriodicSobolevSpace n F s)
    (w : PeriodicL2 n F) :
    negativeOrderedDerivative s i is hlen u = PeriodicSobolevNegativeOne.ofL2 w ↔
      HasPeriodicWeakDerivativeList (i :: is) (toL2 s u) w := by
  constructor
  · intro h φ hφ
    have he := DFunLike.congr_fun h (ofSmooth 1 φ hφ)
    rw [negativeOrderedDerivative_apply_smooth, PeriodicSobolevNegativeOne.ofL2_apply,
      inner_periodicL2_ofSmooth] at he
    exact he.symm
  · intro h
    apply DFunLike.coe_injective
    apply (denseRange_ofSmooth 1).equalizer
      (negativeOrderedDerivative s i is hlen u).continuous
      (PeriodicSobolevNegativeOne.ofL2 w).continuous
    funext φ
    simp only [Function.comp_apply, negativeOrderedDerivative_apply_smooth,
      PeriodicSobolevNegativeOne.ofL2_apply, inner_periodicL2_ofSmooth]
    exact (h φ.val φ.property).symm

/-- On smooth fields the H⁻¹ derivative is the classical derivative embedded
in H⁻¹ (`app:ch_background:eq:bg-commutator`). -/
theorem negativeOrderedDerivative_ofSmooth (s : ℕ) (i : Fin n)
    (is : List (Fin n)) (hlen : is.length ≤ s)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    negativeOrderedDerivative s i is hlen (ofSmooth s f hf) =
      PeriodicSobolevNegativeOne.ofL2 (toL2 0 (ofSmooth 0
        (periodicCoordinateDerivList (i :: is) f) (hf.coordinateDerivList _))) :=
  (negativeOrderedDerivative_eq_ofL2_iff s i is hlen _ _).mpr
    (hf.hasPeriodicWeakDerivativeList (i :: is) s 0)

variable (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
  (E₁ Q₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1)
  (hself : IsSelfAdjoint E)
  (hE₁ : ∀ u, toL2 1 (E₁ u) = E (toL2 1 u))
  (hQ₁ : ∀ u, toL2 1 (Q₁ u) = E.inverse (toL2 1 u))

include hself hE₁ hQ₁

/-- H⁻¹ uniqueness uses the transpose of the H¹ restriction of the *same*
coercive L² inverse (`app:ch_background:prop:bg-inverse`). -/
theorem transpose_eq_ofL2_iff_inverse {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫)
    (u : PeriodicSobolevNegativeOne n F) (f : PeriodicL2 n F) :
    PeriodicSobolevNegativeOne.transpose E₁ u = PeriodicSobolevNegativeOne.ofL2 f ↔
      u = PeriodicSobolevNegativeOne.ofL2 (E.inverse f) :=
  PeriodicSobolevNegativeOne.transpose_eq_ofL2_iff E E.inverse E₁ Q₁
    (CoerciveInverse.inverse_isSelfAdjoint E hself hc hgap) hE₁ hQ₁
    (CoerciveInverse.isInvertible_of_gap E hc hgap).self_comp_inverse
    (CoerciveInverse.isInvertible_of_gap E hc hgap).inverse_comp_self u f

omit Q₁ hQ₁ in
/-- Extend the smooth differential identity to all Hˢ inputs by density.
The action on the missing derivative is independently defined by H¹ duality;
no regularity of that derivative is assumed
(`app:ch_background:eq:bg-commutator`). -/
theorem transpose_negativeOrderedDerivative_commutator
    (s : ℕ) (i : Fin n) (is : List (Fin n)) (hlen : is.length ≤ s)
    (K : PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F)
    (hK : ∀ (f : Torus n → F) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList (i :: is) (E (toL2 s (ofSmooth s f hf)))
        (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (i :: is) f)
          (hf.coordinateDerivList _))) + K (ofSmooth s f hf)))
    (u : PeriodicSobolevSpace n F s) (φ : Torus n → F) (hφ : IsSmoothPeriodic φ) :
    PeriodicSobolevNegativeOne.transpose E₁
        (negativeOrderedDerivative s i is hlen u) (ofSmooth 1 φ hφ) =
      (-1 : ℝ) ^ (i :: is).length *
        (∫ x, ⟪E (toL2 s u) x, periodicCoordinateDerivList (i :: is).reverse φ x⟫) -
        (∫ x, ⟪K u x, φ x⟫) := by
  have he :
      (fun v : PeriodicSobolevSpace n F s ↦
        PeriodicSobolevNegativeOne.transpose E₁
          (negativeOrderedDerivative s i is hlen v) (ofSmooth 1 φ hφ)) =
      (fun v ↦ (-1 : ℝ) ^ (i :: is).length *
        ⟪E (toL2 s v), toL2 0 (ofSmooth 0
          (periodicCoordinateDerivList (i :: is).reverse φ) (hφ.coordinateDerivList _))⟫ -
        ⟪K v, toL2 0 (ofSmooth 0 φ hφ)⟫) := by
    apply (denseRange_ofSmooth s).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, negativeOrderedDerivative_ofSmooth,
      PeriodicSobolevNegativeOne.transpose_ofL2 E E₁ hself hE₁,
      PeriodicSobolevNegativeOne.ofL2_apply, inner_periodicL2_ofSmooth]
    have hh := hK f.val f.property φ hφ
    rw [← inner_periodicL2_ofSmooth _ 0 φ hφ, inner_add_left,
      inner_periodicL2_ofSmooth, inner_periodicL2_ofSmooth] at hh
    linarith
  simpa only [inner_periodicL2_ofSmooth] using congrFun he u

/-- The missing derivative is the original L² inverse applied to the
differentiated equation. This justifies the highest weak derivative, rather
than presupposing it (`app:ch_background:prop:bg-inverse`). -/
theorem weakDerivativeList_inverse_rhs {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫)
    (s : ℕ) (i : Fin n) (is : List (Fin n)) (hlen : is.length ≤ s)
    (K : PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F)
    (hK : ∀ (f : Torus n → F) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList (i :: is) (E (toL2 s (ofSmooth s f hf)))
        (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (i :: is) f)
          (hf.coordinateDerivList _))) + K (ofSmooth s f hf)))
    (u : PeriodicSobolevSpace n F s) (w : PeriodicL2 n F)
    (hw : HasPeriodicWeakDerivativeList (i :: is) (E (toL2 s u)) w) :
    HasPeriodicWeakDerivativeList (i :: is) (toL2 s u) (E.inverse (w - K u)) := by
  apply (negativeOrderedDerivative_eq_ofL2_iff s i is hlen u _).mp
  apply (transpose_eq_ofL2_iff_inverse E E₁ Q₁ hself hE₁ hQ₁ hc hgap _ _).mp
  apply DFunLike.coe_injective
  apply (denseRange_ofSmooth 1).equalizer
    (PeriodicSobolevNegativeOne.transpose E₁
      (negativeOrderedDerivative s i is hlen u)).continuous
    (PeriodicSobolevNegativeOne.ofL2 (w - K u)).continuous
  funext φ
  simp only [Function.comp_apply,
    transpose_negativeOrderedDerivative_commutator E E₁ hself hE₁ s i is hlen K hK,
    PeriodicSobolevNegativeOne.ofL2_apply, inner_sub_left, inner_periodicL2_ofSmooth,
    hw φ.val φ.property]

/-- The actual Fourier Hˢ-to-Hˢ⁺¹ regularity implication required as `hreg`
by `ContinuumInverse.inverse_mem`, from continuous smooth commutator identities
and first-order inverse preservation (`app:ch_background:prop:bg-inverse`). -/
theorem mem_succ_of_commutators {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫)
    (s : ℕ)
    (K : (is : List (Fin n)) → is.length = s + 1 →
      PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F)
    (hK : ∀ (is : List (Fin n)) (hlen : is.length = s + 1)
      (f : Torus n → F) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList is (E (toL2 s (ofSmooth s f hf)))
        (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is))) + K is hlen (ofSmooth s f hf)))
    (v : PeriodicL2 n F) (hv : v ∈ periodicSobolevLevel n F s)
    (hev : E v ∈ periodicSobolevLevel n F (s + 1)) :
    v ∈ periodicSobolevLevel n F (s + 1) := by
  apply mem_periodicSobolevLevel_succ_of_top_weakDerivativeLists s v hv
  intro is hlen
  obtain ⟨w, hw⟩ := (mem_periodicSobolevLevel_iff_weakDerivativeLists (s + 1) (E v)).mp
    hev is hlen.le
  cases is with
  | nil => simp at hlen
  | cons i is =>
    exact ⟨E.inverse (w - K (i :: is) hlen (ofL2 s v hv)),
      weakDerivativeList_inverse_rhs E E₁ Q₁ hself hE₁ hQ₁ hc hgap s i is
        (by simpa using hlen.le) (K (i :: is) hlen) (hK (i :: is) hlen)
        (ofL2 s v hv) w hw⟩

/-- The top derivative estimate before reconstructing the Sobolev norm.
The commutator's single high budget `A` multiplies only the L² norm, and the
coercive inverse contributes the same gap `c` at every order
(`app:ch_background:eq:bg-commutator`, `app:ch_background:eq:bg-r-inverse`). -/
theorem exists_top_weakDerivative_norm_le {c : ℝ} (hc : 0 < c)
    (hgap : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪E v, v⟫)
    (s : ℕ) (i : Fin n) (is : List (Fin n)) (hlen : (i :: is).length = s + 1)
    (K : PeriodicSobolevSpace n F s →L[ℝ] PeriodicL2 n F)
    (hK : ∀ (f : Torus n → F) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList (i :: is) (E (toL2 s (ofSmooth s f hf)))
        (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList (i :: is) f)
          (hf.coordinateDerivList _))) + K (ofSmooth s f hf)))
    (C A : ℝ) (hbound : ∀ u, ‖K u‖ ≤ C * (‖u‖ + A * ‖toL2 s u‖))
    (u : PeriodicSobolevSpace n F s)
    (he : E (toL2 s u) ∈ periodicSobolevLevel n F (s + 1)) :
    ∃ w : PeriodicL2 n F, HasPeriodicWeakDerivativeList (i :: is) (toL2 s u) w ∧
      ‖w‖ ≤ c⁻¹ * (‖ofL2 (s + 1) (E (toL2 s u)) he‖ +
        C * (‖u‖ + A * ‖toL2 s u‖)) := by
  let e := ofL2 (s + 1) (E (toL2 s u)) he
  let de := Exterior.derivativeToL2 (s + 1) (i :: is) hlen.le e
  refine ⟨E.inverse (de - K u), ?_, ?_⟩
  · exact weakDerivativeList_inverse_rhs E E₁ Q₁ hself hE₁ hQ₁ hc hgap s i is
      (by simpa using hlen.le) K hK u de
      (hasWeakDerivativeList_derivativeToL2 (s + 1) (i :: is) hlen.le e)
  · exact (CoerciveInverse.norm_inverse_apply_le E hc hgap _).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
        (add_le_add (norm_derivativeToL2_le (s + 1) (i :: is) hlen.le e) (hbound u)))
        (inv_nonneg.mpr hc.le))

end JanetCartan.ContinuumCommutator.HigherRegularity
