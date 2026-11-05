module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Differentiation

/-!
# Schwartz periodizations on the unit torus

For `main:lem:smoothing` and `main:eq:smoothing-low`, descend the convergent
Schwartz lattice sum to a continuous function on the normalized unit torus.
-/

@[expose] public noncomputable section

open scoped SchwartzMap

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `main:lem:smoothing`: the unit-torus quotient in product coordinates. -/
def coordinateTorusQuotient (n : ℕ) : C((Fin n → ℝ), Torus n) :=
  ⟨fun x i ↦ (x i : AddCircle (1 : ℝ)),
    Continuous.piMap (fun _ ↦ AddCircle.continuous_mk' 1)⟩

/-- `main:lem:smoothing`: the coordinate quotient is a topological quotient map. -/
theorem coordinateTorusQuotient_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (coordinateTorusQuotient n) :=
  (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
    (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun x : ℝ ↦ (x : AddCircle (1 : ℝ)))))).isQuotientMap

/-- `main:lem:smoothing`: continuous Schwartz periodization in product coordinates. -/
def coordinateSchwartzPeriodization (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    C((Fin n → ℝ), F) :=
  ⟨fun x ↦ schwartzLatticePeriodization f (WithLp.toLp 2 x),
    (contDiff_schwartzLatticePeriodization f).continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ))⟩

/-- `main:lem:smoothing`: the lattice sum is constant on quotient fibers. -/
theorem coordinateSchwartzPeriodization_factors
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    Function.FactorsThrough (coordinateSchwartzPeriodization f) (coordinateTorusQuotient n) := by
  intro x y h
  have hi (i : Fin n) : ∃ k : ℤ, (k : ℝ) = y i - x i := by
    have he : ((y i - x i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, show (y i : AddCircle (1 : ℝ)) = (x i : AddCircle (1 : ℝ))
        from (congrFun h i).symm, sub_self]
    simpa using (AddCircle.coe_eq_zero_iff 1).mp he
  choose k hk using hi
  have hy : WithLp.toLp 2 y =
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) + WithLp.toLp 2 (fun i ↦ (k i : ℝ)) := by
    ext i
    change y i = x i + (k i : ℝ)
    rw [hk i]
    ring
  change schwartzLatticePeriodization f (WithLp.toLp 2 x) =
    schwartzLatticePeriodization f (WithLp.toLp 2 y)
  rw [hy, schwartzLatticePeriodization_add_int]

/-- `main:lem:smoothing`: the continuous unit-torus function obtained by
periodizing a Schwartz function over the integer lattice. -/
def schwartzTorusPeriodization (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) : C(Torus n, F) :=
  (coordinateTorusQuotient_isQuotientMap n).lift (coordinateSchwartzPeriodization f)
    (coordinateSchwartzPeriodization_factors f)

/-- `main:lem:smoothing`: the descended function retains the actual convergent
lattice sum at every Euclidean representative. -/
@[simp] theorem schwartzTorusPeriodization_torusQuotient
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (x : EuclideanSpace ℝ (Fin n)) :
    schwartzTorusPeriodization f (torusQuotient x) = schwartzLatticePeriodization f x := by
  exact congrArg (fun g : C((Fin n → ℝ), F) ↦ g (WithLp.ofLp x))
    ((coordinateTorusQuotient_isQuotientMap n).lift_comp
      (coordinateSchwartzPeriodization f) (coordinateSchwartzPeriodization_factors f))

end JanetCartan
