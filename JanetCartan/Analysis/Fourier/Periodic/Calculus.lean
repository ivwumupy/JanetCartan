module

public import JanetCartan.Analysis.Fourier.Periodic

/-!
# Calculus of periodic lifts

For the unit-torus convention of Appendix A (`app:sec:notation`), integer translations
preserve lifts and all their Fréchet derivatives. Every Euclidean point is an integer
translate of a point in the compact closed fundamental cell. Consequently derivative
bounds on the cell hold everywhere, as needed for the smooth series in `main:lem:history`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan

variable {n : ℕ}

/-- Appendix A (`app:sec:notation`): an integer period in Euclidean coordinates. -/
def integerTranslation (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ (k i : ℝ))

/-- Appendix A (`app:sec:notation`): coordinates of an integer period. -/
@[simp] theorem integerTranslation_apply (k : Fin n → ℤ) (i : Fin n) :
    integerTranslation k i = (k i : ℝ) := rfl

/-- Appendix A (`app:sec:notation`): the quotient identifies integer translates. -/
@[simp] theorem torusQuotient_add_integerTranslation (x : EuclideanSpace ℝ (Fin n))
    (k : Fin n → ℤ) : torusQuotient (x + integerTranslation k) = torusQuotient x := by
  funext i
  change ((x i + (k i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (x i : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  have hk : ((k i : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨k i, by simp⟩
  rw [hk, add_zero]

/-- Appendix A (`app:sec:notation`): every torus field has an integer-periodic lift. -/
theorem periodicLift_periodic {F : Type*} (f : Torus n → F) (k : Fin n → ℤ) :
    Function.Periodic (periodicLift f) (integerTranslation k) := by
  intro x
  simp [periodicLift]

/-- Appendix A (`app:sec:notation`): the origin belongs to the closed fundamental cell. -/
theorem zero_mem_fundamentalCell (n : ℕ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ fundamentalCell n := by
  intro i
  norm_num

/-- Appendix A (`app:sec:notation`): the closed fundamental cell is nonempty. -/
theorem fundamentalCell_nonempty (n : ℕ) : (fundamentalCell n).Nonempty :=
  ⟨0, zero_mem_fundamentalCell n⟩

/-- Appendix A (`app:sec:notation`): the closed fundamental cell is compact. -/
theorem isCompact_fundamentalCell (n : ℕ) : IsCompact (fundamentalCell n) := by
  have hbox : IsCompact {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)} :=
    isCompact_pi_infinite (fun _ ↦ isCompact_Icc)
  convert hbox.image (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)) using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

/-- Appendix A (`app:sec:notation`): every point is an integer translate of a point
in the closed fundamental cell, by rounding each coordinate down after adding `1/2`. -/
theorem exists_mem_fundamentalCell_add_integerTranslation (x : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ fundamentalCell n, ∃ k : Fin n → ℤ, x = y + integerTranslation k := by
  let k : Fin n → ℤ := fun i ↦ ⌊x i + 1 / 2⌋
  refine ⟨x - integerTranslation k, ?_, k, ?_⟩
  · intro i
    change -(1 / 2 : ℝ) ≤ x i - (⌊x i + 1 / 2⌋ : ℝ) ∧
      x i - (⌊x i + 1 / 2⌋ : ℝ) ≤ 1 / 2
    constructor
    · linarith [Int.floor_le (x i + 1 / 2)]
    · linarith [Int.lt_floor_add_one (x i + 1 / 2)]
  · exact (sub_add_cancel x (integerTranslation k)).symm

/-- Appendix A (`app:sec:notation`): the range of an integer-periodic map is already
attained on the closed fundamental cell. -/
theorem range_eq_image_fundamentalCell {F : Type*} {g : EuclideanSpace ℝ (Fin n) → F}
    (hg : ∀ k : Fin n → ℤ, Function.Periodic g (integerTranslation k)) :
    Set.range g = g '' fundamentalCell n := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    exact ⟨y, hy, (hg k y).symm⟩
  · rintro ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix A (`app:sec:notation`): the Fréchet derivative of a lift is periodic.
The identity also holds at points where the totalized derivative is zero. -/
theorem fderiv_periodicLift_periodic (f : Torus n → F) (k : Fin n → ℤ) :
    Function.Periodic (fderiv ℝ (periodicLift f)) (integerTranslation k) := by
  intro x
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  exact periodicLift_periodic f k y

/-- Appendix A (`app:sec:notation`), `main:lem:history`: every iterated Fréchet derivative
of a lift is integer-periodic, without needing a differentiability hypothesis. -/
theorem iteratedFDeriv_periodicLift_periodic (f : Torus n → F) (r : ℕ)
    (k : Fin n → ℤ) :
    Function.Periodic (iteratedFDeriv ℝ r (periodicLift f)) (integerTranslation k) := by
  intro x
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext y
  exact periodicLift_periodic f k y

/-- `main:lem:history`: the range of a lifted derivative is attained on the cell. -/
theorem range_iteratedFDeriv_periodicLift (f : Torus n → F) (r : ℕ) :
    Set.range (iteratedFDeriv ℝ r (periodicLift f)) =
      iteratedFDeriv ℝ r (periodicLift f) '' fundamentalCell n :=
  range_eq_image_fundamentalCell (iteratedFDeriv_periodicLift_periodic f r)

/-- `main:lem:history`: a bound on a lifted derivative on the cell holds everywhere,
with exactly the same constant and without additional regularity assumptions. -/
theorem norm_iteratedFDeriv_periodicLift_le (f : Torus n → F) (r : ℕ) {C : ℝ}
    (hC : ∀ x ∈ fundamentalCell n, ‖iteratedFDeriv ℝ r (periodicLift f) x‖ ≤ C)
    (x : EuclideanSpace ℝ (Fin n)) : ‖iteratedFDeriv ℝ r (periodicLift f) x‖ ≤ C := by
  obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
  rw [iteratedFDeriv_periodicLift_periodic f r k y]
  exact hC y hy

/-- `main:lem:history`: cell bounds and global bounds for lifted derivatives are equivalent. -/
theorem norm_iteratedFDeriv_periodicLift_le_iff (f : Torus n → F) (r : ℕ) (C : ℝ) :
    (∀ x, ‖iteratedFDeriv ℝ r (periodicLift f) x‖ ≤ C) ↔
      ∀ x ∈ fundamentalCell n, ‖iteratedFDeriv ℝ r (periodicLift f) x‖ ≤ C :=
  ⟨fun h x _ ↦ h x, fun h ↦ norm_iteratedFDeriv_periodicLift_le f r h⟩

/-- `main:lem:history`: each derivative of a smooth periodic field has a global bound. -/
theorem IsSmoothPeriodic.exists_bound_iteratedFDeriv {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (r : ℕ) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ r (periodicLift f) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_fundamentalCell n).exists_bound_of_continuousOn
    (hf.2.continuous_iteratedFDeriv (by simp : (r : WithTop ℕ∞) ≤ ∞)).continuousOn
  exact ⟨C, norm_iteratedFDeriv_periodicLift_le f r hC⟩

end JanetCartan
