module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Characterization

/-!
# Iterated distributional derivatives and integer Sobolev membership

For the integer induction in `app:ch_background:prop:bg-inverse`, an ordered
coordinate list defines a distribution by testing against the reverse list of
classical derivatives. No intermediate L² derivatives are part of this definition.
We prove that L² representatives of all derivatives through order `s` are
equivalent to actual Fourier Sobolev membership.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- Concatenation composes the existing classical coordinate derivative lists
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem periodicCoordinateDerivList_append (is js : List (Fin n)) (f : Torus n → F) :
    periodicCoordinateDerivList (is ++ js) f =
      periodicCoordinateDerivList is (periodicCoordinateDerivList js f) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, periodicCoordinateDerivList, ih]

/-- An L² representative of the iterated distributional derivative indexed by
an ordered coordinate list. Transposition reverses the order of differentiation
on the smooth test field (`app:ch_background:prop:bg-inverse`). -/
def HasPeriodicWeakDerivativeList (is : List (Fin n)) (u v : PeriodicL2 n F) : Prop :=
  ∀ (φ : Torus n → F), IsSmoothPeriodic φ →
    (∫ x, ⟪v x, φ x⟫) = (-1 : ℝ) ^ is.length *
      (∫ x, ⟪u x, periodicCoordinateDerivList is.reverse φ x⟫)

omit [FiniteDimensional ℝ F] in
/-- A single distributional derivative is the original weak coordinate derivative
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem hasPeriodicWeakDerivativeList_singleton (i : Fin n) (u v : PeriodicL2 n F) :
    HasPeriodicWeakDerivativeList [i] u v ↔ HasPeriodicWeakDerivative i u v := by
  simp [HasPeriodicWeakDerivativeList, HasPeriodicWeakDerivative, periodicCoordinateDerivList]

namespace HasPeriodicWeakDerivativeList

omit [FiniteDimensional ℝ F] in
/-- The empty derivative list represents the original distribution
(`app:ch_background:prop:bg-inverse`). -/
theorem nil (u : PeriodicL2 n F) : HasPeriodicWeakDerivativeList [] u u := by
  intro φ _
  simp [periodicCoordinateDerivList]

/-- Smooth density makes every iterated L² distributional derivative unique
(`app:ch_background:prop:bg-inverse`). -/
theorem unique {is : List (Fin n)} {u v w : PeriodicL2 n F}
    (hv : HasPeriodicWeakDerivativeList is u v) (hw : HasPeriodicWeakDerivativeList is u w) :
    v = w := by
  apply (PeriodicSobolevSpace.denseRange_toL2_ofSmooth (n := n) (F := F) 0).eq_of_inner_left ℝ
  intro φ
  simp only [inner_periodicL2_ofSmooth]
  exact (hv φ.1 φ.2).trans (hw φ.1 φ.2).symm

omit [FiniteDimensional ℝ F] in
/-- Taking a weak coordinate derivative of an iterated derivative gives the
longer distributional derivative (`app:ch_background:prop:bg-inverse`). -/
theorem cons {is : List (Fin n)} {i : Fin n} {u v w : PeriodicL2 n F}
    (hv : HasPeriodicWeakDerivativeList is u v) (hw : HasPeriodicWeakDerivative i v w) :
    HasPeriodicWeakDerivativeList (i :: is) u w := by
  intro φ hφ
  simp only [List.length_cons, List.reverse_cons, periodicCoordinateDerivList_append,
    periodicCoordinateDerivList]
  rw [hw φ hφ, hv _ (hφ.coordinateDeriv i), pow_succ]
  ring

omit [FiniteDimensional ℝ F] in
/-- If the first derivative and a higher derivative of the original distribution
are represented in L², the latter is an iterated weak derivative of the former.
This discharges the compatibility needed for induction
(`app:ch_background:prop:bg-inverse`). -/
theorem of_append_singleton {is : List (Fin n)} {i : Fin n} {u v w : PeriodicL2 n F}
    (hw : HasPeriodicWeakDerivativeList (is ++ [i]) u w)
    (hv : HasPeriodicWeakDerivative i u v) : HasPeriodicWeakDerivativeList is v w := by
  intro φ hφ
  have h := hw φ hφ
  simp only [List.length_append, List.length_singleton, List.reverse_append,
    List.reverse_singleton, List.singleton_append, periodicCoordinateDerivList] at h
  rw [hv _ (hφ.coordinateDerivList _), h, pow_succ]
  ring

end HasPeriodicWeakDerivativeList

/-- The empty distributional derivative is exactly the input L² element
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem hasPeriodicWeakDerivativeList_nil (u v : PeriodicL2 n F) :
    HasPeriodicWeakDerivativeList [] u v ↔ v = u :=
  ⟨fun h ↦ h.unique (.nil u), fun h ↦ h ▸ .nil u⟩

/-- On smooth fields the iterated distribution is the existing classical
coordinate derivative list (`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem IsSmoothPeriodic.hasPeriodicWeakDerivativeList {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (is : List (Fin n)) (s t : ℕ) :
    HasPeriodicWeakDerivativeList is
      (PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s f hf))
      (PeriodicSobolevSpace.toL2 t (PeriodicSobolevSpace.ofSmooth t
        (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) := by
  induction is with
  | nil =>
    apply (hasPeriodicWeakDerivativeList_nil _ _).mpr
    apply Lp.ext
    exact (PeriodicSobolevSpace.toL2_ofSmooth_ae t f hf).trans
      (PeriodicSobolevSpace.toL2_ofSmooth_ae s f hf).symm
  | cons i is ih =>
    exact ih.cons ((hf.coordinateDerivList is).hasPeriodicWeakDerivative i t t)

/-- A Sobolev field has every iterated distributional derivative in the level
obtained by subtracting its order (`app:ch_background:prop:bg-inverse`). -/
theorem exists_periodicWeakDerivativeList_of_mem (s : ℕ) (is : List (Fin n))
    (u : PeriodicL2 n F) (hu : u ∈ periodicSobolevLevel n F (s + is.length)) :
    ∃ v : PeriodicL2 n F,
      v ∈ periodicSobolevLevel n F s ∧ HasPeriodicWeakDerivativeList is u v := by
  induction is generalizing s with
  | nil => exact ⟨u, hu, .nil u⟩
  | cons i is ih =>
    have hu' : u ∈ periodicSobolevLevel n F ((s + 1) + is.length) := by
      simpa only [List.length_cons, Nat.add_right_comm, Nat.add_assoc] using hu
    obtain ⟨v, hv, hdv⟩ := ih (s + 1) hu'
    obtain ⟨w, hw, hdw⟩ := (exists_periodicWeakDerivatives_of_mem_succ s v hv).2 i
    exact ⟨w, hw, hdv.cons hdw⟩

/-- Any L² representative of an iterated derivative of an `H^(s+|is|)`
field belongs to `H^s`, by distributional uniqueness
(`app:ch_background:prop:bg-inverse`). -/
theorem HasPeriodicWeakDerivativeList.mem_periodicSobolevLevel {s : ℕ}
    {is : List (Fin n)} {u v : PeriodicL2 n F} (h : HasPeriodicWeakDerivativeList is u v)
    (hu : u ∈ periodicSobolevLevel n F (s + is.length)) :
    v ∈ periodicSobolevLevel n F s := by
  obtain ⟨w, hw, hd⟩ := exists_periodicWeakDerivativeList_of_mem s is u hu
  rwa [h.unique hd]

/-- L² representatives of all distributional derivatives through order `s`
imply integer Fourier Sobolev membership. Compatibility between successive
derivatives is proved from their test identities, not assumed
(`app:ch_background:prop:bg-inverse`). -/
theorem mem_periodicSobolevLevel_of_weakDerivativeLists (s : ℕ) (u : PeriodicL2 n F)
    (h : ∀ is : List (Fin n), is.length ≤ s →
      ∃ v : PeriodicL2 n F, HasPeriodicWeakDerivativeList is u v) :
    u ∈ periodicSobolevLevel n F s := by
  induction s generalizing u with
  | zero => rw [periodicSobolevLevel_zero]; trivial
  | succ s ih =>
    apply (mem_periodicSobolevLevel_succ_iff s u).mpr
    refine ⟨ih u (fun is his ↦ h is (his.trans (Nat.le_succ s))), ?_⟩
    intro i
    obtain ⟨v, hv⟩ := h [i] (by simp)
    have hv' := (hasPeriodicWeakDerivativeList_singleton i u v).mp hv
    refine ⟨v, ih v ?_, hv'⟩
    intro is his
    obtain ⟨w, hw⟩ := h (is ++ [i]) (by simpa using Nat.succ_le_succ his)
    exact ⟨w, hw.of_append_singleton hv'⟩

/-- Integer Sobolev membership is precisely L² representability of all
distributional derivatives up to that order, in every dimension including zero
(`app:ch_background:prop:bg-inverse`). -/
theorem mem_periodicSobolevLevel_iff_weakDerivativeLists (s : ℕ) (u : PeriodicL2 n F) :
    u ∈ periodicSobolevLevel n F s ↔
      ∀ is : List (Fin n), is.length ≤ s →
        ∃ v : PeriodicL2 n F, HasPeriodicWeakDerivativeList is u v := by
  refine ⟨?_, mem_periodicSobolevLevel_of_weakDerivativeLists s u⟩
  intro hu is his
  obtain ⟨v, _, hv⟩ := exists_periodicWeakDerivativeList_of_mem 0 is u
    (by simpa only [Nat.zero_add] using antitone_periodicSobolevLevel his hu)
  exact ⟨v, hv⟩

/-- The precise induction step in the inverse regularity argument: an `H^s`
field whose order `s+1` distributional derivatives are in L² lies in `H^(s+1)`
(`app:ch_background:prop:bg-inverse`). -/
theorem mem_periodicSobolevLevel_succ_of_top_weakDerivativeLists (s : ℕ)
    (u : PeriodicL2 n F) (hu : u ∈ periodicSobolevLevel n F s)
    (h : ∀ is : List (Fin n), is.length = s + 1 →
      ∃ v : PeriodicL2 n F, HasPeriodicWeakDerivativeList is u v) :
    u ∈ periodicSobolevLevel n F (s + 1) := by
  apply mem_periodicSobolevLevel_of_weakDerivativeLists
  intro is his
  rcases Nat.eq_or_lt_of_le his with heq | hlt
  · exact h is heq
  · exact (mem_periodicSobolevLevel_iff_weakDerivativeLists s u).mp hu is
      (Nat.lt_succ_iff.mp hlt)

end JanetCartan
