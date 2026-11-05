module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.SuccessorJet
public import JanetCartan.Analysis.Sobolev.Local.Fourier.VectorDerivatives

/-!
# Natural-order vector Fourier regularity constructs genuine weak jets

The whole-space and restriction conversions for `app:not:fourier` and
`app:ch_regular_base:eq:sector-theorem-residual`. The constant depends only
on dimension, finite fiber dimension, and derivative order. Coordinate
derivatives retain the `2π` normalization, and every multilinear operator
norm is bounded by the proved tensor synthesis estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

namespace JanetCartan.LocalSobolev

open Pseudodifferential

/-- Every natural Fourier order constructs a genuine weak jet of the chosen
L² representative with an explicit dimension-only constant. This is the
norm conversion for `app:not:fourier`; no weak jet or norm comparison is
assumed in the input. -/
theorem exists_vector_weakJet_nat_explicit (n r s : ℕ)
    (u : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hu : MemVectorFourierSobolev (s : ℝ) u) :
    ∃ J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
        (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] EuclideanSpace ℂ (Fin r),
      Mollification.HasWeakJetOn volume u J univ s ∧
      (∀ j ≤ s, MemLp (J j) 2 volume) ∧
      (∑ j ∈ Finset.range (s + 1), (eLpNorm (J j) 2 volume).toReal) ≤
        ((((r : ℝ) + 1) * (1 + 2 * Real.pi * n)) ^ s) * vectorFourierSobolevNorm (s : ℝ) u := by
  let C : ℝ := ((r : ℝ) + 1) * (1 + 2 * Real.pi * n)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (by linarith [Nat.cast_nonneg (α := ℝ) r]) (le_add_of_nonneg_right (by positivity))
  induction s generalizing u with
  | zero =>
    let J := fun j ↦ iteratedFDeriv ℝ j (u : EuclideanSpace ℝ (Fin n) → _)
    have hm : MemLp (J 0) 2 volume :=
      (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin r))).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' (Lp.memLp u)
    refine ⟨J, ⟨rfl, fun j hj ↦ by omega⟩, ?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      exact hm
    · have hzero : eLpNorm (J 0) 2 volume = eLpNorm u 2 volume := by
        apply eLpNorm_congr_norm_ae hm.aestronglyMeasurable (Lp.aestronglyMeasurable u)
        exact Eventually.of_forall fun x ↦ norm_iteratedFDeriv_zero
      simp [hzero, ← Lp.norm_def]
  | succ s ih =>
    have hu' : MemVectorFourierSobolev ((s : ℝ) + 1) u := by
      simpa only [Nat.cast_add, Nat.cast_one] using hu
    obtain ⟨v, hv, hD, hb⟩ := exists_vector_coordinateDerivatives_norm_bounds
      (s := (s : ℝ)) (by positivity) u hu'
    choose K hw hm hnorm using fun i ↦ ih (v i) (hv i)
    refine ⟨successorWeakJet u K, hasWeakJetOn_successorWeakJet hD hw,
      memLp_successorWeakJet (Lp.memLp u) hm, ?_⟩
    calc
      _ ≤ ‖u‖ + ∑ i, ∑ j ∈ Finset.range (s + 1), (eLpNorm (K i j) 2 volume).toReal :=
        successorWeakJet_normSum_le (Lp.memLp u) hm
      _ ≤ C ^ s * ‖u‖ + ∑ i, C ^ s * vectorFourierSobolevNorm (s : ℝ) (v i) :=
        add_le_add (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hC))
          (Finset.sum_le_sum fun i _ ↦ hnorm i)
      _ = C ^ s * (‖u‖ + ∑ i, vectorFourierSobolevNorm (s : ℝ) (v i)) := by
        rw [mul_add, Finset.mul_sum]
      _ ≤ C ^ s * (C * vectorFourierSobolevNorm ((s : ℝ) + 1) u) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- The positive constant precedes the whole-space datum at every natural
order, as needed by the sector estimate in
`app:ch_regular_base:eq:sector-theorem-residual`. -/
theorem exists_vector_weakJet_nat (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))), MemVectorFourierSobolev (s : ℝ) u →
      ∃ J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
          (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] EuclideanSpace ℂ (Fin r),
        Mollification.HasWeakJetOn volume u J univ s ∧
        (∀ j ≤ s, MemLp (J j) 2 volume) ∧
        (∑ j ∈ Finset.range (s + 1), (eLpNorm (J j) 2 volume).toReal) ≤
          C * vectorFourierSobolevNorm (s : ℝ) u :=
  ⟨(((r : ℝ) + 1) * (1 + 2 * Real.pi * n)) ^ s, by positivity,
    exists_vector_weakJet_nat_explicit n r s⟩

/-- Natural-order vector Fourier regularity constructs actual whole-space
extensions of any agreeing local L² class, for `app:not:fourier`. -/
theorem exists_vector_sobolevExtension_nat (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))), MemVectorFourierSobolev (s : ℝ) u →
      ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 U (EuclideanSpace ℂ (Fin r))),
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      ∃ e : SobolevExtension U s v,
        e.toFun = u ∧ e.toL2 = u ∧ e.jetNorm ≤ C * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, h⟩ := exists_vector_weakJet_nat n r s
  refine ⟨C, hC, fun u hu U v huv ↦ ?_⟩
  obtain ⟨J, hw, hm, hb⟩ := h u hu
  let e : SobolevExtension U s v := ⟨u, J, hw, Lp.memLp u, hm, huv⟩
  refine ⟨e, rfl, ?_, hb⟩
  apply Lp.ext
  exact e.toL2_coeFn

/-- Natural-order Fourier membership implies genuine restriction membership
and the restriction norm estimate, for
`app:ch_regular_base:eq:sector-theorem-residual`. The parent construction must
supply the actual Fourier premise and a.e. restriction identity. -/
theorem vector_restrictionSobolev_nat_bounds (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))), MemVectorFourierSobolev (s : ℝ) u →
      ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 U (EuclideanSpace ℂ (Fin r))),
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      MemRestrictionSobolev U s v ∧
        restrictionSobolevNorm U s v ≤ C * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, h⟩ := exists_vector_sobolevExtension_nat n r s
  refine ⟨C, hC, fun u hu U v huv ↦ ?_⟩
  obtain ⟨e, _, _, hb⟩ := h u hu U v huv
  exact ⟨⟨e⟩, (restrictionSobolevNorm_le e).trans hb⟩

end JanetCartan.LocalSobolev
