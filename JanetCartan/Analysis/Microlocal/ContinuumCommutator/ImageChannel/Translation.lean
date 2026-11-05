module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Translation.Estimates

/-!
# The translation commutator of the literal image normal

For `app:ch_background:eq:bg-commutator` and `app:ch_background:prop:bg-inverse`,
the actual `imageChannel c χmeas χsrc` and its Hilbert adjoint have a uniform
divided-translation bound. The proof expands its finite coefficient/Bessel
factorization; no global PDO representation of an image remainder is required.

The primitive first jets have exactly the `iteratedFDeriv` form supplied by
`ContinuumRow.ImageGeometry.exists_reference_imageChannel` and
`ContinuumRow.HistoryImage.exists_imageChannel`, at order one. The common
coefficient profile and the fixed cutoffs provide the budgets. The parent
`jc-continuum-elliptic-bootstrap` must instantiate these inputs for its same row,
add the carrier/exterior bound of `Translation.Assembly`, and supply coercivity
to `periodicCoerciveInverseH1`. Those mixed-normal and geometric instantiations
are not asserted here.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannelTranslation

open ContinuumRow

variable {n : ℕ}

private theorem coordinate_bound_of_first_jet (f : Euclidean n → ℝ)
    {K : ℝ} (hK : ∀ x, ‖iteratedFDeriv ℝ 1 f x‖ ≤ K) (i : Fin n) (x : Euclidean n) :
    ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ K := by
  have hb := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i 1)
  have hj := hK x
  rw [norm_iteratedFDeriv_one] at hj
  simpa [EuclideanSpace.single, PiLp.norm_single] using hb.trans
    (mul_le_mul_of_nonneg_right hj (norm_nonneg _))

/-- Explicit uniform bound for the SAME image operator composed with its
literal Hilbert adjoint. The constant uses only dimension and fixed C¹ budgets,
including both cutoffs and all first/zeroth coefficients, and works for every
step (even the totalized zero step). This is the image contribution to the
translation hypothesis of `periodicCoerciveInverseH1`
(`app:ch_background:eq:bg-commutator`; `app:ch_background:prop:bg-inverse`). -/
theorem norm_conjugationDifference_imageNormal_le
    {C K M S Km Ks : ℝ} (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hM0 : 0 ≤ M) (hS0 : 0 ≤ S) (hKm0 : 0 ≤ Km) (hKs0 : 0 ≤ Ks)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (hC : ∀ j x, |c j x| ≤ C)
    (hK : ∀ j x, ‖iteratedFDeriv ℝ 1 (periodicLift (c j)) x‖ ≤ K)
    (χmeas χsrc : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic χmeas) (hs : IsSmoothPeriodic χsrc)
    (hM : ∀ x, ‖χmeas x‖ ≤ M) (hS : ∀ x, ‖χsrc x‖ ≤ S)
    (hKm : ∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift χmeas) x‖ ≤ Km)
    (hKs : ∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift χsrc) x‖ ≤ Ks)
    (i : Fin n) (h : ℝ) :
    let L := (n : ℝ) ^ 3 + (n : ℝ) ^ 2
    let A := imageChannel c χmeas χsrc
    ‖periodicConjugationDifference (A.comp A.adjoint) i h‖ ≤
      2 * (M * (L * C) * S) * (Km * (L * C * S) + M * (L * K * S + L * C * Ks)) := by
  dsimp only
  have hn : ‖imageChannel c χmeas χsrc‖ ≤
      M * (((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * C) * S := by
    have hb := imageChannel_norm_le_of_bounds c χmeas χsrc hC0 hC0
      (fun j r s ↦ hC _) (fun r s ↦ hC _)
    rw [← add_mul] at hb
    apply hb.trans
    gcongr
    · exact (ContinuousMap.norm_le _ hM0).mpr hM
    · exact (ContinuousMap.norm_le _ hS0).mpr hS
  have hd := norm_conjugationDifference_imageChannel_le hC0 hK0 hM0 hS0 hKm0 hKs0
    c (fun j ↦ (hc j).2.differentiable (by simp)) hC χmeas χsrc
    (hm.2.differentiable (by simp)) (hs.2.differentiable (by simp)) hM hS i
    (fun j ↦ coordinate_bound_of_first_jet _ (hK j) i)
    (coordinate_bound_of_first_jet _ hKm i) (coordinate_bound_of_first_jet _ hKs i) h
  apply (norm_conjugationDifference_normal_le _ i h).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hd
    (norm_nonneg _) (by positivity)

/-- Choose a single image-normal translation constant BEFORE the coefficient
arrays, the cutoffs within their fixed budgets, the coordinate, and the step.
The assumptions are primitive smoothness/value/first-jet data, supplied by the
common coefficient profile and the fixed cutoff construction. No normal or
commutator estimate is an input (`app:ch_background:prop:bg-inverse`). -/
theorem exists_uniform_imageNormal_translation_bound
    (n : ℕ) (C K M S Km Ks : ℝ) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hM0 : 0 ≤ M) (hS0 : 0 ≤ S) (hKm0 : 0 ≤ Km) (hKs0 : 0 ≤ Ks) :
    ∃ B ≥ 0,
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)),
      (∀ j, IsSmoothPeriodic (c j)) →
      (∀ j x, |c j x| ≤ C) →
      (∀ j x, ‖iteratedFDeriv ℝ 1 (periodicLift (c j)) x‖ ≤ K) →
      ∀ (χmeas χsrc : C(Torus n, ℝ)),
      IsSmoothPeriodic χmeas → IsSmoothPeriodic χsrc →
      (∀ x, ‖χmeas x‖ ≤ M) → (∀ x, ‖χsrc x‖ ≤ S) →
      (∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift χmeas) x‖ ≤ Km) →
      (∀ x, ‖iteratedFDeriv ℝ 1 (periodicLift χsrc) x‖ ≤ Ks) →
      ∀ (i : Fin n) (h : ℝ),
        ‖periodicConjugationDifference
          ((imageChannel c χmeas χsrc).comp (imageChannel c χmeas χsrc).adjoint) i h‖ ≤ B := by
  let L := (n : ℝ) ^ 3 + (n : ℝ) ^ 2
  refine ⟨2 * (M * (L * C) * S) *
    (Km * (L * C * S) + M * (L * K * S + L * C * Ks)), by dsimp [L]; positivity, ?_⟩
  intro c hc hC hK χmeas χsrc hm hs hM hS hKm hKs i h
  exact norm_conjugationDifference_imageNormal_le hC0 hK0 hM0 hS0 hKm0 hKs0
    c hc hC hK χmeas χsrc hm hs hM hS hKm hKs i h

end JanetCartan.ContinuumCommutator.ImageChannelTranslation
