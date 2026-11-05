module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Source

/-!
# Qualitative closure of literal reverse coefficients

The admissibility predicate for the reverse specialization of
`fullAmplitudeDerivativeTerms_expansion_of_regularized_pairings` contains only
primitive smoothness and physical support. Smoothness is required away from zero
frequency. The phase gap is imposed only on the common physical support.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- First output amplitude for an already reversed coefficient. It differentiates
`y`, retaining original `(x,y,η)` order and introducing no further conjugation.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def reverseFirstOutputAmplitude (C : FullAmplitude n r) (i : Fin n) : FullAmplitude n r :=
  fun x y η ↦ partialDeriv (fun z ↦ C x z η) y i +
    (Complex.I * (η i : ℂ)) • C x y η

/-- Qualitative reverse-amplitude admissibility for the finite weak expansion.
The support is in original `(x,y)` order; the amplitude is already conjugate
transposed at initialization. No operator identity is part of this predicate.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
structure ReverseAmplitudeAdmissible (K : Set (E × E)) (C : FullAmplitude n r) : Prop where
  smooth : ∀ p : (E × E) × E, p.2 ≠ 0 →
    ContDiffAt ℝ ∞ (fun q : (E × E) × E ↦ C q.1.1 q.1.2 q.2) p
  support : tsupport (fun p : (E × E) × E ↦ C p.1.1 p.1.2 p.2) ⊆
    {p | p.1 ∈ K}

private theorem contDiffAt_reverse_sourcePartial
    (C : FullAmplitude n r) (p : (E × E) × E)
    (hC : ContDiffAt ℝ ∞ (fun q : (E × E) × E ↦ C q.1.1 q.1.2 q.2) p)
    (i : Fin n) : ContDiffAt ℝ ∞
      (fun q : (E × E) × E ↦ partialDeriv (fun x ↦ C x q.1.2 q.2) q.1.1 i) p := by
  have h := hC.comp (p, p.1.1)
    ((contDiffAt_snd.prodMk contDiffAt_fst.fst.snd).prodMk contDiffAt_fst.snd)
  exact (h.fderiv contDiffAt_fst.fst (by simp)).clm_apply contDiffAt_const

private theorem contDiffAt_reverse_outputPartial
    (C : FullAmplitude n r) (p : (E × E) × E)
    (hC : ContDiffAt ℝ ∞ (fun q : (E × E) × E ↦ C q.1.1 q.1.2 q.2) p)
    (i : Fin n) : ContDiffAt ℝ ∞
      (fun q : (E × E) × E ↦ partialDeriv (fun y ↦ C q.1.1 y q.2) q.1.2 i) p := by
  have h := hC.comp (p, p.1.2)
    ((contDiffAt_fst.fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
  exact (h.fderiv contDiffAt_fst.snd (by simp)).clm_apply contDiffAt_const

/-- Primitive phase smoothness implies joint smoothness of the actual mixed
matrix, in the coordinate order used in the adjoint trade. Consumed by reverse
coefficient closure. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem contDiffAt_mixedPhaseMatrix_of_phase
    (S : E → E → ℝ) (p : E × E)
    (hS : ContDiffAt ℝ ∞ (Function.uncurry S) p) :
    ContDiffAt ℝ ∞ (Function.uncurry (mixedPhaseMatrix S)) p := by
  let pack : (Fin n → Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { LinearMap.id with cont := continuous_id }
  apply pack.contDiff.contDiffAt.comp p
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hx : ContDiffAt ℝ ∞
      (fun q : E × E ↦ partialDeriv (fun x ↦ S x q.2) q.1 i) p := by
    have h := hS.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    exact (h.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const
  have h := hx.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (h.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

/-- Smoothness of the actual matrix inverse follows from primitive phase
smoothness and its determinant gap; it is not an assumed coefficient field.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem contDiffAt_mixedPhaseMatrix_inverse_of_phase
    (S : E → E → ℝ) (p : E × E)
    (hS : ContDiffAt ℝ ∞ (Function.uncurry S) p)
    (hinv : IsUnit (mixedPhaseMatrix S p.1 p.2).det) :
    ContDiffAt ℝ ∞ (fun q : E × E ↦ (mixedPhaseMatrix S q.1 q.2)⁻¹) p := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr hinv
  have hi : ContDiffAt ℝ ∞ Ring.inverse (mixedPhaseMatrix S p.1 p.2) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def, Function.uncurry_def] using
    hi.comp p (contDiffAt_mixedPhaseMatrix_of_phase S p hS)

private theorem reverse_sourcePartial_eq_zero_of_notMem_tsupport
    (C : FullAmplitude n r) (p : (E × E) × E)
    (hp : p ∉ tsupport (fun q : (E × E) × E ↦ C q.1.1 q.1.2 q.2))
    (i : Fin n) : partialDeriv (fun x ↦ C x p.1.2 p.2) p.1.1 i = 0 := by
  have he := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
    (((continuous_id.prodMk continuous_const).prodMk continuous_const).tendsto p.1.1)
  rw [partialDeriv, fderiv_of_notMem_tsupport ℝ]
  · rfl
  · exact notMem_tsupport_iff_eventuallyEq.mpr he

private theorem reverse_outputPartial_eq_zero_of_notMem_tsupport
    (C : FullAmplitude n r) (p : (E × E) × E)
    (hp : p ∉ tsupport (fun q : (E × E) × E ↦ C q.1.1 q.1.2 q.2))
    (i : Fin n) : partialDeriv (fun y ↦ C p.1.1 y p.2) p.1.2 i = 0 := by
  have he := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
    (((continuous_const.prodMk continuous_id).prodMk continuous_const).tendsto p.1.2)
  rw [partialDeriv, fderiv_of_notMem_tsupport ℝ]
  · rfl
  · exact notMem_tsupport_iff_eventuallyEq.mpr he

/-- Multiplication by the actual mixed inverse does not enlarge support.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem tsupport_adjointTransferDatum_subset
    (S : E → E → ℝ) (C : FullAmplitude n r) (i j : Fin n) :
    tsupport (fun p : (E × E) × E ↦ adjointTransferDatum S i j C p.1.1 p.1.2 p.2) ⊆
      tsupport (fun p : (E × E) × E ↦ C p.1.1 p.1.2 p.2) :=
  tsupport_smul_subset_right _ _

/-- All physical derivatives in the full reverse remainder preserve support,
including the derivatives of the inverse-weighted datum branches.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem tsupport_adjointTransferRemainder_subset
    (S : E → E → ℝ) (C : FullAmplitude n r) (i : Fin n) :
    tsupport (fun p : (E × E) × E ↦ adjointTransferRemainder S i C p.1.1 p.1.2 p.2) ⊆
      tsupport (fun p : (E × E) × E ↦ C p.1.1 p.1.2 p.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hy := reverse_outputPartial_eq_zero_of_notMem_tsupport C p hn i
  have hx (j) := reverse_sourcePartial_eq_zero_of_notMem_tsupport
    (adjointTransferDatum S i j C) p
    (fun hm ↦ hn (tsupport_adjointTransferDatum_subset S C i j hm)) j
  exact hp (by simp [adjointTransferRemainder, hy, hx])

/-- Admissibility of each reverse datum branch, from primitive phase smoothness
and the actual inverse gap only on the physical support. This discharges `hP`
in the reverse finite expansion. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem ReverseAmplitudeAdmissible.adjointTransferDatum
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (i j : Fin n) : ReverseAmplitudeAdmissible K (adjointTransferDatum S i j C) := by
  refine ⟨?_, (tsupport_adjointTransferDatum_subset S C i j).trans hC.support⟩
  intro p hη
  by_cases hp : p ∈ tsupport (fun q : (E × E) × E ↦ C q.1.1 q.1.2 q.2)
  · let ev : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))
    have hi := contDiffAt_mixedPhaseMatrix_inverse_of_phase S (p.1.1, p.2)
      (hS _ _ hη) (hinv p.1 (hC.support hp) p.2 hη)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (ev.contDiff.contDiffAt.comp p (hi.comp p
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)))).smul (hC.smooth p hη)
  · apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    change C q.1.1 q.1.2 q.2 = 0 at hq
    change (_ : ℂ) • C q.1.1 q.1.2 q.2 = 0
    rw [hq, smul_zero]

/-- Admissibility of the full reverse remainder. Both physical derivatives and
the derivative of the complete inverse product are retained. This discharges
`hR` in the reverse finite expansion.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.adjointTransferRemainder
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (i : Fin n) : ReverseAmplitudeAdmissible K (adjointTransferRemainder S i C) := by
  refine ⟨?_, (tsupport_adjointTransferRemainder_subset S C i).trans hC.support⟩
  intro p hη
  exact (contDiffAt_reverse_outputPartial C p (hC.smooth p hη) i).add
    (ContDiffAt.sum fun j _ ↦ contDiffAt_reverse_sourcePartial _ p
      ((hC.adjointTransferDatum S hS hinv i j).smooth p hη) j)

/-- The first output amplitude is admissible as well. This is used only for
compact regularized integration; no symbol-order bound is claimed.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem ReverseAmplitudeAdmissible.reverseFirstOutputAmplitude
    {K : Set (E × E)} {C : FullAmplitude n r} (hC : ReverseAmplitudeAdmissible K C)
    (i : Fin n) : ReverseAmplitudeAdmissible K (reverseFirstOutputAmplitude C i) := by
  refine ⟨?_, Set.Subset.trans ?_ hC.support⟩
  · intro p hη
    have hc : ContDiffAt ℝ ∞ (fun q : (E × E) × E ↦ Complex.I * (q.2 i : ℂ)) p := by
      apply contDiffAt_const.mul
      apply Complex.ofRealCLM.contDiff.contDiffAt.comp p
      exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).contDiff.contDiffAt.comp p contDiffAt_snd
    exact (contDiffAt_reverse_outputPartial C p (hC.smooth p hη) i).add
      (hc.smul (hC.smooth p hη))
  · apply closure_minimal _ (isClosed_tsupport _)
    intro p hp
    by_contra hn
    have hy := reverse_outputPartial_eq_zero_of_notMem_tsupport C p hn i
    have hz := image_eq_zero_of_notMem_tsupport hn
    exact hp (by simp [FourierIntegral.reverseFirstOutputAmplitude, hy, hz])

/-- Differentiating the already reversed oscillatory amplitude produces the
explicit first output amplitude, without conjugating a transfer branch.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem partialDeriv_reverseGraphOscillation_smul_amplitude
    (S : E → E → ℝ) (C : FullAmplitude n r) (x y η : E) (i : Fin n)
    (hC : DifferentiableAt ℝ (fun z ↦ C x z η) y) :
    partialDeriv (fun z ↦ star (graphOscillation S x z η) • C x z η) y i =
      star (graphOscillation S x y η) • reverseFirstOutputAmplitude C i x y η := by
  simpa only [adjointFirstOutputAmplitude, reverseFirstOutputAmplitude,
    Matrix.conjTranspose_conjTranspose] using
    partialDeriv_adjointGraphOscillation_smul_amplitude S
      (fun x y η ↦ (C x y η).conjTranspose) x y η i hC.star

end JanetCartan.FourierIntegral
