module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstDerivatives
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.TransferAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Transfer

/-!
# Source integration by parts for the nonlinear graph and its literal adjoint

The fixed physical covector step of
`app:ch_regular_base:eq:graph-derivative-transfer`. These identities retain the
entire two-position amplitude, including every physical mask. The reverse
amplitude `C` is stored in original coordinate order and is initialized by
`C x y η = (A x y η).conjTranspose`.

The consumer is the compact-frequency weak derivative argument in `WeakTransfer`.
These are source integral identities, not yet weak operator derivatives.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Forward source transfer with the shared coefficients, using Euler's identity
for the actual phase. Source: `app:ch_regular_base:eq:graph-derivative-transfer`.
The neighborhood homogeneity is precisely that of `PhaseTrade`. -/
theorem integral_graphFirstOutputAmplitude_transfer
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ) (x η : Euclidean n) (i : Fin n)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hx : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hη : ∀ j, DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η)
    (hhom : ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η)) :
    (∫ y, graphOscillation S x y η • (graphFirstOutputAmplitude S A i x y η).mulVec (u y)) =
      (∫ y, graphOscillation S x y η • (graphTransferRemainder S i A x y η).mulVec (u y)) +
      ∑ j, ∫ y, graphOscillation S x y η •
        (graphTransferDatum S i j A x y η).mulVec (partialDeriv u y j) := by
  exact ResponseTransfer.integral_forwardOutputAmplitude_transfer S A
    (mixedPhaseMatrix S) u x η i hA hu hus
    (partialDeriv_eq_mixedPhaseMatrix_mulVec hx hη hhom i)

private theorem smooth_mulVec
    {a : Euclidean n → Matrix (Fin r) (Fin r) ℂ} {u : Euclidean n → Fin r → ℂ}
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x ↦ (a x).mulVec (u x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ ∞ (fun x ↦ ∑ k, a x i k * u x k)
  have ha' (k : Fin r) : ContDiff ℝ ∞ (fun x ↦ a x i k) := by
    let ev : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M ↦ M i k
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact ev.toContinuousLinearMap.contDiff.comp ha
  exact ContDiff.sum (fun k _ ↦ (ha' k).mul (contDiff_pi.mp hu k))

private theorem compact_mulVec
    (a : Euclidean n → Matrix (Fin r) (Fin r) ℂ) {u : Euclidean n → Fin r → ℂ}
    (hus : HasCompactSupport u) : HasCompactSupport (fun x ↦ (a x).mulVec (u x)) := by
  apply hus.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp [hx]

private theorem integrable_smul_mulVec
    {e : Euclidean n → ℂ} {a : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    {u : Euclidean n → Fin r → ℂ}
    (he : Continuous e) (ha : Continuous a) (hu : Continuous u)
    (hus : HasCompactSupport u) :
    Integrable (fun x ↦ e x • (a x).mulVec (u x)) := by
  have hc : Continuous (fun x ↦ (a x).mulVec (u x)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact (he.smul hc).integrable_of_hasCompactSupport (compact_mulVec a hus).smul_left

/-- Source integration by parts for the conjugate oscillation against the entire
matrix amplitude. In the adjoint trade `a x` is the product of the actual inverse
coefficient with `C x y η`; its derivative includes both factors.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem adjointGraphOscillation_source_mulVec_integration_by_parts
    (S : Euclidean n → Euclidean n → ℝ) (y η : Euclidean n) (j : Fin n)
    (a : Euclidean n → Matrix (Fin r) (Fin r) ℂ) (u : Euclidean n → Fin r → ℂ)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η))
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    -(∫ x, partialDeriv (fun z ↦ star (graphOscillation S z y η)) x j •
      (a x).mulVec (u x)) =
      (∫ x, star (graphOscillation S x y η) • (partialDeriv a x j).mulVec (u x)) +
      ∫ x, star (graphOscillation S x y η) • (a x).mulVec (partialDeriv u x j) := by
  let e := fun x ↦ star (graphOscillation S x y η)
  have he : ContDiff ℝ ∞ e := by
    dsimp only [e]
    simp_rw [star_graphOscillation]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub hS))).cexp
  have hg := smooth_mulVec ha hu
  have hgs := compact_mulVec a hus
  have hi : Integrable (fun x ↦ e x • (a x).mulVec (u x)) :=
    (he.continuous.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hie : Integrable (fun x ↦ partialDeriv e x j • (a x).mulVec (u x)) :=
    (((he.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hig : Integrable (fun x ↦ e x • partialDeriv (fun z ↦ (a z).mulVec (u z)) x j) :=
    (he.continuous.smul ((hg.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hgs.fderiv_apply ℝ (EuclideanSpace.single j 1)).smul_left
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hie hig hi
    (fun x _ ↦ he.differentiable (by simp) x) (fun x _ ↦ hg.differentiable (by simp) x)
  change (∫ x, e x • partialDeriv (fun z ↦ (a z).mulVec (u z)) x j) =
    -(∫ x, partialDeriv e x j • (a x).mulVec (u x)) at h
  rw [← h]
  simp_rw [ResponseTransfer.partialDeriv_matrix_mulVec a u _ j
    (ha.differentiable (by simp) _) (hu.differentiable (by simp) _), smul_add]
  apply integral_add
  · exact integrable_smul_mulVec he.continuous
      ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) hu.continuous hus
  · exact integrable_smul_mulVec he.continuous ha.continuous
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hus.fderiv_apply ℝ (EuclideanSpace.single j 1))

/-- The actual inverse phase trade integrated in the adjoint source position.
The smoothness premise concerns the explicit inverse-weighted coefficients, not
an operator recurrence. It is discharged from the smooth mixed inverse on the
phase chart. Homogeneity and the inverse gap are required only where `C ≠ 0`. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem integral_adjointGraphOscillation_transfer
    (S : Euclidean n → Euclidean n → ℝ) (C : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ) (y η : Euclidean n) (i : Fin n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η))
    (hP : ∀ j, ContDiff ℝ ∞ (fun x ↦ adjointTransferDatum S i j C x y η))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hη : ∀ x, C x y η ≠ 0 → ∀ j,
      DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η)
    (hhom : ∀ x, C x y η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η))
    (hinv : ∀ x, C x y η ≠ 0 → IsUnit (mixedPhaseMatrix S x η).det) :
    (Complex.I * (η i : ℂ)) • (∫ x, star (graphOscillation S x y η) •
      (C x y η).mulVec (u x)) =
      ∑ j, ((∫ x, star (graphOscillation S x y η) •
        (partialDeriv (fun z ↦ adjointTransferDatum S i j C z y η) x j).mulVec (u x)) +
        ∫ x, star (graphOscillation S x y η) •
          (adjointTransferDatum S i j C x y η).mulVec (partialDeriv u x j)) := by
  let e := fun x ↦ star (graphOscillation S x y η)
  have he : ContDiff ℝ ∞ e := by
    dsimp only [e]
    simp_rw [star_graphOscillation]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub hS))).cexp
  have hp (x) : (Complex.I * (η i : ℂ)) • (e x • (C x y η).mulVec (u x)) =
      -∑ j, partialDeriv e x j • (adjointTransferDatum S i j C x y η).mulVec (u x) := by
    by_cases hz : C x y η = 0
    · simp [adjointTransferDatum, hz]
    rw [← mul_smul, graphOscillation_adjoint_trade
      (hS.differentiable (by simp) x) (hη x hz) (hhom x hz) (hinv x hz)]
    simp only [neg_smul, Finset.sum_smul, adjointTransferDatum, Matrix.smul_mulVec,
      mul_smul, e]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  have hi (j) : Integrable (fun x ↦ partialDeriv e x j •
      (adjointTransferDatum S i j C x y η).mulVec (u x)) :=
    integrable_smul_mulVec ((he.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hP j).continuous hu.continuous hus
  change (Complex.I * (η i : ℂ)) • (∫ x, e x • (C x y η).mulVec (u x)) = _
  rw [← integral_smul]
  simp_rw [hp]
  rw [integral_neg, integral_finsetSum Finset.univ (fun j _ ↦ hi j), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact adjointGraphOscillation_source_mulVec_integration_by_parts S y η j
    (fun x ↦ adjointTransferDatum S i j C x y η) u hS (hP j) hu hus

/-- Full first-output-amplitude transfer for a reverse graph. In particular,
putting `C = A†` gives the literal adjoint, without changing coordinates or
conjugating the coefficients a second time.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem integral_reverseFirstOutputAmplitude_transfer
    (S : Euclidean n → Euclidean n → ℝ) (C : FullAmplitude n r)
    (u : Euclidean n → Fin r → ℂ) (y η : Euclidean n) (i : Fin n)
    (hS : ContDiff ℝ ∞ (fun x ↦ S x η))
    (hC : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ C p.1 p.2 η))
    (hP : ∀ j, ContDiff ℝ ∞ (fun x ↦ adjointTransferDatum S i j C x y η))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hη : ∀ x, C x y η ≠ 0 → ∀ j,
      DifferentiableAt ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η)
    (hhom : ∀ x, C x y η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η))
    (hinv : ∀ x, C x y η ≠ 0 → IsUnit (mixedPhaseMatrix S x η).det) :
    (∫ x, star (graphOscillation S x y η) •
      (partialDeriv (fun z ↦ C x z η) y i + (Complex.I * (η i : ℂ)) • C x y η).mulVec (u x)) =
      (∫ x, star (graphOscillation S x y η) •
        (adjointTransferRemainder S i C x y η).mulVec (u x)) +
      ∑ j, ∫ x, star (graphOscillation S x y η) •
        (adjointTransferDatum S i j C x y η).mulVec (partialDeriv u x j) := by
  let e := fun x ↦ star (graphOscillation S x y η)
  let dy := fun x ↦ partialDeriv (fun z ↦ C x z η) y i
  have he : ContDiff ℝ ∞ e := by
    dsimp only [e]
    simp_rw [star_graphOscillation]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub hS))).cexp
  have hc : ContDiff ℝ ∞ (fun x ↦ C x y η) := hC.comp (contDiff_id.prodMk contDiff_const)
  have hdy : Continuous dy := by
    exact ((hC.fderiv (contDiff_const : ContDiff ℝ ∞ (fun _ : Euclidean n ↦ y))
      (by simp)).clm_apply contDiff_const).continuous
  have hi := integrable_smul_mulVec he.continuous hc.continuous hu.continuous hus
  have hiy := integrable_smul_mulVec he.continuous hdy hu.continuous hus
  have hip (j) : Integrable (fun x ↦ star (graphOscillation S x y η) •
      (partialDeriv (fun z ↦ adjointTransferDatum S i j C z y η) x j).mulVec (u x)) :=
    integrable_smul_mulVec he.continuous
    (((hP j).continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single j 1))) hu.continuous hus
  have ht := integral_adjointGraphOscillation_transfer S C u y η i hS hP hu hus hη hhom hinv
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, smul_add]
  simp_rw [smul_comm (star (graphOscillation S _ y η)) (Complex.I * (η i : ℂ))]
  have his : Integrable (fun x ↦ (Complex.I * (η i : ℂ)) •
      star (graphOscillation S x y η) • (C x y η).mulVec (u x)) :=
    hi.smul (Complex.I * (η i : ℂ))
  rw [integral_add hiy his, integral_smul, ht]
  simp only [adjointTransferRemainder, Matrix.add_mulVec, Matrix.sum_mulVec,
    smul_add, Finset.smul_sum]
  rw [integral_add hiy (integrable_finsetSum Finset.univ (fun j _ ↦ hip j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hip j), Finset.sum_add_distrib, add_assoc]

end JanetCartan.FourierIntegral
