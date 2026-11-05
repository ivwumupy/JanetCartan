module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Restriction
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Physical
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.Sector

/-!
# Conjugate letters in the normalized residual envelope

The sign in `selectedFullPhysicalResidualTerm` is whole-operator conjugation.
It is different from the literal adjoint in the characteristic envelope theorem.
Conjugation preserves every natural Fourier Sobolev order and changes the sign
of the physical carrier. These facts give the precise reflected-letter input
to the mixed-word application in `app:ch_response:eq:response-graded-reduced`.
The estimate for the original factor at the opposite carrier remains an input;
no characteristic envelope estimate is inferred from an adjoint estimate.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open Pseudodifferential LocalSobolev
open ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer ResponseTransfer.Complement RegularSector.Realization

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

local instance : StarModule ℝ H where
  star_smul c u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul (star c) (star u), Lp.coeFn_star u] with x h₁ h₂ h₃ h₄
    simp only [Pi.star_apply] at h₁ h₄
    simp only [h₁, h₂, h₃, Pi.smul_apply, h₄, star_smul]

private theorem starFiber_compLp (u : H) :
    (starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.compLp u = star u := by
  apply Lp.ext
  filter_upwards [(starL' ℝ : F ≃L[ℝ] F).toContinuousLinearMap.coeFn_compLp u,
    Lp.coeFn_star u] with x hx hy
  exact hx.trans hy.symm

/-- Whole conjugation has no derivative loss on the actual vector Fourier
Sobolev space. Genuine weak extensions produce the bound, so membership is
retained together with the numerical norm
(`app:ch_regular_base:eq:signed-graph-factor`). -/
theorem exists_star_fourierSobolev_constant (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (Euclidean n)), MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (star u) ∧
          vectorFourierSobolevNorm (s : ℝ) (star u) ≤
            C * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨A, hA, hforward⟩ := exists_vector_sobolevExtension_nat n r s
  obtain ⟨B, hB, hback⟩ := exists_vector_extension_fourier_constant n r s
  let L := (starL' ℝ : EuclideanSpace ℂ (Fin r) ≃L[ℝ]
    EuclideanSpace ℂ (Fin r)).toContinuousLinearMap
  refine ⟨B * (‖L‖ + 1) * A, by positivity, ?_⟩
  intro u hu
  let v : LocalL2 (univ : Set (Euclidean n)) (EuclideanSpace ℂ (Fin r)) :=
    ((Lp.memLp u).restrict univ).toLp u
  obtain ⟨e, _, he, heBound⟩ := hforward u hu univ v
    ((Lp.memLp u).restrict univ).coeFn_toLp.symm
  have hmap : (e.mapCLM L).toL2 = star u := by
    rw [e.toL2_mapCLM, he]
    exact starFiber_compLp u
  obtain ⟨hm, hb⟩ := hback univ _ (e.mapCLM L)
  rw [hmap] at hm hb
  refine ⟨hm, hb.trans ?_⟩
  calc
    B * (e.mapCLM L).jetNorm ≤ B * (‖L‖ * e.jetNorm) :=
      mul_le_mul_of_nonneg_left (e.jetNorm_mapCLM_le L) hB.le
    _ ≤ B * ((‖L‖ + 1) * e.jetNorm) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (by linarith : ‖L‖ ≤ ‖L‖ + 1) e.jetNorm_nonneg) hB.le
    _ ≤ B * ((‖L‖ + 1) * (A * vectorFourierSobolevNorm (s : ℝ) u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heBound (by positivity)) hB.le
    _ = (B * (‖L‖ + 1) * A) * vectorFourierSobolevNorm (s : ℝ) u := by ring

/-- An already proved envelope keeps its scale after whole conjugation.
This is used only for the reflected letters of the complete normalized
residual (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem hasEnvelopeProfile_star {I : Type*} {u : I → H} {A K : I → ℝ}
    (hu : HasEnvelopeProfile vectorFourierSobolevScale u A K) :
    HasEnvelopeProfile vectorFourierSobolevScale (fun i ↦ star (u i)) A K := by
  intro s
  obtain ⟨C, hC, hbound⟩ := hu s
  obtain ⟨D, hD, hstar⟩ := exists_star_fourierSobolev_constant n r s
  refine ⟨D * C, mul_nonneg hD.le hC, ?_⟩
  intro i
  obtain ⟨hm, hb⟩ := hbound i
  obtain ⟨hsm, hsb⟩ := hstar (u i) hm
  refine ⟨hsm, ?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hsm]
  rw [vectorFourierSobolevScale_gradeNorm s hm] at hb
  exact hsb.trans ((mul_le_mul_of_nonneg_left hb hD.le).trans_eq (by ring))

private theorem star_carrier (ρ : ℝ) (φ : E → ℝ) (x : E) :
    star (carrier ρ φ x) = carrier (-ρ) φ x := by
  simp only [carrier, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, neg_mul, Complex.ofReal_neg, mul_neg]

/-- The actual L² carrier changes sign under conjugation. This is the
reflected source needed by whole conjugate residual letters, with no
projection to either real quadrature (`app:ch_regular_base:eq:signed-graph-factor`). -/
theorem star_carrierMultiplication (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    star (carrierMultiplication ρ φ hφ u) =
      carrierMultiplication (-ρ) φ hφ (star u) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (carrierMultiplication ρ φ hφ u),
    carrierMultiplication_ae ρ φ hφ u,
    carrierMultiplication_ae (-ρ) φ hφ (star u), Lp.coeFn_star u]
    with x hstar hforward hback hu
  simp only [Pi.star_apply] at hstar hu
  rw [hstar, hforward, hback, hu, star_smul, star_carrier]

/-- Conjugating a literal factor and demodulating at the positive carrier
equals conjugating its negative-carrier envelope. The input and output
carriers retain their opposite signs
(`app:ch_response:eq:response-graded-reduced`). -/
theorem demodulated_boundedConjugate_eq (T : H →L[ℂ] H)
    (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    carrierMultiplication (-ρ) φ hφ
      (boundedConjugate T (carrierMultiplication ρ φ hφ u)) =
      star (carrierMultiplication ρ φ hφ
        (T (carrierMultiplication (-ρ) φ hφ (star u)))) := by
  change carrierMultiplication (-ρ) φ hφ
    (star (T (star (carrierMultiplication ρ φ hφ u)))) = _
  rw [star_carrierMultiplication, star_carrierMultiplication]

/-- Real directional derivative words commute with conjugation, including
at points where the total derivative uses its default value. The continuous
linear equivalence, rather than a differentiability premise, proves this
identity (`app:ch_response:cor:finite-jets`). -/
theorem orderedTransferAction_star {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (ps : List P) (u : P → H) :
    orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps (fun c ↦ star (u c)) =
      fun c ↦ star (orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps u c) := by
  induction ps with
  | nil => rfl
  | cons v ps ih =>
    simp only [orderedTransferAction, ih]
    funext c
    exact congrArg (fun D : P →L[ℝ] H ↦ D v)
      ((starL' ℝ : H ≃L[ℝ] H).comp_fderiv)

/-- The reflected normalized residual letter inherits the proved opposite
carrier envelope, for every ordered parameter derivative. The hypothesis
is the original operator's negative-carrier estimate; an adjoint estimate
cannot replace it (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem conjugate_letter_envelope_of_opposite_carrier
    {I P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : I → H →L[ℂ] H) (ρ A K : I → ℝ)
    (φ : I → P → E → ℝ) (hφ : ∀ i c, Continuous (φ i c))
    (u : I → P → H) (V : Set P) (ps : List P)
    (hnegative : HasEnvelopeProfile vectorFourierSobolevScale
      (fun q : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
        (fun c ↦ carrierMultiplication (ρ q.1) (φ q.1 c) (hφ q.1 c)
          (T q.1 (carrierMultiplication (-(ρ q.1)) (φ q.1 c) (hφ q.1 c)
            (star (u q.1 c))))) q.2)
      (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) :
    HasEnvelopeProfile vectorFourierSobolevScale
      (fun q : I × V ↦ orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
        (fun c ↦ carrierMultiplication (-(ρ q.1)) (φ q.1 c) (hφ q.1 c)
          (boundedConjugate (T q.1)
            (carrierMultiplication (ρ q.1) (φ q.1 c) (hφ q.1 c) (u q.1 c)))) q.2)
      (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  have hs := hasEnvelopeProfile_star hnegative
  apply (hasEnvelopeProfile_congr (f := fun q : I × V ↦ star
    (orderedTransferAction (fun v g c ↦ fderiv ℝ g c v) ps
      (fun c ↦ carrierMultiplication (ρ q.1) (φ q.1 c) (hφ q.1 c)
        (T q.1 (carrierMultiplication (-(ρ q.1)) (φ q.1 c) (hφ q.1 c)
          (star (u q.1 c))))) q.2)) ?_).mp hs
  intro q
  simp only [demodulated_boundedConjugate_eq, orderedTransferAction_star]

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
