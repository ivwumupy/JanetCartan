module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.OperatorIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Modulation
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.IntegratedEnvelope.Assembly.Words
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Restore the complete PDO after its literal annular split

The near part is the selected diagonal PDO estimate; the complementary part
is the actual complete-symbol kernel realization. Their exact L² equality
identifies every ordered parameter derivative of the SAME full physical PDO.
No smoothing order is lost when the arbitrary complementary precision is
chosen to match the original symbol order.

Consumers: the endpoint, algebraic and elliptic residual letters in
`app:ch_response:eq:fixed-factor-transfer`. The analytic inputs are produced by
`exists_diagonalPDO_joint_sobolev_of_primitive_jets`, its adjoint counterpart,
`contDiffOn_complete_diagonal_annular_envelope`, and
`completeDiagonalAnnularComplement_sobolev`; their concrete symbol instantiation
remains part of the one-letter construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes

open Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.AnnularComplement
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
open CharacteristicTransport.CompleteResidual

variable {d r : ℕ} {I Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The complementary kernel's almost-everywhere action is the literal
difference of the same two carrier-conjugated L² operators. The actual datum
is identified by its own representative (`new:eq:carrier-ibp`). -/
theorem remainder_eq_demodulated_difference_of_ae
    (Tfull Tcut : H →L[ℂ] H) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (a : E → F) (u R : H) (hu : u =ᵐ[volume] a)
    (hR : ∃ w : H, w =ᵐ[volume] (fun x ↦ carrier lam φ x • a x) ∧
      R =ᵐ[volume] fun x ↦ carrier (-lam) φ x • ((Tfull w - Tcut w) x)) :
    R = demodulatedL2Operator lam φ hφ Tfull u -
      demodulatedL2Operator lam φ hφ Tcut u := by
  obtain ⟨w,hw,hR⟩ := hR
  have hwu : w = carrierMultiplication lam φ hφ u := by
    apply Lp.ext
    filter_upwards [hw,hu,carrierMultiplication_ae lam φ hφ u] with x hx hux hmx
    rw [hx,hmx,hux]
  have hRe : R = carrierMultiplication (-lam) φ hφ (Tfull w - Tcut w) := by
    apply Lp.ext
    exact hR.trans (carrierMultiplication_ae (-lam) φ hφ (Tfull w-Tcut w)).symm
  rw [hRe,hwu,map_sub]
  rfl

/-- The full masked physical PDO retains its original order and all ordered
parameter envelopes after restoring the complete complementary symbol.
The two analytic inputs concern the actual near operator and actual remainder;
this deduction provides no substitute for their primitive-symbol producers
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem full_pdo_ordered_envelopes_of_annular_remainder
    (χout χsource : E → ℂ) (σ : I → E → E → Mat) (π : I → E → ℂ)
    (adj : Bool) (lam A K : I → ℝ) (p : ℤ)
    (hlam : ∀ i, 1 ≤ lam i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (φ : I → Par → E → ℝ) (hφ : ∀ i c, Continuous (φ i c))
    (a : I → Par → E → F) (u R : I → Par → H)
    {V : Set Par} (hV : IsOpen V)
    (hu : ∀ i c, c ∈ V → u i c =ᵐ[volume] a i c)
    (hRsm : ∀ i, ContDiffOn ℝ ∞ (R i) V) :
    let Tfull := fun i ↦ annularGraphOrientation adj (maskedPhysicalPDO χout χsource (σ i))
    let Tcut := fun i ↦ annularGraphOrientation adj (maskedPhysicalPDO χout χsource
      (fun y ξ ↦ π i ((lam i)⁻¹ • ξ) • σ i y ξ))
    let full := fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Tfull i) (u i c)
    let near := fun i c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c) (Tcut i) (u i c)
    (∀ i, ContDiffOn ℝ ∞ (near i) V) →
    (∀ i c, c ∈ V → ∃ w : H,
      w =ᵐ[volume] (fun x ↦ carrier (lam i) (φ i c) x • a i c x) ∧
      R i c =ᵐ[volume] fun x ↦ carrier (-lam i) (φ i c) x • ((Tfull i w-Tcut i w) x)) →
    (∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near q.1) q.2)
        (fun q ↦ lam q.1 ^ p * A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) →
    (∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ w : Fin k → Par, (∀ j, ‖w j‖ ≤ 1) →
        MemVectorFourierSobolev s (iteratedFDeriv ℝ k (R i) c w) ∧
        vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (R i) c w) ≤ C*A i*lam i^(-Q)) →
    (∀ i, ContDiffOn ℝ ∞ (full i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (full q.1) q.2)
        (fun q ↦ lam q.1 ^ p * A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  intro Tfull Tcut full near hnearSm hRidentity hnear htail
  have hsum i {c : Par} (hc : c ∈ V) : full i c = near i c + R i c := by
    have he := remainder_eq_demodulated_difference_of_ae (Tfull i) (Tcut i) (lam i)
      (φ i c) (hφ i c) (a i c) (u i c) (R i c) (hu i c hc) (hRidentity i c hc)
    change R i c = full i c - near i c at he
    rw [he]
    abel
  have hfullSm i : ContDiffOn ℝ ∞ (full i) V :=
    ((hnearSm i).add (hRsm i)).congr (fun c hc ↦ hsum i hc)
  refine ⟨hfullSm,?_⟩
  intro ps hps s
  obtain ⟨Cnear,hCnear,hnearBound⟩ := hnear ps hps s
  obtain ⟨Ctail,hCtail,htailBound⟩ := htail (s : ℝ) ps.length (-(p : ℝ))
  refine ⟨Cnear+Ctail,add_nonneg hCnear hCtail,?_⟩
  intro q
  have hsame : full q.1 =ᶠ[𝓝 (q.2 : Par)] fun c ↦ near q.1 c + R q.1 c := by
    filter_upwards [hV.mem_nhds q.2.property] with c hc
    exact hsum q.1 hc
  have hsplit : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (full q.1) q.2 =
      orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near q.1) q.2 +
      iteratedFDeriv ℝ ps.length (R q.1) q.2 ps.get := by
    rw [orderedParameterWord_congr_nhds hsame ps,
      orderedParameterWord_eq_iteratedFDeriv hV ((hnearSm q.1).add (hRsm q.1)) ps q.2.property,
      orderedParameterWord_eq_iteratedFDeriv hV (hnearSm q.1) ps q.2.property]
    exact congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin ps.length ↦ Par) H ↦ D ps.get)
      (iteratedFDeriv_add_apply (i := ps.length)
      (((hnearSm q.1).contDiffAt (hV.mem_nhds q.2.property)).of_le (by simp))
      (((hRsm q.1).contDiffAt (hV.mem_nhds q.2.property)).of_le (by simp)))
  obtain ⟨hn,hbn⟩ := hnearBound q
  obtain ⟨ht,hbt⟩ := htailBound q.1 q.2 q.2.property ps.get
    (fun j ↦ hps _ (List.get_mem _ _))
  have htGrade : vectorFourierSobolevScale.gradeNorm s
      (iteratedFDeriv ℝ ps.length (R q.1) q.2 ps.get) ≤
      Ctail*(lam q.1^p*A q.1*K q.1^ps.length)*K q.1^s := by
    rw [vectorFourierSobolevScale_gradeNorm s ht]
    simp only [neg_neg,Real.rpow_intCast] at hbt
    refine hbt.trans ?_
    have hAi := hA q.1
    have hlampos := hlam q.1
    calc
      Ctail*A q.1*lam q.1^p ≤
          (Ctail*A q.1*lam q.1^p) * (K q.1^(ps.length+s)) :=
        le_mul_of_one_le_right (by positivity)
          (one_le_pow₀ (hK q.1))
      _ = _ := by rw [pow_add]; ring
  dsimp only
  rw [hsplit]
  exact ⟨(vectorFourierSobolevScale.level s).add_mem hn ht,
    (gradeNorm_add_le vectorFourierSobolevScale hn ht).trans
      ((add_le_add hbn htGrade).trans_eq (by ring))⟩


/-- Restore the actual remainder while retaining natural subtraction in every
reserved output grade. The remainder's arbitrary precision supplies a bound
independent of the slow scale even below the reserve. The intended `full`,
`near`, and `R` are the same concrete masked operators and kernel family
identified above (`app:ch_response:cor:current-atoms`). -/
theorem ordered_reserved_bounds_of_annular_remainder
    (full near R : I → Par → H) {V : Set Par} (hV : IsOpen V)
    (hsum : ∀ i c, c ∈ V → full i c = near i c + R i c)
    (hnearSm : ∀ i, ContDiffOn ℝ ∞ (near i) V)
    (hRsm : ∀ i, ContDiffOn ℝ ∞ (R i) V)
    (lam A K : I → ℝ) (p : ℤ) (reserve : ℕ)
    (hlam : ∀ i, 1 ≤ lam i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hnear : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        let w := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near i) c
        MemVectorFourierSobolev (s : ℝ) w ∧ vectorFourierSobolevNorm (s : ℝ) w ≤
          C*lam i^p*A i*K i^(s+ps.length-reserve))
    (htail : ∀ (s : ℝ) (k : ℕ) (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ w : Fin k → Par, (∀ j, ‖w j‖ ≤ 1) →
        MemVectorFourierSobolev s (iteratedFDeriv ℝ k (R i) c w) ∧
        vectorFourierSobolevNorm s (iteratedFDeriv ℝ k (R i) c w) ≤ C*A i*lam i^(-Q)) :
    (∀ i, ContDiffOn ℝ ∞ (full i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        let w := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (full i) c
        MemVectorFourierSobolev (s : ℝ) w ∧ vectorFourierSobolevNorm (s : ℝ) w ≤
          C*lam i^p*A i*K i^(s+ps.length-reserve) := by
  have hfullSm i : ContDiffOn ℝ ∞ (full i) V :=
    ((hnearSm i).add (hRsm i)).congr (fun c hc ↦ hsum i c hc)
  refine ⟨hfullSm,?_⟩
  intro ps hps s
  obtain ⟨Cnear,hCnear,hnb⟩ := hnear ps hps s
  obtain ⟨Ctail,hCtail,htb⟩ := htail (s : ℝ) ps.length (-(p : ℝ))
  refine ⟨Cnear+Ctail,add_nonneg hCnear hCtail,?_⟩
  intro i c hc w
  have heq : full i =ᶠ[𝓝 c] fun a ↦ near i a + R i a := by
    filter_upwards [hV.mem_nhds hc] with a ha
    exact hsum i a ha
  have hsplit : w = orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (near i) c +
      iteratedFDeriv ℝ ps.length (R i) c ps.get := by
    rw [show w = orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (full i) c from rfl,
      orderedParameterWord_congr_nhds heq ps,
      orderedParameterWord_eq_iteratedFDeriv hV ((hnearSm i).add (hRsm i)) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hnearSm i) ps hc]
    exact congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin ps.length ↦ Par) H ↦ D ps.get)
      (iteratedFDeriv_add_apply (i := ps.length)
        (((hnearSm i).contDiffAt (hV.mem_nhds hc)).of_le (by simp))
        (((hRsm i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)))
  obtain ⟨hn,hbn⟩ := hnb i c hc
  obtain ⟨ht,hbt⟩ := htb i c hc ps.get (fun j ↦ hps _ (List.get_mem _ _))
  have htailBound : vectorFourierSobolevNorm (s : ℝ)
      (iteratedFDeriv ℝ ps.length (R i) c ps.get) ≤
      Ctail*lam i^p*A i*K i^(s+ps.length-reserve) := by
    simp only [neg_neg,Real.rpow_intCast] at hbt
    have hAi := hA i
    have hlampos := hlam i
    calc
      _ ≤ Ctail*A i*lam i^p := hbt
      _ ≤ (Ctail*A i*lam i^p)*K i^(s+ps.length-reserve) :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ (hK i))
      _ = _ := by ring
  rw [hsplit]
  have hmem := (vectorFourierSobolevScale.level s).add_mem hn ht
  refine ⟨hmem,?_⟩
  have hadd := gradeNorm_add_le vectorFourierSobolevScale hn ht
  rw [vectorFourierSobolevScale_gradeNorm s hmem,
    vectorFourierSobolevScale_gradeNorm s hn,vectorFourierSobolevScale_gradeNorm s ht] at hadd
  exact hadd.trans ((add_le_add hbn htailBound).trans_eq (by ring))

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
