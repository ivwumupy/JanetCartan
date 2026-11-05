module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualEnvelopes.Conjugation
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Modulation

/-!
# Original conjugated sources with the same natural reserve

Whole-operator conjugation uses the negative original source phase and the
conjugate of the same source amplitude. The Fourier classes and all parameter
jets are constructed from those original functions. This preserves arbitrary
scalar amplitude sizes and the naturally truncated reserve, including its
low-order plateau. Consumer: the normalized signed residual alphabet in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
open ResponseTransfer ResponseTransfer.Complement Pseudodifferential
open ResponseTransfer.DirectEvolution.AnnularSobolev
open RegularSector.Realization
variable {n r : ℕ} {Par I : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Moving the sign from the original phase to its frequency preserves the
literal carrier multiplier (`new:eq:carrier-ibp`). -/
theorem carrierMultiplication_negative_phase_eq (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) :
    carrierMultiplication (r := r) lam (fun y ↦ -φ y) hφ.neg =
      carrierMultiplication (-lam) φ hφ := by
  ext1 u
  apply Lp.ext
  filter_upwards [carrierMultiplication_ae lam (fun y ↦ -φ y) hφ.neg u,
    carrierMultiplication_ae (-lam) φ hφ u] with y hy hz
  rw [hy,hz]
  simp only [carrier,mul_neg,neg_mul]

/-- A whole-conjugate letter is the conjugate of the ORIGINAL operator's
negative-source response, with the original source amplitude conjugated.
This does not use a Hilbert adjoint (`signed-graph-factor`). -/
theorem demodulated_conjugate_eq_star_negative_source
    (T : H →L[ℂ] H) (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    demodulatedL2Operator lam φ hφ (boundedConjugate T) u =
      star (demodulatedL2Operator lam (fun y ↦ -φ y) hφ.neg T (star u)) := by
  change carrierMultiplication (-lam) φ hφ (boundedConjugate T
    (carrierMultiplication lam φ hφ u)) = _
  rw [demodulated_boundedConjugate_eq]
  simp only [demodulatedL2Operator,ContinuousLinearMap.comp_apply]
  rw [carrierMultiplication_negative_phase_eq (-lam) φ hφ,
    carrierMultiplication_negative_phase_eq lam φ hφ,neg_neg]

/-- Exact parameter jets of the original conjugate amplitude, with no
regularity assumption or change of representative (`finite-jets`). -/
theorem conjugate_source_parameter_jet (a : E × Par → F) (l : ℕ)
    (w : Fin l → Par) (c : Par) (y : E) :
    iteratedFDeriv ℝ l (fun q ↦ star (a (y,q))) c w =
      star (iteratedFDeriv ℝ l (fun q ↦ a (y,q)) c w) :=
  congrArg (fun D : Par [×l]→L[ℝ] F ↦ D w)
    ((starL' ℝ : F ≃L[ℝ] F).iteratedFDeriv_comp_left)

/-- The source Fourier profile is preserved under actual conjugation at
EVERY natural reserve. Constants precede the source family and scale, and
no negative power is extracted at low orders (`response-graded-source`). -/
theorem exists_conjugate_source_fourier_profiles
    (Csource : ℕ → ℕ → ℝ) (hCsource : ∀ l s, 0 ≤ Csource l s) :
    ∃ Cstar : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Cstar l s) ∧
      ∀ (a : I → E × Par → F) (A K : I → ℝ) (reserve : ℕ) (V : Set Par),
      (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s*A i*K i^(s+l-reserve)) →
      ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ star (a i (y,q))) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Cstar l s*A i*K i^(s+l-reserve) := by
  choose D hD hstar using exists_star_fourierSobolev_constant n r
  refine ⟨fun l s ↦ D s*Csource l s,fun l s ↦ mul_nonneg (hD s).le (hCsource l s),?_⟩
  intro a A K reserve V hsource i c hc l w hw s fstar
  obtain ⟨hm,hmem,hbound⟩ := hsource i c hc l w hw s
  let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
  have heq : fstar = star f := funext fun y ↦ conjugate_source_parameter_jet (a i) l w c y
  rw [heq]
  have hLp : hm.star.toLp (star f) = star (hm.toLp f) := by
    apply Lp.ext
    filter_upwards [hm.star.coeFn_toLp,Lp.coeFn_star (hm.toLp f),hm.coeFn_toLp] with y hy hs hf
    have hf' : (hm.toLp f) y = f y := hf
    have hs' : (star (hm.toLp f)) y = star ((hm.toLp f) y) := hs
    exact hy.trans ((congrArg star hf').symm.trans hs'.symm)
  obtain ⟨hstarMem,hstarBound⟩ := hstar s (hm.toLp f) hmem
  rw [← hLp] at hstarMem hstarBound
  exact ⟨hm.star,hstarMem,hstarBound.trans
    ((mul_le_mul_of_nonneg_left hbound (hD s).le).trans_eq (by ring))⟩

/-- Every ordered whole-conjugate output keeps the actual negative-source
bound with the same natural reserve and scalar size. The Fourier conjugation
constant changes only the numeric coefficient (`fixed-factor-transfer`). -/
theorem conjugate_letter_reserved_bound_of_negative_phase
    (T : I → H →L[ℂ] H) (lam A K : I → ℝ)
    (φ : I → Par → E → ℝ) (hφ : ∀ i c, Continuous (φ i c))
    (u : I → Par → H) (V : Set Par) (reserve s : ℕ) (ps : List Par)
    (hnegative : ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ demodulatedL2Operator (lam i) (fun y ↦ -φ i c y) (hφ i c).neg
            (T i) (star (u i c))) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ demodulatedL2Operator (lam i) (fun y ↦ -φ i c y) (hφ i c).neg
            (T i) (star (u i c))) c) ≤ C*A i*K i^(s+ps.length-reserve)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c)
            (boundedConjugate (T i)) (u i c)) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ demodulatedL2Operator (lam i) (φ i c) (hφ i c)
            (boundedConjugate (T i)) (u i c)) c) ≤ C*A i*K i^(s+ps.length-reserve) := by
  obtain ⟨C,hC,hbound⟩ := hnegative
  obtain ⟨D,hD,hstar⟩ := exists_star_fourierSobolev_constant n r s
  refine ⟨D*C,mul_nonneg hD.le hC,fun i c hc ↦ ?_⟩
  simp only [demodulated_conjugate_eq_star_negative_source,orderedTransferAction_star]
  obtain ⟨hm,hb⟩ := hbound i c hc
  obtain ⟨hsm,hsb⟩ := hstar _ hm
  exact ⟨hsm,hsb.trans ((mul_le_mul_of_nonneg_left hb hD.le).trans_eq (by ring))⟩

end JanetCartan.FixedDomainInverse.FiniteResidualEnvelopes
