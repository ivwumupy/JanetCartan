module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles.Expansion

/-!
# One original annular Leibniz term from Sobolev envelopes

The matrix and envelope share a single source derivative budget. This is the
termwise estimate consumed by the mixed original amplitude profile of
`app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open Complement.ParameterDerivatives Complement.InactiveSource JanetCartan.Pseudodifferential
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "M" => Matrix (Fin r) (Fin r) ℂ

private theorem norm_sourceJet_matrixAction_local_sobolev
    {U : Set E} (hU : IsOpen U) {m : E → M} (hm : ContDiffOn ℝ ∞ m U)
    {a : E → F} (ha : ContDiff ℝ ∞ a) (halp : MemLp a 2 volume)
    {B C : ℕ → ℝ} (hB : ∀ i, 0 ≤ B i)
    {A H L K : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    (hmem : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ) (halp.toLp a))
    (hprofile : ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ) (halp.toLp a) ≤
      C s * A * K ^ s) (k : ℕ) {z : E} (hz : z ∈ U)
    (hjet : ∀ i ≤ k, ‖iteratedFDeriv ℝ i m z‖ ≤ B i * H * L ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => annularMatrixAction r (m y) (a y)) z‖ ≤
      sourceProductBudget (d + 1) r B C k * (H * A * K ^ (d + 1 + 1)) * K ^ k := by
  have hK0 := zero_le_one.trans hK
  have hp := (annularMatrixAction r).norm_iteratedFDerivWithin_le_of_bilinear
    hm ha.contDiffOn hU.uniqueDiffOn hz (n := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hz] at hp
  apply hp.trans
  unfold sourceProductBudget
  rw [mul_assoc, mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
  have hBi := hB i
  have he := norm_iteratedFDeriv_le_envelope_profile ha.continuous halp hA hK
    hmem hprofile (k - i) z
  have hbi := (hjet i hik).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hL hLK i) (mul_nonneg (hB i) hH))
  calc
    _ ≤ (k.choose i : ℝ) * (B i * H * K ^ i) *
        (envelopeJetProfileConstant (d + 1) C (k - i) *
          ((A * K ^ (d + 1 + 1)) * K ^ (k - i))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbi (Nat.cast_nonneg _)) he
        (norm_nonneg _) (by positivity)
    _ = (k.choose i : ℝ) * B i * envelopeJetProfileConstant (d + 1) C (k - i) *
        (H * A * K ^ (d + 1 + 1)) * K ^ (i + (k - i)) := by rw [pow_add]; ring
    _ = _ := by rw [Nat.add_sub_of_le hik]; ring

set_option maxHeartbeats 400000 in
/-- Source derivatives of one literal external Leibniz term. The matrix
consumes `k+vs.length` original symbol jets, while the envelope consumes only
`ws.length` carrier derivatives, independently of `k`. The fixed source
reserve is exactly `n+1`, where `n=d+1`. Source:
`app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_sourceJet_originalAnnularLeibnizTerm_le
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {J : Set (TwoTimePoint d)} (hJ : IsOpen J)
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) J)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {V : Set P} {X U T : Set E} (hV : IsOpen V) (hX : IsOpen X)
    (hU : IsOpen U) (hT : IsCompact T)
    (hmap : ∀ q ∈ X ×ˢ U, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ J)
    {a : P → E → F} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (has : ∀ c ∈ V, tsupport (a c) ⊆ T)
    {O S B : ℕ → ℝ} (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i)
    (hB : ∀ i, 0 ≤ B i) {Mβ Mπ A₀ L K : ℝ}
    (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ) (hA : 0 ≤ A₀)
    (hL : 1 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    (hβξ : ‖β ξ‖ ≤ Mβ) (hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ Mπ)
    (vs : List E) (ws : List P) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1)
    {c : P} (hc : c ∈ V) {x z : E} (hx : x ∈ X) (hz : z ∈ U)
    (C : ℕ → ℝ)
    (hmem : ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
      ((parameterSource_memLp hT hV ha has ws.length ws.get hc).toLp
        (fun z => parameterListJet (fun q => a q z) ws c)))
    (hprofile : ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
      ((parameterSource_memLp hT hV ha has ws.length ws.get hc).toLp
        (fun z => parameterListJet (fun q => a q z) ws c)) ≤
          C s * A₀ * K ^ (s + ws.length))
    (k : ℕ)
    (hout : ∀ i ≤ k + vs.length,
      ‖iteratedFDeriv ℝ i χout (if adjoint then z else x)‖ ≤ O i)
    (hsource : ∀ i ≤ k + vs.length,
      ‖iteratedFDeriv ℝ i χsource (if adjoint then x else z)‖ ≤ S i)
    (hsymbol : ∀ i ≤ k + vs.length, ‖iteratedFDeriv ℝ i (jointAmplitude b)
      (elapsedPoint t ((if adjoint then (z, x) else (x, z)), ξ))‖ ≤ B i * L ^ i) :
    ‖iteratedFDeriv ℝ k
      (originalAnnularLeibnizTerm adjoint b χout χsource β π t lam ξ a vs ws c x) z‖ ≤
      sourceProductBudget (d + 1) r
        (fun i => originalMatrixBudget O S B Mβ Mπ (i + vs.length)) C k *
          A₀ * K ^ (d + 1 + 1 + (vs.length + ws.length)) * K ^ k := by
  have hK0 := zero_le_one.trans hK
  have hL0 := zero_le_one.trans hL
  have hm := contDiffOn_parameterListJet_joint hX hU
    (contDiffOn_originalAnnularMatrix adjoint b χout χsource β π t lam ξ hb ho hs hmap) vs
  have hmz : ContDiffOn ℝ ∞ (fun y => parameterListJet (fun w =>
      originalAnnularMatrix adjoint b χout χsource β π t lam ξ (w, y)) vs x) U :=
    hm.comp (s := U) (f := fun y : E => (x, y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨hx, hy⟩)
  have hprofile' (s : ℕ) : vectorFourierSobolevNorm (s : ℝ)
      ((parameterSource_memLp hT hV ha has ws.length ws.get hc).toLp
        (fun z => parameterListJet (fun q => a q z) ws c)) ≤
          C s * (A₀ * K ^ ws.length) * K ^ s := by
    convert hprofile s using 1
    simp only [pow_add]
    ring
  have hjet (i : ℕ) (hi : i ≤ k) : ‖iteratedFDeriv ℝ i (fun y =>
      parameterListJet (fun w => originalAnnularMatrix adjoint b χout χsource β π
        t lam ξ (w, y)) vs x) z‖ ≤
      originalMatrixBudget O S B Mβ Mπ (i + vs.length) * K ^ vs.length * L ^ i := by
    have hbnd := norm_sourceJet_originalAnnularMatrix_external_le adjoint b χout χsource β π
      t lam ξ hJ hb ho hs hX hU hmap hO hS hB hβ hπ hL hβξ hπξ vs hv i hx hz
      (fun j hj => hout j (by omega)) (fun j hj => hsource j (by omega))
      (fun j hj => hsymbol j (by omega))
    apply hbnd.trans
    rw [pow_add]
    calc
      _ = originalMatrixBudget O S B Mβ Mπ (i + vs.length) * L ^ vs.length * L ^ i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLK _)
          (originalMatrixBudget_nonneg hO hS hB hβ hπ _)) (pow_nonneg hL0 _)
  have h := norm_sourceJet_matrixAction_local_sobolev hU hmz
    (contDiff_originalSourceListJet hV ha ws hc)
    (parameterSource_memLp hT hV ha has ws.length ws.get hc)
    (fun i => originalMatrixBudget_nonneg hO hS hB hβ hπ (i + vs.length))
    (mul_nonneg hA (pow_nonneg hK0 _)) (pow_nonneg hK0 _) hL0 hLK hK
    hmem hprofile' k hz hjet
  change ‖iteratedFDeriv ℝ k (fun y => annularMatrixAction r
    (parameterListJet (fun w => originalAnnularMatrix adjoint b χout χsource β π
      t lam ξ (w, y)) vs x) (parameterListJet (fun q => a q y) ws c)) z‖ ≤ _
  apply h.trans_eq
  simp only [pow_add]
  ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
