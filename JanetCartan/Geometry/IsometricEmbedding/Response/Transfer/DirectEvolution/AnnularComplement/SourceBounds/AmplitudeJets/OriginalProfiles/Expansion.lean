module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles.Matrix
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles.Leibniz
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles.Envelope

/-!
# Literal finite external expansion of the original annular amplitude

Both orientations use the published elapsed amplitude and matrix action.
Only the original envelope is differentiated in the carrier variable.
Source: `app:ch_response:lem:energy-carrier-jets`.
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

/-- One literal external Leibniz term: matrix jets in output directions,
original envelope jets in carrier directions. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
def originalAnnularLeibnizTerm (adjoint : Bool) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (t lam : ℝ) (ξ : E)
    (a : P → E → F) (vs : List E) (ws : List P) (c : P) (x z : E) : F :=
  annularMatrixAction r
    (parameterListJet (fun y => originalAnnularMatrix adjoint b χout χsource β π
      t lam ξ (y, z)) vs x)
    (parameterListJet (fun q => a q z) ws c)

/-- Exact external expansion of the published vector amplitude. No support
extension or equality premise is used. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem parameterListJet_annularExternalAmplitude
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {J : Set (TwoTimePoint d)}
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) J)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {V : Set P} {X U : Set E} (hV : IsOpen V) (hX : IsOpen X)
    (hmap : ∀ q ∈ X ×ˢ U, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ J)
    {a : P → E → F} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (vs : List (P × E)) {c : P} (hc : c ∈ V) {x z : E} (hx : x ∈ X) (hz : z ∈ U) :
    parameterListJet (fun q => annularExternalAmplitude adjoint
      (elapsedAmplitude b χout χsource β t) π lam a ξ q z) vs (c, x) =
      ((parameterLeibnizSplittings vs).map (fun s =>
        originalAnnularLeibnizTerm adjoint b χout χsource β π t lam ξ a
          (s.1.map Prod.snd) (s.2.map Prod.fst) c x z)).sum := by
  have hm := contDiffOn_originalAnnularMatrix adjoint b χout χsource β π t lam ξ
    hb ho hs hmap
  have hmx : ContDiffOn ℝ ∞ (fun y => originalAnnularMatrix adjoint b χout χsource β π
      t lam ξ (y, z)) X :=
    hm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy => ⟨hy, hz⟩)
  have hac : ContDiffOn ℝ ∞ (fun q => a q z) V :=
    ha.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hq => ⟨hq, mem_univ _⟩)
  have he : (fun q => annularExternalAmplitude adjoint
      (elapsedAmplitude b χout χsource β t) π lam a ξ q z) =
      fun q : P × E => annularMatrixAction r
        (originalAnnularMatrix adjoint b χout χsource β π t lam ξ (q.2, z)) (a q.1 z) := by
    funext q
    exact annularExternalAmplitude_eq_originalAnnularMatrix adjoint b χout χsource β π
      t lam a ξ q z
  have hmx' : ContDiffOn ℝ ∞ (fun q : P × E =>
      originalAnnularMatrix adjoint b χout χsource β π t lam ξ (q.2, z)) (V ×ˢ X) :=
    hmx.comp contDiffOn_snd (fun _ hq => hq.2)
  have hac' : ContDiffOn ℝ ∞ (fun q : P × E => a q.1 z) (V ×ˢ X) :=
    hac.comp contDiffOn_fst (fun _ hq => hq.1)
  rw [he, parameterListJet_bilinear (annularMatrixAction r) _ _ (hV.prod hX)
    hmx' hac' vs ⟨hc, hx⟩]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  have hmjet := parameterListJet_comp_continuousLinearMap (ContinuousLinearMap.snd ℝ P E)
    hX hmx s.1 (c := (c, x)) hx
  have hajet := parameterListJet_comp_continuousLinearMap (ContinuousLinearMap.fst ℝ P E)
    hV hac s.2 (c := (c, x)) hc
  exact congrArg₂ (fun m v => annularMatrixAction r m v) hmjet hajet

/-- Mixed matrix jets are produced from original joint symbol jets; the source
and external orders share one symbol derivative budget. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_sourceJet_originalAnnularMatrix_external_le
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {J : Set (TwoTimePoint d)} (hJ : IsOpen J)
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) J)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {X U : Set E} (hX : IsOpen X) (hU : IsOpen U)
    (hmap : ∀ q ∈ X ×ˢ U, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ J)
    {O S B : ℕ → ℝ} (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i)
    (hB : ∀ i, 0 ≤ B i) {Mβ Mπ L : ℝ}
    (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ) (hL : 1 ≤ L)
    (hβξ : ‖β ξ‖ ≤ Mβ) (hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ Mπ)
    (vs : List E) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (k : ℕ)
    {x z : E} (hx : x ∈ X) (hz : z ∈ U)
    (hout : ∀ i ≤ k + vs.length,
      ‖iteratedFDeriv ℝ i χout (if adjoint then z else x)‖ ≤ O i)
    (hsource : ∀ i ≤ k + vs.length,
      ‖iteratedFDeriv ℝ i χsource (if adjoint then x else z)‖ ≤ S i)
    (hsymbol : ∀ i ≤ k + vs.length, ‖iteratedFDeriv ℝ i (jointAmplitude b)
      (elapsedPoint t ((if adjoint then (z, x) else (x, z)), ξ))‖ ≤ B i * L ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => parameterListJet (fun w =>
      originalAnnularMatrix adjoint b χout χsource β π t lam ξ (w, y)) vs x) z‖ ≤
        originalMatrixBudget O S B Mβ Mπ (k + vs.length) * L ^ (k + vs.length) := by
  apply (norm_sourceJet_parameterListJet_le_joint hX hU
    (contDiffOn_originalAnnularMatrix adjoint b χout χsource β π t lam ξ hb ho hs hmap)
    vs hv k hx hz).trans
  exact norm_iteratedFDeriv_originalAnnularMatrix_le adjoint b χout χsource β π
    t lam ξ hJ hb ho hs hO hS hB hβ hπ hL hβξ hπξ (x, z) (k + vs.length)
    (hmap _ ⟨hx, hz⟩) hout hsource hsymbol

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
