module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.SelectedSupport
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.SourceBox
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.EllipticSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.EllipticAdjointSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.OperatorIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Finite scale compression for the actual elliptic annular estimate

The complete original coefficient profiles are used only to produce the actual
selected symbol jets at their original scale. Only the finitely many jets
consumed by the sharp PDO theorem are compared with a compressed scale.
Consumer: `selected_elliptic_annular_reserved_ordered_bounds`, retaining the
natural source reserve in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap

namespace JanetCartan.ResponseTransfer.FullEllipticApplication

open DiagonalPdo FullSourceEnvelopes FullSourceStationary
open JanetCartan.ResponseTransfer.Complement
open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization NearCarrierFullLow

variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

variable {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}

/-- Apply the actual elliptic inverse or residual after compressing only
its required finite phase and amplitude jets. The two scale comparisons are
numerical inputs from `ReserveCompression`; symbol estimates still come from
the original actual family. The mixed source input is produced by
`exists_fullSource_reserved_mixedL2_profile`, with no change of datum
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem elliptic_annular_sobolev_of_finite_scale_compression
    (fam : ActualMaskFamily Ωcoeff x RQ Aref K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*fam.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold)
    {ra rb : ℝ} (hra : 0 < ra) (hrb : 0 < rb)
    (basis : OrthonormalBasis ι ℝ W)
    (s : ℕ) (ps : List Par) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rstar Rnear : ℕ) (hRstar : 2 ≤ Rstar) (hRnear : fullLowReserve (d+1)+2 < Rnear)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hK : ∀ i, 1 ≤ K i)
    (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ωcoeff)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ωcoeff)
    (hmap : ∀ i, MapsTo (Q i) Ωcoeff (closedBall Aref fam.coefficientRadius))
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hphaseScale : ∀ i j, j ≤ fullLowReserve (d+1)+(s+ps.length)+2 →
      L i ^ (j-Rstar) ≤ K i ^ (j-Rnear))
    (hampScale : ∀ i j, j ≤ fullLowReserve (d+1)+(s+ps.length) →
      L i ^ (j+2-Rstar) ≤ K i ^ (j+2-Rnear))
    (S : Set E) (hS : IsCompact S)
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (Dprofile : ℕ → ℝ) (hDprofile : ∀ j, 0 ≤ Dprofile j)
    (hdatum : ∀ i c, c ∈ V → ∀ j, j ≤ s+ps.length →
      ∃ hm : MemLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c)) 2 volume,
        ‖hm.toLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c))‖ ≤
          Adata i * Dprofile j * K i ^ j) :
    let π := annularSelector (n := d+1) ra rb hra hrb
    ∀ residual adj : Bool,
    let σ := fun i y ξ ↦ π ((lam i)⁻¹ • ξ) •
      (if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
        else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ)
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO χout (fun y ↦ (fam.inputMask y : ℂ)) (σ i)))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ≤
          C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length) := by
  classical
  intro π residual adj σ output
  let χsource := fun y ↦ (fam.inputMask y : ℂ)
  let X := tsupport χout ∪ tsupport χsource
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let KP := closedBall x (3*fam.physicalRadius) ×ˢ Kpar
  let Ubox := ball x (3*fam.physicalRadius) ×ˢ V
  let D := e ⁻¹' (ball x (3*fam.physicalRadius) ×ˢ
    ball (0 : E) (1+max (Aphase 2) (2*rb)))
  let Kcrit := e ⁻¹' (X ×ˢ tsupport π)
  let Wcompact := e ⁻¹' (closedBall x (3*fam.physicalRadius) ×ˢ
    closedBall (0 : E) (1+max (Aphase 2) (2*rb)))
  let Kjoint := KP ×ˢ Wcompact
  have hKP : IsCompact KP := (isCompact_closedBall _ _).prod hKpar
  have hKjoint : IsCompact Kjoint := hKP.prod
    (e.toHomeomorph.isCompact_preimage.mpr ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)))
  have hproj (v : (E × Par) × W) (hv : v ∈ Kjoint) :
      v.1 ∈ KP ∧ (v.2.fst,v.1.2) ∈ KP := ⟨hv.1,hv.2.1,hv.1.2⟩
  obtain ⟨Ajoint,hAjoint,hjoint⟩ := exists_diagonal_fullSourcePhase_joint_profiles hKjoint Aphase hAphase
  have hphase i j (hj : j ≤ fullLowReserve (d+1)+(s+ps.length)+2) v (hv : v ∈ Ubox ×ˢ D) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (carrierPhase (fun y ξ : E ↦ inner ℝ y ξ) (φ i))) v‖ ≤
        Ajoint j * K i ^ (j-Rnear) := by
    have hb := hjoint (φ i) (hφ i) KP hproj Rstar (L i) (hL i) (hφjets i) j
      v ⟨⟨ball_subset_closedBall hv.1.1,hVK hv.1.2⟩,
        ball_subset_closedBall hv.2.1,ball_subset_closedBall hv.2.2⟩
    exact hb.trans (mul_le_mul_of_nonneg_left (hphaseScale i j hj) (hAjoint j))
  obtain ⟨hD,hDconv,hgeometry⟩ := diagonal_source_box_geometry x (3*fam.physicalRadius)
    (Aphase 2) (2*rb) hKpar hVK
  obtain ⟨hX,hXball,hKcrit,hKcritD,hsupport⟩ :=
    selected_diagonalAmplitude_source_box_support (r := d+1) fam χout hoc hos hra hrb (Aphase 2)
  let Rcell := ‖x‖ + 3*fam.physicalRadius + 1
  have hRcell : 0 < Rcell := by
    dsimp only [Rcell]
    linarith [norm_nonneg x,fam.physicalRadius_pos]
  have hXnorm (y : E) (hy : y ∈ X) : ‖y‖ < Rcell := by
    have hd := hXball hy
    rw [mem_ball] at hd
    have hn := norm_le_norm_sub_add y x
    rw [← dist_eq_norm] at hn
    dsimp only [Rcell]
    linarith
  have hXcell : X ⊆ ball (0 : E) Rcell := fun y hy ↦ mem_ball_zero_iff.mpr (hXnorm y hy)
  have hYbox (y : E) (hy : y ∈ X) (j : Fin (d+1)) : |y j| ≤ Rcell := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y j).trans (hXnorm y hy).le
  have hcell : Rcell / (4*Rcell) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 4*Rcell)).mpr
    linarith
  have hπ : ContDiff ℝ ∞ π := contDiff_annularSelector ra rb hra hrb
  have hcπ : HasCompactSupport π := hasCompactSupport_annularSelector ra rb hra hrb
  have hzero : (0 : E) ∉ tsupport π := by
    intro hz
    have hh := (tsupport_annularSelector_subset ra rb hra hrb hz).1
    simp only [norm_zero] at hh
    linarith
  obtain ⟨Aamp,hAamp,hamp⟩ := exists_elliptic_selected_joint_profiles fam hK₀ hΩcoeff hball
    χout ho hoc hos threshold ht π hπ hcπ hzero AQ AB hAQ hAB
  obtain ⟨Cf,hCf,hforward⟩ := exists_diagonalPDO_joint_sobolev_of_primitive_jets
    (r := d+1) Rcell (4*Rcell) (by positivity) hcell basis s ps hps Ajoint Aamp hAjoint hAamp
    (hAphase 2) (by positivity : 0 ≤ 2*rb)
  obtain ⟨Cr,hCr,hreverse⟩ := exists_diagonalPDO_adjoint_joint_sobolev_of_primitive_jets
    (r := d+1) Rcell (4*Rcell) (by positivity) hcell basis s ps hps Ajoint Aamp hAjoint hAamp
    (hAphase 2) (by positivity : 0 ≤ 2*rb)
  let C := if adj then Cr else Cf
  have hC : 0 ≤ C := by cases adj <;> assumption
  refine ⟨C * ∑ j ∈ Finset.range (s+ps.length+1), Dprofile j,
    mul_nonneg hC (Finset.sum_nonneg (fun j _ ↦ hDprofile j)),?_⟩
  intro i c hc
  let F₀ := (fun ξ : E ↦ (lam i)⁻¹ • ξ) ⁻¹' tsupport π
  have hFclosed : IsClosed F₀ := (isClosed_tsupport π).preimage (continuous_const_smul _)
  have hFzero : (0 : E) ∉ F₀ := by simpa only [F₀,mem_preimage,smul_zero] using hzero
  have hXU : X ×ˢ V ⊆ Ubox := fun z hz ↦ ⟨hXball hz.1,hz.2⟩
  have hφsource (b : Par) (_hb : b ∈ V) : ContDiffOn ℝ ∞ (fun y ↦ φ i y b) univ :=
    ((hφ i).comp (contDiff_id.prodMk contDiff_const)).contDiffOn
  have hcφ (b : Par) : Continuous (fun y ↦ φ i y b) :=
    (hφ i).continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨hκD,hsegment⟩ := hgeometry (φ i) (hφ i) (hcap i)
  let rawsymbol := if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i)
    else ellipticInverseSymbol fam hK₀ threshold (Q i)
  have hn : lam i ≠ 0 := (zero_lt_one.trans_le (hlam i)).ne'
  obtain ⟨hscrit,hsoutput,hsslice⟩ := hsupport rawsymbol (lam i) hn (-1) adj
  obtain ⟨hα,hαjet⟩ := hamp Rstar hRstar (L i) (lam i) (hL i) (hlam i)
    (Q i) (B i) (hQ i) (hB i) (hmap i) (hQp i) (hBp i) residual adj
  have hshape : (fun a b ξ ↦ π ((lam i)⁻¹ • ξ) • orientedMaskedPDOAmplitude false χout χsource
      (if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i)
        else ellipticInverseSymbol fam hK₀ threshold (Q i)) a b ξ) =
      fun a b ξ ↦ (χout a * χsource b) • σ i a ξ := by
    funext a b ξ
    dsimp only [orientedMaskedPDOAmplitude,Bool.false_eq_true,↓reduceIte,σ]
    cases residual <;> exact smul_comm _ _ _
  dsimp only [χsource] at hshape
  rw [hshape] at hα hαjet
  let Ddata := fun j ↦ Adata i * Dprofile j * K i ^ j
  have hDdata j : 0 ≤ Ddata j :=
    mul_nonneg (mul_nonneg (hAdata i) (hDprofile j)) (pow_nonneg (zero_le_one.trans (hK i)) j)
  have hj j (hj : j ≤ s+ps.length) : ∃ hm : MemLp
      (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c)) 2 volume,
      ‖hm.toLp (fun y : E ↦ iteratedFDeriv ℝ j (a i) (y,c))‖ ≤ Ddata j := hdatum i c hc j hj
  have hbound : MemVectorFourierSobolev (s : ℝ)
      (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ≤
          (C * ∑ j ∈ Finset.range (s+ps.length+1), Dprofile j) *
            lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length) := by
    cases adj <;>
      simp only [rawsymbol,ite_apply,Bool.false_eq_true,↓reduceIte] at hscrit hsoutput hsslice hα hαjet
    · obtain ⟨hm,_,hb⟩ := hforward X X F₀ hX hYbox hFclosed hFzero hXcell
        Rnear hRnear (K i) (lam i) (hK i) (hlam i) (-1)
        (φ i) (σ i) χout χsource univ KP Ubox D isOpen_univ (hφ i).contDiffOn
        hKP (subset_univ _) (hcap i) (isOpen_ball.prod hV) (subset_univ _) hD hDconv
        hκD hsegment (fun j hj v hv ↦ hphase i j hj v hv) hα.contDiffOn
        (fun j hj v _ ↦ (hαjet j v).trans (mul_le_mul_of_nonneg_left (hampScale i j hj) (hAamp j)))
        Kcrit hKcrit hKcritD
        (fun z _ ↦ hscrit z) (fun v hv ↦ (hsoutput v hv).1) V hV hXU hcφ
        (fun b hb z hz ↦ (hsslice V b hb z hz).1)
        (fun b hb z hz ↦ (hsslice V b hb z hz).2.1)
        (fun b hb z hz ↦ ⟨(hsslice V b hb z hz).2.2.1,
          (hsslice V b hb z hz).2.2.2.1,(hsslice V b hb z hz).2.2.2.2⟩)
        S univ hS isOpen_univ (subset_univ _) hφsource (a i) (ha i) (has i) c hc
        Ddata hDdata hj
      exact ⟨hm,hb (K i) (Adata i) Dprofile le_rfl (fun _ _ ↦ le_rfl)⟩
    · obtain ⟨hm,_,hb⟩ := hreverse X X F₀ hX hX hYbox hFclosed hFzero hXcell
        Rnear hRnear (K i) (lam i) (hK i) (hlam i) (-1)
        (φ i) (σ i) χout χsource univ KP Ubox D isOpen_univ (hφ i).contDiffOn
        hKP (subset_univ _) (hcap i) (isOpen_ball.prod hV) (subset_univ _) hD hDconv
        hκD hsegment (fun j hj v hv ↦ hphase i j hj v hv) hα.contDiffOn
        (fun j hj v _ ↦ (hαjet j v).trans (mul_le_mul_of_nonneg_left (hampScale i j hj) (hAamp j)))
        Kcrit hKcrit hKcritD
        (fun z _ ↦ hscrit z) (fun v hv ↦ (hsoutput v hv).1) V hV hXU hcφ
        (fun b hb z hz ↦ (hsslice V b hb z hz).1)
        (fun b hb z hz ↦ (hsslice V b hb z hz).2.1)
        (fun b hb z hz ↦ ⟨(hsslice V b hb z hz).2.2.2.1,
          (hsslice V b hb z hz).2.2.1,(hsslice V b hb z hz).2.2.2.2⟩)
        S univ hS isOpen_univ (subset_univ _) hφsource (a i) (ha i) (has i) c hc
        Ddata hDdata hj
      exact ⟨hm,hb (K i) (Adata i) Dprofile le_rfl (fun _ _ ↦ le_rfl)⟩
  exact hbound

end JanetCartan.ResponseTransfer.FullEllipticApplication
