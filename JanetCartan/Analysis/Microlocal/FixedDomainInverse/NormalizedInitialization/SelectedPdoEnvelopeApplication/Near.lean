module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.SourceBox
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.JointSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.AdjointJointSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.OperatorIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

/-!
# Finite near-carrier application for the same selected PDO letters

Apply the actual full-frequency diagonal PDO theorem to the endpoint and
algebraic normalized amplitudes. Its primitive profiles are supplied by
`ReservedEndpointSymbol` and `ReservedAlgebraicSymbol`; this shared deduction
constructs every source-box, stationary-phase and support input. The original
source jets are only used through the derivative order requested by the
consumer, before the finite reserve compression is restored.

Consumer: complete selected PDO envelopes in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open ResponseTransfer ResponseTransfer.DiagonalPdo ResponseTransfer.FullSourceEnvelopes FullSourceStationary
open ResponseTransfer.Complement ResponseTransfer.DirectEvolution
open ResponseTransfer.DirectEvolution.AnnularSobolev ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open CharacteristicTransport.CompleteResidual ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer.NearCarrierFullLow
variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The actual annular masked PDO retains its total source order when the
finite primitive jets are placed on a compressed scale. This lemma is applied
to the checked endpoint and algebraic symbol producers; it assumes no
response-output estimate (`app:ch_response:eq:direct-envelope-profile`). -/
theorem selected_pdo_annular_sobolev_of_finite_scale_compression
    (x : E) (radius : ℝ) (hradius : 0 < radius) (χout χsource : E → ℂ)
    (hoc : HasCompactSupport χout) (hsc : HasCompactSupport χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ ball x radius)
    {ra rb : ℝ} (hra : 0 < ra) (hrb : 0 < rb)
    (basis : OrthonormalBasis ι ℝ W)
    (s : ℕ) (ps : List Par) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rstar Rnear : ℕ) (hRnear : fullLowReserve (d+1)+2 < Rnear)
    (Aphase Aamp : ℕ → ℝ) (hAphase : ∀ j, 0 ≤ Aphase j) (hAamp : ∀ j, 0 ≤ Aamp j)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hK : ∀ i, 1 ≤ K i)
    (hAdata : ∀ i, 0 ≤ Adata i)
    (symbol : I → E → E → Mat)
    (hsymbol : ∀ i (adj : Bool),
      let A : FullAmplitude (d+1) (d+1) := fun y z ξ ↦ (χout y * χsource z) •
        (annularSelector ra rb hra hrb ((lam i)⁻¹ • ξ) • symbol i y ξ)
      let α := fun (q : E × Par) (w : W) ↦ (lam i ^ (-1 : ℤ))⁻¹ •
        normalizedFullAmplitude (if adj then exchangedAdjointAmplitude A else A)
          (lam i) (q.1,w.fst,w.snd)
      ContDiff ℝ ∞ (Function.uncurry α) ∧ ∀ j v,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) v‖ ≤ Aamp j * L i ^ (j+2-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x radius ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x radius ×ˢ Kpar →
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
    ∀ adj : Bool,
    let σ := fun i y ξ ↦ π ((lam i)⁻¹ • ξ) • symbol i y ξ
    let output := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (σ i)))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      MemVectorFourierSobolev (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (output i) c) ≤
          C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length) := by
  classical
  intro π adj σ output
  let X := tsupport χout ∪ tsupport χsource
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let KP := closedBall x (radius) ×ˢ Kpar
  let Ubox := ball x (radius) ×ˢ V
  let D := e ⁻¹' (ball x (radius) ×ˢ
    ball (0 : E) (1+max (Aphase 2) (2*rb)))
  let Kcrit := e ⁻¹' (X ×ˢ tsupport π)
  let Wcompact := e ⁻¹' (closedBall x (radius) ×ˢ
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
  obtain ⟨hD,hDconv,hgeometry⟩ := diagonal_source_box_geometry x (radius)
    (Aphase 2) (2*rb) hKpar hVK
  obtain ⟨hX,hXball,hKcrit,hKcritD,hsupport⟩ :=
    selected_pdo_source_box_support (r := d+1) x radius χout χsource hoc hsc hmask hra hrb (Aphase 2)
  let Rcell := ‖x‖ + radius + 1
  have hRcell : 0 < Rcell := by
    dsimp only [Rcell]
    linarith [norm_nonneg x,hradius]
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
  have hn : lam i ≠ 0 := (zero_lt_one.trans_le (hlam i)).ne'
  obtain ⟨hscrit,hsoutput,hsslice⟩ := hsupport (symbol i) (lam i) hn (-1) adj
  obtain ⟨hα,hαjet⟩ := hsymbol i adj
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
      simp only [Bool.false_eq_true,↓reduceIte] at hscrit hsoutput hsslice hα hαjet
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

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
