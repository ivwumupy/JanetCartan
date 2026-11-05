module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.FullEllipticApplication.Signed
public import JanetCartan.Analysis.Microlocal.EllipticLocalization.CommonOutput
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators

/-!
# Actual elliptic branches of the same normalized solver

The original common output is absorbed by its proved plateau. The elliptic
operator's literal factor `1 / I` is retained through adjunction and whole
conjugation, and the normalized half-pair is applied to those actual operators.
The full covector, original source and carrier factor are unchanged.

Consumers: `NormalizedSolver.pairedSolver`, `NormalizedSolver.pairedResidual`,
and their ordered source estimates in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Set Metric MeasureTheory Filter FourierTransform
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap

namespace JanetCartan.ResponseTransfer.FullEllipticApplication

open JanetCartan.ResponseTransfer.Complement
open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.AnnularComplement
open DirectEvolution.IntegratedEnvelope.Assembly
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds Pseudodifferential
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open RegularSector.EllipticLocalization RegularSector.Realization
open CharacteristicTransport.CompleteResidual

variable {d : ℕ} {I ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp F 2 (volume : Measure E)
local notation "ScalarH" => Lp ℂ 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "Coeff" => Fin (d+1) → Mat

private theorem scalar_fourier_complex_smul (s : ℝ) (z : ℂ) (u : ScalarH)
    (hu : MemFourierSobolev s u) :
    MemFourierSobolev s (z • u) ∧
      fourierSobolevNorm s (z • u) = ‖z‖ * fourierSobolevNorm s u := by
  have hf : 𝓕 (z • u) = z • 𝓕 u := map_smul (fourierCLM ℂ ScalarH) z u
  have hw : weightedL2Fourier s (z • u) =ᵐ[volume] z • weightedL2Fourier s u := by
    filter_upwards [Lp.coeFn_smul z (𝓕 u)] with ξ hξ
    simp only [weightedL2Fourier,hf,hξ,Pi.smul_apply]
    exact smul_comm _ _ _
  have hm : MemFourierSobolev s (z • u) := (hu.const_smul z).ae_eq hw.symm
  have he : hm.toLp (weightedL2Fourier s (z • u)) = z • hu.toLp (weightedL2Fourier s u) := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ hw
  refine ⟨hm,?_⟩
  have hn := congrArg norm he
  rw [norm_smul] at hn
  simpa only [Lp.norm_toLp,fourierSobolevNorm] using hn

private theorem vector_fourier_complex_smul (s : ℝ) (z : ℂ) (u : H)
    (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s (z • u) ∧
      vectorFourierSobolevNorm s (z • u) ≤ ‖z‖ * vectorFourierSobolevNorm s u := by
  have hc j : finiteL2CoordinateIsometry volume (z • u) j =
      z • finiteL2CoordinateIsometry volume u j := by
    exact congrArg (fun f ↦ f j) (map_smul (finiteL2CoordinateIsometry volume) z u)
  have hm : MemVectorFourierSobolev s (z • u) := by
    intro j
    rw [hc]
    exact (scalar_fourier_complex_smul s z _ (hu j)).1
  refine ⟨hm,vectorFourierSobolevNorm_le_of_coordinate_bounds (norm_nonneg z) _ _ ?_⟩
  intro j
  rw [hc]
  exact (scalar_fourier_complex_smul s z _ (hu j)).2.le

private theorem complex_smul_ordered_envelopes
    {V : Set Par} (hV : IsOpen V) (g : I → Par → H) (A K : I → ℝ)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (g i) V)
    (hprofile : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g q.1) q.2)
        (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) (z : ℂ) :
    (∀ i, ContDiffOn ℝ ∞ (fun c ↦ z • g i c) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ z • g q.1 c) q.2)
        (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  let Mz : H →L[ℝ] H := (z • (ContinuousLinearMap.id ℂ H)).restrictScalars ℝ
  have hsmz i : ContDiffOn ℝ ∞ (fun c ↦ z • g i c) V :=
    Mz.contDiff.comp_contDiffOn (hsm i)
  refine ⟨hsmz,?_⟩
  intro ps hps s
  obtain ⟨C,hC,hbound⟩ := hprofile ps hps s
  refine ⟨‖z‖*C,mul_nonneg (norm_nonneg z) hC,?_⟩
  intro q
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ z • g q.1 c) q.2 =
      z • orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g q.1) q.2 := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsmz q.1) ps q.2.property,
      orderedParameterWord_eq_iteratedFDeriv hV (hsm q.1) ps q.2.property]
    have hat : ContDiffAt ℝ ps.length (g q.1) q.2 :=
      ((hsm q.1).contDiffAt (hV.mem_nhds q.2.property)).of_le (by simp)
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get)
      (Mz.iteratedFDeriv_comp_left hat (le_refl (ps.length : ℕ∞ω)))
  obtain ⟨hm,hb⟩ := hbound q
  obtain ⟨hmz,hbz⟩ := vector_fourier_complex_smul (s : ℝ) z _ hm
  dsimp only
  rw [he]
  refine ⟨hmz,?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hmz]
  rw [vectorFourierSobolevScale_gradeNorm s hm] at hb
  exact hbz.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg z)).trans_eq (by ring))

private theorem add_ordered_envelopes
    {V : Set Par} (hV : IsOpen V) (g h : I → Par → H) (A K : I → ℝ)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) V) (hh : ∀ i, ContDiffOn ℝ ∞ (h i) V)
    (hgp : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g q.1) q.2)
        (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1))
    (hhp : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (h q.1) q.2)
        (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) :
    (∀ i, ContDiffOn ℝ ∞ (fun c ↦ g i c+h i c) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ g q.1 c+h q.1 c) q.2)
        (fun q ↦ A q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  have hsum i : ContDiffOn ℝ ∞ (fun c ↦ g i c+h i c) V := (hg i).add (hh i)
  refine ⟨hsum,?_⟩
  intro ps hps s
  obtain ⟨Cg,hCg,hgb⟩ := hgp ps hps s
  obtain ⟨Ch,hCh,hhb⟩ := hhp ps hps s
  refine ⟨Cg+Ch,add_nonneg hCg hCh,?_⟩
  intro q
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ g q.1 c+h q.1 c) q.2 =
      orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g q.1) q.2 +
        orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (h q.1) q.2 := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsum q.1) ps q.2.property,
      orderedParameterWord_eq_iteratedFDeriv hV (hg q.1) ps q.2.property,
      orderedParameterWord_eq_iteratedFDeriv hV (hh q.1) ps q.2.property]
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get) (iteratedFDeriv_add_apply (i := ps.length)
      (((hg q.1).contDiffAt (hV.mem_nhds q.2.property)).of_le (by simp))
      (((hh q.1).contDiffAt (hV.mem_nhds q.2.property)).of_le (by simp)))
  obtain ⟨hgm,hgb⟩ := hgb q
  obtain ⟨hhm,hhb⟩ := hhb q
  dsimp only
  rw [he]
  exact ⟨(vectorFourierSobolevScale.level s).add_mem hgm hhm,
    (gradeNorm_add_le vectorFourierSobolevScale hgm hhm).trans
      ((add_le_add hgb hhb).trans_eq (by ring))⟩

private theorem complex_smul_reserved_ordered_bounds
    {V : Set Par} (hV : IsOpen V) (g : I → Par → H) (lam A K : I → ℝ) (reserve : ℕ)
    (hsm : ∀ i, ContDiffOn ℝ ∞ (g i) V)
    (hprofile : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ≤
            C * lam i ^ (-1 : ℤ) * A i * K i ^ (s+ps.length-reserve)) (z : ℂ) :
    (∀ i, ContDiffOn ℝ ∞ (fun c ↦ z • g i c) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ z • g i c) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ z • g i c) c) ≤
            C * lam i ^ (-1 : ℤ) * A i * K i ^ (s+ps.length-reserve) := by
  let Mz : H →L[ℝ] H := (z • (ContinuousLinearMap.id ℂ H)).restrictScalars ℝ
  have hsmz i : ContDiffOn ℝ ∞ (fun c ↦ z • g i c) V :=
    Mz.contDiff.comp_contDiffOn (hsm i)
  refine ⟨hsmz,?_⟩
  intro ps hps s
  obtain ⟨C,hC,hbound⟩ := hprofile ps hps s
  refine ⟨‖z‖*C,mul_nonneg (norm_nonneg z) hC,?_⟩
  intro i c hc
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ z • g i c) c =
      z • orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsmz i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hsm i) ps hc]
    have hat : ContDiffAt ℝ ps.length (g i) c := ((hsm i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get)
      (Mz.iteratedFDeriv_comp_left hat (le_refl (ps.length : ℕ∞ω)))
  obtain ⟨hm,hb⟩ := hbound i c hc
  obtain ⟨hmz,hbz⟩ := vector_fourier_complex_smul (s : ℝ) z _ hm
  rw [he]
  exact ⟨hmz,hbz.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg z)).trans_eq (by ring))⟩

private theorem add_reserved_ordered_bounds
    {V : Set Par} (hV : IsOpen V) (g h : I → Par → H) (lam A K : I → ℝ) (reserve : ℕ)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) V) (hh : ∀ i, ContDiffOn ℝ ∞ (h i) V)
    (hgp : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c) ≤
            C * lam i ^ (-1 : ℤ) * A i * K i ^ (s+ps.length-reserve))
    (hhp : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (h i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (h i) c) ≤
            C * lam i ^ (-1 : ℤ) * A i * K i ^ (s+ps.length-reserve)) :
    (∀ i, ContDiffOn ℝ ∞ (fun c ↦ g i c+h i c) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ g i c+h i c) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ g i c+h i c) c) ≤
            C * lam i ^ (-1 : ℤ) * A i * K i ^ (s+ps.length-reserve) := by
  have hsum i : ContDiffOn ℝ ∞ (fun c ↦ g i c+h i c) V := (hg i).add (hh i)
  refine ⟨hsum,?_⟩
  intro ps hps s
  obtain ⟨Cg,hCg,hgb⟩ := hgp ps hps s
  obtain ⟨Ch,hCh,hhb⟩ := hhp ps hps s
  refine ⟨Cg+Ch,add_nonneg hCg hCh,?_⟩
  intro i c hc
  have he : orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (fun c ↦ g i c+h i c) c =
      orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (g i) c +
        orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (h i) c := by
    rw [orderedParameterWord_eq_iteratedFDeriv hV (hsum i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hg i) ps hc,
      orderedParameterWord_eq_iteratedFDeriv hV (hh i) ps hc]
    exact congrArg (fun D : Par [×ps.length]→L[ℝ] H ↦ D ps.get) (iteratedFDeriv_add_apply (i := ps.length)
      (((hg i).contDiffAt (hV.mem_nhds hc)).of_le (by simp))
      (((hh i).contDiffAt (hV.mem_nhds hc)).of_le (by simp)))
  obtain ⟨hgm,hgb⟩ := hgb i c hc
  obtain ⟨hhm,hhb⟩ := hhb i c hc
  rw [he]
  have hm := (vectorFourierSobolevScale.level s).add_mem hgm hhm
  have hadd := gradeNorm_add_le vectorFourierSobolevScale hgm hhm
  rw [vectorFourierSobolevScale_gradeNorm s hm,vectorFourierSobolevScale_gradeNorm s hgm,
    vectorFourierSobolevScale_gradeNorm s hhm] at hadd
  exact ⟨hm,hadd.trans ((add_le_add hgb hhb).trans_eq (by ring))⟩

variable {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {Aref : Fin (d+1) → MetricTensor (d+1)} {K₀ : Set (Euclidean (d+1))}

/-- The literal common-output elliptic branches and their normalized
half-pairs satisfy the full ordered source envelopes. This includes the
actual `1 / I` normalization, adjoints and whole conjugates, with no new
operator or source selected. The frequency factor is exactly `lam⁻¹`, hence
exactly the extra `τ` at `lam = τ⁻¹`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem actual_elliptic_normalized_ordered_envelopes
    (fam : ActualMaskFamily Ωcoeff x RQ Aref K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x fam.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : fam.radialThreshold ≤ threshold)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rstar : ℕ) (hRstar : fullLowReserve (d+1)+2 < Rstar)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ωcoeff)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ωcoeff)
    (hmap : ∀ i, MapsTo (Q i) Ωcoeff (closedBall Aref fam.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hsourceBand : ∀ i c, c ∈ V → ∀ y ∈ ball x (3*fam.physicalRadius),
      a₀ ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ B₀)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x (3*fam.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l)) :
    ∀ residual adj : Bool,
    let raw := fun i ↦ (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
      (if residual then ellipticResidual fam hK₀ threshold (Q i) (B i)
        else ellipticSolver fam hK₀ threshold (Q i))
    let u := fun i c ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)
    let signed := fun (reflected : Bool) i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (if reflected then boundedConjugate (annularGraphOrientation adj (raw i))
        else annularGraphOrientation adj (raw i)) (u i c)
    (∀ reflected : Bool, (∀ i, ContDiffOn ℝ ∞ (signed reflected i) V) ∧
      ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
        HasEnvelopeProfile vectorFourierSobolevScale
          (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (signed reflected q.1) q.2)
          (fun q ↦ lam q.1 ^ (-1 : ℤ) * Adata q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1)) ∧
    let normalized := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (NormalizedSolver.normalizedPair (raw i))) (u i c)
    (∀ i, ContDiffOn ℝ ∞ (normalized i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (normalized q.1) q.2)
        (fun q ↦ lam q.1 ^ (-1 : ℤ) * Adata q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
  classical
  intro residual adj raw u signed
  let χout := fun y ↦ (output y : ℂ)
  let χsource := fun y ↦ (fam.inputMask y : ℂ)
  have hχout : ContDiff ℝ ∞ χout := Complex.ofRealCLM.contDiff.comp ho
  have hcχout : HasCompactSupport χout := hoc.comp_left Complex.ofReal_zero
  have hsχout : tsupport χout ⊆ closedBall x (2*fam.physicalRadius) :=
    (commonOutput_elliptic_carrier fam output hoc hos).2
  let σ := fun i y ξ ↦
    if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
      else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ
  let core := fun i ↦ maskedPhysicalPDO χout χsource (σ i)
  let coreSigned := fun (reflected : Bool) i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
    ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    (if reflected then boundedConjugate (annularGraphOrientation adj (core i))
      else annularGraphOrientation adj (core i)) (u i c)
  have hcore := complete_elliptic_signed_ordered_envelopes fam hK₀ hΩcoeff hball
    χout hχout hcχout hsχout threshold ht basis hV hKpar hVK Rstar hRstar AQ AB Aphase
    hAQ hAB hAphase hν hν1 ha₀ hB₀ lam L K Adata hlam hL hLK hscale hAdata
    Q B hQ hB hmap hQl hBl hQp hBp φ hφ hcap hφjets hsourceBand
    S hS hSU a ha has Csource hfourier residual adj
  have habs i : (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
      (maskedPhysicalPDO (fun y ↦ (fam.outputMask y : ℂ)) χsource (σ i)) = core i := by
    apply commonOutput_ellipticPDO_eq_masked fam hK₀ hΩcoeff hball output ho hos hob ht
      (Q i) (B i) (hQ i) (hB i) (hmap i) (hQl i) (hBl i) (σ i)
    cases residual <;> simp only [σ,Bool.false_eq_true,↓reduceIte,mem_insert_iff,mem_singleton_iff,true_or,or_true]
  have hraw i : raw i = (1/Complex.I) • core i := by
    rw [← habs i]
    cases residual <;> simp only [raw,Bool.false_eq_true,↓reduceIte,ellipticSolver,ellipticResidual,σ]
    all_goals
      apply ContinuousLinearMap.ext
      intro v
      exact map_smul (sourceCutMultiplier output ho.continuous hob) (1/Complex.I) _
  let cadj : ℂ := if adj then star (1/Complex.I) else 1/Complex.I
  have horient i : annularGraphOrientation adj (raw i) =
      cadj • annularGraphOrientation adj (core i) := by
    rw [hraw]
    cases adj <;> simp only [cadj,annularGraphOrientation,Bool.false_eq_true,↓reduceIte,map_smulₛₗ,starRingEnd_apply]
  have hactual : ∀ reflected : Bool, (∀ i, ContDiffOn ℝ ∞ (signed reflected i) V) ∧
      ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) →
        HasEnvelopeProfile vectorFourierSobolevScale
          (fun q : I × V ↦ orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (signed reflected q.1) q.2)
          (fun q ↦ lam q.1 ^ (-1 : ℤ) * Adata q.1 * K q.1 ^ ps.length) (fun q ↦ K q.1) := by
    intro reflected
    let z : ℂ := if reflected then star cadj else cadj
    have hsign i : (if reflected then boundedConjugate (annularGraphOrientation adj (raw i))
        else annularGraphOrientation adj (raw i)) =
        z • (if reflected then boundedConjugate (annularGraphOrientation adj (core i))
          else annularGraphOrientation adj (core i)) := by
      rw [horient]
      cases reflected
      · rfl
      · apply ContinuousLinearMap.ext
        intro v
        exact star_smul cadj (annularGraphOrientation adj (core i) (star v))
    have heq i : signed reflected i = fun c ↦ z • coreSigned reflected i c := by
      funext c
      change demodulatedL2Operator (lam i) (fun y ↦ φ i y c) _
        (if reflected then boundedConjugate (annularGraphOrientation adj (raw i))
          else annularGraphOrientation adj (raw i)) (u i c) = _
      rw [hsign]
      simp only [coreSigned,demodulatedL2Operator,ContinuousLinearMap.comp_apply,
        smul_apply,map_smul]
    have hb := complex_smul_ordered_envelopes hV (coreSigned reflected)
      (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K (hcore reflected).1 (hcore reflected).2 z
    simpa only [heq] using hb
  refine ⟨hactual,?_⟩
  intro normalized
  have hsum := add_ordered_envelopes hV (signed false) (signed true)
    (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K (hactual false).1 (hactual true).1
    (hactual false).2 (hactual true).2
  have hhalf := complex_smul_ordered_envelopes hV (fun i c ↦ signed false i c+signed true i c)
    (fun i ↦ lam i ^ (-1 : ℤ) * Adata i) K hsum.1 hsum.2 (1/2 : ℂ)
  have hpairOp i : annularGraphOrientation adj (NormalizedSolver.normalizedPair (raw i)) =
      (1/2 : ℂ) • (annularGraphOrientation adj (raw i)+
        boundedConjugate (annularGraphOrientation adj (raw i))) := by
    cases adj
    · exact NormalizedSolver.normalizedPair_eq (raw i)
    · change (NormalizedSolver.normalizedPair (raw i)).adjoint = _
      rw [NormalizedSolver.normalizedPair_adjoint]
      exact NormalizedSolver.normalizedPair_eq _
  have heq i : normalized i = fun c ↦ (1/2 : ℂ) • (signed false i c+signed true i c) := by
    funext c
    change demodulatedL2Operator (lam i) (fun y ↦ φ i y c) _
      (annularGraphOrientation adj (NormalizedSolver.normalizedPair (raw i))) (u i c) = _
    rw [hpairOp]
    simp only [signed,demodulatedL2Operator,ContinuousLinearMap.comp_apply,
      smul_apply,add_apply,map_smul,map_add,Bool.false_eq_true,↓reduceIte]
  simpa only [heq] using hhalf


/-- The actual common-output elliptic inverse and residual, their signed
orientations and their normalized half-pairs retain `K^(s+length-Rsource)`
with natural subtraction. In particular all orders below the reserve keep
the original amplitude. The literal `1 / I`, adjoint, whole conjugate and
half-normalization are the same ones used by `NormalizedSolver.pairedSolver`
and `NormalizedSolver.pairedResidual`
(`app:ch_response:eq:response-graded-reduced`). -/
theorem actual_elliptic_normalized_reserved_ordered_bounds
    (fam : ActualMaskFamily Ωcoeff x RQ Aref K₀ M) (hK₀ : IsCompact K₀)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x fam.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) (ht : fam.radialThreshold ≤ threshold)
    (basis : OrthonormalBasis ι ℝ W)
    {V Kpar : Set Par} (hV : IsOpen V) (hKpar : IsCompact Kpar) (hVK : V ⊆ Kpar)
    (Rsource Rstar : ℕ) (hRstar : Rsource+fullLowReserve (d+1)+3 ≤ Rstar)
    (AQ AB Aphase : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) (hAphase : ∀ j, 0 ≤ Aphase j)
    {ν a₀ B₀ : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (ha₀ : 0 < a₀) (hB₀ : 0 < B₀)
    (lam L K Adata : I → ℝ)
    (hlam : ∀ i, 1 ≤ lam i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hscale : ∀ i, K i ≤ lam i ^ (1-ν)) (hAdata : ∀ i, 0 ≤ Adata i)
    (Q : I → E → Coeff) (B : I → E → Mat)
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ωcoeff)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) Ωcoeff)
    (hmap : ∀ i, MapsTo (Q i) Ωcoeff (closedBall Aref fam.coefficientRadius))
    (hQl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (Q i) ≤ M)
    (hBl : ∀ i, cNorm (closedBall x RQ) (2*(d+2)+2) (B i) ≤ M)
    (hQp : ∀ i j, cNorm (closedBall x RQ) j (Q i) ≤ AQ j * L i ^ (j-Rstar))
    (hBp : ∀ i j, cNorm (closedBall x RQ) j (B i) ≤ AB j * L i ^ (j-Rstar))
    (φ : I → E → Par → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (hcap : ∀ i, cNorm (closedBall x (3*fam.physicalRadius) ×ˢ Kpar) 2
      (Function.uncurry (φ i)) ≤ Aphase 2)
    (hφjets : ∀ i j q, q ∈ closedBall x (3*fam.physicalRadius) ×ˢ Kpar →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) q‖ ≤ Aphase j * L i ^ (j-Rstar))
    (hsourceBand : ∀ i c, c ∈ V → ∀ y ∈ ball x (3*fam.physicalRadius),
      a₀ ≤ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ∧ ‖fderiv ℝ (fun z ↦ φ i z c) y‖ ≤ B₀)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ ball x (3*fam.physicalRadius))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ S → a i q = 0) (Csource : ℕ → ℕ → ℝ)
    (hfourier : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ Csource l s * Adata i * K i ^ (s+l-Rsource)) :
    ∀ residual adj : Bool,
    let raw := fun i ↦ (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
      (if residual then ellipticResidual fam hK₀ threshold (Q i) (B i)
        else ellipticSolver fam hK₀ threshold (Q i))
    let u := fun i c ↦ graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)
    let signed := fun (reflected : Bool) i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (if reflected then boundedConjugate (annularGraphOrientation adj (raw i))
        else annularGraphOrientation adj (raw i)) (u i c)
    (∀ reflected : Bool, (∀ i, ContDiffOn ℝ ∞ (signed reflected i) V) ∧
      ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
          MemVectorFourierSobolev (s : ℝ)
            (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (signed reflected i) c) ∧
          vectorFourierSobolevNorm (s : ℝ)
            (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (signed reflected i) c) ≤
              C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource)) ∧
    let normalized := fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
      ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
      (annularGraphOrientation adj (NormalizedSolver.normalizedPair (raw i))) (u i c)
    (∀ i, ContDiffOn ℝ ∞ (normalized i) V) ∧
    ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
        MemVectorFourierSobolev (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (normalized i) c) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (normalized i) c) ≤
            C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
  classical
  intro residual adj raw u signed
  let χout := fun y ↦ (output y : ℂ)
  let χsource := fun y ↦ (fam.inputMask y : ℂ)
  have hχout : ContDiff ℝ ∞ χout := Complex.ofRealCLM.contDiff.comp ho
  have hcχout : HasCompactSupport χout := hoc.comp_left Complex.ofReal_zero
  have hsχout : tsupport χout ⊆ closedBall x (2*fam.physicalRadius) :=
    (commonOutput_elliptic_carrier fam output hoc hos).2
  let σ := fun i y ξ ↦
    if residual then ellipticResidualSymbol fam hK₀ threshold (Q i) (B i) y ξ
      else ellipticInverseSymbol fam hK₀ threshold (Q i) y ξ
  let core := fun i ↦ maskedPhysicalPDO χout χsource (σ i)
  let coreSigned := fun (reflected : Bool) i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c)
    ((hφ i).continuous.comp (continuous_id.prodMk continuous_const))
    (if reflected then boundedConjugate (annularGraphOrientation adj (core i))
      else annularGraphOrientation adj (core i)) (u i c)
  have hcore := complete_elliptic_signed_reserved_ordered_bounds fam hK₀ hΩcoeff hball
    χout hχout hcχout hsχout threshold ht basis hV hKpar hVK Rsource Rstar hRstar AQ AB Aphase
    hAQ hAB hAphase hν hν1 ha₀ hB₀ lam L K Adata hlam hL hLK hscale hAdata
    Q B hQ hB hmap hQl hBl hQp hBp φ hφ hcap hφjets hsourceBand
    S hS hSU a ha has Csource hfourier residual adj
  have habs i : (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
      (maskedPhysicalPDO (fun y ↦ (fam.outputMask y : ℂ)) χsource (σ i)) = core i := by
    apply commonOutput_ellipticPDO_eq_masked fam hK₀ hΩcoeff hball output ho hos hob ht
      (Q i) (B i) (hQ i) (hB i) (hmap i) (hQl i) (hBl i) (σ i)
    cases residual <;> simp only [σ,Bool.false_eq_true,↓reduceIte,mem_insert_iff,mem_singleton_iff,true_or,or_true]
  have hraw i : raw i = (1/Complex.I) • core i := by
    rw [← habs i]
    cases residual <;> simp only [raw,Bool.false_eq_true,↓reduceIte,ellipticSolver,ellipticResidual,σ]
    all_goals
      apply ContinuousLinearMap.ext
      intro v
      exact map_smul (sourceCutMultiplier output ho.continuous hob) (1/Complex.I) _
  let cadj : ℂ := if adj then star (1/Complex.I) else 1/Complex.I
  have horient i : annularGraphOrientation adj (raw i) =
      cadj • annularGraphOrientation adj (core i) := by
    rw [hraw]
    cases adj <;> simp only [cadj,annularGraphOrientation,Bool.false_eq_true,↓reduceIte,map_smulₛₗ,starRingEnd_apply]
  have hactual : ∀ reflected : Bool, (∀ i, ContDiffOn ℝ ∞ (signed reflected i) V) ∧
      ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
          MemVectorFourierSobolev (s : ℝ)
            (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (signed reflected i) c) ∧
          vectorFourierSobolevNorm (s : ℝ)
            (orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (signed reflected i) c) ≤
              C * lam i ^ (-1 : ℤ) * Adata i * K i ^ (s+ps.length-Rsource) := by
    intro reflected
    let z : ℂ := if reflected then star cadj else cadj
    have hsign i : (if reflected then boundedConjugate (annularGraphOrientation adj (raw i))
        else annularGraphOrientation adj (raw i)) =
        z • (if reflected then boundedConjugate (annularGraphOrientation adj (core i))
          else annularGraphOrientation adj (core i)) := by
      rw [horient]
      cases reflected
      · rfl
      · apply ContinuousLinearMap.ext
        intro v
        exact star_smul cadj (annularGraphOrientation adj (core i) (star v))
    have heq i : signed reflected i = fun c ↦ z • coreSigned reflected i c := by
      funext c
      change demodulatedL2Operator (lam i) (fun y ↦ φ i y c) _
        (if reflected then boundedConjugate (annularGraphOrientation adj (raw i))
          else annularGraphOrientation adj (raw i)) (u i c) = _
      rw [hsign]
      simp only [coreSigned,demodulatedL2Operator,ContinuousLinearMap.comp_apply,
        smul_apply,map_smul]
    have hb := complex_smul_reserved_ordered_bounds hV (coreSigned reflected)
      lam Adata K Rsource (hcore reflected).1 (hcore reflected).2 z
    simpa only [heq] using hb
  refine ⟨hactual,?_⟩
  intro normalized
  have hsum := add_reserved_ordered_bounds hV (signed false) (signed true)
    lam Adata K Rsource (hactual false).1 (hactual true).1
    (hactual false).2 (hactual true).2
  have hhalf := complex_smul_reserved_ordered_bounds hV (fun i c ↦ signed false i c+signed true i c)
    lam Adata K Rsource hsum.1 hsum.2 (1/2 : ℂ)
  have hpairOp i : annularGraphOrientation adj (NormalizedSolver.normalizedPair (raw i)) =
      (1/2 : ℂ) • (annularGraphOrientation adj (raw i)+
        boundedConjugate (annularGraphOrientation adj (raw i))) := by
    cases adj
    · exact NormalizedSolver.normalizedPair_eq (raw i)
    · change (NormalizedSolver.normalizedPair (raw i)).adjoint = _
      rw [NormalizedSolver.normalizedPair_adjoint]
      exact NormalizedSolver.normalizedPair_eq _
  have heq i : normalized i = fun c ↦ (1/2 : ℂ) • (signed false i c+signed true i c) := by
    funext c
    change demodulatedL2Operator (lam i) (fun y ↦ φ i y c) _
      (annularGraphOrientation adj (NormalizedSolver.normalizedPair (raw i))) (u i c) = _
    rw [hpairOp]
    simp only [signed,demodulatedL2Operator,ContinuousLinearMap.comp_apply,
      smul_apply,add_apply,map_smul,map_add,Bool.false_eq_true,↓reduceIte]
  simpa only [heq] using hhalf

end JanetCartan.ResponseTransfer.FullEllipticApplication
