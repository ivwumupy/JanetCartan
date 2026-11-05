module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.ReverseBranchFamily
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Branches
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.JointEnvelope

/-!
# Joint Sobolev transfer for the literal adjoint diagonal PDO

The original full-frequency symbol is exchanged and conjugate-transposed
inside the branch amplitude. The actual identity normal chart and original
source phase discharge all critical geometry. The derivative expansion uses
the literal Hilbert adjoint with its exchanged physical supports.

Sources: `app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
open Set Metric MeasureTheory Filter LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open DirectEvolution DirectEvolution.AnnularSobolev DirectEvolution.CompactTransfer
open DirectEvolution.BranchAmplitudes DirectEvolution.ModifiedLow
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds
open RegularSector.Characteristic.EvolutionIntegral CharacteristicTransport.CompleteResidual
open Pseudodifferential FullSourceStationary
variable {d r : ℕ} {ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "Vf" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp Vf 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)

/-- The literal Hilbert adjoint of the same masked full-frequency PDO has a
joint Sobolev envelope from
original phase/symbol jets and original mixed source jets. The diagonal normal
chart, stationary map, zero value, averaged inverse and weak expansions are
constructed. Constants precede the varying source, coefficient scale and
frequency. The sharp source profile has the same total order `s+ps.length`
whenever `L ≤ Kinput`, including `L=1`, with no added derivative loss
(`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem exists_diagonalPDO_adjoint_joint_sobolev_of_primitive_jets
    (R ℓ : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    (basis : OrthonormalBasis ι ℝ W)
    (s : ℕ) (ps : List Param) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {Bsource radius : ℝ} (hBsource : 0 ≤ Bsource) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d+1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
      X₀ ⊆ ball 0 R →
    ∀ (Rstar : ℕ), fullLowReserve (d+1) + 2 < Rstar →
    ∀ L lam : ℝ, 1 ≤ L → 1 ≤ lam → ∀ p : ℤ,
    ∀ (φ : E → Param → ℝ) (symbol : E → E → Mat) (χout χsource : E → ℂ),
    let f := carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ
    let κ : E × Param → W := fun q ↦ WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
    let α := fun (q : E × Param) (w : W) ↦ (lam ^ p)⁻¹ • normalizedFullAmplitude
      (fun x z ξ ↦ ((χout z * χsource x) • symbol z ξ).conjTranspose) lam (q.1, w.fst, w.snd)
    ∀ (Ω KP U : Set (E × Param)) (Dcrit : Set W),
    IsOpen Ω → ContDiffOn ℝ ∞ (Function.uncurry φ) Ω → IsCompact KP → KP ⊆ Ω →
    cNorm KP 2 (Function.uncurry φ) ≤ Bsource →
    IsOpen U → U ⊆ Ω → IsOpen Dcrit → Convex ℝ Dcrit → MapsTo κ U Dcrit →
    (∀ q ∈ U, ∀ w ∈ Dcrit, ∀ t ∈ Icc (0 : ℝ) 1,
      ((κ q + t • (w-κ q)).fst, q.2) ∈ KP) →
    (∀ j ≤ fullLowReserve (d+1) + (s + ps.length) + 2, ∀ q ∈ U ×ˢ Dcrit,
      ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L ^ (j-Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d+1) + (s + ps.length), ∀ q ∈ U ×ˢ Dcrit,
      ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j+2-Rstar)) →
    ∀ Kcrit : Set W, IsCompact Kcrit → Kcrit ⊆ Dcrit →
    (∀ q ∈ U, Function.support (α q) ⊆ Kcrit) →
    (∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ Y₀) →
    ∀ Cpar : Set Param, IsOpen Cpar → Y₀ ×ˢ Cpar ⊆ U →
    ∀ hcφ : ∀ param, Continuous (fun x ↦ φ x param),
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.2 ∈ X₀ ∧ q.1.1 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    ∀ (Ksource Ssource : Set E) (hKsource : IsCompact Ksource), IsOpen Ssource →
    Ksource ⊆ Ssource → (∀ param ∈ Cpar, ContDiffOn ℝ ∞ (fun x ↦ φ x param) Ssource) →
    ∀ (a : E × Param → Vf) (ha : ContDiff ℝ ∞ a) (has : ∀ q, q.1 ∉ Ksource → a q = 0),
    ∀ param ∈ Cpar, ∀ Ddata : ℕ → ℝ, (∀ j, 0 ≤ Ddata j) →
    (∀ j, j ≤ s + ps.length → ∃ hm : MemLp (fun x : E ↦ iteratedFDeriv ℝ j a (x,param)) 2 volume,
      ‖hm.toLp (fun x : E ↦ iteratedFDeriv ℝ j a (x,param))‖ ≤ Ddata j) →
    let output := orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
      (fun c ↦ demodulatedL2Operator lam (fun x ↦ φ x c) (hcφ c)
        (maskedPhysicalPDO χout χsource symbol).adjoint
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
    MemVectorFourierSobolev (s : ℝ) output ∧
      vectorFourierSobolevNorm (s : ℝ) output ≤ C * lam ^ p *
        (∑ j ∈ Finset.range (s+ps.length+1), L ^ (s+ps.length-j) * Ddata j) ∧
      ∀ (Kinput A₀ : ℝ) (Dprofile : ℕ → ℝ), L ≤ Kinput →
        (∀ j, j ≤ s+ps.length → Ddata j ≤ A₀ * Dprofile j * Kinput ^ j) →
        vectorFourierSobolevNorm (s : ℝ) output ≤
          (C * ∑ j ∈ Finset.range (s+ps.length+1), Dprofile j) *
            lam ^ p * A₀ * Kinput ^ (s+ps.length) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E E
  let B := ‖e.symm.toContinuousLinearMap‖ * (1+Bsource) * ‖e.toContinuousLinearMap‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨Cb, hCb, hbuild⟩ := exists_diagonalReverseBranchFamily_of_primitive_jets
    (r := r) R ℓ hℓ hRcell basis s (ps.map fun v ↦ ((0 : E), v))
    Aphase Aamp hphase hamp hB hradius
  let Cs := ((r : ℝ) * (d+1+1 : ℝ)^s) *
    (((Fintype.card ι + 2 : ℕ) : ℝ)^(s+ps.length) * Cb)
  refine ⟨Cs, by dsimp [Cs]; positivity, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero hX₀ Rstar hRstar L lam hL hlam p
    φ symbol χout χsource f κ α Ω KP U Dcrit hΩ hφ hKP hKPΩ hBsrc hU hUΩ hD hcD hκD
    hsegment hp hα hαjet Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq
    hsupport Ksource Ssource hKsource hSsource hKS hφsource a ha has param hparam Ddata hDdata hj
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam
  have hκ : ContDiffOn ℝ ∞ κ U := by
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.contDiff.comp_contDiffOn
      (contDiffOn_fst.prodMk ((contDiffOn_full_source_gradient hΩ hφ).mono hUΩ))
  have hc (q) (hq : q ∈ U) := diagonal_fullSourcePhase_stationary_value φ q
    (((hφ.contDiffAt (hΩ.mem_nhds (hUΩ hq))).comp q.1
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hcrit : ∀ q ∈ U, gradient (f q) (κ q) = 0 := fun q hq ↦ (hc q hq).1
  have hvalue : ∀ q ∈ U, f q (κ q) = 0 := fun q hq ↦ (hc q hq).2
  have hInv (q) (hq : q ∈ U) (w) (hw : w ∈ Dcrit) :
      IsUnit (averagedPhaseHessian f κ q w) ∧ ‖Ring.inverse (averagedPhaseHessian f κ q w)‖ ≤ B := by
    have h := diagonal_fullSourcePhase_averagedHessian_bound hΩ hφ hKP hKPΩ κ q w (hsegment q hq w hw)
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hBsrc) (norm_nonneg _)) (norm_nonneg _))⟩
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Dcrit) := by
    intro v hv
    have hw : (v.2.fst, v.1.2) ∈ Ω := hKPΩ (by
      simpa only [one_smul, add_sub_cancel] using hsegment v.1 hv.1 v.2 hv.2 1 ⟨zero_le_one,le_rfl⟩)
    have hx := hφ.contDiffAt (hΩ.mem_nhds (hUΩ hv.1))
    have hy := hφ.contDiffAt (hΩ.mem_nhds hw)
    exact ((((contDiffAt_fst.fst.inner ℝ ((WithLp.sndL 2 ℝ E E).contDiff.contDiffAt.comp v contDiffAt_snd)).sub
      (((WithLp.fstL 2 ℝ E E).contDiff.contDiffAt.comp v contDiffAt_snd).inner ℝ
        ((WithLp.sndL 2 ℝ E E).contDiff.contDiffAt.comp v contDiffAt_snd))).add
      (hy.comp v (((WithLp.fstL 2 ℝ E E).contDiff.contDiffAt.comp v contDiffAt_snd).prodMk
        contDiffAt_fst.snd))).sub (hx.comp v contDiffAt_fst)).contDiffWithinAt
  have hfamily (c : Param) (hc : c ∈ Cpar) := hbuild X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero hX₀
    Rstar hRstar L lam hL hlam p φ κ α U Dcrit hU hD hcD hf hκ hκD hcrit
    (fun q hq w hw ↦ (hInv q hq w hw).1) (fun q hq w hw ↦ (hInv q hq w hw).2)
    (by simpa only [List.length_map] using hp) hα (by simpa only [List.length_map] using hαjet)
    c (hs c hc) (hsfreq c hc) (hsupport c hc)
  let Ψ : TwoTimePhase d := fun _ _ x ξ ↦ inner ℝ x ξ
  have hΨ : elapsedPhase Ψ 0 = (fun x ξ : E ↦ inner ℝ x ξ) := by
    funext x ξ
    exact elapsedPhase_zero Ψ (fun _ _ _ ↦ rfl) x ξ
  have hf' : adjointCarrierPhase (elapsedPhase Ψ 0) φ = f := by
    rw [hΨ, diagonal_adjointCarrierPhase_eq]
  let T := fun branch ↦ reverseAnnularBranchOperator basis Ψ 0 lam p φ κ α branch param (hcφ param)
  let da := fun ds ↦ graphTestToLp (vectorOriginalDatumTest a ha hKsource has ds param)
  let output := orderedTransferAction (fun v F c ↦ fderiv ℝ F c v) ps
    (fun c ↦ demodulatedL2Operator lam (fun x ↦ φ x c) (hcφ c)
      (maskedPhysicalPDO χout χsource symbol).adjoint
      (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
  let aPi := fun q ↦ (a q).ofLp
  have haPi : ContDiff ℝ ∞ aPi := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).contDiff.comp ha
  have hasPi : ∀ q, q.1 ∉ Ksource → aPi q = 0 := fun q hq ↦ congrArg WithLp.ofLp (has q hq)
  have hweak (is : List (Fin (d+1))) (his : is.length ≤ s) :
      orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (output : 𝓢'(E,Vf)) =
      ((jointTransferTerms basis ((is.map fun i ↦ (EuclideanSpace.single i (1 : ℝ),(0 : Param))) ++
        ps.map (fun v ↦ ((0 : E),v)))).map fun branch ↦ (T branch (da branch.datumWord) : 𝓢'(E,Vf))).sum := by
    have h := WeakTransfer.reverseAnnularBranchFamily_joint_derivative_expansion basis Ψ 0 hlampos p φ κ
      hU hD hcD hKcrit hKD (hf'.symm ▸ hf) hα haPi hsupportCrit hκ
      (hf'.symm ▸ hcrit) (hf'.symm ▸ hvalue) hκD
      (hf'.symm ▸ (fun q hq w hw ↦ (hInv q hq w hw).1)) hKsource hSsource hKS hasPi
      ps is hYcompact houtput hCpar hXU hcφ hφsource
      (fun c hc ds hd branch hb ↦ by
        rw [hΨ, diagonal_adjointCarrierPhase_eq]
        exact (hfamily c hc).2 ds (by simpa only [List.length_map] using (show ds.length ≤ s + ps.length by omega)) branch hb)
      (by intro c hc ds hd branch hb x z θ _; rw [hΨ]; simp [inner_smul_right]) param hparam
    dsimp only [Ψ, α] at h
    simp only [reverseAnnularBranchOperator_initial_maskedPDO basis φ κ symbol χout χsource hlampos.ne'] at h
    simpa only [T, da, output, Ψ, α, vectorOriginalDatumTest, initialJointTransferTerm] using h
  obtain ⟨w, heq, hw, hnorm⟩ := annular_joint_sobolev_of_expansion s Cb hCb basis ps hps T
    L lam p hL hlampos a ha param da
    (fun ds _ _ ↦ vectorOriginalDatumTest_toLp_ae a ha hKsource has ds param)
    Ddata hDdata hj (output : 𝓢'(E,Vf)) hweak
    (fun is his branch hb ↦ by simpa only [List.length_map, T, Ψ] using (hfamily param hparam).1 is his branch hb (hcφ param))
  have he : w = output := (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := Vf) (μ := (volume : Measure E)) (p := 2))) heq
  rw [he] at hw hnorm
  have hweighted : vectorFourierSobolevNorm (s : ℝ) output ≤ Cs * lam ^ p *
      (∑ j ∈ Finset.range (s+ps.length+1), L ^ (s+ps.length-j) * Ddata j) := by
    simpa only [Cs, Nat.cast_add, Nat.cast_one] using hnorm
  refine ⟨hw, hweighted, ?_⟩
  intro Kinput A₀ Dprofile hLK hdata
  apply hweighted.trans
  calc
    _ ≤ Cs * lam ^ p *
        (A₀ * (∑ j ∈ Finset.range (s+ps.length+1), Dprofile j) *
          Kinput ^ (s+ps.length)) :=
      mul_le_mul_of_nonneg_left
        (jointWeightedProfile_le_inputScale (s+ps.length) hL hLK Ddata Dprofile hDdata hdata)
        (by dsimp [Cs]; positivity)
    _ = _ := by ring

end JanetCartan.ResponseTransfer.DiagonalPdo
