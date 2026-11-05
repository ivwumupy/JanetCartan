module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.AdjointJointSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.EllipticJointProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Branches
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.JointEnvelope

/-!
# Joint Sobolev transfer for the literal adjoint selected elliptic PDO

Instantiate the sharp symbol profiles of the original family, full Q/B,
physical masks and annular selector. The actual diagonal geometry supplies
all normal-map and critical inverse inputs. Source phase/domain and mixed
source jets remain the original inputs of the response application.

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
variable {d : ℕ} {ι : Type} [Fintype ι]
local notation "E" => Euclidean (d+1)
local notation "Param" => Euclidean 3 × Euclidean d
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Vf" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp Vf 2 (volume : Measure E)
local notation "W" => CarrierVariables (d+1)

open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.EllipticComplement
open ArbitraryAccuracy.ResidualLocalization NearCarrierFullLow
variable {Ωcoeff : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Apply the literal Hilbert adjoint of the selected elliptic inverse or
full residual to the
original full source. The primitive symbol and normal-chart inputs are all
discharged. Original source phase/domain and mixed source jets are retained,
with the sharp inverse-frequency weighted and K profiles
(`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem exists_selected_ellipticPDO_adjoint_joint_sobolev
    (fam : ActualMaskFamily Ωcoeff x RQ A₀ K M) (hK : IsCompact K)
    (hΩcoeff : IsOpen Ωcoeff) (hball : closedBall x RQ ⊆ Ωcoeff)
    (χout χsource : E → ℂ) (hχsource : χsource = fun z ↦ (fam.inputMask z : ℂ))
    (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (hos : tsupport χout ⊆ closedBall x (2*fam.physicalRadius))
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (π : E → ℝ) (hπ : ContDiff ℝ ∞ π) (hcπ : HasCompactSupport π)
    (hzero : (0 : E) ∉ tsupport π)
    (AQ AB : ℕ → ℝ) (hAQ : ∀ k, 0 ≤ AQ k) (hAB : ∀ k, 0 ≤ AB k)
    (R ℓ : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    (basis : OrthonormalBasis ι ℝ W)
    (s : ℕ) (ps : List Param) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (Aphase : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j)
    {Bsource radius : ℝ} (hBsource : 0 ≤ Bsource) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d+1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
      X₀ ⊆ ball 0 R →
    ∀ (Rstar : ℕ), fullLowReserve (d+1) + 2 < Rstar →
    ∀ L lam : ℝ, 1 ≤ L → 1 ≤ lam →
    ∀ (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1)),
    ContDiffOn ℝ ∞ Q Ωcoeff → ContDiffOn ℝ ∞ B Ωcoeff →
    MapsTo Q Ωcoeff (closedBall A₀ fam.coefficientRadius) →
    (∀ k, cNorm (closedBall x RQ) k Q ≤ AQ k * L ^ (k-Rstar)) →
    (∀ k, cNorm (closedBall x RQ) k B ≤ AB k * L ^ (k-Rstar)) →
    ∀ (residual : Bool) (φ : E → Param → ℝ),
    let symbol := fun y ξ ↦ π (lam⁻¹ • ξ) •
      (if residual then ellipticResidualSymbol fam hK threshold Q B y ξ
        else ellipticInverseSymbol fam hK threshold Q y ξ)
    let f := carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ
    let κ : E × Param → W := fun q ↦ WithLp.toLp 2 (q.1, gradient (fun y ↦ φ y q.2) q.1)
    let α := fun (q : E × Param) (w : W) ↦ (lam ^ (-1 : ℤ))⁻¹ • normalizedFullAmplitude
      (fun x z ξ ↦ ((χout z * χsource x) • symbol z ξ).conjTranspose) lam (q.1, w.fst, w.snd)
    ∀ (Ω KP U : Set (E × Param)) (Dcrit : Set W),
    IsOpen Ω → ContDiffOn ℝ ∞ (Function.uncurry φ) Ω → IsCompact KP → KP ⊆ Ω →
    cNorm KP 2 (Function.uncurry φ) ≤ Bsource →
    IsOpen U → U ⊆ Ω → IsOpen Dcrit → Convex ℝ Dcrit → MapsTo κ U Dcrit →
    (∀ q ∈ U, ∀ w ∈ Dcrit, ∀ t ∈ Icc (0 : ℝ) 1,
      ((κ q + t • (w-κ q)).fst, q.2) ∈ KP) →
    (∀ j ≤ fullLowReserve (d+1) + (s + ps.length) + 2, ∀ q ∈ U ×ˢ Dcrit,
      ‖iteratedFDeriv ℝ j (Function.uncurry f) q‖ ≤ Aphase j * L ^ (j-Rstar)) →
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
      vectorFourierSobolevNorm (s : ℝ) output ≤ C * lam ^ (-1 : ℤ) *
        (∑ j ∈ Finset.range (s+ps.length+1), L ^ (s+ps.length-j) * Ddata j) ∧
      ∀ (Kinput A₀ : ℝ) (Dprofile : ℕ → ℝ), L ≤ Kinput →
        (∀ j, j ≤ s+ps.length → Ddata j ≤ A₀ * Dprofile j * Kinput ^ j) →
        vectorFourierSobolevNorm (s : ℝ) output ≤
          (C * ∑ j ∈ Finset.range (s+ps.length+1), Dprofile j) *
            lam ^ (-1 : ℤ) * A₀ * Kinput ^ (s+ps.length) := by
  subst χsource
  obtain ⟨Aamp, hAamp, hamp⟩ := exists_elliptic_selected_joint_profiles fam hK hΩcoeff hball
    χout ho hoc hos threshold ht π hπ hcπ hzero AQ AB hAQ hAB
  obtain ⟨C, hC, hb⟩ := exists_diagonalPDO_adjoint_joint_sobolev_of_primitive_jets
    (r := d+1) R ℓ hℓ hRcell basis s ps hps Aphase Aamp hphase hAamp hBsource hradius
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero hX₀ Rstar hRstar L lam hL hlam
    Q B hQ hB hmap hQp hBp residual φ symbol f κ α Ω KP U Dcrit
    hΩ hφ hKP hKPΩ hBsrc hU hUΩ hD hcD hκD hsegment hp
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    Ksource Ssource hKsource hSsource hKS hφsource a ha has param hparam Ddata hDdata hj
  have hRtwo : 2 ≤ Rstar := by omega
  obtain ⟨hα, hαjet⟩ := hamp Rstar hRtwo L lam hL hlam Q B hQ hB hmap hQp hBp residual true
  have he : (fun a b ξ ↦ π (lam⁻¹ • ξ) • orientedMaskedPDOAmplitude false χout
      (fun z ↦ (fam.inputMask z : ℂ))
      (if residual then ellipticResidualSymbol fam hK threshold Q B
        else ellipticInverseSymbol fam hK threshold Q) a b ξ) =
      (fun a b ξ ↦ (χout a * (fam.inputMask b : ℂ)) • symbol a ξ) := by
    funext a b ξ
    dsimp only [orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte, symbol]
    cases residual <;> exact smul_comm _ _ _
  simp only [↓reduceIte, he] at hα hαjet
  exact hb X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero hX₀ Rstar hRstar L lam hL hlam (-1)
    φ symbol χout (fun z ↦ (fam.inputMask z : ℂ)) Ω KP U Dcrit hΩ hφ hKP hKPΩ hBsrc
    hU hUΩ hD hcD hκD hsegment hp hα.contDiffOn (fun j _ q _ ↦ hαjet j q)
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    Ksource Ssource hKsource hSsource hKS hφsource a ha has param hparam Ddata hDdata hj

end JanetCartan.ResponseTransfer.DiagonalPdo