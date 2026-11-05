module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.Basic

/-!
# The actual next source in a finite measured residual chain

Apply the fixed smooth realization to each literal measured letter, sum those
representatives, and recover the exact uniform source Fourier profile from the
already proved one-letter estimates. The original spatial and parameter
supports are retained. This is the one-step deduction used in
`app:ch_regular:lem:finite-chain`; its quantitative input is supplied separately
by the characteristic, reflected, and full elliptic envelope producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles

open Pseudodifferential FourierIntegral ResponseTransfer ResponseTransfer.Complement
open RegularSector.FiniteAssembly
open FiniteChain.Graph.KernelLimits
open ResponseTransfer.DirectEvolution.AnnularSobolev
open ResponseTransfer.DirectEvolution.CompactTransfer
open ResponseTransfer.DirectEvolution.IntegratedEnvelope.Assembly
open FiniteResidualEnvelopes ResidualSmoothEnvelopes

variable {d r : ℕ} {I J : Type*} [Fintype J]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The same finite measured residual has a supported globally smooth
amplitude with the original natural source reserve. Ordinary all-order graph
bounds produce its smoothness; the supplied one-letter envelopes produce its
Fourier profile. Thus no regularity or estimate of an intermediate amplitude
is assumed (`app:ch_regular:lem:finite-chain`,
`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_measured_sum_reserved_source_profile
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    {V Csrc : Set Par} (hV : IsOpen V)
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (hS : IsCompact (tsupport χout))
    (raw : I → J → H →L[ℂ] H) (P : I → H →L[ℂ] H)
    (hP : ∀ i, P i = ∑ j, measuredOperator χout χin ho hi hob hib (raw i j))
    (hordinary : ∀ i j (s : ℕ), ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d+1) r,
        MemVectorFourierSobolev (s : ℝ)
          (measuredOperator χout χin ho hi hob hib (raw i j) (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ)
          (measuredOperator χout χin ho hi hob hib (raw i j) (graphTestToLp u)) ≤
            C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (lam A K : I → ℝ) (reserve : ℕ)
    (φ : I → Par → E → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (Function.uncurry (φ i)))
    (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (has : ∀ i q, q.1 ∉ tsupport χout → a i q = 0)
    (hap : ∀ i c, c ∉ Csrc → ∀ y, a i (y,c) = 0)
    (hstep : ∀ j (ps : List Par), (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
          (fun c ↦ demodulatedL2Operator (lam q.1) (φ q.1 c)
            ((hφ q.1).continuous.comp (continuous_const.prodMk continuous_id))
            (measuredOperator χout χin ho hi hob hib (raw q.1 j))
            (graphTestToLp (vectorOriginalDatumTest (a q.1) (ha q.1) hS (has q.1) [] c))) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve)) :
    ∃ b : I → E × Par → F, (∀ i, ContDiff ℝ ∞ (b i)) ∧
      (∀ i q, q.1 ∉ tsupport χout → b i q = 0) ∧
      (∀ i c, c ∉ Csrc → ∀ y, b i (y,c) = 0) ∧
      (∀ i c, (fun y ↦ b i (y,c)) =ᵐ[volume]
        demodulatedL2Operator (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (P i)
          (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) ∧
      ∃ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) ∧
        ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
          let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ b i (y,q)) c w
          ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
            vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
              Csource l s * A i * K i ^ (s+l-reserve) := by
  classical
  let source := fun i c ↦ vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c
  have hsource i : ContDiff ℝ ∞ (fun q : E × Par ↦ (source i q.2).val q.1) := by
    simpa only [source, vectorOriginalDatumTest_val, originalDatumDerivative, orderedTransferAction] using ha i
  have hsourceS i c : tsupport (source i c).val ⊆ tsupport χout := by
    apply closure_minimal _ (isClosed_tsupport χout)
    intro y hy
    by_contra hn
    exact hy (by simpa only [source, vectorOriginalDatumTest_val,
      originalDatumDerivative, orderedTransferAction] using has i (y,c) hn)
  have hsourceP i c (hc : c ∉ Csrc) : source i c = 0 := by
    apply Subtype.ext
    funext y
    change (source i c).val y = 0
    simpa only [source, vectorOriginalDatumTest_val, originalDatumDerivative, orderedTransferAction] using hap i c hc y
  choose b hb hbs hbe hbz using fun j i ↦
    exists_jointly_smooth_measured_envelope e he
      (EuclideanSpace.finAddEquivProd : Euclidean (3+d) ≃L[ℝ] Par) hS
      χout χin ho hi hob hib (raw i j) (hordinary i j) (source i)
      (hsource i) (hsourceS i) (lam i) (fun z ↦ φ i z.2 z.1)
      ((hφ i).comp (contDiff_snd.prodMk contDiff_fst))
  let one := fun j i c ↦ demodulatedL2Operator (lam i) (φ i c)
    ((hφ i).continuous.comp (continuous_const.prodMk continuous_id))
    (measuredOperator χout χin ho hi hob hib (raw i j)) (graphTestToLp (source i c))
  let total := fun i c ↦ demodulatedL2Operator (lam i) (φ i c)
    ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) (P i)
    (graphTestToLp (source i c))
  have hbe' j i c : (fun y ↦ b j i (y,c)) =ᵐ[volume] one j i c := hbe j i c
  have hone j i : ContDiffOn ℝ ∞ (one j i) V :=
    contDiffOn_l2_of_supported_joint_representative hV hS (b j i) (hb j i) (hbs j i)
      (one j i) (fun c _ ↦ (hbe' j i c).symm)
  have hsum i : (fun c ↦ ∑ j, one j i c) = total i := by
    funext c
    dsimp only [one, total]
    rw [hP i]
    simp only [demodulatedL2Operator, ContinuousLinearMap.comp_apply,
      _root_.sum_apply, map_sum]
  let result := fun i z ↦ ∑ j, b j i z
  have hresult i : ContDiff ℝ ∞ (result i) := ContDiff.sum (fun j _ ↦ hb j i)
  have hresultS i q (hq : q.1 ∉ tsupport χout) : result i q = 0 := by
    exact Finset.sum_eq_zero fun j _ ↦ hbs j i q hq
  have hresultP i c (hc : c ∉ Csrc) (y : E) : result i (y,c) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact congrFun (hbz j i c (hsourceP i c hc)) y
  have hresultE i c : (fun y ↦ result i (y,c)) =ᵐ[volume] total i c := by
    have hbSum := (eventuallyEq_sum fun j (_ : j ∈ (Finset.univ : Finset J)) ↦ hbe' j i c)
    have heSum := Lp.coeFn_finsetSum Finset.univ (fun j ↦ one j i c)
    have he := hbSum.trans heSum.symm
    have hf : (∑ j, fun y ↦ b j i (y,c)) = (fun y ↦ result i (y,c)) := by
      funext y
      simp only [Finset.sum_apply, result]
    rw [hf] at he
    rw [← congrFun (hsum i) c]
    exact he
  have htotal : ∀ ps : List Par, (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
        let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps (total q.1) q.2
        MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
          C * A q.1 * K q.1 ^ (s+ps.length-reserve) := by
    have h := ordered_reserved_bounds_finite_sum hV one hone A K reserve hstep
    simpa only [hsum] using h
  obtain ⟨Csource, hCsource, hprofile⟩ := exists_supported_reserved_source_profile_of_ordered_bounds
    hV hS result hresult hresultS total (fun i c _ ↦ (hresultE i c).symm) A K reserve htotal
  exact ⟨result, hresult, hresultS, hresultP, hresultE, Csource, hCsource, hprofile⟩

end JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles
