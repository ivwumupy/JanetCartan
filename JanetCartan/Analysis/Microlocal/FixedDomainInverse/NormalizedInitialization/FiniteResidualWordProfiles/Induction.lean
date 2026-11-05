module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.FiniteResidualWordProfiles.OneStep

/-!
# Finite powers with one fixed source reserve

Induct on the actual complete measured residual power. Each next source is the
globally smooth representative constructed from the ordinary all-order bounds
and the one-step quantitative estimate, and every step keeps the original
spatial support, parameter support, amplitude, and natural derivative reserve.

This is an independent deduction for `app:ch_regular:lem:finite-chain`.
The universal one-step premise is produced separately by the actual
characteristic, reflected, and full elliptic estimates; this implication does
not assert that producer or the unconditional inverse theorem.
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

variable {d r : ℕ} {I J : Type*} [Fintype J]
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Every finite power of the SAME measured residual has an actual globally
smooth supported amplitude and a uniform Fourier source profile at the
unchanged natural reserve. The quantitative premise is only the single-letter
statement for arbitrary original smooth supported sources, independently
produced by `FiniteResidualEnvelopes` and `FullEllipticApplication`.
No intermediate smoothness, Fourier profile, or depth-dependent coefficient
reserve is assumed (`app:ch_regular:lem:finite-chain`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_actual_residual_power_reserved_source_profiles
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
    (hstep : ∀ (a : I → E × Par → F) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (has : ∀ i q, q.1 ∉ tsupport χout → a i q = 0),
      (∀ i c, c ∉ Csrc → ∀ y, a i (y,c) = 0) →
      ∀ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) →
      (∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Csource l s * A i * K i ^ (s+l-reserve)) →
      ∀ j (ps : List Par), (∀ v ∈ ps, ‖v‖ ≤ 1) → ∀ s : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ q : I × V,
          let value := orderedTransferAction (fun v f c ↦ fderiv ℝ f c v) ps
            (fun c ↦ demodulatedL2Operator (lam q.1) (φ q.1 c)
              ((hφ q.1).continuous.comp (continuous_const.prodMk continuous_id))
              (measuredOperator χout χin ho hi hob hib (raw q.1 j))
              (graphTestToLp (vectorOriginalDatumTest (a q.1) (ha q.1) hS (has q.1) [] c))) q.2
          MemVectorFourierSobolev (s : ℝ) value ∧ vectorFourierSobolevNorm (s : ℝ) value ≤
            C * A q.1 * K q.1 ^ (s+ps.length-reserve))
    (a₀ : I → E × Par → F) (ha₀ : ∀ i, ContDiff ℝ ∞ (a₀ i))
    (has₀ : ∀ i q, q.1 ∉ tsupport χout → a₀ i q = 0)
    (hap₀ : ∀ i c, c ∉ Csrc → ∀ y, a₀ i (y,c) = 0)
    (C₀ : ℕ → ℕ → ℝ) (hC₀ : ∀ l s, 0 ≤ C₀ l s)
    (hfourier₀ : ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a₀ i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ C₀ l s * A i * K i ^ (s+l-reserve)) :
    ∀ N : ℕ, ∃ b : I → E × Par → F, (∀ i, ContDiff ℝ ∞ (b i)) ∧
      (∀ i q, q.1 ∉ tsupport χout → b i q = 0) ∧
      (∀ i c, c ∉ Csrc → ∀ y, b i (y,c) = 0) ∧
      (∀ i c, (fun y ↦ b i (y,c)) =ᵐ[volume]
        demodulatedL2Operator (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) ((P i)^N)
          (graphTestToLp (vectorOriginalDatumTest (a₀ i) (ha₀ i) hS (has₀ i) [] c))) ∧
      ∃ Csource : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Csource l s) ∧
        ∀ i c, c ∈ V → ∀ l (w : Fin l → Par), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
          let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ b i (y,q)) c w
          ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
            vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
              Csource l s * A i * K i ^ (s+l-reserve) := by
  intro N
  induction N with
  | zero =>
    refine ⟨a₀, ha₀, has₀, hap₀, ?_, C₀, hC₀, hfourier₀⟩
    intro i c
    simpa only [pow_zero, demodulatedL2Operator, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, carrierMultiplication_neg_cancel, originalDatumDerivative, orderedTransferAction] using
      (vectorOriginalDatumTest_toLp_ae (a₀ i) (ha₀ i) hS (has₀ i) [] c).symm
  | succ N ih =>
    obtain ⟨a, ha, has, hap, hae, Csource, hCsource, hfourier⟩ := ih
    obtain ⟨b, hb, hbs, hbp, hbe, Cnext, hCnext, hnext⟩ :=
      exists_measured_sum_reserved_source_profile e he hV χout χin ho hi hob hib hS
        raw P hP hordinary lam A K reserve φ hφ a ha has hap
        (hstep a ha has hap Csource hCsource hfourier)
    refine ⟨b, hb, hbs, hbp, ?_, Cnext, hCnext, hnext⟩
    intro i c
    have haClass : graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c) =
        demodulatedL2Operator (lam i) (φ i c)
          ((hφ i).continuous.comp (continuous_const.prodMk continuous_id)) ((P i)^N)
          (graphTestToLp (vectorOriginalDatumTest (a₀ i) (ha₀ i) hS (has₀ i) [] c)) := by
      apply Lp.ext
      have ht : (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c) : E → F)
          =ᵐ[volume] fun y ↦ a i (y,c) := by
        simpa only [originalDatumDerivative, orderedTransferAction] using
          vectorOriginalDatumTest_toLp_ae (a i) (ha i) hS (has i) [] c
      exact ht.trans (hae i c)
    have hcomp : (P i).comp ((P i)^N) = (P i)^(N+1) := (pow_succ' (P i) N).symm
    have hbClass := hbe i c
    rw [haClass, demodulated_comp_apply_same_phase, hcomp] at hbClass
    exact hbClass

end JanetCartan.FixedDomainInverse.FiniteResidualWordProfiles
