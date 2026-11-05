module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.LocalIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Differentiating the literal compact-frequency graph

The compact-frequency step of the parameter-complement paragraph in
`app:ch_response:thm:response-literal-transfer`. Primitive joint smoothness,
the original fixed compact amplitude support, and finite-dimensional parameters
give integrability, domination and differentiation of the original graph. The
finite Leibniz expansion and passage to the unregularized L² realization are
separate consumers of the resulting actual `iteratedFDeriv` identity.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

open FourierIntegral

variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n

variable (O : Euclidean n → Euclidean n → Euclidean n → ℂ) (A : FullAmplitude n r)
  (q : Euclidean n → ℂ) (ζ : P → Euclidean n) (ψ : P → Euclidean n → Euclidean n → ℝ) (ρ : ℝ)
  (u : P → Euclidean n → Fin r → ℂ) (x : Euclidean n) {U : Set P}

/-- Primitive joint smoothness gives smoothness of the entire original
integrand, including parameter dependence of the source and moving selector.
No differentiability of a graph output is assumed
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_parameterGraphIntegrand (hU : IsOpen U)
    (hO : ContDiff ℝ ∞ (fun z : E × E ↦ O x z.2 z.1))
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z : E × E ↦ A x z.2 z.1 i j))
    (hq : ContDiff ℝ ∞ q) (hζ : ContDiffOn ℝ ∞ ζ U)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × E ↦ ψ p.1 x p.2) (U ×ˢ univ))
    (hu : ∀ i, ContDiffOn ℝ ∞ (fun p : P × E ↦ u p.1 p.2 i) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦
      parameterGraphIntegrand O A q ζ ψ ρ u p.1 x p.2.2 p.2.1) (U ×ˢ univ) := by
  intro p hp
  have hz : ContDiffAt ℝ ∞ (fun a : P × (E × E) ↦ ζ a.1) p :=
    (hζ.contDiffAt (hU.mem_nhds hp.1)).comp p contDiffAt_fst
  have ho : ContDiffAt ℝ ∞ (fun a : P × (E × E) ↦
      normalizedCarrierOffset ζ ρ a.2.1 a.1) p := by
    unfold normalizedCarrierOffset
    exact (contDiffAt_snd.fst.sub (hz.const_smul ρ)).const_smul ρ⁻¹
  have hp' : (p.1, p.2.2) ∈ U ×ˢ (univ : Set E) := ⟨hp.1, mem_univ _⟩
  have hs : ContDiffAt ℝ ∞ (fun a : P × (E × E) ↦ ψ a.1 x a.2.2) p :=
    (hψ.contDiffAt ((hU.prod isOpen_univ).mem_nhds hp')).comp p
      (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  have he : ContDiffAt ℝ ∞ (fun a : P × (E × E) ↦
      parameterCarrierFactor ψ ρ a.1 x a.2.2) p := by
    unfold parameterCarrierFactor
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp p (hs.const_smul ρ)).const_smul
      Complex.I).cexp
  have hc : ContDiffAt ℝ ∞ (fun a : P × (E × E) ↦
      complementaryCarrierCoefficient q ζ ψ ρ a.1 x a.2.2 a.2.1) p :=
    he.mul (contDiffAt_const.sub (hq.contDiffAt.comp p ho))
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ ∞ (fun a : P × (E × E) ↦
    O x a.2.2 a.2.1 * (complementaryCarrierCoefficient q ζ ψ ρ a.1 x a.2.2 a.2.1 *
      ∑ j, A x a.2.2 a.2.1 i j * u a.1 a.2.2 j)) p
  apply (hO.contDiffAt.comp p contDiffAt_snd).mul
  apply hc.mul
  apply ContDiffAt.sum
  intro j _
  exact ((hA i j).contDiffAt.comp p contDiffAt_snd).mul
    (((hu j).contDiffAt ((hU.prod isOpen_univ).mem_nhds hp')).comp p
      (contDiffAt_fst.prodMk contDiffAt_snd.snd))

variable {K : Set (Euclidean n × Euclidean n)}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The unchanged amplitude support supplies a common compact support for
the entire parameter integrand. The source is not projected or truncated
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegrand_eq_zero_off_support
    (hA : ∀ z ∉ K, A x z.2 z.1 = 0) (c : P) (z : E × E) (hz : z ∉ K) :
    parameterGraphIntegrand O A q ζ ψ ρ u c x z.2 z.1 = 0 := by
  simp [parameterGraphIntegrand, hA z hz]

/-- Fubini identifies the original iterated graph with its compact joint
integral. Joint smoothness here is supplied by
`contDiffOn_parameterGraphIntegrand`, rather than an integral identity input
(`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterGraphIntegral_eq_jointIntegral (hU : IsOpen U)
    (hJ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦
      parameterGraphIntegrand O A q ζ ψ ρ u p.1 x p.2.2 p.2.1) (U ×ˢ univ))
    (hK : IsCompact K) (hs : ∀ z ∉ K, A x z.2 z.1 = 0)
    {c : P} (hc : c ∈ U) :
    parameterGraphIntegral O A q ζ ψ ρ u c x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z : E × E,
        parameterGraphIntegrand O A q ζ ψ ρ u c x z.2 z.1 := by
  have hi0 := integrable_parameterJet_of_compactSupport (μ := volume) hU hJ hK
    (fun b _ z hz ↦
      parameterGraphIntegrand_eq_zero_off_support O A q ζ ψ ρ u x hs b z hz) 0 hc
  have hi : Integrable (fun z : E × E ↦
      parameterGraphIntegrand O A q ζ ψ ρ u c x z.2 z.1) := by
    simpa only [ContinuousMultilinearMap.apply_apply, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ P) (Fin r → ℂ)
        (fun i ↦ Fin.elim0 i)).integrable_comp hi0
  exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·) (integral_integral hi)

variable [FiniteDimensional ℝ P]

/-- The same original graph is smooth on the parameter neighborhood. The
integrand regularity premise has the primitive producer
`contDiffOn_parameterGraphIntegrand`. This is used by the L² derivative
construction (`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_parameterGraphIntegral (hU : IsOpen U)
    (hJ : ContDiffOn ℝ ∞ (fun p : P × (E × E) ↦
      parameterGraphIntegrand O A q ζ ψ ρ u p.1 x p.2.2 p.2.1) (U ×ˢ univ))
    (hK : IsCompact K) (hs : ∀ z ∉ K, A x z.2 z.1 = 0) :
    ContDiffOn ℝ ∞ (fun b ↦ parameterGraphIntegral O A q ζ ψ ρ u b x) U := by
  have hJs := fun b (_ : b ∈ U) z (hz : z ∉ K) ↦
    parameterGraphIntegrand_eq_zero_off_support O A q ζ ψ ρ u x hs b z hz
  apply ((contDiffOn_integral_parameterCompactSupport (μ := volume) hU hJ hK hJs).const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹)).congr
  intro b hb
  exact parameterGraphIntegral_eq_jointIntegral O A q ζ ψ ρ u x hU hJ hK hs hb

/-- Actual parameter derivatives of the original normalized iterated graph
integral. The right side integrates the actual integrand jets; its finite
Leibniz expansion is supplied separately. Primitive regularity is produced
by the fixed phase/amplitude/cutoff data and the original source family.
This theorem assumes neither graph differentiability nor a derivative formula.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem iteratedFDeriv_parameterGraphIntegral (hU : IsOpen U)
    (hO : ContDiff ℝ ∞ (fun z : E × E ↦ O x z.2 z.1))
    (hA : ∀ i j, ContDiff ℝ ∞ (fun z : E × E ↦ A x z.2 z.1 i j))
    (hq : ContDiff ℝ ∞ q) (hζ : ContDiffOn ℝ ∞ ζ U)
    (hψ : ContDiffOn ℝ ∞ (fun p : P × E ↦ ψ p.1 x p.2) (U ×ˢ univ))
    (hu : ∀ i, ContDiffOn ℝ ∞ (fun p : P × E ↦ u p.1 p.2 i) (U ×ˢ univ))
    (hK : IsCompact K) (hs : ∀ z ∉ K, A x z.2 z.1 = 0)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ U) :
    iteratedFDeriv ℝ k (fun b ↦ parameterGraphIntegral O A q ζ ψ ρ u b x) c v =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z : E × E,
        iteratedFDeriv ℝ k
          (fun b ↦ parameterGraphIntegrand O A q ζ ψ ρ u b x z.2 z.1) c v := by
  let J : P × (E × E) → (Fin r → ℂ) := fun p ↦
    parameterGraphIntegrand O A q ζ ψ ρ u p.1 x p.2.2 p.2.1
  have hJ : ContDiffOn ℝ ∞ J (U ×ˢ univ) :=
    contDiffOn_parameterGraphIntegrand O A q ζ ψ ρ u x hU hO hA hq hζ hψ hu
  have hJs : ∀ b ∈ U, ∀ z ∉ K, J (b, z) = 0 := fun b _ z hz ↦
    parameterGraphIntegrand_eq_zero_off_support O A q ζ ψ ρ u x hs b z hz
  have hi (b : P) (hb : b ∈ U) : Integrable (fun z ↦ J (b, z)) := by
    have hi0 := integrable_parameterJet_of_compactSupport
      (μ := volume) hU hJ hK hJs 0 hb
    simpa only [ContinuousMultilinearMap.apply_apply, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ P) (Fin r → ℂ)
        (fun i ↦ Fin.elim0 i)).integrable_comp hi0
  have he : (fun b ↦ parameterGraphIntegral O A q ζ ψ ρ u b x) =ᶠ[𝓝 c]
      (fun b ↦ ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z, J (b, z)) := by
    filter_upwards [hU.mem_nhds hc] with b hb
    exact congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·) (integral_integral (hi b hb))
  have hG := contDiffOn_integral_parameterCompactSupport (μ := volume) hU hJ hK hJs
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' ((hG.contDiffAt (hU.mem_nhds hc)).of_le (by simp))]
  change ((2 * Real.pi) ^ n : ℂ)⁻¹ •
    (iteratedFDeriv ℝ k (fun b ↦ ∫ z, J (b, z)) c v) = _
  rw [iteratedFDeriv_integral_parameterCompactSupport hU hJ hK hJs k hc,
    ContinuousMultilinearMap.integral_apply
      (integrable_parameterJet_of_compactSupport (μ := volume) hU hJ hK hJs k hc)]

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
