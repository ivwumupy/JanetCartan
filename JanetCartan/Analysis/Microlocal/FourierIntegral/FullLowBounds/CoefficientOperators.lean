module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.ShellInputs
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Realization
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.Primitive
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.CompactSupport
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.OperatorLimit
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxScaling

/-!
# Full-amplitude low graph construction

The coefficient-jet step of `app:ch_regular_base:thm:actual-calculus`, Step 1,
converts the actual source Fourier coefficients to the normalized multilinear
budgets required by the source-independent low graph theorem. It preserves the
Frobenius norm, original physical covectors and exact source coefficient decay.
The total reserve is `3 * n + 4` and allows symbol budget zero.

The coefficient graph constant is chosen before the full amplitude and its
budget, for the uniform reserve in the Sobolev derivative expansions.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion LowBounds NormalComparison FrequencyCutoff AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-! The coefficient-level part of Step 1 is kept separate from the source
summation.  The primitive graph theorem is instantiated with the exact source
decay budget and the normalized jet reserve. -/

/-- A finite coefficient bound also bounds every coefficient jet by the
coefficient seminorm. This is the seminorm-valued budget used when the same
operator is consumed by `exists_literalSourceFourierExpansion`, whose bound
interface quantifies over all admissible budgets. -/
theorem hasCoefficientSymbolBound_coefficientSymbolSeminorm
    {a : E → E → Mat} {N : ℕ} {B : ℝ}
    (hb : HasCoefficientSymbolBound a N B) :
    HasCoefficientSymbolBound a N (coefficientSymbolSeminorm a N) := by
  have hB : 0 ≤ B := by
    exact (mul_nonneg (coefficientCovectorWeight_pos [] (0 : E)).le
      (norm_nonneg _)).trans (hb [] (by simp) 0 0)
  intro is hi x η
  apply le_csSup
  · rw [bddAbove_def]
    refine ⟨B, ?_⟩
    intro b hb'
    rcases hb' with rfl | ⟨is', hi', x', η', rfl⟩
    · exact hB
    · exact hb is' hi' x' η'
  · exact Set.mem_insert_of_mem _ ⟨is, hi, x, η, rfl⟩

/-- Construct every source coefficient graph with the same primitive constant.
The coefficient budget is the exact source decay estimate multiplied by the
normalized jet reserve. Source: `app:ch_regular_base:thm:actual-calculus`,
Step 1. -/
theorem exists_coefficientGraphL2_of_fullSourceBound
    (hn : 0 < n) (R M L : ℝ) {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) :
    ∃ C > 0, ∀ {ℓ : ℝ} (_hℓ : 0 < ℓ) (_hRcell : R / ℓ < 1 / 2)
    (A : FullAmplitude n r)
    (_hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {B : ℝ} (_hb : HasFullSourceSymbolBound A
      (primitiveNormalReserve n + lowReserve n) B)
    (S : E → E → ℝ) (hS : Continuous (Function.uncurry S))
    {X D : Set E} {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables n)} {c : ℝ}
    (_hc : 1 ≤ c)
    (_chart : AveragedGradientChart S X D η J δ)
    (_hgeom : ∀ k : Fin n → ℤ,
      PrimitiveNormalGeometry X D S (matrixCoefficient ℓ A k)
        (matrixCoefficient ℓ A k) η J W K)
    (_hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (_hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℕ → Set (NormalVariables n))
    (_hUopen : ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain X D S) l))
    (_hVopen : ∀ l, IsOpen (V l))
    (_hη : ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D S) l))
    (_hmap : ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D S) l) (V l))
    (_hJ : ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables n ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) (V l))
    (_hgap : ∀ l z, z ∈ V l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) J z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ l z, z ∈ V l → ∀ i ≤ primitiveNormalReserve n,
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain X D S) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve n →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) η)) z‖ ≤ L)
    (_hscale : ∀ l z, z ∈ V l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    {Kout : Set E} (hKout : IsCompact Kout)
    (_hsout : ∀ x y ξ, x ∉ Kout → A x y ξ = 0)
    (hscoef : ∀ k x ξ, x ∉ Kout → matrixCoefficient ℓ A k x ξ = 0)
    (_hsdomain : ∀ x y ξ, x ∉ X ∨ ξ ∉ D → A x y ξ = 0)
    (_hforward : ∀ k, ContinuousOn (normalForwardCoordinates S)
      (jointNormalCarrier (matrixCoefficient ℓ A k) (matrixCoefficient ℓ A k))),
    ∀ k : Fin n → ℤ, ∃ T : H →L[ℂ] H,
      ‖T‖ ≤ C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
        coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n)) ∧
      ‖T.adjoint‖ ≤ C * (normalizedCoefficientJetConstant n (primitiveNormalReserve n) c *
        coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n)) ∧
      (∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S
          (fun z _ ξ ↦ matrixCoefficient ℓ A k z ξ)
          (graphTestToSchwartz u) x)) ∧
      (∀ u : SchwartzMap E (Fin r → ℂ), T (schwartzVectorToLp u) =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (graphOperator S
          (fun z _ ξ ↦ matrixCoefficient ℓ A k z ξ) u x)) ∧
      (∀ f : H, Tendsto (fun l ↦ compactVectorGraph hS
        (cutAmplitude_entry_continuous
          (contDiff_matrixCoefficient A hA ℓ k).continuous l)
        (cutAmplitude_entry_hasCompactSupport hKout (hscoef k) l) f) atTop (𝓝 (T f))) ∧
      coefficientSymbolSeminorm (matrixCoefficient ℓ A k) (primitiveNormalReserve n) ≤
        ((r : ℝ)^2 * coefficientConstant n (lowReserve n) ℓ * B *
          decayWeight (lowReserve n) k) := by
  obtain ⟨C₀, hC₀, hlow⟩ := exists_graphL2_of_primitive_inputs
    (n := n) (r := r) hn R M L hδ hF
  refine ⟨C₀, hC₀, ?_⟩
  intro ℓ hℓ hRcell A hs hA B hb S hS X D η J W K c hc chart hgeom hR
    hgrowth V hUopen hVopen hη hmap hJ hgap hJjet hηjet hscale Kout hKout
    _hsout hscoef hsdomain hforward
  have hB : 0 ≤ B := by
    have h := hb [] [] (by simp) (0 : E) (0 : E) (0 : E)
    exact (mul_nonneg (coefficientCovectorWeight_pos [] (0 : E)).le
      (norm_nonneg _)).trans (by simpa [coefficientCovectorWeight] using h)
  intro k
  let b : ℝ := (r : ℝ)^2 * coefficientConstant n (lowReserve n) ℓ * B *
    decayWeight (lowReserve n) k
  let s : ℝ := coefficientSymbolSeminorm (matrixCoefficient ℓ A k)
    (primitiveNormalReserve n)
  let a : ℝ := normalizedCoefficientJetConstant n (primitiveNormalReserve n) c * s
  have hbnonneg : 0 ≤ b := by
    dsimp [b]
    have hfreq : 0 ≤ 1 + frequencyNorm k := by
      linarith [frequencyNorm_nonneg k]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg (r : ℝ))
      (coefficientConstant_pos n (lowReserve n) ℓ).le) hB)
      (inv_nonneg.mpr (pow_nonneg hfreq _))
  have hcoef : HasCoefficientSymbolBound (matrixCoefficient ℓ A k)
      (primitiveNormalReserve n) b :=
    hasCoefficientSymbolBound_matrixCoefficient_lowReserve hn hℓ hRcell A hs hA
      (primitiveNormalReserve n) hb k
  have hcoefS : HasCoefficientSymbolBound (matrixCoefficient ℓ A k)
      (primitiveNormalReserve n) s :=
    hasCoefficientSymbolBound_coefficientSymbolSeminorm hcoef
  have hsnonneg : 0 ≤ s := by
    have h := hcoefS [] (by simp) (0 : E) (0 : E)
    exact (norm_nonneg _).trans (by simpa [coefficientCovectorWeight] using h)
  have hanonneg : 0 ≤ a :=
    mul_nonneg (normalizedCoefficientJetConstant_pos (n := n)
      (primitiveNormalReserve n) hc).le hsnonneg
  have hsem_le : s ≤ b := coefficientSymbolSeminorm_le_of_bound hcoef
  have hshell : ∀ l, PrimitiveNormalShellInputs
      (matrixCoefficient ℓ A k) (matrixCoefficient ℓ A k) η J ((2 : ℝ)^l)
      (primitiveNormalReserve n) M L δ a a
      (normalDyadicShell (bufferedNormalDomain X D S) l) (V l) := by
    intro l
    exact primitiveNormalShellInputs_of_coefficientSymbolBound
      (matrixCoefficient ℓ A k) (contDiff_matrixCoefficient A hA ℓ k) η J hcoefS
      (N := primitiveNormalReserve n) (B := s) (ρ := (2 : ℝ)^l)
      (M := M) (L := L) (δ := δ) (by positivity) hc
      (normalDyadicShell (bufferedNormalDomain X D S) l) (V l)
      (hUopen l)
      (hVopen l) (hη l) (hmap l) (hJ l)
      (fun z hz ↦ hgap l z hz) (fun z hz ↦ hJjet l z hz)
      (fun z hz i hi ↦ hηjet l z hz i hi)
      (fun z hz ↦ hscale l z hz)
  have hAc : Continuous (Function.uncurry (matrixCoefficient ℓ A k)) :=
    (contDiff_matrixCoefficient A hA ℓ k).continuous
  have hsAc : ∀ x ξ, x ∉ Kout → matrixCoefficient ℓ A k x ξ = 0 := by
    exact hscoef k
  have hpoly : ∀ x ξ, ‖matrixCoefficient ℓ A k x ξ‖ ≤
      (2 * s) * (1 + ‖ξ‖ ^ (0 : ℕ)) := by
    intro x ξ
    have h := hcoefS [] (by simp) x ξ
    have hh : ‖matrixCoefficient ℓ A k x ξ‖ ≤ s := by
      change 1 * ‖matrixCoefficient ℓ A k x ξ‖ ≤ s at h
      simpa using h
    simpa using hh.trans (by linarith [hsnonneg])
  have hcarrier : ∀ x u, x ∉ X ∨ u ∉ D → matrixCoefficient ℓ A k x u = 0 := by
    intro x u hx
    exact matrixCoefficient_eq_zero_of_fiber ℓ A k x u
      (fun y ↦ hsdomain x y u hx)
  obtain ⟨T, hT, hTa, htest, hschwartz, hstrong, _hadjoint, _⟩ :=
    hlow X D S (matrixCoefficient ℓ A k) η J W K V a hanonneg chart
      (hgeom k) hR hgrowth hshell hS hAc Kout hKout hsAc
      hcarrier (hforward k) (2 * s) 0 hpoly
  refine ⟨T, ?_, ?_, htest, hschwartz, ?_, hsem_le⟩
  · simpa [a, b, mul_assoc] using hT
  · simpa [a, b, mul_assoc] using hTa
  · intro f
    simpa only [Function.comp_apply] using hstrong f

end JanetCartan.FourierIntegral.FullLowBounds
