module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.CompactMultiplier

/-!
# The literal finite Leibniz formula for observed inverse remainders

The same fixed source-to-output operator commutes with every parameter
derivative. Only the demodulation operator varies. Its coefficients are the
original finite carrier polynomials, and its actual L² derivatives have
already been constructed by compact multiplication. Consumer:
`app:ch_regular:eq:inverse-remainder` and the differentiated finite Neumann
identity in `app:ch_regular:eq:finite-neumann-identity`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ObservedParameterRemainders

open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The original demodulation and SAME fixed observation have this exact
finite parameter expansion. The source jets are actual Fréchet derivatives;
the inverse depth is unchanged when it is included in the source family
(`app:ch_regular:eq:finite-neumann-identity`). -/
theorem iteratedFDeriv_demodulated_fixed_operator_eq_leibniz
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (ρ : ℝ) (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (S : Z →L[ℝ] H) (u : Par → Z) (hu : ContDiffOn ℝ ∞ u V)
    (k : ℕ) (v : Fin k → Par) {c : Par} (hc : c ∈ V) :
    iteratedFDeriv ℝ k
      (fun a ↦ carrierMultiplication (-ρ) (φ a) (hφc a) (S (u a))) c v =
      ((parameterLeibnizSplittings (List.ofFn v)).map (fun t ↦
        parameterListJet
          (fun a ↦ (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ)
          t.1 c (S (parameterListJet u t.2 c)))).sum := by
  let D := fun a ↦
    (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ
  have hD : ContDiffOn ℝ ∞ D V :=
    contDiffOn_demodulationOperators hV hX ρ φ hφc hφ hs
  have hSu : ContDiffOn ℝ ∞ (fun a ↦ S (u a)) V := S.contDiff.comp_contDiffOn hu
  have he := parameterListJet_bilinear (ContinuousLinearMap.id ℝ (H →L[ℝ] H))
    D (fun a ↦ S (u a)) hV hD hSu (List.ofFn v) hc
  rw [parameterListJet_ofFn] at he
  simp only [ContinuousLinearMap.id_apply] at he
  change iteratedFDeriv ℝ k (fun a ↦ D a (S (u a))) c v = _
  rw [he]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  have hj := S.iteratedFDeriv_comp_left
    ((hu.contDiffAt (hV.mem_nhds hc)).of_le
      (show (t.2.length : ℕ∞ω) ≤ ∞ by simp)) (le_refl (t.2.length : ℕ∞ω))
  exact congrArg (fun h : H ↦ (parameterListJet D t.1 c : H →L[ℝ] H) h)
    (congrArg (fun M ↦ M t.2.get) hj)

/-- Each operator coefficient in the finite observation expansion is the
original carrier polynomial from `parameterCarrierJet_eq_leibnizPolynomial`.
The actual negative carrier and both complex quadratures are retained
(`app:ch_response:eq:response-graded-reduced`). -/
theorem parameterListJet_demodulationOperators_eq_carrierPolynomial_ae
    {p : ℕ} {V : Set (Euclidean p)} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (ρ : ℝ) (φ : Euclidean p → E → ℝ) (hφc : ∀ c, Continuous (φ c))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (vs : List (Euclidean p)) {c : Euclidean p} (hc : c ∈ V) (u : H) :
    parameterListJet
      (fun a ↦ (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ)
      vs c u =ᵐ[volume] fun x ↦
        carrier (-ρ) (φ c) x •
          ((∑ b : CarrierJetBranch vs.length,
            ((-ρ : ℝ) : ℂ) ^ carrierJetDegree b * sourcePhaseCoefficient φ vs b c x) • u x) := by
  filter_upwards [parameterListJet_demodulationOperators_ae hV hX ρ φ hφc hφ hs vs hc u]
    with x hx
  have hp : ContDiffOn ℝ ∞ (fun a ↦ φ a x) V :=
    hφ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun a ha ↦ ⟨ha, mem_univ x⟩)
  rw [hx, parameterListJet_carrier_eq_polynomial (φ := φ) hV (-ρ) x hp vs hc,
    mul_smul]

end JanetCartan.FixedDomainInverse.ObservedParameterRemainders
