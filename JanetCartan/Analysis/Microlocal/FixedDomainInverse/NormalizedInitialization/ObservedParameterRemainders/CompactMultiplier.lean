module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.InactiveDerivatives.FiniteExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles.Leibniz

/-!
# Parameter differentiation of the actual compact-phase multiplier

The negative carrier is the identity plus a compactly supported defect.
Lift that defect through a continuous bilinear multiplication map on the
original vector L² space. This proves norm differentiability before applying
the finite Leibniz rule in `app:ch_regular:eq:inverse-remainder`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ObservedParameterRemainders

open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.ParameterRealization.L2Family
open ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

private def compactCoefficient {X : Set E} [CompactSpace X] (f : C(X, ℂ)) : E → ℂ :=
  Function.extend Subtype.val f 0

private theorem compactCoefficient_mem {X : Set E} [CompactSpace X]
    (f : C(X, ℂ)) {x : E} (hx : x ∈ X) :
    compactCoefficient f x = f ⟨x, hx⟩ :=
  Subtype.coe_injective.extend_apply _ _ ⟨x, hx⟩

private theorem compactCoefficient_notMem {X : Set E} [CompactSpace X]
    (f : C(X, ℂ)) {x : E} (hx : x ∉ X) : compactCoefficient f x = 0 :=
  Function.extend_apply' _ _ _ (by simpa using hx)

private def compactCoefficientMask {X : Set E} (hX : IsCompact X)
    [CompactSpace X] (f : C(X, ℂ)) : InactiveSource.BoundedMask n where
  symbol := compactCoefficient f
  measurable :=
    (MeasurableEmbedding.subtype_coe hX.isClosed.measurableSet).stronglyMeasurable_extend
      f.continuous.stronglyMeasurable stronglyMeasurable_zero
  bound := ‖f‖
  bound_nonneg := norm_nonneg _
  norm_le x := by
    by_cases hx : x ∈ X
    · rw [compactCoefficient_mem f hx]
      exact f.norm_coe_le_norm _
    · rw [compactCoefficient_notMem f hx, norm_zero]
      exact norm_nonneg _

/-- Compact coefficient multiplication is continuous bilinear on the literal
vector L² space. The coefficient norm controls the operator norm, independently
of all source Sobolev orders (`app:ch_regular:eq:inverse-remainder`). -/
private def compactCoefficientAction {X : Set E} (hX : IsCompact X) [CompactSpace X] :
    C(X, ℂ) →L[ℝ] H →L[ℝ] H :=
  LinearMap.mkContinuous₂
    { toFun f :=
        { toFun := (compactCoefficientMask hX f).multiply
          map_add' u v := by
            apply Lp.ext
            filter_upwards [(compactCoefficientMask hX f).multiply_ae (u + v),
              (compactCoefficientMask hX f).multiply_ae u,
              (compactCoefficientMask hX f).multiply_ae v,
              Lp.coeFn_add u v,
              Lp.coeFn_add ((compactCoefficientMask hX f).multiply u)
                ((compactCoefficientMask hX f).multiply v)] with x hu hv hw ha hb
            simp only [hu, hv, hw, ha, hb, Pi.add_apply, smul_add]
          map_smul' a u := by
            apply Lp.ext
            filter_upwards [(compactCoefficientMask hX f).multiply_ae (a • u),
              (compactCoefficientMask hX f).multiply_ae u, Lp.coeFn_smul a u,
              Lp.coeFn_smul a ((compactCoefficientMask hX f).multiply u)] with x h₁ h₂ h₃ h₄
            simp only [h₁, h₂, h₃, h₄, Pi.smul_apply, RingHom.id_apply]
            exact smul_comm _ _ _ }
      map_add' f g := by
        ext1 u
        change (compactCoefficientMask hX (f + g)).multiply u =
          (compactCoefficientMask hX f).multiply u + (compactCoefficientMask hX g).multiply u
        apply Lp.ext
        filter_upwards [(compactCoefficientMask hX (f + g)).multiply_ae u,
          (compactCoefficientMask hX f).multiply_ae u,
          (compactCoefficientMask hX g).multiply_ae u,
          Lp.coeFn_add ((compactCoefficientMask hX f).multiply u)
            ((compactCoefficientMask hX g).multiply u)] with x h₁ h₂ h₃ h₄
        rw [h₁, h₄, Pi.add_apply, h₂, h₃]
        change compactCoefficient (f + g) x • u x =
          compactCoefficient f x • u x + compactCoefficient g x • u x
        by_cases hx : x ∈ X
        · simp [compactCoefficient_mem _ hx, add_smul]
        · simp [compactCoefficient_notMem _ hx]
      map_smul' a f := by
        ext1 u
        change (compactCoefficientMask hX (a • f)).multiply u =
          a • (compactCoefficientMask hX f).multiply u
        apply Lp.ext
        filter_upwards [(compactCoefficientMask hX (a • f)).multiply_ae u,
          (compactCoefficientMask hX f).multiply_ae u,
          Lp.coeFn_smul a ((compactCoefficientMask hX f).multiply u)] with x h₁ h₂ h₃
        rw [h₁, h₃, Pi.smul_apply, h₂]
        change compactCoefficient (a • f) x • u x = a • (compactCoefficient f x • u x)
        by_cases hx : x ∈ X
        · rw [compactCoefficient_mem _ hx, compactCoefficient_mem _ hx]
          exact smul_assoc a (f ⟨x, hx⟩) (u x)
        · simp [compactCoefficient_notMem _ hx] }
    1 (fun f u ↦ by
      change ‖(compactCoefficientMask hX f).multiply u‖ ≤ 1 * ‖f‖ * ‖u‖
      have hb := (compactCoefficientMask hX f).norm_multiply_le u
      change ‖(compactCoefficientMask hX f).multiply u‖ ≤ ‖f‖ * ‖u‖ at hb
      simpa only [one_mul] using hb)

private theorem compactCoefficientAction_ae {X : Set E} (hX : IsCompact X)
    [CompactSpace X] (f : C(X, ℂ)) (u : H) :
    compactCoefficientAction hX f u =ᵐ[volume] fun x ↦ compactCoefficient f x • u x :=
  (compactCoefficientMask hX f).multiply_ae u

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par]

private theorem compactFamily_jet_apply {X : Set E} [CompactSpace X]
    {V : Set Par} (hV : IsOpen V) {g : Par → E → ℂ}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (vs : List Par) {c : Par} (hc : c ∈ V) (x : X) :
    parameterListJet (compactFamily (K := X) g) vs c x =
      parameterListJet (fun a ↦ g a x) vs c := by
  have hd := (ContinuousMap.evalCLM ℝ x (M := ℂ)).iteratedFDeriv_comp_left
    (compactFamily_contDiffAt vs.length hV hg hc) (le_refl (vs.length : ℕ∞ω))
  have he : ((ContinuousMap.evalCLM ℝ x (M := ℂ)) ∘ compactFamily (K := X) g) =ᶠ[𝓝 c]
      (fun a ↦ g a x) := by
    filter_upwards [hV.mem_nhds hc] with a ha
    exact compactFamily_apply hg ha x
  rw [(he.iteratedFDeriv ℝ vs.length).eq_of_nhds] at hd
  exact (congrArg (fun D ↦ D vs.get) hd).symm

private theorem compactFamily_contDiffOn {X : Set E} [CompactSpace X]
    {V : Set Par} (hV : IsOpen V) {g : Par → E → ℂ}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (compactFamily (K := X) g) V := by
  rw [contDiffOn_infty]
  intro k c hc
  exact (compactFamily_contDiffAt k hV hg hc).contDiffWithinAt

private theorem contDiffOn_carrierDefect {V : Set Par}
    {φ : Par → E → ℝ} (ρ : ℝ)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : Par × E ↦ carrier (-ρ) (φ z.1) z.2 - 1)
      (V ×ˢ univ) := by
  unfold carrier
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul hφ))).cexp).sub contDiffOn_const

private theorem demodulationOperators_eq_id_add_compact
    {V : Set Par} (_hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    [CompactSpace X]
    (ρ : ℝ) (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X) {c : Par} (hc : c ∈ V) :
    (carrierMultiplication (-ρ) (φ c) (hφc c) : H →L[ℂ] H).restrictScalars ℝ =
      ContinuousLinearMap.id ℝ H + compactCoefficientAction hX
        (compactFamily (K := X) (fun c x ↦ carrier (-ρ) (φ c) x - 1) c) := by
  let defect := fun c x ↦ carrier (-ρ) (φ c) x - 1
  have hd := contDiffOn_carrierDefect ρ hφ
  ext1 u
  change carrierMultiplication (-ρ) (φ c) (hφc c) u =
    u + compactCoefficientAction hX (compactFamily (K := X) defect c) u
  apply Lp.ext
  filter_upwards [carrierMultiplication_ae (-ρ) (φ c) (hφc c) u,
    compactCoefficientAction_ae hX (compactFamily (K := X) defect c) u,
    Lp.coeFn_add u (compactCoefficientAction hX (compactFamily (K := X) defect c) u)]
    with x h₁ h₂ h₃
  rw [h₁, h₃, Pi.add_apply, h₂]
  by_cases hx : x ∈ X
  · rw [compactCoefficient_mem _ hx, compactFamily_apply (g := defect) hd hc]
    dsimp [defect]
    rw [sub_smul, one_smul]
    abel
  · rw [compactCoefficient_notMem _ hx, zero_smul, add_zero]
    have hzero : φ c x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs c hc h))
    simp [carrier, hzero]

/-- The actual demodulation operators form a smooth family in operator norm.
Only compact support and joint smoothness of the original phase are used;
the output datum has no spatial differentiability assumption
(`app:ch_response:eq:response-graded-reduced`). -/
theorem contDiffOn_demodulationOperators
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (ρ : ℝ) (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X) :
    ContDiffOn ℝ ∞
      (fun c ↦ (carrierMultiplication (-ρ) (φ c) (hφc c) : H →L[ℂ] H).restrictScalars ℝ) V := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  have hh : ContDiffOn ℝ ∞
      (fun c ↦ ContinuousLinearMap.id ℝ H + compactCoefficientAction hX
        (compactFamily (K := X) (fun c x ↦ carrier (-ρ) (φ c) x - 1) c)) V :=
    contDiffOn_const.add ((compactCoefficientAction (r := r) hX).contDiff.comp_contDiffOn
      (compactFamily_contDiffOn hV (contDiffOn_carrierDefect ρ hφ)))
  exact hh.congr fun c hc ↦
    demodulationOperators_eq_id_add_compact hV hX ρ φ hφc hφ hs hc

set_option maxHeartbeats 1200000 in
/-- The parameter jet of the original demodulation operator acts by the
literal parameter jet of its scalar carrier. This is an equality of actual
L² representatives, proved from operator-norm differentiation of the compact
defect (`app:ch_regular:eq:inverse-remainder`). -/
theorem parameterListJet_demodulationOperators_ae
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (ρ : ℝ) (φ : Par → E → ℝ) (hφc : ∀ c, Continuous (φ c))
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (φ c) ⊆ X)
    (vs : List Par) {c : Par} (hc : c ∈ V) (u : H) :
    parameterListJet
      (fun c ↦ (carrierMultiplication (-ρ) (φ c) (hφc c) : H →L[ℂ] H).restrictScalars ℝ)
      vs c u =ᵐ[volume]
        fun x ↦ parameterListJet (fun a ↦ carrier (-ρ) (φ a) x) vs c • u x := by
  classical
  cases vs with
  | nil =>
    simpa only [parameterListJet, List.length_nil, iteratedFDeriv_zero_apply,
      ContinuousLinearMap.coe_restrictScalars'] using
        carrierMultiplication_ae (-ρ) (φ c) (hφc c) u
  | cons v vs =>
    let : CompactSpace X := isCompact_iff_compactSpace.mp hX
    let defect := fun a x ↦ carrier (-ρ) (φ a) x - 1
    have hd := contDiffOn_carrierDefect ρ hφ
    have hdC := compactFamily_contDiffOn (X := X) (g := defect) hV hd
    have he : (fun a ↦
        (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ) =ᶠ[𝓝 c]
        (fun a ↦ ContinuousLinearMap.id ℝ H +
          compactCoefficientAction hX (compactFamily (K := X) defect a)) := by
      filter_upwards [hV.mem_nhds hc] with a ha
      exact demodulationOperators_eq_id_add_compact hV hX ρ φ hφc hφ hs ha
    have hj : parameterListJet
        (fun a ↦ (carrierMultiplication (-ρ) (φ a) (hφc a) : H →L[ℂ] H).restrictScalars ℝ)
        (v :: vs) c = compactCoefficientAction hX
          (parameterListJet (compactFamily (K := X) defect) (v :: vs) c) := by
      unfold parameterListJet
      rw [(he.iteratedFDeriv ℝ (v :: vs).length).eq_of_nhds]
      have hdc := (hdC.contDiffAt (hV.mem_nhds hc)).of_le
        (show ((v :: vs).length : ℕ∞ω) ≤ ∞ by simp)
      have hh := (compactCoefficientAction (r := r) hX).iteratedFDeriv_comp_left hdc
        (le_refl ((v :: vs).length : ℕ∞ω))
      change iteratedFDeriv ℝ (v :: vs).length
        ((fun _ : Par ↦ ContinuousLinearMap.id ℝ H) +
          (compactCoefficientAction (r := r) hX) ∘ compactFamily (K := X) defect) c (v :: vs).get = _
      rw [iteratedFDeriv_add_apply contDiffAt_const
        ((compactCoefficientAction (r := r) hX).contDiff.contDiffAt.comp c hdc)]
      simp only [List.length_cons, iteratedFDeriv_succ_const, Pi.zero_apply, zero_add]
      exact congrArg (fun D ↦ D (v :: vs).get) hh
    rw [hj]
    filter_upwards [compactCoefficientAction_ae hX
      (parameterListJet (compactFamily (K := X) defect) (v :: vs) c) u] with x hx
    rw [hx]
    by_cases hxX : x ∈ X
    · rw [compactCoefficient_mem _ hxX,
        compactFamily_jet_apply (g := defect) hV hd (v :: vs) hc]
      congr 1
      have hcarrier : ContDiffAt ℝ ∞ (fun a ↦ carrier (-ρ) (φ a) x) c := by
        have hp : ContDiffAt ℝ ∞ (fun a ↦ φ a x) c :=
          (hφ.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)).comp c
            (contDiffAt_id.prodMk contDiffAt_const)
        unfold carrier
        exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp c
          (contDiffAt_const.mul hp))).cexp
      unfold parameterListJet
      change iteratedFDeriv ℝ (vs.length + 1)
        ((fun a ↦ carrier (-ρ) (φ a) x) - fun _ ↦ (1 : ℂ)) c (v :: vs).get = _
      rw [iteratedFDeriv_sub_apply (hcarrier.of_le (by simp)) contDiffAt_const]
      simp [iteratedFDeriv_succ_const]
    · rw [compactCoefficient_notMem _ hxX]
      have hconstant : (fun a ↦ carrier (-ρ) (φ a) x) =ᶠ[𝓝 c] (fun _ ↦ (1 : ℂ)) := by
        filter_upwards [hV.mem_nhds hc] with a ha
        have hz : φ a x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxX (hs a ha h))
        simp [carrier, hz]
      unfold parameterListJet
      rw [(hconstant.iteratedFDeriv ℝ (v :: vs).length).eq_of_nhds]
      simp [iteratedFDeriv_succ_const]

end JanetCartan.FixedDomainInverse.ObservedParameterRemainders
