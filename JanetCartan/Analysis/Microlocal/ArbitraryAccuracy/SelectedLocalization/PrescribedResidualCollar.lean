module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedPhaseGaps
public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.ResidualCarriers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Phase

/-!
# A supported primitive Fourier collar for the selected residual

Use the even mask witnesses themselves and the original conic gaps on
their canonical shoulders. Beyond the protected physical elapsed interval
the graph-clock derivative separates the same literal kernel. On the
supported carrier the smooth phase constructed for the Fourier estimate
has the original conic germs. Its primitive profile at order zero supplies
a fixed upper bound. Strictly opening the two gradient inequalities now
gives the domains of the primitive half-space estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open SelectedEvenProofMasks
open RegularSector.Characteristic RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization
open ProtectedMasks SelectedSectorProtection
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x₀ : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E
local notation "Z" => RootState (Euclidean d)
local notation "T" => TwoTimePoint (Euclidean d)

/-- Construct the open tangential/interior collars for the exact masks
returned with terminal protection. The raw geometric short-time gaps, retained
phase germ and primitive phase grades supply every input; the late clock and
compact-carrier bound produce the full supported collar estimate. Constants
precede phases, masks and histories. Consumer:
`exists_directResidual_integral_fourier_bound_of_primitive_grades`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:joint-kernel-phase`). -/
theorem exists_prescribed_selected_residual_collar_domains
    (f : ActualMaskFamily Ω x₀ RQ A₀ K M) (j : f.centers)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eT : Module.Basis ι ℝ (JointVariables E)) (eI : Module.Basis κ ℝ V)
    (output : E → ℝ) (aPhase bPhase θ a b Rbase εcollar δT δI : ℝ)
    (hε : 0 < εcollar) (hT : 0 < δT) (hI : 0 < δI)
    (χ : V → ℂ) (Hcollar : ℕ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hone : ∀ v : V, |v.1| ≤ εcollar / 4 → χ v = 1)
    (hsupp : tsupport χ ⊆ {v : V | |v.1| ≤ εcollar / 2})
    (hχder : ∀ l v, ‖iteratedFDeriv ℝ l χ v‖ ≤ Hcollar l)
    (ψ : E → ℝ) (hψ : HasCompactSupport ψ)
    (threshold c C : ℝ) (ht : f.radialThreshold ≤ threshold)
    (hout : tsupport output ⊆ ball x₀ f.physicalRadius) (Θ : ℝ → ℂ)
    (ra rb : ℝ) {tlo thi : ℝ} (hlo : 0 < tlo) (hra : 0 < ra)
    (hleft : aPhase ≤ ra / thi) (hright : ra / tlo ≤ bPhase)
    (hK : IsCompact (selectedRetainedResidualCarrier f j output threshold c C a b Θ
      ra rb tlo thi))
    (P₀ : ℕ → ℝ) (hP₀ : ∀ l, 0 ≤ P₀ l) :
    let Kjet := selectedRetainedResidualCarrier f j output threshold c C a b Θ
      ra rb tlo thi
    ∃ δT' δI' G : ℝ, 0 < δT' ∧ 0 < δI' ∧
      ∀ (Cphase : OpenPartialHomeomorph T T) (Gext : T → ℝ),
      ContDiffOn ℝ ∞ Gext {q | q.2.2.2 ≠ 0} →
      (∀ q ∈ ConicPhase.domain (f.chart j).radialSection
        (closedBall ((coordinateSplit (f.chart j).index x₀).1,
          ((coordinateSplit (f.chart j).index x₀).1,
            ((coordinateSplit (f.chart j).index x₀).2,
              (coordinateSplit (f.chart j).index j.val.val).2)))
          (2*(f.chart j).maskRadius)),
        Gext =ᶠ[𝓝 q] ConicPhase.phase (f.chart j).radialSection Cphase) →
      ∀ mi mo : LocalizerSymbol (d+1),
      (∀ (o : Bool) (ρ : ℝ), 0 < ρ → ∀ (x y : E) (r' : ℝ) (p : JointVariables E),
        r' ∈ Icc 0 (6*f.physicalRadius) → r' ≤ (f.chart j).maskRadius →
        p.1.1 0 ∈ closedBall (coordinateSplit (f.chart j).index x₀).1 ((f.chart j).maskRadius/2) →
        spatialPart p.1.1 ∈ closedBall (coordinateSplit (f.chart j).index x₀).2 ((f.chart j).maskRadius/2) →
        spatialPart p.2.1 ∈ ConicPhase.radialSectionBand (f.chart j).radialSection
          (coordinateSplit (f.chart j).index j.val.val).2 ((f.chart j).maskRadius/2) aPhase bPhase →
        (y,p.2.2.1) ∈ cthickening (θ/2) (tsupport mi) →
        (x,p.2.2.2) ∈ tsupport (fun q ↦ 1-mo q) →
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ
              (curriedPhase (f.chart j).radialSection Cphase)) x y) (r',p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ
              (curriedPhase (f.chart j).radialSection Cphase)) x y (r',w)) p)) ∧
        (δI ≤ phaseGradientSquare eI (jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ Gext (t,s,u,η))) x y) (r',p) ∧
          (r' ≤ εcollar → δT ≤ phaseGradientSquare eT (fun w ↦ jointElapsedPhase o
            (SymbolBudgets.normalizedTwoTimePhase ρ (fun t s u η ↦ Gext (t,s,u,η))) x y (r',w)) p))) →
      Prod.fst '' tsupport mi ⊆ closedBall (0 : E) Rbase →
      ∀ (ρ L : ℝ), 1 ≤ ρ → 1 ≤ L → ∀ Ψ : TwoTimePhase d,
      ContDiff ℝ ∞ (SymbolBudgets.jointPhase Ψ) →
      let Ψn := SymbolBudgets.normalizedTwoTimePhase ρ Ψ
      (∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi, ∀ v ∈ elapsedOutputJetCarrier Kjet mi mo x y,
        0 ≤ v.1 → SymbolBudgets.jointPhase Ψn =ᶠ[𝓝 (elapsedJointCoordinates v)]
          SymbolBudgets.jointPhase (curriedPhase (f.chart j).radialSection Cphase)) →
      (∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi, ∀ v ∈ elapsedOutputJetCarrier Kjet mi mo x y,
        ∀ l, ‖iteratedFDeriv ℝ l (fderiv ℝ (SymbolBudgets.jointPhase Ψn))
          (elapsedJointCoordinates v)‖ ≤ P₀ l * L ^ l) →
      ∃ UT UI : Bool → E → E → Set V,
        0 < εcollar/4 ∧ ContDiff ℝ ∞ χ ∧ (∀ v, |v.1| < εcollar/4 → χ v = 1) ∧
        ∀ backward, ∀ x ∈ tsupport ψ, ∀ y ∈ Prod.fst '' tsupport mi,
          let F := jointElapsedPhase backward Ψn x y
          let Kxy := elapsedOutputJetCarrier Kjet mi mo x y
          IsOpen (UT backward x y) ∧ IsOpen (UI backward x y) ∧
          Kxy ∩ tsupport χ ⊆ UT backward x y ∧
          (Kxy ∩ tsupport (1-χ)) ∩ {v | 0 < v.1} ⊆ UI backward x y ∧
          (∀ r, 0 ≤ r → ∀ w, (r,w) ∈ UT backward x y →
            δT' ≤ phaseGradientSquare eT (fun w ↦ F (r,w)) w ∧ ‖fderiv ℝ F (r,w)‖ ≤ G) ∧
          (∀ v ∈ UI backward x y ∩ {v | 0 < v.1},
            δI' ≤ phaseGradientSquare eI F v ∧ ‖fderiv ℝ F v‖ ≤ G) ∧
          (∀ v ∈ Kxy, ∀ l, ‖iteratedFDeriv ℝ l χ v‖ ≤ Hcollar l) := by
  intro Kjet
  obtain ⟨δt, δi, hδt, hδi, hret⟩ := exists_prescribed_retained_phase_gaps
    f j eT eI output aPhase bPhase θ a b εcollar δT δI hT hI
    threshold c C ht hout Θ ra rb hlo hra hleft hright
  let dT := δt / 2
  let dI := δi / 2
  obtain ⟨P, _, hP⟩ := ResidualLocalization.exists_residual_joint_phase_profile
    hψ (isCompact_closedBall (0 : E) Rbase) hK P₀ hP₀
  let G := P 0 + 1
  refine ⟨dT, dI, G, half_pos hδt, half_pos hδi, ?_⟩
  intro Cphase Gext hG hgermExt mi mo hshort hbase ρ L hρ hL Ψ hΨ Ψn hgerm hgrade
  let F := fun backward x y ↦ jointElapsedPhase backward Ψn x y
  have hΨn := contDiff_normalizedTwoTimePhase_joint ρ Ψ hΨ
  have hF backward x y := contDiff_jointElapsedPhase backward Ψn x y hΨn
  let ST := fun (o : Bool) (x y : E) (v : V) ↦ phaseGradientSquare eT (fun w ↦ F o x y (v.1,w)) v.2
  let SI := fun (o : Bool) (x y : E) (v : V) ↦ phaseGradientSquare eI (F o x y) v
  let B := fun (o : Bool) (x y : E) ↦ {v | ‖fderiv ℝ (F o x y) v‖ < G}
  let UT := fun o x y ↦ {v : V | v.1 < 0} ∪ ({v | dT < ST o x y v} ∩ B o x y)
  let UI := fun o x y ↦ {v | dI < SI o x y v} ∩ B o x y
  refine ⟨UT, UI, by positivity, hχ, fun v hv ↦ hone v hv.le, ?_⟩
  intro o x hx y hy Fxy Kxy
  have hdf := (hF o x y).continuous_fderiv (by simp)
  have hdt : ContDiff ℝ ∞ (fun v : V ↦ fderiv ℝ (fun w ↦ Fxy (v.1,w)) v.2) := by
    apply ContDiff.fderiv (m := ∞) (g := Prod.snd) _ contDiff_snd (by simp)
    exact (hF o x y).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hTcont : Continuous (ST o x y) := continuous_finsetSum _ fun i _ ↦
    (hdt.continuous.clm_apply (continuous_const (y := eT i))).pow 2
  have hIcont : Continuous (SI o x y) := continuous_finsetSum _ fun i _ ↦
    (hdf.clm_apply (continuous_const (y := eI i))).pow 2
  have hB : IsOpen (B o x y) := isOpen_lt hdf.norm continuous_const
  have hY : y ∈ closedBall (0 : E) Rbase := hbase hy
  have hub (v : V) (hv : v ∈ Kxy) : v ∈ B o x y := by
    have hg := hP L hL Ψn hΨn o x hx y hY v hv.1 (hgrade x hx y hy v hv) 0
    apply lt_of_le_of_lt _ (lt_add_one (P 0))
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hg
  have hlocal (v : V) (hv : v ∈ Kxy) (hr : 0 ≤ v.1) :
      dI < SI o x y v ∧ (v.1 ≤ εcollar → dT < ST o x y v) := by
    have hg := (hret Cphase Gext hG hgermExt mi mo hshort o ρ (zero_lt_one.trans_le hρ) x y v hv hr).1
    let Ψ₀ := curriedPhase (f.chart j).radialSection Cphase
    have hn : SymbolBudgets.normalizedTwoTimePhase ρ Ψ₀ = Ψ₀ :=
      normalizedTwoTimePhase_curriedExtend _ _ (zero_lt_one.trans_le hρ)
    dsimp only at hg
    rw [show SymbolBudgets.normalizedTwoTimePhase ρ
      (curriedPhase (f.chart j).radialSection Cphase) = Ψ₀ from hn] at hg
    have he := hgerm x hx y hy v hv hr
    have heI := (jointElapsedPhase_eventuallyEq_of_twoTimePhase o Ψ₀ Ψn x y v he).fderiv_eq (𝕜 := ℝ)
    have heT := fderiv_jointElapsedPhase_slice_eq_of_twoTimePhase_germ o Ψ₀ Ψn x y v.1 v.2 he
    dsimp only [SI, ST, F]
    simp only [phaseGradientSquare, heI, heT]
    exact ⟨(half_lt_self hδi).trans_le hg.1, fun h ↦ (half_lt_self hδt).trans_le (hg.2 h)⟩
  refine ⟨(isOpen_lt continuous_fst continuous_const).union
    ((isOpen_lt continuous_const hTcont).inter hB), (isOpen_lt continuous_const hIcont).inter hB,
    ?_, ?_, ?_, ?_, fun v _ l ↦ hχder l v⟩
  · rintro v ⟨hv, hχv⟩
    rcases lt_or_ge v.1 0 with hn | hp
    · exact Or.inl hn
    · have ht := hsupp hχv
      change |v.1| ≤ εcollar/2 at ht
      exact Or.inr ⟨(hlocal v hv hp).2 (by linarith [le_abs_self v.1]), hub v hv⟩
  · rintro v ⟨⟨hv, _⟩, hp⟩
    exact ⟨(hlocal v hv hp.le).1, hub v hv⟩
  · intro r hr w hw
    rcases hw with hn | ⟨hg, hb⟩
    · exact False.elim ((not_lt_of_ge hr) hn)
    · exact ⟨hg.le, hb.le⟩
  · exact fun v hv ↦ ⟨hv.1.1.le, hv.1.2.le⟩

end JanetCartan.ArbitraryAccuracy.SelectedLocalization

