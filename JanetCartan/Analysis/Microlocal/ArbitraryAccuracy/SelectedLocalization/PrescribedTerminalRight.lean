module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrescribedLocalizers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.UniformIdentity
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Ordinary
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization.Sobolev
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.LocalizerAdjoint
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.WholeSpaceRestriction

/-!
# Terminal localization of the supplied masks

The input and intermediate proof masks come with the fixed terminal plateau.
Their primitive geometry yields the right-to-right defect, followed by the
literal whole-space restriction used in the complete mixed chain.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential FiniteChain.Graph
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic
open SelectedEvenProofMasks RegularSector.Characteristic.EvolutionIntegral
open ResidualLocalization ResidualLocalization.IdentityDefect
open LocalSobolev RegularSector.Characteristic.RetardedLocalization
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The supplied input and intermediate masks localize into the prescribed
terminal right mask. All support, jet, range and plateau data are the literal
outputs of terminal protection; constants precede the varying masks. Consumer:
the final defect in the complete mixed chain (`app:ch_regular:lem:finite-chain`). -/
theorem exists_prescribed_terminal_right_leakage_constants
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {buffer : ℝ} (hbuffer : 0 < buffer) (order : ℕ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ mi mb : LocalizerSymbol (d+1),
      ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mb → HasCompactSupport mb →
      (∀ p, mb p ∈ Icc (0 : ℝ) 1) →
      tsupport mi ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      tsupport mb ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Hmask k) →
      (∀ k p, ‖iteratedFDeriv ℝ k mb p‖ ≤ Hmask k) →
      (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {z | mb z = 1}) →
      (∀ p ∈ tsupport mb, closedBall p buffer ⊆ interior {z | mt z = 1}) →
      ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ Ri Lbridge Mt : H →L[ℂ] H,
      (∀ u, Ri u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lbridge u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ mb (fun z ↦ (u z).ofLp) y)) →
      (∀ u, Mt u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mt (fun z ↦ (u z).ofLp) y)) →
      ∀ q u, MemVectorFourierSobolev (order : ℝ) ((1-Mt) (Ri u)) ∧
        vectorFourierSobolevNorm (order : ℝ) ((1-Mt) (Ri u)) ≤
          C q * ρ^(2*(d+1)+order) * L^(order+(d+1+1)) * (L/ρ)^q * ‖u‖ := by
  choose Dt hDt hjt using fun j ↦ htc.exists_bound_iteratedFDeriv ht j
  obtain ⟨I0, hI0, hid0⟩ := exists_identityLeakage_fourierSobolev_bound_of_uniform_profiles
    (n := d+1) (r := d+1) b Hmask Hmask hHmask hHmask hbuffer 0
  obtain ⟨Im, hIm, hidm⟩ := exists_identityLeakage_fourierSobolev_bound_of_uniform_profiles
    (n := d+1) (r := d+1) b Hmask Hmask hHmask hHmask hbuffer order
  obtain ⟨Xt, hXt, hcross⟩ := FiniteChains.CrossQuantization.exists_crossQuantization_sobolev_bound
    (r := d+1) (closedBall (0 : E) Rbase) (isCompact_closedBall _ _)
    Hmask Dt hHmask hDt 0 0 hbuffer (le_max_left 0 b) order
  obtain ⟨Tcost, hTcost, htcost⟩ := exists_leftLocalizer_adjoint_sobolev_bound
    (r := d+1) mt ht htc order
  obtain ⟨C0, hC0, hlow⟩ := exists_prescribed_localizer_low_constant b Rbase Hmask hHmask
  refine ⟨fun q ↦ Im q + Tcost*I0 q + Xt q*C0,
    fun q ↦ add_nonneg (add_nonneg (hIm q) (mul_nonneg hTcost (hI0 q)))
      (mul_nonneg (hXt q) hC0), ?_⟩
  intro mi mb hmi hmic hmb hmbc hmbr hsuppI hsuppB hjetI hjetB hid hterminal
    ρ L hL hLρ Ri Lbridge Mt hRi hLb hMt q u
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hρ0 : 0 ≤ ρ := hρpos.le
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hratio : 0 ≤ L/ρ := div_nonneg hL0 hρ0
  have hfreq : Prod.snd '' tsupport mi ⊆ closedBall (0 : E) b := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hsuppI hp).2
  have hbase : Prod.fst '' tsupport mb ⊆ closedBall (0 : E) Rbase := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hsuppB hp).1
  have hann : ∀ p ∈ tsupport mb, ‖p.2‖ ≤ max 0 b := by
    intro p hp
    have h := (hsuppB hp).2
    simp only [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_right _ _)
  have hcrossPlateau : ∀ p ∈ tsupport mb, ∀ z : E × E,
      dist z p ≤ buffer → mt z = 1 := by
    intro p hp z hz
    exact interior_subset (s := {z | mt z = 1}) (hterminal p hp hz)
  have hbridgeJets (l : ℕ) (p : E × E) :
      ‖iteratedFDeriv ℝ l mb p‖ ≤ Hmask l*L^(l+0) :=
    (hjetB l p).trans (le_mul_of_one_le_right (hHmask l) (one_le_pow₀ hL))
  have htJets (l : ℕ) (p : E × E) : ‖iteratedFDeriv ℝ l mt p‖ ≤ Dt l*L^(l+0) :=
    (hjt l l le_rfl p).trans (le_mul_of_one_le_right (hDt l) (one_le_pow₀ hL))
  have hleftRi := leftLocalizer_adjoint_ae_of_rightLocalizer hρpos.ne'
    mi hmi.continuous hmic Ri hRi
  have hRiNorm := (hlow mi hmi hmic hsuppI hjetI ρ hρ Ri Ri.adjoint hRi hleftRi).1
  have hleftMt := leftLocalizer_adjoint_ae_of_rightLocalizer hρpos.ne' mt ht.continuous htc Mt hMt
  let v := (1-Lbridge) (Ri u)
  have hv := hidm _ _ hmi hmic
    hmb hmbr hfreq hjetI hjetB
    hid ρ L hL hLρ Ri Lbridge hRi hLb q u
  have hv0 := hid0 _ _ hmi hmic
    hmb hmbr hfreq hjetI hjetB
    hid ρ L hL hLρ Ri Lbridge hRi hLb q u
  have hvnorm : ‖v‖ ≤ I0 q*ρ^(d+1)*(L/ρ)^q*‖u‖ := by
    simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, Nat.add_zero] using hv0.2
  have htv := htcost ρ hρ Mt.adjoint hleftMt v
  simp only [ContinuousLinearMap.adjoint_adjoint] at htv
  have hx := hcross _ mt hmb hmbc ht htc
    hbase hann hcrossPlateau ρ L hL hLρ hbridgeJets htJets Lbridge Mt hLb hMt q (Ri u)
  have hImq := hIm q
  have hI0q := hI0 q
  have hXtq := hXt q
  let W := ρ^(2*(d+1)+order)*L^(order+(d+1+1))*(L/ρ)^q*‖u‖
  have hvb : vectorFourierSobolevNorm (order : ℝ) v ≤ Im q*W := by
    apply hv.2.trans
    calc
      _ ≤ Im q*ρ^(2*(d+1)+order)*(L/ρ)^q*‖u‖ := by gcongr; omega
      _ = Im q*ρ^(2*(d+1)+order)*1*(L/ρ)^q*‖u‖ := by ring
      _ ≤ Im q*ρ^(2*(d+1)+order)*L^(order+(d+1+1))*(L/ρ)^q*‖u‖ := by
        gcongr
        exact one_le_pow₀ hL
      _ = _ := by dsimp [W]; ring
  have htvb : vectorFourierSobolevNorm (order : ℝ) (Mt v) ≤ (Tcost*I0 q)*W := by
    apply htv.2.trans
    calc
      _ ≤ Tcost*ρ^(d+1+order)*(I0 q*ρ^(d+1)*(L/ρ)^q*‖u‖) := by gcongr
      _ = (Tcost*I0 q)*ρ^(2*(d+1)+order)*1*(L/ρ)^q*‖u‖ := by
        rw [show 2*(d+1)+order = (d+1+order)+(d+1) by omega, pow_add]
        ring
      _ ≤ (Tcost*I0 q)*ρ^(2*(d+1)+order)*L^(order+(d+1+1))*(L/ρ)^q*‖u‖ := by
        gcongr
        exact one_le_pow₀ hL
      _ = _ := by dsimp [W]; ring
  have hxb : vectorFourierSobolevNorm (order : ℝ) (((1-Mt).comp Lbridge) (Ri u)) ≤
      (Xt q*C0)*W := by
    apply hx.2.trans
    simp only [Nat.add_zero]
    calc
      _ ≤ Xt q*ρ^order*L^(order+(d+1+1))*(L/ρ)^q*(C0*‖u‖) := by
        gcongr
        exact Ri.le_of_opNorm_le hRiNorm u
      _ ≤ Xt q*ρ^(2*(d+1)+order)*L^(order+(d+1+1))*(L/ρ)^q*(C0*‖u‖) := by
        gcongr; omega
      _ = _ := by dsimp [W]; ring
  have hneg := TerminalBounds.neg_bound htv.1
  have hadd := TerminalBounds.add_bound hv.1 hneg.1
  have hall := TerminalBounds.add_bound hadd.1 hx.1
  have he : (1-Mt) (Ri u) = (v + -(Mt v)) + ((1-Mt).comp Lbridge) (Ri u) := by
    simp only [v, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [he]
  refine ⟨hall.1, hall.2.trans ?_⟩
  calc
    _ ≤ (vectorFourierSobolevNorm (order : ℝ) v +
        vectorFourierSobolevNorm (order : ℝ) (Mt v)) +
        vectorFourierSobolevNorm (order : ℝ) (((1-Mt).comp Lbridge) (Ri u)) := by
      rw [hneg.2] at hadd
      exact add_le_add hadd.2 le_rfl
    _ ≤ (Im q*W + (Tcost*I0 q)*W) + (Xt q*C0)*W :=
      add_le_add (add_le_add hvb htvb) hxb
    _ = _ := by dsimp [W]; ring

/-- Restrict the prescribed terminal right defect to the analytic
whole-space scale. The original zero extension, fixed terminal mask and
constants are retained (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_prescribed_terminal_right_restriction_constants
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {buffer : ℝ} (hbuffer : 0 < buffer) (order : ℕ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ mi mb : LocalizerSymbol (d+1),
      ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mb → HasCompactSupport mb →
      (∀ p, mb p ∈ Icc (0 : ℝ) 1) →
      tsupport mi ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      tsupport mb ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Hmask k) →
      (∀ k p, ‖iteratedFDeriv ℝ k mb p‖ ≤ Hmask k) →
      (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {z | mb z = 1}) →
      (∀ p ∈ tsupport mb, closedBall p buffer ⊆ interior {z | mt z = 1}) →
      ∀ ρ L : ℝ, 1 ≤ L → L ≤ ρ →
      ∀ Ri Lbridge Mt : H →L[ℂ] H,
      (∀ u, Ri u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Lbridge u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ mb (fun z ↦ (u z).ofLp) y)) →
      (∀ u, Mt u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mt (fun z ↦ (u z).ofLp) y)) →
      ∀ q (u : LocalL2 (univ : Set E) (EuclideanSpace ℂ (Fin (d+1)))),
        let v := (1-localRetardedOperator MeasurableSet.univ univ Mt)
          (localRetardedOperator MeasurableSet.univ univ Ri u)
        let G := restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ
        v ∈ G.level order ∧ G.gradeNorm order v ≤
          C q * ρ^(2*(d+1)+order) * L^(order+(d+1+1)) * (L/ρ)^q * ‖u‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_prescribed_terminal_right_leakage_constants
    b Rbase Hmask hHmask mt ht htc hbuffer order
  obtain ⟨D, hD, hcompare⟩ := exists_restrictionScale_fourier_comparison (d+1) (d+1) order
  refine ⟨fun q ↦ D*C q, fun q ↦ mul_nonneg hD.le (hC q), ?_⟩
  intro mi mb hmi hmic hmb hmbc hmbr hsuppI hsuppB hjetI hjetB hid hterminal
    ρ L hL hLρ Ri Lbridge Mt hRi hLb hMt q u v G
  have h := hbound mi mb hmi hmic hmb hmbc hmbr hsuppI hsuppB hjetI hjetB hid hterminal
    ρ L hL hLρ Ri Lbridge Mt hRi hLb hMt q (SmallSupport.zeroExtend MeasurableSet.univ u)
  have he : v = restrictL2 univ ((1-Mt) (Ri (SmallSupport.zeroExtend MeasurableSet.univ u))) :=
    congrArg (fun S ↦ S u) (local_univ_rightLocalizer_defect_eq Ri Mt)
  rw [he]
  obtain ⟨hm, hn⟩ := hcompare univ MeasurableSet.univ _ _ h.1
    (restrictL2_coeFn univ _).symm
  refine ⟨hm, hn.trans ?_⟩
  simpa only [LinearIsometry.norm_map, mul_assoc] using
    mul_le_mul_of_nonneg_left h.2 hD.le

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
