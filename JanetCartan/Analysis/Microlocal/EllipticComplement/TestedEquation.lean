module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.CutEquation
public import JanetCartan.Analysis.Microlocal.EllipticComplement.SymbolBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization

/-!
# The uncut tested elliptic equation

Use the same compact frequency sequence for the three original-coordinate
PDOs. Their strong limits preserve the tested equation, and density gives it
for every original Lebesgue L² datum. The coefficient extensions are used
only to test on the actual output plateau.
Source: `app:ch_regular_base:eq:sector-theorem-identity`,
`app:ch_regular_base:sec:energy-construction`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open ActualCarriers FiniteMasks.ActualFamily Characteristic Characteristic.EvolutionIntegral
open Characteristic.ResidualCoordinates Characteristic.PdoRealization FourierIntegral
open FourierIntegral.FullLowBounds FourierIntegral.LowBounds.FrequencyCutoff Characteristic.EvolutionIntegral.KernelIdentification
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "FV" => Fin (d+1) → ℂ
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- Smooth test coefficients which agree with the original physical operator
on the *same* measurement ball. Used for integration by parts and its weak
closure in `sector-theorem-identity`. -/
theorem exists_elliptic_test_coefficients (hΩ : IsOpen Ω)
    (Q : E → Coeff) (B : E → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω) :
    ∃ A : E → Coeff, ∃ B' : E → Mat,
      (∀ a i j, ContDiff ℝ ∞ (fun y ↦ A y a i j)) ∧
      (∀ i j, ContDiff ℝ ∞ (fun y ↦ B' y i j)) ∧
      ∀ y ∈ closedBall x f.physicalRadius,
        A y = (fun a ↦ pencil (Q y) (EuclideanSpace.single a 1)) ∧ B' y = B y := by
  have hid (y : E) : physicalCoordinates (0 : Fin (d+1)) y = y := by simp [physicalCoordinates]
  have hsub : closedBall x f.physicalRadius ⊆ Ω := (closedBall_subset_closedBall
    (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 4*f.physicalRadius)).trans
      f.physicalBall_subset
  obtain ⟨A, B', hA, hB', he⟩ := exists_smooth_coordinate_coefficients 0 hΩ Q B hQ hB
    isClosed_closedBall (fun y hy ↦ by simpa only [hid] using hsub hy)
  refine ⟨A, B', (fun a i j ↦ (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
    ((contDiff_pi.mp hA) a)), (fun i j ↦
      (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp hB'), ?_⟩
  intro y hy
  refine ⟨?_, by simpa only [zeroth, hid] using (he y hy).2.eq_of_nhds⟩
  rw [(he y hy).1.eq_of_nhds]
  funext a
  simp only [coefficient, hid]

/-- The tested equation for the actual L² solver, complementary source and
full order-minus-one residual. The original source mask acts before the
canonical graph. The equation is measured on the actual output plateau and
requires no supplied regularization or equation (`sector-theorem-identity`). -/
theorem ellipticSolver_tested (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    {L : ℝ} (hL : f.radialThreshold ≤ L)
    (Q : E → Coeff) (B : E → Mat) (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (hQl : cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M)
    (hBl : cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M)
    (u : H) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ ball x f.physicalRadius) (i : Fin (d+1)) :
    physicalTestAction (fun y a ↦ pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (ellipticSolver f hK L Q u y).ofLp) φ i =
      ∫ y, φ y • ((ellipticSourcePDO f hK L + ellipticResidual f hK L Q B) u) y i := by
  obtain ⟨A, B', hA, hB', he⟩ := exists_elliptic_test_coefficients f hΩ Q B hQ hB
  rw [← physicalTestAction_eq_of_coefficients_on_support A
    (fun y a ↦ pencil (Q y) (EuclideanSpace.single a 1)) B' B _ φ
    (fun y hy ↦ (he y (ball_subset_closedBall (hsφ hy))).1)
    (fun y hy ↦ (he y (ball_subset_closedBall (hsφ hy))).2) i]
  apply physicalTestAction_eq_of_graphTests A B' hA hB' _ _ hφ hcφ i _ u
  intro w
  let χo := fun y ↦ (f.outputMask y : ℂ)
  let χs := fun z ↦ (f.inputMask z : ℂ)
  have hs : ContDiff ℝ ∞ χs := Complex.ofRealCLM.contDiff.comp f.inputMask_smooth
  let v := graphTestToSchwartz (complexSourceMaskTest χs hs w)
  have hvc : HasCompactSupport (v : E → FV) :=
    (complexSourceMaskTest χs hs w).property.2.comp_left (g := WithLp.ofLp) rfl
  let c := ellipticInverseSymbol f hK L Q
  let p := ellipticResidualSymbol f hK L Q B
  let b := ellipticSourceSymbol f hK L
  let θ := complexPhysicalCutoff (n := d+1)
  let Amp (s : E → E → CMat) := fun y z ζ ↦ (χo y * χs z) • s y ζ
  let reg (s : E → E → CMat) (k : ℕ) : H := fullGraphOperator (fun y ξ ↦ inner ℝ y ξ)
      (frequencyCutFullAmplitude (θ k) (Amp s)) (graphTestToLp w)
  let val (s : E → E → CMat) := maskedPhysicalPDO χo χs s (graphTestToLp w)
  let cut (s : E → E → CMat) (k : ℕ) (y : E) := cutPhysicalPDO (θ k) s v y
  have hreg (s : E → E → CMat) {R N : ℝ}
      (hb : GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χo χs s) R N) :
      (∀ k, reg s k =ᵐ[volume] fun y ↦ WithLp.toLp 2 (χo y • cut s k y)) ∧
        Tendsto (reg s) atTop (𝓝 (val s)) := by
    refine ⟨fun k ↦ ?_, tendsto_canonicalGraph_frequencyCut (Nat.succ_pos d) (Amp s) hb θ
      complexPhysicalCutoff_contDiff le_rfl complexPhysicalCutoff_norm_le complexPhysicalCutoff_tendsto _⟩
    exact (canonicalGraph_frequencyCut_realizes (Nat.succ_pos d) (Amp s) hb (θ k)
      (complexPhysicalCutoff_contDiff k) zero_le_one (complexPhysicalCutoff_norm_le k) w).trans
      (Eventually.of_forall fun y ↦ congrArg (WithLp.toLp 2)
        (masked_cutPhysicalPDO_eq_graphOperator s (θ k) χo χs hs w y).symm)
  obtain ⟨_, _, _, _, _, _, hbud⟩ := exists_ellipticSymbols_pdo_budgets f hK hΩ hRQΩ
  have hbcp := hbud L hL Q B hQ hB hmap hQl hBl
  obtain ⟨hcRep, hcLim⟩ := hreg c (hbcp c (Or.inl rfl)).1
  obtain ⟨hpRep, hpLim⟩ := hreg p (hbcp p (Or.inr rfl)).1
  obtain ⟨_, _, _, _, hbs⟩ := exists_ellipticSourcePDO_budgets f hK
  obtain ⟨hbRep, hbLim⟩ := hreg b (hbs L).1
  let z : ℂ := 1 / Complex.I
  let F := fun k y ↦ χo y • z • cut c k y
  let G := fun k y ↦ χo y • (cut b k y + z • cut p k y)
  have hLp := zero_lt_one.trans_le (f.radialThreshold_ge_one.trans hL)
  have hc := contDiff_ellipticInverseSymbol f hK hΩ hLp Q hQ hmap
  have hF k : ContDiff ℝ 1 (F k) := ((Complex.ofRealCLM.contDiff.comp f.outputMask_smooth).smul
    ((contDiff_cutPhysicalPDO (θ k) c v (complexPhysicalCutoff_contDiff k)
      (complexPhysicalCutoff_hasCompactSupport k) hc hvc).const_smul z)).of_le (by simp)
  have hFre (k : ℕ) : z • reg c k =ᵐ[volume] fun y ↦ WithLp.toLp 2 (F k y) := by
    filter_upwards [Lp.coeFn_smul z (reg c k), hcRep k] with y hy hcy
    rw [hy, Pi.smul_apply, hcy]
    exact congrArg (WithLp.toLp 2) (smul_comm z (χo y) (cut c k y))
  have hGre (k : ℕ) : reg b k + z • reg p k =ᵐ[volume] fun y ↦ WithLp.toLp 2 (G k y) := by
    filter_upwards [Lp.coeFn_add (reg b k) (z • reg p k), Lp.coeFn_smul z (reg p k),
      hbRep k, hpRep k] with y hy hy' hby hpy
    rw [hy, Pi.add_apply, hby, hy', Pi.smul_apply, hpy]
    apply congrArg (WithLp.toLp 2)
    change χo y • cut b k y + z • χo y • cut p k y = χo y • (cut b k y + z • cut p k y)
    rw [smul_add, smul_comm z (χo y)]
  have hpde (k : ℕ) : WKB.firstOrderApply (fun y a ↦ ((A y a).map Complex.ofReal).mulVecLin)
      (fun y ↦ ((B' y).map Complex.ofReal).mulVecLin) (F k) =ᵐ[volume.restrict
        (ball x f.physicalRadius)] G k := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    have hy' := ball_subset_closedBall hy
    rw [firstOrderApply_eq_of_coefficients _ (fun y a ↦ (pencil (Q y)
      (EuclideanSpace.single a 1)).map Complex.ofReal) _ (fun y ↦ (B y).map Complex.ofReal)
      (F k) (by rw [(he y hy').1]) (by rw [(he y hy').2])]
    exact firstOrderApply_cutEllipticSolver_on_plateau f hK hΩ hLp Q B hQ hmap (θ k)
      (complexPhysicalCutoff_contDiff k) (complexPhysicalCutoff_hasCompactSupport k) v hvc hy'
  exact firstOrderApply_test_of_strongL2 A B' hA hB' isOpen_ball.measurableSet
    (fun k ↦ z • reg c k) (fun k ↦ reg b k + z • reg p k) (z • val c) (val b + z • val p)
    F G hF hFre hGre (hcLim.const_smul z) (hbLim.add (hpLim.const_smul z)) hpde hφ hcφ hsφ i

end JanetCartan.RegularSector.EllipticComplement
