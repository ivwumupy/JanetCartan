module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.JointAssembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseAssembly.Joint
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates

/-!
# Joint two-scale profiles for the same annular operator and literal adjoint

The primitive joint Sobolev producers already identify the actual parameter
derivatives with the finite branch expansion. Here their weighted estimates
are converted to the input scale, with total order `s + ps.length`, without
changing the physical graph, frequency, or coefficient scale.
Consumer: `jc-direct-evolution-envelope`, for the joint assertion following
`app:ch_response:eq:direct-envelope-profile` and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option cleanup.letToHave false
open Set MeasureTheory Filter LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open Pseudodifferential FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds
open FourierIntegral.SourceExpansion NormalComparison FrequencyCutoff AmplitudeBound
open FullAmplitudePrimitiveBudget.Local CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "Vf" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp Vf 2 (volume : Measure E)
local instance jointEnvelopeAnnularComplexMatrixTopology : TopologicalSpace Mat :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

attribute [local irreducible] normalizedTermAmplitude elapsedCarrierPhase
  averagedPhaseHessian modifiedAmplitude fullGraphOperator

/-- Convert the original mixed-datum weighted sum to its sharp input-scale
profile at total order `N`. The coefficient scale satisfies `1 ≤ L ≤ Kinput`;
no output estimate or higher datum order enters this algebraic step
(`app:ch_response:eq:direct-envelope-profile`, `new:eq:carrier-ibp`). -/
theorem jointWeightedProfile_le_inputScale
    (N : ℕ) {L Kinput A₀ : ℝ} (hL : 1 ≤ L) (hLK : L ≤ Kinput)
    (Ddata Dprofile : ℕ → ℝ) (hDdata : ∀ j, 0 ≤ Ddata j)
    (hb : ∀ j, j ≤ N → Ddata j ≤ A₀ * Dprofile j * Kinput ^ j) :
    (∑ j ∈ Finset.range (N + 1), L ^ (N - j) * Ddata j) ≤
      A₀ * (∑ j ∈ Finset.range (N + 1), Dprofile j) * Kinput ^ N := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hK0 : 0 ≤ Kinput := hL0.trans hLK
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), A₀ * Dprofile j * Kinput ^ N := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        _ ≤ Kinput ^ (N - j) * (A₀ * Dprofile j * Kinput ^ j) :=
          mul_le_mul (pow_le_pow_left₀ hL0 hLK _) (hb j hjN)
            (hDdata j) (pow_nonneg hK0 _)
        _ = _ := by rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hjN]
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The actual joint derivative of the annular elapsed operator
has the original weighted profile and the `Kinput^(s+ps.length)` bound in the
existing vector Sobolev scale. The primitive joint theorem supplies all branch
bounds, weak identities, and output membership. The only datum bounds concern
actual original mixed derivatives. Parameter differentiation fixes the physical
operator and frequency. Both `p = 0` and `p = -1` use the same low reserve,
independent of the spatial and parameter orders. Sources:
`app:ch_response:lem:energy-carrier-jets`, `new:eq:carrier-ibp`, and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_annularEnvelope_joint_envelope_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (s : ℕ) (ps : List P) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∀ (Ψ : TwoTimePhase d) (t : ℝ)
    (_hS : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)))
    {X D : Set E} {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables (d + 1))}
    (_chart : AveragedGradientChart (elapsedPhase Ψ t) X D η J δ)
    (_hopen : IsOpen (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hηinput : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hmapinput : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)) W)
    (_hJinput : ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J q.1 q.2.1 q.2.2) W)
    (_hgapinput : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (_hrightInverse : ∀ q ∈ bufferedNormalDomain X D (elapsedPhase Ψ t),
      normalForwardCoordinates (elapsedPhase Ψ t) (normalInverseCoordinates η q) = q)
    (_hcarrier : ∀ q ∈ W, q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ → q ∈ K)
    (_hclosed : IsClosed (normalForwardCoordinates (elapsedPhase Ψ t) '' K))
    (_hbuffer : normalForwardCoordinates (elapsedPhase Ψ t) '' K ⊆ bufferedNormalDomain X D (elapsedPhase Ψ t))
    (_hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (_hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient (elapsedPhase Ψ t) x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℕ → Set (NormalVariables (d + 1)))
    (_hUopen : ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hVopen : ∀ l, IsOpen (V l))
    (_hη : ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hmap : ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l) (V l))
    (_hJ : ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) (V l))
    (_hgap : ∀ l z, z ∈ V l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) J z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ l z, z ∈ V l → ∀ i ≤ primitiveNormalReserve (d + 1),
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve (d + 1) →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) η)) z‖ ≤ G)
    (_hscale : ∀ l z, z ∈ V l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    (_hX₀ : X₀ ⊆ X) (_hF₀ : F₀ ⊆ D),
    ∀ (Rstar : ℕ), fullLowReserve (d + 1) + 2 < Rstar →
    ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam → ∀ (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    (A : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ),
    let α := normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
    ∀ (U : Set (E × P)) (Dcrit : Set (CarrierVariables (d + 1))),
    IsOpen U → IsOpen Dcrit → Convex ℝ Dcrit →
    ContDiffOn ℝ ∞ (Function.uncurry (elapsedCarrierPhase Ψ t φ)) (U ×ˢ Dcrit) →
    ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U Dcrit →
    (∀ q ∈ U, gradient (elapsedCarrierPhase Ψ t φ q) (w₀ q) = 0) →
    (∀ q ∈ U, elapsedCarrierPhase Ψ t φ q (w₀ q) = 0) →
    (∀ q ∈ U, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian (elapsedCarrierPhase Ψ t φ) w₀ q w)) →
    (∀ q ∈ U, ∀ w ∈ Dcrit,
      ‖Ring.inverse (averagedPhaseHessian (elapsedCarrierPhase Ψ t φ) w₀ q w)‖ ≤ B) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length) + 2,
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (elapsedCarrierPhase Ψ t φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length),
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar)) →
    ∀ (Kcrit : Set (CarrierVariables (d + 1))), IsCompact Kcrit → Kcrit ⊆ Dcrit →
    (∀ q ∈ U, Function.support (α q) ⊆ Kcrit) →
    (∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X₀) →
    ∀ (Cpar : Set P), IsOpen Cpar → X₀ ×ˢ Cpar ⊆ U →
    ∀ (hcφ : ∀ param, Continuous (fun x => φ x param)),
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.1 ∈ X₀ ∧ q.1.2 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    (∀ x ∈ X₀, ∀ θ, lam • θ ∈ F₀ →
      elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ) →
    ∀ (Ksource Ssource : Set E) (hKsource : IsCompact Ksource), IsOpen Ssource →
    Ksource ⊆ Ssource → (∀ param ∈ Cpar, ContDiffOn ℝ ∞ (fun x => φ x param) Ssource) →
    ∀ (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
      (has : ∀ q, q.1 ∉ Ksource → a q = 0),
    ∀ param ∈ Cpar, ∀ (Ddata : ℕ → ℝ), (∀ j, 0 ≤ Ddata j) →
    (∀ j, j ≤ s + ps.length →
      ∃ hm : MemLp (fun x : E => iteratedFDeriv ℝ j a (x, param)) 2 volume,
        ‖hm.toLp (fun x : E => iteratedFDeriv ℝ j a (x, param))‖ ≤ Ddata j) →
    let output := orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
      (fun c => annularEnvelopeOperator Ψ A χout χsource β π t lam
        (fun x => φ x c) (hcφ c)
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
    MemVectorFourierSobolev (s : ℝ) output ∧
      vectorFourierSobolevNorm (s : ℝ) output ≤ C * lam ^ p *
        (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * Ddata j) ∧
      ∀ (Kinput nu A₀ : ℝ) (Dprofile : ℕ → ℝ), L ≤ Kinput →
        Kinput ≤ lam ^ (1 - nu) → 0 < nu → nu < 1 →
        (∀ j, j ≤ s + ps.length → Ddata j ≤ A₀ * Dprofile j * Kinput ^ j) →
        output ∈ (Complement.vectorFourierSobolevScale (d := d + 1) (I := Fin r)).level s ∧
          Complement.vectorFourierSobolevScale.gradeNorm s output ≤
            (C * ∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j) *
              lam ^ p * A₀ * Kinput ^ (s + ps.length) := by
  obtain ⟨C, hC, hbuild⟩ := exists_annularEnvelope_joint_sobolev_of_primitive_jets
    (r := r) (P := P) R ℓ M G c hℓ hRcell hδ hF hc basis s ps hps
    Aphase Aamp hphase hamp hB hradius
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
    Ψ t hS X D η J Wnormal Knormal chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
  dsimp only
  let α := normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
  intro U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    hΘ Ksource Ssource hKsource hSsource hKS hφ a ha has param hparam Ddata hDdata hj
  have hb := hbuild
    X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
    Ψ t hS chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
    U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport hΘ
    Ksource Ssource hKsource hSsource hKS hφ a ha has param hparam Ddata hDdata hj
  refine ⟨hb.1, hb.2, ?_⟩
  intro Kinput nu A₀ Dprofile hLK _hKlam _hnu _hnu1 hdata
  refine ⟨hb.1, ?_⟩
  rw [Complement.vectorFourierSobolevScale_gradeNorm s hb.1]
  apply hb.2.trans
  calc
    _ ≤ C * lam ^ p * (A₀ * (∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j) *
        Kinput ^ (s + ps.length)) :=
      mul_le_mul_of_nonneg_left
        (jointWeightedProfile_le_inputScale (s + ps.length) hL hLK Ddata Dprofile hDdata hdata)
        (mul_nonneg hC (zpow_nonneg (zero_le_one.trans hlam) p))
    _ = _ := by ring

/-- The actual joint derivative of the literal annular Hilbert adjoint
has the original weighted profile and the `Kinput^(s+ps.length)` bound in the
existing vector Sobolev scale. The primitive joint theorem supplies all branch
bounds, weak identities, and output membership. The only datum bounds concern
actual original mixed derivatives. Parameter differentiation fixes the physical
operator and frequency. Both `p = 0` and `p = -1` use the same low reserve,
independent of the spatial and parameter orders. Sources:
`app:ch_response:lem:energy-carrier-jets`, `new:eq:carrier-ibp`, and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_annularEnvelope_adjoint_joint_envelope_of_primitive_jets
    (R ℓ M G c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c)
    (basis : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (s : ℕ) (ps : List P) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (Aphase Aamp : ℕ → ℝ) (hphase : ∀ j, 0 ≤ Aphase j) (hamp : ∀ j, 0 ≤ Aamp j)
    {B radius : ℝ} (hB : 0 ≤ B) (hradius : 0 ≤ radius) :
    ∃ C ≥ 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ → IsCompact Y₀ →
      (∀ y ∈ Y₀, ∀ i : Fin (d + 1), |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∀ (Ψ : TwoTimePhase d) (t : ℝ)
    (_hS : ContDiff ℝ ∞ (Function.uncurry (elapsedPhase Ψ t)))
    {X D : Set E} {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables (d + 1))}
    (_chart : AveragedGradientChart (elapsedPhase Ψ t) X D η J δ)
    (_hopen : IsOpen (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hηinput : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)))
    (_hmapinput : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D (elapsedPhase Ψ t)) W)
    (_hJinput : ContDiffOn ℝ ∞ (fun q : NormalVariables (d + 1) ↦ J q.1 q.2.1 q.2.2) W)
    (_hgapinput : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (_hrightInverse : ∀ q ∈ bufferedNormalDomain X D (elapsedPhase Ψ t),
      normalForwardCoordinates (elapsedPhase Ψ t) (normalInverseCoordinates η q) = q)
    (_hcarrier : ∀ q ∈ W, q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ → q ∈ K)
    (_hclosed : IsClosed (normalForwardCoordinates (elapsedPhase Ψ t) '' K))
    (_hbuffer : normalForwardCoordinates (elapsedPhase Ψ t) '' K ⊆ bufferedNormalDomain X D (elapsedPhase Ψ t))
    (_hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (_hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient (elapsedPhase Ψ t) x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℕ → Set (NormalVariables (d + 1)))
    (_hUopen : ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hVopen : ∀ l, IsOpen (V l))
    (_hη : ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l))
    (_hmap : ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l) (V l))
    (_hJ : ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) (V l))
    (_hgap : ∀ l z, z ∈ V l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) J z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ l z, z ∈ V l → ∀ i ≤ primitiveNormalReserve (d + 1),
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables (d + 1) ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain X D (elapsedPhase Ψ t)) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve (d + 1) →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) η)) z‖ ≤ G)
    (_hscale : ∀ l z, z ∈ V l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    (_hX₀ : X₀ ⊆ X) (_hF₀ : F₀ ⊆ D),
    ∀ (Rstar : ℕ), fullLowReserve (d + 1) + 2 < Rstar →
    ∀ (L lam : ℝ), 1 ≤ L → 1 ≤ lam → ∀ (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    (A : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ),
    let α := normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
    ∀ (U : Set (E × P)) (Dcrit : Set (CarrierVariables (d + 1))),
    IsOpen U → IsOpen Dcrit → Convex ℝ Dcrit →
    ContDiffOn ℝ ∞ (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) (U ×ˢ Dcrit) →
    ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U Dcrit →
    (∀ q ∈ U, gradient (adjointCarrierPhase (elapsedPhase Ψ t) φ q) (w₀ q) = 0) →
    (∀ q ∈ U, adjointCarrierPhase (elapsedPhase Ψ t) φ q (w₀ q) = 0) →
    (∀ q ∈ U, ∀ w ∈ Dcrit, IsUnit (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ q w)) →
    (∀ q ∈ U, ∀ w ∈ Dcrit,
      ‖Ring.inverse (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ t) φ) w₀ q w)‖ ≤ B) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length) + 2,
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ t) φ)) q‖ ≤
          Aphase j * L ^ (j - Rstar)) →
    ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ Dcrit) →
    (∀ j ≤ fullLowReserve (d + 1) + (s + ps.length),
      ∀ q ∈ U ×ˢ Dcrit,
        ‖iteratedFDeriv ℝ j (Function.uncurry α) q‖ ≤ Aamp j * L ^ (j + 2 - Rstar)) →
    ∀ (Kcrit : Set (CarrierVariables (d + 1))), IsCompact Kcrit → Kcrit ⊆ Dcrit →
    (∀ q ∈ U, Function.support (α q) ⊆ Kcrit) →
    (∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ Y₀) →
    ∀ (Cpar : Set P), IsOpen Cpar → Y₀ ×ˢ Cpar ⊆ U →
    ∀ (hcφ : ∀ param, Continuous (fun x => φ x param)),
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      normalizedSlice param q ∈ U ×ˢ Dcrit) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) → ‖q.2‖ ≤ radius) →
    (∀ param ∈ Cpar, ∀ q, normalizedSlice param q ∈ tsupport (Function.uncurry α) →
      q.1.2 ∈ X₀ ∧ q.1.1 ∈ Y₀ ∧ lam • q.2 ∈ F₀) →
    (∀ x ∈ X₀, ∀ θ, lam • θ ∈ F₀ →
      elapsedPhase Ψ t x (lam • θ) = lam * elapsedPhase Ψ t x θ) →
    ∀ (Ksource Ssource : Set E) (hKsource : IsCompact Ksource), IsOpen Ssource →
    Ksource ⊆ Ssource → (∀ param ∈ Cpar, ContDiffOn ℝ ∞ (fun x => φ x param) Ssource) →
    ∀ (a : E × P → Vf) (ha : ContDiff ℝ ∞ a)
      (has : ∀ q, q.1 ∉ Ksource → a q = 0),
    ∀ param ∈ Cpar, ∀ (Ddata : ℕ → ℝ), (∀ j, 0 ≤ Ddata j) →
    (∀ j, j ≤ s + ps.length →
      ∃ hm : MemLp (fun x : E => iteratedFDeriv ℝ j a (x, param)) 2 volume,
        ‖hm.toLp (fun x : E => iteratedFDeriv ℝ j a (x, param))‖ ≤ Ddata j) →
    let output := orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
      (fun c => (annularEnvelopeOperator Ψ A χout χsource β π t lam
        (fun x => φ x c) (hcφ c)).adjoint
        (graphTestToLp (vectorOriginalDatumTest a ha hKsource has [] c))) param
    MemVectorFourierSobolev (s : ℝ) output ∧
      vectorFourierSobolevNorm (s : ℝ) output ≤ C * lam ^ p *
        (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * Ddata j) ∧
      ∀ (Kinput nu A₀ : ℝ) (Dprofile : ℕ → ℝ), L ≤ Kinput →
        Kinput ≤ lam ^ (1 - nu) → 0 < nu → nu < 1 →
        (∀ j, j ≤ s + ps.length → Ddata j ≤ A₀ * Dprofile j * Kinput ^ j) →
        output ∈ (Complement.vectorFourierSobolevScale (d := d + 1) (I := Fin r)).level s ∧
          Complement.vectorFourierSobolevScale.gradeNorm s output ≤
            (C * ∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j) *
              lam ^ p * A₀ * Kinput ^ (s + ps.length) := by
  obtain ⟨C, hC, hbuild⟩ := exists_annularEnvelope_adjoint_joint_sobolev_of_primitive_jets
    (r := r) (P := P) R ℓ M G c hℓ hRcell hδ hF hc basis s ps hps
    Aphase Aamp hphase hamp hB hradius
  refine ⟨C, hC, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero
    Ψ t hS X D η J Wnormal Knormal chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
  dsimp only
  let α := normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π t lam p
  intro U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport
    hΘ Ksource Ssource hKsource hSsource hKS hφ a ha has param hparam Ddata hDdata hj
  have hb := hbuild
    X₀ Y₀ F₀ hXcompact hYcompact hYbox hFclosed hFzero
    Ψ t hS chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀ Rstar hRstar L lam hL hlam p φ w₀ A χout χsource β π
    U Dcrit hU hDcrit hcD hf hw₀ h₀ hcrit hvalue hu hi hp hα hαjet
    Kcrit hKcrit hKD hsupportCrit houtput Cpar hCpar hXU hcφ hs hsfreq hsupport hΘ
    Ksource Ssource hKsource hSsource hKS hφ a ha has param hparam Ddata hDdata hj
  refine ⟨hb.1, hb.2, ?_⟩
  intro Kinput nu A₀ Dprofile hLK _hKlam _hnu _hnu1 hdata
  refine ⟨hb.1, ?_⟩
  rw [Complement.vectorFourierSobolevScale_gradeNorm s hb.1]
  apply hb.2.trans
  calc
    _ ≤ C * lam ^ p * (A₀ * (∑ j ∈ Finset.range (s + ps.length + 1), Dprofile j) *
        Kinput ^ (s + ps.length)) :=
      mul_le_mul_of_nonneg_left
        (jointWeightedProfile_le_inputScale (s + ps.length) hL hLK Ddata Dprofile hDdata hdata)
        (mul_nonneg hC (zpow_nonneg (zero_le_one.trans hlam) p))
    _ = _ := by ring

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
