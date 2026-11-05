module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Physical
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.KernelJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.ParameterRealization.L2Family.CompactFamily
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual parameter derivatives of inactive complementary sources

This leaf supplies the parameter-realization and fixed-operator steps in the
parameter-complement paragraph of `app:ch_response:thm:response-literal-transfer`.
A common compact spatial support and joint smoothness produce genuine parameter
derivatives in the original Euclidean vector L² space. The normalized
`parameterCarrierJet` factors the actual derivative into the fixed carrier and
an actual envelope jet, retaining both carrier and source terms. Fixed Fourier
masks and physical carriers commute with these derivatives as continuous linear
operators; their Fourier symbols remain evaluated at `2πξ`. The inactive
source precision wrapper delegates only the already proved source-shell estimate
while retaining all phase, support, gap, profile, and cutoff hypotheses.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

variable {d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

def extendZeroVector {K : Set E} [CompactSpace K] (f : C(K, F)) : E → F :=
  Function.extend Subtype.val f 0

lemma extendZeroVector_mem {K : Set E} [CompactSpace K] (f : C(K, F)) {x : E} (hx : x ∈ K) :
    extendZeroVector f x = f ⟨x, hx⟩ := by
  exact Subtype.coe_injective.extend_apply _ _ ⟨x, hx⟩

lemma extendZeroVector_notMem {K : Set E} [CompactSpace K] (f : C(K, F)) {x : E} (hx : x ∉ K) :
    extendZeroVector f x = 0 := by
  exact Function.extend_apply' _ _ _ (by simpa using hx)

lemma extendZeroVector_memLp {K : Set E} (hK : IsCompact K) [CompactSpace K]
    (f : C(K, F)) : MemLp (extendZeroVector f) 2 volume := by
  have hm : StronglyMeasurable (extendZeroVector f) :=
    (MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet).stronglyMeasurable_extend
      f.continuous.stronglyMeasurable stronglyMeasurable_zero
  have hs : HasCompactSupport (extendZeroVector f) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (extendZeroVector_notMem f hn)
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖f‖
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [extendZeroVector_mem f hx]
    exact f.norm_coe_le_norm _
  · rw [extendZeroVector_notMem f hx, norm_zero]
    exact norm_nonneg _

def compactToL2Vector {K : Set E} (hK : IsCompact K) [CompactSpace K] : C(K, F) →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (extendZeroVector_memLp hK f).toLp (extendZeroVector f)
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [extendZeroVector_mem _ hx]
        · simp [extendZeroVector_notMem _ hx]
      map_smul' := by
        intro a f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ K
        · simp [extendZeroVector_mem _ hx]
        · simp [extendZeroVector_notMem _ hx] }
    ‖indicatorConstLp (μ := (volume : Measure E)) 2
      hK.isClosed.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖
    (fun f ↦ by
      rw [mul_comm]
      change ‖(extendZeroVector_memLp hK f).toLp (extendZeroVector f)‖ ≤ _
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(extendZeroVector_memLp hK f).coeFn_toLp,
        indicatorConstLp_coeFn (μ := (volume : Measure E)) (p := 2)
          (hs := hK.isClosed.measurableSet)
          (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hx hy
      rw [hx, hy]
      by_cases hxK : x ∈ K
      · simp only [extendZeroVector_mem _ hxK, indicator_of_mem hxK, norm_one, mul_one]
        exact f.norm_coe_le_norm _
      · simp [extendZeroVector_notMem _ hxK, indicator_of_notMem hxK])

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

@[expose] noncomputable section
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open JanetCartan.ResponseTransfer.ParameterRealization.L2Family
variable {p d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

def parameterSourceFunction (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F) : P → E → F :=
  fun c x ↦ carrier ρ (φ c) x • f c x

private lemma compactFamilyVector_apply {K : Set E} [CompactSpace K] {V : Set P} {g : P → E → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    {c : P} (hc : c ∈ V) (x : K) : compactFamily (K := K) g c x = g c x := by
  exact compactFamily_apply hg hc x

private lemma compactFamilyVector_iterated_apply {K : Set E} [CompactSpace K]
    {V : Set P} {g : P → E → F}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) (x : K) :
    (iteratedFDeriv ℝ k (compactFamily (K := K) g) c v) x =
      iteratedFDeriv ℝ k (fun a ↦ g a x) c v := by
  have hh := (ContinuousMap.evalCLM ℝ x (M := F)).iteratedFDeriv_comp_left
    (compactFamily_contDiffAt k hV hg hc) (le_refl (k : ℕ∞ω))
  have he : ((ContinuousMap.evalCLM ℝ x (M := F)) ∘ compactFamily (K := K) g) =ᶠ[𝓝 c]
      (fun a ↦ g a x) := by
    filter_upwards [hV.mem_nhds hc] with a ha
    exact compactFamily_apply hg ha x
  rw [he.iteratedFDeriv ℝ k |>.eq_of_nhds] at hh
  exact (congrArg (fun m ↦ m v) hh).symm

private lemma parameterSource_differential_zero {K : Set E}
    {V : Set P} (hV : IsOpen V) {g : P → E → F}
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V)
    {x : E} (hx : x ∉ K) :
    iteratedFDeriv ℝ k (fun a ↦ g a x) c v = 0 := by
  have he : (fun a ↦ g a x) =ᶠ[𝓝 c] (fun _ ↦ (0 : F)) := by
    filter_upwards [hV.mem_nhds hc] with a ha
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs a ha h))
  rw [he.iteratedFDeriv ℝ k |>.eq_of_nhds]
  cases k with
  | zero => exact iteratedFDeriv_zero_apply _
  | succ k => simp

private lemma parameterSource_extension_differential {K : Set E} (_hK : IsCompact K)
    [CompactSpace K] {V : Set P} (hV : IsOpen V)
    {g : P → E → F} (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    extendZeroVector (iteratedFDeriv ℝ k (compactFamily (K := K) g) c v) =
      fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v := by
  funext x
  by_cases hx : x ∈ K
  · rw [extendZeroVector_mem _ hx]
    exact compactFamilyVector_iterated_apply hV hg k v hc ⟨x, hx⟩
  · rw [extendZeroVector_notMem _ hx, parameterSource_differential_zero hV hs k v hc hx]

theorem parameterSource_memLp {K : Set E} (hK : IsCompact K)
    {V : Set P} (hV : IsOpen V)
    {g : P → E → F} (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    MemLp (fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v) 2 volume := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [← parameterSource_extension_differential hK hV hg hs k v hc]
  exact extendZeroVector_memLp hK _

private lemma parameterSource_compactToL2_eq {K : Set E} (hK : IsCompact K)
    [CompactSpace K] {V : Set P} (_hV : IsOpen V)
    {g : P → E → F} (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ K)
    (hmem : ∀ a, MemLp (g a) 2 volume) {c : P} (hc : c ∈ V) :
    compactToL2Vector hK (compactFamily (K := K) g c) = (hmem c).toLp (g c) := by
  change (extendZeroVector_memLp hK _).toLp _ = _
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · rw [extendZeroVector_mem _ hx]
    exact compactFamily_apply hg hc ⟨x, hx⟩
  · rw [extendZeroVector_notMem _ hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs c hc h))).symm

theorem contDiffAt_parameterSourceClass {K : Set E} (hK : IsCompact K)
    {V : Set P} (hV : IsOpen V) {g : P → E → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ K)
    (hmem : ∀ a, MemLp (g a) 2 volume) (k : ℕ) {c : P} (hc : c ∈ V) :
    ContDiffAt ℝ k (fun a ↦ (hmem a).toLp (g a)) c := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply ((compactToL2Vector hK).contDiff.contDiffAt.comp c
    (compactFamily_contDiffAt k hV hg hc)).congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hc] with a ha
  exact (parameterSource_compactToL2_eq hK hV hg hs hmem ha).symm

theorem iteratedFDeriv_parameterSourceClass {K : Set E} (hK : IsCompact K)
    {V : Set P} (hV : IsOpen V) {g : P → E → F}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ a ∈ V, tsupport (g a) ⊆ K)
    (hmem : ∀ a, MemLp (g a) 2 volume)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    iteratedFDeriv ℝ k (fun a ↦ (hmem a).toLp (g a)) c v =
      (parameterSource_memLp hK hV hg hs k v hc).toLp
        (fun x ↦ iteratedFDeriv ℝ k (fun a ↦ g a x) c v) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hh := (compactToL2Vector hK).iteratedFDeriv_comp_left
    (compactFamily_contDiffAt k hV hg hc) (le_refl (k : ℕ∞ω))
  have he : ((compactToL2Vector hK) ∘ compactFamily (K := K) g) =ᶠ[𝓝 c]
      (fun a ↦ (hmem a).toLp (g a)) := by
    filter_upwards [hV.mem_nhds hc] with a ha
    exact parameterSource_compactToL2_eq hK hV hg hs hmem ha
  rw [he.iteratedFDeriv ℝ k |>.eq_of_nhds] at hh
  rw [hh]
  change (extendZeroVector_memLp hK _).toLp _ = _
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall
    (congrFun (parameterSource_extension_differential hK hV hg hs k v hc))

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {p d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

def carrierSourceFamily {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hφ : ∀ c, ContDiffOn ℝ ∞ (φ c) U)
    (hf : ∀ c, ContDiffOn ℝ ∞ (f c) U)
    (hs : ∀ c, tsupport (f c) ⊆ U)
    (hc : ∀ c, HasCompactSupport (f c)) (c : P) : H :=
  InactiveSource.carrierSource hU ρ (φ c) (f c) (hφ c) (hf c) (hs c) (hc c)

theorem carrierSourceFamily_ae {U : Set E} (hU : IsOpen U)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hφ : ∀ c, ContDiffOn ℝ ∞ (φ c) U)
    (hf : ∀ c, ContDiffOn ℝ ∞ (f c) U)
    (hs : ∀ c, tsupport (f c) ⊆ U)
    (hc : ∀ c, HasCompactSupport (f c)) (c : P) :
    carrierSourceFamily hU ρ φ f hφ hf hs hc c =ᵐ[volume]
      parameterSourceFunction ρ φ f c :=
  InactiveSource.carrierSource_ae hU ρ (φ c) (f c) (hφ c) (hf c) (hs c) (hc c)

theorem iteratedFDeriv_carrierSourceFamily {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) {V : Set P} (hV : IsOpen V)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hφ : ∀ c, ContDiffOn ℝ ∞ (φ c) U)
    (hf : ∀ c, ContDiffOn ℝ ∞ (f c) U)
    (hs : ∀ c, tsupport (f c) ⊆ U)
    (hc : ∀ c, HasCompactSupport (f c))
    (hjoint : ContDiffOn ℝ ∞ (Function.uncurry (parameterSourceFunction ρ φ f))
      (V ×ˢ univ))
    (hsK : ∀ a ∈ V, tsupport (parameterSourceFunction ρ φ f a) ⊆ K)
    (k : ℕ) (v : Fin k → P) {c : P} (hcv : c ∈ V) :
    iteratedFDeriv ℝ k (fun a ↦ carrierSourceFamily hU ρ φ f hφ hf hs hc a) c v =
      (parameterSource_memLp hK hV hjoint hsK k v hcv).toLp
        (fun x ↦ iteratedFDeriv ℝ k
          (fun a ↦ parameterSourceFunction ρ φ f a x) c v) := by
  let hmem : ∀ a, MemLp (parameterSourceFunction ρ φ f a) 2 volume :=
    fun a ↦ InactiveSource.memLp_carrier_source hU ρ (φ a) (f a) (hφ a) (hf a) (hs a) (hc a)
  have he := iteratedFDeriv_parameterSourceClass hK hV hjoint hsK hmem k v hcv
  change iteratedFDeriv ℝ k (fun a ↦ (hmem a).toLp (parameterSourceFunction ρ φ f a)) c v = _
  exact he

/-- The finite carrier/source Leibniz estimate for actual parameter jets. The
carrier phase contributes only its own finite jet; the envelope jet is the
actual pointwise parameter derivative. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_parameterCarrierFunction_le
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F) (k : ℕ) (c : P) (x : E)
    (hcarrier : ContDiff ℝ ∞ (fun a ↦ carrier ρ (φ a) x))
    (hdata : ContDiff ℝ ∞ (fun a ↦ f a x)) :
    ‖iteratedFDeriv ℝ k (fun a ↦ parameterSourceFunction ρ φ f a x) c‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun a ↦ carrier ρ (φ a) x) c‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun a ↦ f a x) c‖ := by
  simpa only [parameterSourceFunction] using
    (norm_iteratedFDeriv_smul_le hcarrier hdata c
      (by simp : (k : ℕ∞ω) ≤ ∞))

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open InactiveSource FourierTransform
variable {d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

def maskMultiplyCLM (m : BoundedMask d) : H →L[ℂ] H := by
  let T : H →ₗ[ℂ] H := {
    toFun := m.multiply
    map_add' := by
      intro u v
      apply Lp.ext
      filter_upwards [m.multiply_ae (u + v), m.multiply_ae u, m.multiply_ae v,
        Lp.coeFn_add u v, Lp.coeFn_add (m.multiply u) (m.multiply v)] with x h h₁ h₂ h₃ h₄
      simp only [h, h₁, h₂, h₃, h₄, Pi.add_apply, smul_add]
    map_smul' := by
      intro c v
      apply Lp.ext
      filter_upwards [m.multiply_ae (c • v), m.multiply_ae v,
        Lp.coeFn_smul c v, Lp.coeFn_smul c (m.multiply v)] with x h h₁ h₂ h₃
      simp only [h, h₁, h₂, h₃, Pi.smul_apply, RingHom.id_apply]
      exact smul_comm _ _ _ }
  exact T.mkContinuous m.bound (fun v ↦ m.norm_multiply_le v)

def fourierMultiplierCLM (m : BoundedMask d) : H →L[ℂ] H :=
  (fourierInvCLM ℂ H).comp ((maskMultiplyCLM m.atUnitFrequency).comp (fourierCLM ℂ H))

theorem fourierMultiplierCLM_apply (m : BoundedMask d) (u : H) :
    fourierMultiplierCLM m u = m.fourierMultiplier u := by
  change (fourierInvCLM ℂ H)
      ((maskMultiplyCLM m.atUnitFrequency) ((fourierCLM ℂ H) u)) = _
  rfl

theorem iteratedFDeriv_maskMultiply_commute {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (m : BoundedMask d) {g : P → H} {k : ℕ} {c : P} (v : Fin k → P)
    (hg : ContDiffAt ℝ k g c) :
    iteratedFDeriv ℝ k (fun a ↦ maskMultiplyCLM m (g a)) c v =
      maskMultiplyCLM m (iteratedFDeriv ℝ k g c v) := by
  have h := (maskMultiplyCLM m).restrictScalars ℝ |>.iteratedFDeriv_comp_left hg
    (le_refl (k : ℕ∞ω))
  exact congrArg (fun z ↦ z v) h

theorem iteratedFDeriv_fourierMultiplier_commute {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (m : BoundedMask d) {g : P → H} {k : ℕ} {c : P} (v : Fin k → P)
    (hg : ContDiffAt ℝ k g c) :
    iteratedFDeriv ℝ k (fun a ↦ m.fourierMultiplier (g a)) c v =
      m.fourierMultiplier (iteratedFDeriv ℝ k g c v) := by
  have h := (fourierMultiplierCLM m).restrictScalars ℝ |>.iteratedFDeriv_comp_left hg
    (le_refl (k : ℕ∞ω))
  have hv := congrArg (fun z ↦ z v) h
  change iteratedFDeriv ℝ k (fun a ↦ m.fourierMultiplier (g a)) c v =
    m.fourierMultiplier (iteratedFDeriv ℝ k g c v) at hv
  exact hv

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open InactiveSource
variable {p d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

def parameterCarrierJet (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) (c : P) : E → F :=
  fun x ↦ carrier (-ρ) (φ c) x •
    iteratedFDeriv ℝ k (fun a ↦ parameterSourceFunction ρ φ f a x) c v

theorem carrier_mul_parameterCarrierJet (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) (c : P) (x : E) :
    carrier ρ (φ c) x • parameterCarrierJet ρ φ f k v c x =
      iteratedFDeriv ℝ k (fun a ↦ parameterSourceFunction ρ φ f a x) c v := by
  simp only [parameterCarrierJet, smul_smul]
  rw [mul_comm, carrier_neg_mul, one_smul]

/-- The normalized jet factors the actual differentiated carrier/source into
one fixed carrier and an actual envelope jet; no source derivative estimate is
assumed. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem carrierSourceJet_eq_actual_parameterDerivative
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) {V : Set P} (hV : IsOpen V)
    (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (hφ : ∀ c, ContDiffOn ℝ ∞ (φ c) U)
    (hjoint : ContDiffOn ℝ ∞ (Function.uncurry (parameterSourceFunction ρ φ f))
      (V ×ˢ univ))
    (hsK : ∀ a ∈ V, tsupport (parameterSourceFunction ρ φ f a) ⊆ K)
    (k : ℕ) (v : Fin k → P)
    (hjet : ∀ c, ContDiffOn ℝ ∞ (parameterCarrierJet ρ φ f k v c) U)
    (hjetSupport : ∀ c, tsupport (parameterCarrierJet ρ φ f k v c) ⊆ U)
    (hjetCompact : ∀ c, HasCompactSupport (parameterCarrierJet ρ φ f k v c))
    {c : P} (hcv : c ∈ V) :
    carrierSource hU ρ (φ c) (parameterCarrierJet ρ φ f k v c)
      (hφ c) (hjet c) (hjetSupport c) (hjetCompact c) =
      (parameterSource_memLp hK hV hjoint hsK k v hcv).toLp
        (fun x ↦ iteratedFDeriv ℝ k
          (fun a ↦ parameterSourceFunction ρ φ f a x) c v) := by
  let hjetMem := InactiveSource.memLp_carrier_source hU ρ (φ c)
    (parameterCarrierJet ρ φ f k v c) (hφ c) (hjet c)
    (hjetSupport c) (hjetCompact c)
  apply MemLp.toLp_congr
  filter_upwards [hjetMem.coeFn_toLp,
    (parameterSource_memLp hK hV hjoint hsK k v hcv).coeFn_toLp] with x hx hj
  exact carrier_mul_parameterCarrierJet ρ φ f k v c x

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {p d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Parameter differentiation preserves a common compact spatial support. -/
theorem tsupport_parameterCarrierJet_subset {K : Set E} (hK : IsCompact K)
    {V : Set P} (hV : IsOpen V) (ρ : ℝ) (φ : P → E → ℝ) (f : P → E → F)
    (k : ℕ) (v : Fin k → P) {c : P} (hcv : c ∈ V)
    (hsK : ∀ a ∈ V, tsupport (parameterSourceFunction ρ φ f a) ⊆ K) :
    tsupport (parameterCarrierJet ρ φ f k v c) ⊆ K := by
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  by_contra hn
  apply hx
  simp only [parameterCarrierJet]
  rw [parameterSource_differential_zero hV hsK k v hcv hn, smul_zero]

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives


namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open InactiveSource
open JanetCartan.Pseudodifferential
open JanetCartan.ArbitraryAccuracy
variable {d r : ℕ} {ι : Type*}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Compatibility alias for the inactive-source estimate on an arbitrary
supplied envelope family. This does NOT derive the profile of
`parameterCarrierJet` or assert decay of actual parameter derivatives.
The source-facing finite expansion and its quantitative Sobolev assembly are
separate obligations (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterJet_masked_carrierSource_arbitrary_precision
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (m : ι → BoundedMask d) (φ : ι → E → ℝ) (jet : ι → E → F)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) U) (hjet : ∀ i, ContDiff ℝ ∞ (jet i))
    (hsupport : ∀ i, tsupport (jet i) ⊆ S)
    (hjetLp : ∀ i, MemLp (jet i) 2 volume)
    (A K ρ : ι → ℝ) (c G M ν : ℝ) (P C : ℕ → ℝ)
    (hc : 0 < c) (hν : ν ∈ Set.Ioo (0 : ℝ) 1)
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i) (hρ : ∀ i, 1 ≤ ρ i)
    (hscale : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hmask : ∀ i, (m i).bound ≤ M)
    (hgap : ∀ i η, (m i).symbol η ≠ 0 → ∀ x ∈ U,
      c * (ρ i + ‖η‖) ≤ ‖ρ i • fderiv ℝ (φ i) x -
        InnerProductSpace.toDual ℝ E η‖)
    (hupper : ∀ i x, x ∈ U → ‖fderiv ℝ (φ i) x‖ ≤ G)
    (hP : ∀ j, 0 ≤ P j)
    (hphase : ∀ i x, x ∈ tsupport (jet i) → ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (φ i) x‖ ≤ P j * K i ^ j)
    (hmem : ∀ i (p : ℕ), MemVectorFourierSobolev (p : ℝ)
      ((hjetLp i).toLp (jet i)))
    (hprofile : ∀ i (p : ℕ), vectorFourierSobolevNorm (p : ℝ)
      ((hjetLp i).toLp (jet i)) ≤ C p * A i * K i ^ p)
    (s : ℝ) (hs : 0 ≤ s) :
    ∀ Q : ℝ, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      MemVectorFourierSobolev s ((m i).fourierMultiplier
        (InactiveSource.carrierSource hU (ρ i) (φ i) (jet i) (hφ i)
          (hjet i).contDiffOn ((hsupport i).trans hSU)
          (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i)))) ∧
      vectorFourierSobolevNorm s ((m i).fourierMultiplier
        (InactiveSource.carrierSource hU (ρ i) (φ i) (jet i) (hφ i)
          (hjet i).contDiffOn ((hsupport i).trans hSU)
          (hS.of_isClosed_subset (isClosed_tsupport _) (hsupport i)))) ≤
        D * A i * (ρ i) ^ (-Q) := by
  exact InactiveSource.masked_carrierSource_arbitrary_precision hU hS hSU m φ jet hφ
    hjet hsupport hjetLp A K ρ c G M ν P C hc hν hA hK hρ hscale hmask hgap hupper hP
    hphase hmem hprofile s hs

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {p d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- One parameter derivative of the literal carrier/source retains both the
carrier contribution and the original envelope derivative. -/
theorem hasLineDerivAt_parameterSourceFunction
    {P₀ : Type*} [NormedAddCommGroup P₀] [NormedSpace ℝ P₀]
    (ρ : ℝ) (φ : P₀ → E → ℝ) (f : P₀ → E → F) {c : P₀} (x : E) (v : P₀)
    (hφ : DifferentiableAt ℝ (fun a ↦ φ a x) c) (df : P₀ →L[ℝ] F)
    (hf : HasFDerivAt (fun a ↦ f a x) df c) :
    HasLineDerivAt ℝ (fun a ↦ carrier ρ (φ a) x • f a x)
      (((Complex.I * ((ρ * fderiv ℝ (fun a ↦ φ a x) c v : ℝ) : ℂ)) *
          carrier ρ (φ c) x) • f c x + carrier ρ (φ c) x • df v) c v := by
  have hc := (((Complex.ofRealCLM.hasFDerivAt.comp c
      (hφ.hasFDerivAt.const_mul ρ)).const_mul Complex.I).cexp)
  have hh := hc.smul hf
  have hl := hh.hasLineDerivAt v
  convert hl using 1
  · funext a
    simp [carrier]
  · simp [carrier, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, mul_comm, mul_left_comm]
    rw [add_comm]


end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {p d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => Euclidean p
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The fixed physical carrier multiplier commutes with every finite parameter
jet on the same Euclidean L² space. -/
theorem iteratedFDeriv_carrierMultiplication_commute
    {g : P → H} (ρ : ℝ) (φ : E → ℝ) (hφ : Continuous φ) {k : ℕ}
    {c : P} (v : Fin k → P) (hg : ContDiffAt ℝ k g c) :
    iteratedFDeriv ℝ k (fun a ↦ carrierMultiplication ρ φ hφ (g a)) c v =
      carrierMultiplication ρ φ hφ (iteratedFDeriv ℝ k g c v) := by
  have h := (carrierMultiplication ρ φ hφ).restrictScalars ℝ |>.iteratedFDeriv_comp_left hg
    (le_refl (k : ℕ∞ω))
  have hv := congrArg (fun z ↦ z v) h
  change iteratedFDeriv ℝ k (fun a ↦ carrierMultiplication ρ φ hφ (g a)) c v =
    carrierMultiplication ρ φ hφ (iteratedFDeriv ℝ k g c v) at hv
  exact hv

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives