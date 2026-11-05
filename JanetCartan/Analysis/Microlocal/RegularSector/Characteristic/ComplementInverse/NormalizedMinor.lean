module
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Regularity
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Homogeneity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Regularity
/-!
# Normalized minor nullvectors for the characteristic complement

The fixed adjugate column is divided by its selected nonzero coordinate. The
selected row is multiplied by the ratio of that minor to its original transport
coefficient. This constructs the degree-zero nullvectors and the normalization
`lᵀ A k = 1` in `app:ch_regular_base:lem:characteristic-kernel`, using the exact
minor and determinant-derivative APIs of `NullTransport`.

The compact-family theorem constructs a common interval and completion gap
from the original minor and transport gaps. It assumes no completed inverse
or budget for it. Consumers are the same `W₁` and `b₋₁ α` as in
`app:ch_regular_base:eq:complement-inverse`.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degree-zero right nullvector, with selected coordinate one
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def minorRightNullvector (H : Matrix ι ι ℝ) (r c : ι) : ι → ℝ :=
  (H.adjugate r c)⁻¹ • NullTransport.rightNullvector H c

/-- The original, unnormalized transport denominator. Its gap is produced
by `NullTransport.transportCoefficient_gap`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def minorTransportCoefficient (H A : Matrix ι ι ℝ) (r c : ι) : ℝ :=
  NullTransport.leftNullvector H r ⬝ᵥ (A *ᵥ NullTransport.rightNullvector H c)

/-- The degree-zero left nullvector with `lᵀ A k = 1`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def minorLeftNullvector (H A : Matrix ι ι ℝ) (r c : ι) : ι → ℝ :=
  (H.adjugate r c / minorTransportCoefficient H A r c) • NullTransport.leftNullvector H r

/-- The complement inverse for the actual normalized fixed-minor nullvectors
(`app:ch_regular_base:eq:complement-inverse`). -/
def minorComplementInverse (H A : Matrix ι ι ℝ) (r c : ι) (e : ℝ) : Matrix ι ι ℝ :=
  complementInverse H A (minorRightNullvector H r c) (minorLeftNullvector H A r c) e

/-- The characteristic equation and the two original nonzero denominators
produce every kernel/normalization input to the complement construction
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minor_normalization {H A : Matrix ι ι ℝ} {r c : ι}
    (hH : H.det = 0) (hm : H.adjugate r c ≠ 0) (ht : minorTransportCoefficient H A r c ≠ 0) :
    H *ᵥ minorRightNullvector H r c = 0 ∧ minorLeftNullvector H A r c ᵥ* H = 0 ∧
      minorLeftNullvector H A r c ⬝ᵥ (A *ᵥ minorRightNullvector H r c) = 1 ∧
      (∀ v, H *ᵥ v = 0 → ∃ a : ℝ, v = a • minorRightNullvector H r c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [minorRightNullvector, mulVec_smul, NullTransport.mulVec_rightNullvector hH]
  · simp [minorLeftNullvector, smul_vecMul, NullTransport.leftNullvector_vecMul hH]
  · simp only [minorRightNullvector, minorLeftNullvector, mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    change (H.adjugate r c)⁻¹ *
      ((H.adjugate r c / minorTransportCoefficient H A r c) * minorTransportCoefficient H A r c) = 1
    field_simp
  · intro v hv
    refine ⟨v r, ?_⟩
    simpa [minorRightNullvector, div_eq_mul_inv, smul_smul] using
      NullTransport.kernel_eq_smul_rightNullvector hH hm hv

/-- The determinant simple-root condition produces the original transport
denominator, using its exact minor factor
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minorTransportCoefficient_ne_zero_of_root {H A : Matrix ι ι ℝ} {r c : ι}
    (hH : H.det = 0) (hm : H.adjugate r c ≠ 0)
    (ht : fderiv ℝ Matrix.det H A ≠ 0) : minorTransportCoefficient H A r c ≠ 0 :=
  NullTransport.transportCoefficient_ne_zero hH hm ht

/-- Degree-zero homogeneity of the same selected right nullvector
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minorRightNullvector_smul (H : Matrix ι ι ℝ) (r c : ι) {a : ℝ} (ha : a ≠ 0) :
    minorRightNullvector (a • H) r c = minorRightNullvector H r c := by
  funext i
  simp only [minorRightNullvector, NullTransport.rightNullvector, adjugate_smul,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_inv_rev]
  field_simp

/-- Degree-zero homogeneity of the same normalized left nullvector
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minorLeftNullvector_smul (H A : Matrix ι ι ℝ) (r c : ι) {a : ℝ} (ha : a ≠ 0) :
    minorLeftNullvector (a • H) A r c = minorLeftNullvector H A r c := by
  have hr : NullTransport.rightNullvector (a • H) c =
      a ^ (Fintype.card ι - 1) • NullTransport.rightNullvector H c := by
    ext i
    simp [NullTransport.rightNullvector, adjugate_smul]
  have hl : NullTransport.leftNullvector (a • H) r =
      a ^ (Fintype.card ι - 1) • NullTransport.leftNullvector H r := by
    ext i
    simp [NullTransport.leftNullvector, adjugate_smul]
  have ht : minorTransportCoefficient (a • H) A r c =
      a ^ (Fintype.card ι - 1) * a ^ (Fintype.card ι - 1) * minorTransportCoefficient H A r c := by
    simp [minorTransportCoefficient, hr, hl, mulVec_smul, smul_dotProduct, dotProduct_smul, mul_assoc]
  ext i
  simp only [minorLeftNullvector, adjugate_smul, Matrix.smul_apply, smul_eq_mul, hl, ht, Pi.smul_apply]
  by_cases hd : minorTransportCoefficient H A r c = 0
  · simp [hd]
  · field_simp

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ∞ω}
/-- Smoothness of the normalized right nullvector on the original minor patch
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_minorRightNullvector {H : E → Matrix ι ι ℝ} (r c : ι)
    (hH : ∀ i j, ContDiffOn ℝ m (fun x ↦ H x i j) s)
    (hm : ∀ x ∈ s, (H x).adjugate r c ≠ 0) :
    ContDiffOn ℝ m (fun x ↦ minorRightNullvector (H x) r c) s :=
  ((NullTransport.contDiffOn_adjugate_entry hH r c).inv hm).smul
    (NullTransport.contDiffOn_rightNullvector hH c)

/-- Smoothness of the original transport denominator
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_minorTransportCoefficient {H A : E → Matrix ι ι ℝ} (r c : ι)
    (hH : ∀ i j, ContDiffOn ℝ m (fun x ↦ H x i j) s)
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s) :
    ContDiffOn ℝ m (fun x ↦ minorTransportCoefficient (H x) (A x) r c) s := by
  unfold minorTransportCoefficient Matrix.mulVec dotProduct
  apply ContDiffOn.sum
  intro i _
  apply (contDiffOn_pi.mp (NullTransport.contDiffOn_leftNullvector hH r) i).mul
  apply ContDiffOn.sum
  intro j _
  exact (hA i j).mul (contDiffOn_pi.mp (NullTransport.contDiffOn_rightNullvector hH c) j)

/-- Smoothness of the normalized left nullvector on the original transport
patch (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiffOn_minorLeftNullvector {H A : E → Matrix ι ι ℝ} (r c : ι)
    (hH : ∀ i j, ContDiffOn ℝ m (fun x ↦ H x i j) s)
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s)
    (ht : ∀ x ∈ s, minorTransportCoefficient (H x) (A x) r c ≠ 0) :
    ContDiffOn ℝ m (fun x ↦ minorLeftNullvector (H x) (A x) r c) s :=
  ((NullTransport.contDiffOn_adjugate_entry hH r c).div
    (contDiffOn_minorTransportCoefficient r c hH hA) ht).smul
      (NullTransport.contDiffOn_leftNullvector hH r)
/-- Joint smoothness of the actual normalized minor complement inverse, with
the original denominators explicit (`app:ch_regular_base:eq:complement-inverse`).
The compact-family constructor supplies the completion determinant condition. -/
theorem contDiffOn_minorComplementInverse {H A : E → Matrix ι ι ℝ} {e : E → ℝ}
    (r c : ι) (hH : ∀ i j, ContDiffOn ℝ m (fun x ↦ H x i j) s)
    (hA : ∀ i j, ContDiffOn ℝ m (fun x ↦ A x i j) s) (he : ContDiffOn ℝ m e s)
    (hm : ∀ x ∈ s, (H x).adjugate r c ≠ 0)
    (ht : ∀ x ∈ s, minorTransportCoefficient (H x) (A x) r c ≠ 0)
    (hd : ∀ x ∈ s, (pencilCompletion (H x) (A x) (minorRightNullvector (H x) r c)
      (minorLeftNullvector (H x) (A x) r c) (e x)).det ≠ 0) :
    ContDiffOn ℝ m (fun x ↦ minorComplementInverse (H x) (A x) r c (e x)) s :=
  contDiffOn_complementInverse hH hA (contDiffOn_minorRightNullvector r c hH hm)
    (contDiffOn_minorLeftNullvector r c hH hA ht) he hd
end Smooth

/-- Degree-minus-one homogeneity for the original pencil and its actual minor
nullvectors (`app:ch_regular_base:eq:complement-inverse`). -/
theorem minorComplementInverse_smul {H A : Matrix ι ι ℝ} {r c : ι} {e a : ℝ}
    (hH : H.det = 0) (hm : H.adjugate r c ≠ 0) (ht : minorTransportCoefficient H A r c ≠ 0)
    (hd : (pencilCompletion H A (minorRightNullvector H r c) (minorLeftNullvector H A r c) e).det ≠ 0)
    (ha : a ≠ 0) :
    minorComplementInverse (a • H) A r c (a * e) = a⁻¹ • minorComplementInverse H A r c e := by
  obtain ⟨hk, hl, hn, _⟩ := minor_normalization hH hm ht
  simpa only [minorComplementInverse, minorRightNullvector_smul _ _ _ ha, minorLeftNullvector_smul _ _ _ _ ha]
    using (complementInverse_smul hk hl hn hd ha).2

section Compact
variable {X : Type*} [TopologicalSpace X]
/-- A compact actual minor family has one interval and completion determinant
gap, derived from the characteristic equation and the fixed original minor/
transport gaps (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_uniform_minor_completion_gap (H A : X → Matrix ι ι ℝ)
    (hH : Continuous H) (hA : Continuous A) {K : Set X} (hK : IsCompact K)
    (r c : ι) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hroot : ∀ x ∈ K, (H x).det = 0)
    (hminor : ∀ x ∈ K, μ ≤ |(H x).adjugate r c|)
    (htransport : ∀ x ∈ K, ν ≤ |minorTransportCoefficient (H x) (A x) r c|) :
    ∃ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ e : ℝ, |e| ≤ ε →
      δ ≤ |(pencilCompletion (H x) (A x) (minorRightNullvector (H x) r c)
        (minorLeftNullvector (H x) (A x) r c) e).det| := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hH' : Continuous (fun x : K ↦ H x) := hH.comp continuous_subtype_val
  have hA' : Continuous (fun x : K ↦ A x) := hA.comp continuous_subtype_val
  have hm : ∀ x : K, (H x).adjugate r c ≠ 0 :=
    fun x ↦ abs_pos.mp (hμ.trans_le (hminor x x.property))
  have ht : ∀ x : K, minorTransportCoefficient (H x) (A x) r c ≠ 0 :=
    fun x ↦ abs_pos.mp (hν.trans_le (htransport x x.property))
  have hmcont : Continuous (fun x : K ↦ (H x).adjugate r c) :=
    (continuous_apply c).comp ((continuous_apply r).comp hH'.matrix_adjugate)
  have hrcont : Continuous (fun x : K ↦ NullTransport.rightNullvector (H x) c) := by
    apply continuous_pi
    intro i
    exact (continuous_apply c).comp ((continuous_apply i).comp hH'.matrix_adjugate)
  have hlcont : Continuous (fun x : K ↦ NullTransport.leftNullvector (H x) r) :=
    (continuous_apply r).comp hH'.matrix_adjugate
  have htcont : Continuous (fun x : K ↦ minorTransportCoefficient (H x) (A x) r c) := by
    unfold minorTransportCoefficient mulVec dotProduct
    fun_prop
  have hkcont : Continuous (fun x : K ↦ minorRightNullvector (H x) r c) :=
    (hmcont.inv₀ hm).smul hrcont
  have hlcont' : Continuous (fun x : K ↦ minorLeftNullvector (H x) (A x) r c) :=
    (hmcont.div htcont ht).smul hlcont
  obtain ⟨ε, hε, δ, hδ, hbound⟩ := exists_uniform_completion_gap
    (fun x : K ↦ H x) (fun x : K ↦ A x)
    (fun x : K ↦ minorRightNullvector (H x) r c) (fun x : K ↦ minorLeftNullvector (H x) (A x) r c)
    hH' hA' hkcont hlcont' isCompact_univ
    (fun x _ ↦ (minor_normalization (hroot x x.property) (hm x) (ht x)).2.1)
    (fun x _ ↦ (minor_normalization (hroot x x.property) (hm x) (ht x)).2.2.1)
    (fun x _ ↦ (minor_normalization (hroot x x.property) (hm x) (ht x)).2.2.2)
  exact ⟨ε, hε, δ, hδ, fun x hx e he ↦ hbound ⟨x, hx⟩ (mem_univ _) e he⟩
end Compact
end JanetCartan.RegularSector.Characteristic
