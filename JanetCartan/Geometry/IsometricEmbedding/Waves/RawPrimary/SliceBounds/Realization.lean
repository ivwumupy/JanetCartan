module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.PhysicalOutput
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WeakDerivatives

/-!
# Weak jets of the constructed physical L² realization

For `app:ch_waves:eq:individual-raw-slice`, this connects the operator produced
by `exists_rawPhysicalSliceOperator` to the exact integral weak jets. The
operator's representative identity, supplied by that producer, is the only
connection premise. Smoothness, weak derivatives, and Sobolev membership are
proved from the original buffered physical charts, not assumed for the output.
The sharp positive-order norm bound remains a separate assembly obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Every physical L² realization produced by `exists_rawPhysicalSliceOperator`
has the original integral weak jets at every finite order. Restriction is of
that SAME L² class, and its whole-space extension is the literal measured raw
field (`app:ch_waves:eq:individual-raw-slice`). The `4K` Fourier-input ceiling
is used only before physical multiplication. -/
theorem exists_rawSliceRealization_sobolevExtensions
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {A : Euclidean n → Euclidean (n - 1) → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {ζ : Euclidean (n - 1)} {τ K : ℝ} (hζ : ζ ∈ V) (hK : 1 ≤ K)
    (hshift : ∀ η ∈ Metric.closedBall 0 (4 * K), ζ + τ • η ∈ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hdb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) (u : Lp F 2 (volume : Measure (Euclidean n)))
    (hu : u =ᵐ[volume] fun x ↦ (χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
      (weightedWideDensity d v) x) (Q : Set (Euclidean n)) :
    let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
      (weightedWideDensity d v) x
    let J := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity d v)
    let uQ := ((Lp.memLp u).restrict Q).toLp u
    (∀ s, LocalSobolev.MemRestrictionSobolev Q s uQ) ∧
      ∀ s, ∃ e : LocalSobolev.SobolevExtension Q s uQ, e.toFun = g ∧ e.jet = J := by
  obtain ⟨_, _, _, hw, hg, hJ⟩ := rawSlice_weightedWideDensity_regular
    hU hV hS hA hχ hχc hχU hζ hK hshift hd hM hdb v
  have hu' : (fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
      (weightedWideDensity d v) x) =ᵐ[volume] u := by
    filter_upwards [hu] with x hx
    rw [hx, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hres : (fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
      (weightedWideDensity d v) x) =ᵐ[volume.restrict Q] u := ae_restrict_of_ae hu'
  let e (s : ℕ) : LocalSobolev.SobolevExtension Q s (((Lp.memLp u).restrict Q).toLp u) :=
    { toFun := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity d v) x
      jet := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity d v)
      weakJet := hw s
      memLp_fun := hg
      memLp_jet := fun j _ ↦ hJ j
      restrict_eq := hres.trans
        (((Lp.memLp u).restrict Q).coeFn_toLp.symm) }
  exact ⟨fun s ↦ ⟨e s⟩, fun s ↦ ⟨e s, rfl, rfl⟩⟩

end JanetCartan.RawPrimary.SliceBounds
