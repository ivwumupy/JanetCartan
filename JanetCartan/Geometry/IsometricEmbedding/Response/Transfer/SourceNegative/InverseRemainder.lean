module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureSource
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.EnvelopeJets.FourierNorm
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality
/-!
# The same inverse remainder on the original real source

The negative component source bound in
`ArbitraryAccuracy.inverse_remainder_restrictionSobolev` is discharged from
`SourceGeometry` and the original Sobolev envelope. Both real quadratures of
that source are restricted and zero extended on the original domain. The
same complete residual and Neumann inverse are used at every depth.

For the full history source, the geometry producer is
`exists_admissible_history_full_source_geometry`; its representative identity
preserves the original source. The fixed inverse producer
`exists_finite_direct_smooth_fixed_inverse` supplies the common forward and
literal-adjoint gain, and `exists_admissible_history_inverse_coefficient_profile`
supplies the displayed coefficient profile. Those producers still have to be
retained on one finite family. This deduction does not construct that family
or the whole compatible response (`app:ch_response:thm:response-compatible-choice`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace JanetCartan.ResponseTransfer.SourceNegative
open LocalSobolev Pseudodifferential ArbitraryAccuracy
open RegularSector.Characteristic.RetardedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "FR" => EuclideanSpace ℝ (Fin q)

/-- Substitute the proved ORIGINAL source decay into the SAME complete inverse's
remainder bound. The source norm is proved here from its existing geometry and
Sobolev envelope, with no negative-decay assumption on a residual output.
The common gain cost, coefficient shift, inverse constant and local-duality
constant are unchanged. The full window `1 ≤ L ≤ K ≤ lam^(1-ν)` includes `K = 1`.
This is the smoothing deduction consumed by the fixed finite expansion in
`app:ch_response:eq:response-graded-reduced`; the same-family gain and coefficient
profiles remain explicit producer inputs (`app:ch_regular:eq:inverse-remainder`). -/
theorem inverse_remainder_modulatedSource_real_quadrature
    {W : Set E} (hW : MeasurableSet W)
    (Kloc : LocalL2 W FR →L[ℝ] LocalL2 W FR)
    {C D a : ℕ → ℝ} {b : ℕ} {θ : ℝ}
    (hKloc : ‖Kloc‖ ≤ θ) (hθ : θ < 1)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hgain : ∀ j u, MemRestrictionSobolev W j u →
      (MemRestrictionSobolev W (j + 1) (Kloc u) ∧
        restrictionSobolevNorm W (j + 1) (Kloc u) ≤ C (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)) ∧
      (MemRestrictionSobolev W (j + 1) (Kloc.adjoint u) ∧
        restrictionSobolevNorm W (j + 1) (Kloc.adjoint u) ≤ C (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)))
    {χ φ : E → ℝ} {S : Set E} {c G L : ℝ} {P X : ℕ → ℝ}
    (g : SourceGeometry χ φ S c G L P X) (hSW : S ⊆ W)
    (hprofile : ∀ j, 1 + a (j + b) ≤ D j * L ^ j)
    {f : E → F} {hf : MemLp f 2 volume} {A K : ℝ} {Csource : ℕ → ℝ}
    (henv : SobolevEnvelopeBounds f hf A K Csource) (hLK : L ≤ K)
    {lam ν : ℝ} (hlam : 1 ≤ lam) (hν : 0 < ν) (hν1 : ν < 1)
    (hwindow : K ≤ lam ^ (1 - ν)) (N s : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    let source := modulatedSource χ φ f lam
    let hm := source_memLp g hf lam
    let h := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hm.toLp source))
    let CN := modulatedSourceNegativeConstant (d + 1) N S c G ν P X Csource
    MemRestrictionSobolev W s (neumannInverse Kloc ((Kloc ^ (N + s)) h)) ∧
    restrictionSobolevNorm W s (neumannInverse Kloc ((Kloc ^ (N + s)) h)) ≤
      (inverseTameConstant θ C s * (powerGainConstant C D s + D s) *
        ((localDualityConstant (d + 1) N (EuclideanSpace.basisFun (Fin q) ℝ) * CN) *
          powerGainConstant C D N)) * A * L ^ s * (L / lam) ^ N := by
  intro source hm h CN
  have hmem : MemVectorFourierSobolev (-(N : ℝ)) (hm.toLp source) :=
    fun _ ↦ memFourierSobolev_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg N)) _
  have hnegative : vectorFourierSobolevNorm (-(N : ℝ)) (hm.toLp source) ≤
      CN * A / lam ^ N := by
    rw [← Complement.InactiveSource.eLpNorm_weighted_vectorFourier _ _ hmem]
    convert modulatedSource_negative_sobolev g henv hLK hlam hν hν1 hwindow N using 1
    rw [Real.rpow_neg (by linarith : 0 ≤ lam), Real.rpow_natCast, div_eq_mul_inv]
  exact inverse_remainder_restrictionSobolev (EuclideanSpace.basisFun (Fin q) ℝ)
    hW Kloc hKloc hθ g.scale_one_le (by linarith) henv.amplitude_nonneg
    (modulatedSourceNegativeConstant_nonneg _ _ _ _ _ _ _ _ _ g.lower_pos.le
      g.cutoff_constants_nonneg henv.constants_nonneg)
    hC hC hD ha ham hprofile
    (fun j u hu ↦ (hgain j u hu).1.1) (fun j u hu ↦ (hgain j u hu).1.2)
    (fun j u hu ↦ (hgain j u hu).2.1) (fun j u hu ↦ (hgain j u hu).2.2)
    N s h ((modulatedSource_real_quadrature_negative_norm_le hW χ φ f lam
      (g.support_subset.trans hSW) hm N ζ hζ).trans hnegative)
end JanetCartan.ResponseTransfer.SourceNegative
