module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.AmplitudeInputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhaseInputs

/-!
# Primitive elapsed inputs on the retained selected witnesses

The phase and amplitude assemblers supply the retarded primitive grades for
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:eq:high-phase`, `app:ch_regular:eq:high-amplitude`,
`app:ch_regular:eq:chain-tail`). Their only analytic inputs are the original
coefficient profile and the literal certificates published by
`RegularSector.FiniteAssembly.exists_finite_direct_operator_bounds`.

Use `exists_selected_elapsed_phase_inputs` to choose the common covector
constants before the current coefficients and scales. The theorem
`exists_selected_buffered_elapsed_cutoffs` constructs each chart's smooth
cutoff on its original slab `3 * maskRadius / 4`. Apply
`exists_selected_elapsed_amplitude_inputs` to those cutoffs and constants;
its exact comparable-carrier equality then instantiates the phase assembler.
Thus the normalized phase germs, phase grades, residual grades and support
bounds use the same compact elapsed carriers. All profiles are uniform over
the fixed finite family, and all amplitude scale offsets are zero.

The constructed phase has both normalized joint and physical base grades.
Its physical supported germs discharge the noncomparable covector comparison.
The physical domain `Ua` is constructed and included in the explicit domain
of the physical residual grade. The original retained smooth extension is
used for the original regularizations, without assuming quantitative bounds
for that extension.

`selected_common_smooth_direct_residual` multiplies BOTH original coefficients
by the existing chart output plateau. Its direct residual is the plateau
times retained `W₂`, preserves the SAME `W₀`, `W₁` and full physical `PW₁`,
and agrees with the original residual under the common masks. The actual
conic seminorms imply both normalized and physical order-minus-one grades;
the comparable estimate is instantiated with that normalized profile.
The masks are `endpointOutputMask`, `chartInputMask`, and
`selectedEndpointMultiplier` at its literal doubled threshold. Both
orientations retain source-before-Fourier ordering.

`exists_selected_direct_residual_carriers` and
`selected_common_residual_retarded_buffer` provide the original lower source
buffer and upper output slab. The theorem
`selected_common_regularizations_aestronglyMeasurable` supplies forward and
literal-adjoint measurability for the SAME common-mask regularizations from
`exists_selected_common_graph_regularizations`.

The parent `jc-selected-complete-factor-grades` retains the actual protected
localizer instantiation, PDO inputs and final `CompleteFactor` application.
These elapsed deductions do not assert the unconditional localization theorem
or Theorem 1.1 (`app:ch_regular_base:eq:energy-complete-residual`).
-/
