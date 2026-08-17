/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.Sobolev.Periodic.Integration

/-!
# Spatial means on the normalized flat torus

The Haar volume on `UnitAddTorus d` has total mass one.  Thus the spatial mean is simply the
Bochner integral.  This file packages that normalization, subtraction of the mean, and the
corresponding orthogonal projection on real or complex `L²`.

The `L²` construction is intrinsic: its range is the orthogonal complement of the normalized
constant function.  Consequently it is contractive and does not choose pointwise representatives.
For complex `L²`, membership in this range is equivalent to vanishing of Mathlib's zero
multivariate Fourier coefficient.

As a first link with the smooth periodic calculus, the integral of an integrable smooth coordinate
derivative is zero.  This is the constant-test-function specialization of periodic integration by
parts, not a weak-derivative claim.

This advances Layer 0, item 3 and its mean-zero Poincare normalization prerequisite in the
`IncompressibleFlows` roadmap.  The projection argument is new library code; the elementary
mean-zero and coordinate-derivative statements generalize proof seeds from
`emberian/navier-stokes-proof` at commit `4daa9649e790893400ebbe6f5b805d13e7a6a6c7`.

## Main declarations

* `TauCeti.UnitAddTorus.mean`: the normalized spatial mean.
* `TauCeti.UnitAddTorus.meanZero`: subtraction of the spatial mean.
* `TauCeti.UnitAddTorus.meanZeroSubspaceL2`: the closed `L²` subspace orthogonal to constants.
* `TauCeti.UnitAddTorus.meanZeroProjectionL2`: the contractive orthogonal projection onto it.
* `TauCeti.UnitAddTorus.mFourierCoeff_zero_eq_mean`: the zero Fourier coefficient is the mean.
* `TauCeti.UnitAddTorus.integral_coordinateDerivative_eq_zero`: smooth coordinate derivatives
  have zero spatial integral.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory

variable {d : Type*} [Fintype d]

/- The default volume on `UnitAddCircle` has mass one.  Mathlib keeps the corresponding
probability instance local to its Fourier-series file, so install the product instance locally
for the normalized unit torus API in this module. -/
local instance unitAddTorusIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure (_root_.UnitAddTorus d)) :=
  ⟨by
    rw [show (volume : Measure (_root_.UnitAddTorus d)) =
      Measure.pi (fun _ : d ↦ (volume : Measure _root_.UnitAddCircle)) from
        MeasureTheory.volume_pi]
    simp [AddCircle.volume_eq_smul_haarAddCircle]⟩

/-- The default product volume on the unit torus is the product of Mathlib's normalized circle
Haar measures.  This bridges the default `volume` notation to `UnitAddTorus.mFourierCoeff`, whose
implementation installs the normalized circle measure locally. -/
theorem volume_eq_pi_haarAddCircle :
    (volume : Measure (_root_.UnitAddTorus d)) =
      Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle) := by
  rw [show (volume : Measure (_root_.UnitAddTorus d)) =
    Measure.pi (fun _ : d ↦ (volume : Measure _root_.UnitAddCircle)) from
      MeasureTheory.volume_pi]
  congr 1
  funext i
  simp [AddCircle.volume_eq_smul_haarAddCircle]

section Mean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spatial mean on the normalized unit torus.  Haar volume has total mass one, so no
additional volume factor occurs. -/
def mean (f : _root_.UnitAddTorus d → E) : E :=
  ∫ x, f x

/-- On the unit torus, the spatial mean agrees with the measure-theoretic average because Haar
volume is a probability measure. -/
theorem mean_eq_average (f : _root_.UnitAddTorus d → E) :
    mean f = ⨍ x, f x := by
  rw [mean, average_eq_integral]

variable [CompleteSpace E]

@[simp]
theorem mean_const (c : E) : mean (fun _ : _root_.UnitAddTorus d ↦ c) = c := by
  simp [mean]

/-- Subtract the normalized spatial mean from a torus field. -/
def meanZero (f : _root_.UnitAddTorus d → E) (x : _root_.UnitAddTorus d) : E :=
  f x - mean f

@[simp]
theorem meanZero_const (c : E) : meanZero (fun _ : _root_.UnitAddTorus d ↦ c) = 0 := by
  ext x
  simp [meanZero]

omit [CompleteSpace E] in
/-- Subtracting the spatial mean preserves integrability. -/
theorem Integrable.meanZero {f : _root_.UnitAddTorus d → E} (hf : Integrable f) :
    Integrable (meanZero f) :=
  hf.sub (integrable_const _)

/-- Subtracting the spatial mean from an integrable field produces a mean-zero field. -/
@[simp]
theorem mean_meanZero (f : _root_.UnitAddTorus d → E) (hf : Integrable f) :
    mean (meanZero f) = 0 := by
  unfold meanZero mean
  rw [integral_sub hf (integrable_const _), integral_const]
  simp

@[simp]
theorem meanZero_meanZero (f : _root_.UnitAddTorus d → E) (hf : Integrable f) :
    meanZero (meanZero f) = meanZero f := by
  ext x
  simp [meanZero, mean_meanZero f hf]

omit [CompleteSpace E] in
theorem meanZero_eq_self_iff (f : _root_.UnitAddTorus d → E) (_hf : Integrable f) :
    meanZero f = f ↔ mean f = 0 := by
  constructor
  · intro h
    have hx := congrFun h (0 : _root_.UnitAddTorus d)
    exact sub_eq_self.mp hx
  · intro h
    ext x
    simp [meanZero, h]

end Mean

section FourierZeroMode

/-- Mathlib's zero multivariate Fourier coefficient is exactly the normalized spatial mean. -/
@[simp]
theorem mFourierCoeff_zero_eq_mean (f : _root_.UnitAddTorus d → ℂ) :
    _root_.UnitAddTorus.mFourierCoeff f 0 = mean f := by
  unfold _root_.UnitAddTorus.mFourierCoeff
  simp only [neg_zero, _root_.UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
  change (∫ t, f t ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)) = ∫ t, f t
  rw [← volume_eq_pi_haarAddCircle]

theorem mean_eq_zero_iff_mFourierCoeff_zero_eq_zero (f : _root_.UnitAddTorus d → ℂ) :
    mean f = 0 ↔ _root_.UnitAddTorus.mFourierCoeff f 0 = 0 := by
  rw [mFourierCoeff_zero_eq_mean]

@[simp]
theorem mFourierCoeff_meanZero_zero (f : _root_.UnitAddTorus d → ℂ) (hf : Integrable f) :
    _root_.UnitAddTorus.mFourierCoeff (meanZero f) 0 = 0 := by
  rw [mFourierCoeff_zero_eq_mean, mean_meanZero f hf]

end FourierZeroMode

section L2Projection

variable {𝕜 : Type*} [RCLike 𝕜]

local notation "TorusL²" =>
  Lp 𝕜 2 (volume : Measure (_root_.UnitAddTorus d))

/-- The real or complex `L²` subspace of unit-torus fields with zero spatial mean.  It is defined
as the orthogonal complement of the normalized constant function, so closedness and the
orthogonal projection are supplied by Hilbert-space geometry. -/
def meanZeroSubspaceL2 : Submodule 𝕜 TorusL² :=
  (𝕜 ∙ Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜))ᗮ

private noncomputable instance constantL2SpanHasOrthogonalProjection :
    (𝕜 ∙ Lp.const 2
      (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜)).HasOrthogonalProjection := by
  let K : Submodule 𝕜 TorusL² :=
    𝕜 ∙ Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜)
  let hK : CompleteSpace K := FiniteDimensional.complete 𝕜 K
  exact @Submodule.HasOrthogonalProjection.ofCompleteSpace 𝕜 TorusL² _ _ _ K hK

private noncomputable instance meanZeroSubspaceL2HasOrthogonalProjection :
    (meanZeroSubspaceL2 (d := d) (𝕜 := 𝕜)).HasOrthogonalProjection := by
  change Submodule.HasOrthogonalProjection
    ((𝕜 ∙ Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜))ᗮ)
  infer_instance

theorem mem_meanZeroSubspaceL2_iff (f : TorusL²) :
    f ∈ meanZeroSubspaceL2 (d := d) (𝕜 := 𝕜) ↔ ∫ x, f x = 0 := by
  rw [meanZeroSubspaceL2, Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [← indicatorConstLp_univ]
  rw [L2.inner_indicatorConstLp_one]
  simp

/-- Orthogonal projection of real or complex `L²` onto the zero-mean subspace. -/
def meanZeroProjectionL2 : TorusL² →L[𝕜] TorusL² :=
  (meanZeroSubspaceL2 (d := d) (𝕜 := 𝕜)).starProjection

theorem meanZeroProjectionL2_mem (f : TorusL²) :
    meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f ∈
      meanZeroSubspaceL2 (d := d) (𝕜 := 𝕜) :=
  Submodule.starProjection_apply_mem _ _

@[simp]
theorem integral_meanZeroProjectionL2 (f : TorusL²) :
    ∫ x, meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f x = 0 :=
  (mem_meanZeroSubspaceL2_iff _).mp (meanZeroProjectionL2_mem f)

theorem meanZeroProjectionL2_eq_self_iff (f : TorusL²) :
    meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f = f ↔ ∫ x, f x = 0 := by
  rw [meanZeroProjectionL2, Submodule.starProjection_eq_self_iff,
    mem_meanZeroSubspaceL2_iff]

@[simp]
theorem meanZeroProjectionL2_idem (f : TorusL²) :
    meanZeroProjectionL2 (d := d) (𝕜 := 𝕜)
      (meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f) =
        meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f := by
  rw [meanZeroProjectionL2_eq_self_iff, integral_meanZeroProjectionL2]

theorem norm_meanZeroProjectionL2_apply_le (f : TorusL²) :
    ‖meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f‖ ≤ ‖f‖ :=
  (meanZeroSubspaceL2 (d := d) (𝕜 := 𝕜)).norm_starProjection_apply_le f

theorem norm_meanZeroProjectionL2_le :
    ‖meanZeroProjectionL2 (d := d) (𝕜 := 𝕜)‖ ≤ 1 :=
  (meanZeroSubspaceL2 (d := d) (𝕜 := 𝕜)).starProjection_norm_le

/-- The intrinsic `L²` projection has the expected formula: subtract the constant field whose
value is the spatial integral. -/
theorem meanZeroProjectionL2_apply (f : TorusL²) :
    meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f =
      f - (∫ x, f x) • Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜) := by
  change Submodule.starProjection
    ((𝕜 ∙ Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜))ᗮ) f = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton]
  · rw [← indicatorConstLp_univ]
    simp only [L2.inner_indicatorConstLp_one, setIntegral_univ]
  · simp [Lp.norm_const]

/-- Representative-level formula for the `L²` projection, stated only almost everywhere. -/
theorem coeFn_meanZeroProjectionL2 (f : TorusL²) :
    meanZeroProjectionL2 (d := d) (𝕜 := 𝕜) f =ᵐ[volume]
      fun x ↦ f x - ∫ y, f y := by
  rw [meanZeroProjectionL2_apply]
  filter_upwards [Lp.coeFn_sub f _, Lp.coeFn_smul (∫ y, f y)
    (Lp.const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜)),
    Lp.coeFn_const 2 (volume : Measure (_root_.UnitAddTorus d)) (1 : 𝕜)] with
      x hsub hsmul hconst
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hconst]
  simp

end L2Projection

section ComplexL2Fourier

local notation "ComplexTorusL²" =>
  Lp ℂ 2 (volume : Measure (_root_.UnitAddTorus d))

theorem mem_meanZeroSubspaceL2_iff_mFourierCoeff_zero (f : ComplexTorusL²) :
    f ∈ meanZeroSubspaceL2 (d := d) (𝕜 := ℂ) ↔
      _root_.UnitAddTorus.mFourierCoeff f 0 = 0 := by
  rw [mem_meanZeroSubspaceL2_iff]
  exact mean_eq_zero_iff_mFourierCoeff_zero_eq_zero f

@[simp]
theorem mFourierCoeff_meanZeroProjectionL2_zero (f : ComplexTorusL²) :
    _root_.UnitAddTorus.mFourierCoeff
      (meanZeroProjectionL2 (d := d) (𝕜 := ℂ) f) 0 = 0 := by
  rw [← mean_eq_zero_iff_mFourierCoeff_zero_eq_zero]
  exact integral_meanZeroProjectionL2 f

end ComplexL2Fourier

section CoordinateDerivative

variable [DecidableEq d]

/-- An integrable classical coordinate derivative has zero normalized spatial integral.  The
slice-wise `C¹` hypothesis is exactly the one used by smooth periodic integration by parts. -/
theorem integral_coordinateDerivative_eq_zero
    (f : _root_.UnitAddTorus d → ℝ) (i : d)
    (hf : ContDiffAlongCoordinate f i)
    (hderiv : Integrable (coordinateDerivative f i)) :
    ∫ x, coordinateDerivative f i x = 0 := by
  have hconst : ContDiffAlongCoordinate (fun _ : _root_.UnitAddTorus d ↦ (1 : ℝ)) i := by
    exact contDiffAlongCoordinate_const 1 i
  have h := integral_mul_coordinateDerivative_eq_neg
    (fun _ : _root_.UnitAddTorus d ↦ (1 : ℝ)) f i hconst hf
    (by simpa using hderiv) (by simp)
  simpa using h

end CoordinateDerivative

end TauCeti.UnitAddTorus
