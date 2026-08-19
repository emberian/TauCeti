/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.WeakDeriv

/-!
# Fourier modes as periodic coordinate test functions

This file connects Mathlib's multivariate unit-torus Fourier modes with Tau Ceti's intrinsic
coordinate calculus.  A mode factors into its selected circle character and a constant transverse
factor.  Its exact coordinate derivative is multiplication by `2 * π * I * m i`.

Since `HasWeakCoordinateDerivative` is real-valued, the real and imaginary parts of a complex
Fourier mode are packaged separately as bounded coordinate test functions.  Their derivative
formulas retain the complex expression before taking real or imaginary parts, which pins both the
unit-period `2π` normalization and its sign.

This advances Layer 0, item 3 and the periodic-gradient Fourier-mode acceptance check in the
`IncompressibleFlows` roadmap.

## Main declarations

* `UnitAddTorus.mFourier_coordinateSplit_symm_coe`: factorization along one coordinate.
* `UnitAddTorus.coordinateDerivative_mFourier_re`: derivative of a mode's real part.
* `UnitAddTorus.coordinateDerivative_mFourier_im`: derivative of a mode's imaginary part.
* `UnitAddTorus.mFourierReCoordinateTest`: real part as a coordinate test function.
* `UnitAddTorus.mFourierImCoordinateTest`: imaginary part as a coordinate test function.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A multivariate Fourier mode factors into its selected circle character and a constant
transverse product. -/
theorem mFourier_coordinateSplit_symm_coe (m : d → ℤ) (i : d)
    (y : CoordinateComplement d i) (r : ℝ) :
    _root_.UnitAddTorus.mFourier m
        ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y)) =
      _root_.fourier (m i) (r : _root_.UnitAddCircle) *
        ∏ j : {j : d // j ≠ i}, _root_.fourier (m j) (y j) := by
  rw [_root_.UnitAddTorus.mFourier]
  change (∏ j : d, _root_.fourier (m j)
    ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y) j)) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  congr 1
  · rw [coordinateSplit_symm_apply_same]
  · apply Finset.prod_congr rfl
    intro j _
    rw [coordinateSplit_symm_apply_ne]

theorem contDiffAlongCoordinate_mFourier_re (m : d → ℤ) (i : d) :
    ContDiffAlongCoordinate
      (fun x : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m x).re) i := by
  apply contDiffAlongCoordinate_of_coordinateSplit
  intro y
  rw [show (fun r : ℝ ↦ (_root_.UnitAddTorus.mFourier m
      ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y))).re) =
    fun r : ℝ ↦ (_root_.fourier (m i) (r : _root_.UnitAddCircle) *
      ∏ j : {j : d // j ≠ i}, _root_.fourier (m j) (y j)).re by
        funext r
        exact congrArg Complex.re (mFourier_coordinateSplit_symm_coe m i y r)]
  simp_rw [_root_.fourier_coe_apply]
  have h : ContDiff ℝ 1 (fun r : ℝ ↦
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m i : ℂ) * (r : ℂ) / (1 : ℂ)) *
        ∏ j : {j : d // j ≠ i}, _root_.fourier (m j) (y j)) := by
    have hr : ContDiff ℝ 1 (fun r : ℝ ↦ (r : ℂ)) := Complex.ofRealCLM.contDiff
    exact ((contDiff_const.mul hr).div_const _).cexp.mul contDiff_const
  simpa [Function.comp_def] using Complex.reCLM.contDiff.comp h

theorem contDiffAlongCoordinate_mFourier_im (m : d → ℤ) (i : d) :
    ContDiffAlongCoordinate
      (fun x : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m x).im) i := by
  apply contDiffAlongCoordinate_of_coordinateSplit
  intro y
  rw [show (fun r : ℝ ↦ (_root_.UnitAddTorus.mFourier m
      ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y))).im) =
    fun r : ℝ ↦ (_root_.fourier (m i) (r : _root_.UnitAddCircle) *
      ∏ j : {j : d // j ≠ i}, _root_.fourier (m j) (y j)).im by
        funext r
        exact congrArg Complex.im (mFourier_coordinateSplit_symm_coe m i y r)]
  simp_rw [_root_.fourier_coe_apply]
  have h : ContDiff ℝ 1 (fun r : ℝ ↦
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m i : ℂ) * (r : ℂ) / (1 : ℂ)) *
        ∏ j : {j : d // j ≠ i}, _root_.fourier (m j) (y j)) := by
    have hr : ContDiff ℝ 1 (fun r : ℝ ↦ (r : ℂ)) := Complex.ofRealCLM.contDiff
    exact ((contDiff_const.mul hr).div_const _).cexp.mul contDiff_const
  simpa [Function.comp_def] using Complex.imCLM.contDiff.comp h

private theorem hasDerivAt_mFourier_coordinateSlice (m : d → ℤ) (i : d)
    (y : CoordinateComplement d i) (r : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ _root_.UnitAddTorus.mFourier m
        ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y)))
      (2 * Real.pi * Complex.I * (m i) *
        _root_.UnitAddTorus.mFourier m
          ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y))) r := by
  let C : ℂ := ∏ j : {j : d // j ≠ i}, _root_.fourier (m j) (y j)
  have hfun : (fun s : ℝ ↦ _root_.UnitAddTorus.mFourier m
      ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y))) =
      fun s : ℝ ↦ _root_.fourier (m i) (s : _root_.UnitAddCircle) * C := by
    funext s
    exact mFourier_coordinateSplit_symm_coe m i y s
  have h := (_root_.hasDerivAt_fourier 1 (m i) r).mul_const C
  rw [← hfun] at h
  apply h.congr_deriv
  rw [mFourier_coordinateSplit_symm_coe]
  simp only [C]
  norm_num
  ring

private theorem hasDerivAt_mFourier_coordinateSlice_re (m : d → ℤ) (i : d)
    (y : CoordinateComplement d i) (r : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ (_root_.UnitAddTorus.mFourier m
        ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y))).re)
      (2 * Real.pi * Complex.I * (m i) *
        _root_.UnitAddTorus.mFourier m
          ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y))).re r := by
  have h := hasDerivAt_mFourier_coordinateSlice m i y r
  simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h

private theorem hasDerivAt_mFourier_coordinateSlice_im (m : d → ℤ) (i : d)
    (y : CoordinateComplement d i) (r : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ (_root_.UnitAddTorus.mFourier m
        ((coordinateSplit i).symm ((s : _root_.UnitAddCircle), y))).im)
      (2 * Real.pi * Complex.I * (m i) *
        _root_.UnitAddTorus.mFourier m
          ((coordinateSplit i).symm ((r : _root_.UnitAddCircle), y))).im r := by
  have h := hasDerivAt_mFourier_coordinateSlice m i y r
  simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h

/-- The real part of a unit-torus Fourier mode has coordinate derivative equal to the real part
of multiplication by `2 * π * I * m i`. -/
theorem coordinateDerivative_mFourier_re (m : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) :
    coordinateDerivative
      (fun z : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m z).re) i x =
      (2 * Real.pi * Complex.I * (m i) * _root_.UnitAddTorus.mFourier m x).re := by
  apply congrFun (coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
    (fun z : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m z).re)
    (fun z : _root_.UnitAddTorus d ↦
      (2 * Real.pi * Complex.I * (m i) * _root_.UnitAddTorus.mFourier m z).re) i ?_) x
  intro y r
  exact hasDerivAt_mFourier_coordinateSlice_re m i y r

/-- The imaginary part of a unit-torus Fourier mode has coordinate derivative equal to the
imaginary part of multiplication by `2 * π * I * m i`. -/
theorem coordinateDerivative_mFourier_im (m : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) :
    coordinateDerivative
      (fun z : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m z).im) i x =
      (2 * Real.pi * Complex.I * (m i) * _root_.UnitAddTorus.mFourier m x).im := by
  apply congrFun (coordinateDerivative_eq_of_hasDerivAt_coordinateSplit
    (fun z : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m z).im)
    (fun z : _root_.UnitAddTorus d ↦
      (2 * Real.pi * Complex.I * (m i) * _root_.UnitAddTorus.mFourier m z).im) i ?_) x
  intro y r
  exact hasDerivAt_mFourier_coordinateSlice_im m i y r

/-- The real part of a Fourier mode, packaged as an admissible real weak-coordinate test
function. -/
@[expose]
def mFourierReCoordinateTest (m : d → ℤ) (i : d) : CoordinateTestFunction d i where
  toFun := fun x ↦ (_root_.UnitAddTorus.mFourier m x).re
  contDiffAlongCoordinate := contDiffAlongCoordinate_mFourier_re m i
  memLp_top :=
    (Complex.continuous_re.comp
      (_root_.UnitAddTorus.mFourier m).continuous).memLp_top_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)) volume
  coordinateDerivative_memLp_top := by
    rw [show coordinateDerivative
        (fun x : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m x).re) i =
      fun x ↦ (2 * Real.pi * Complex.I * (m i) *
        _root_.UnitAddTorus.mFourier m x).re by
          funext x
          exact coordinateDerivative_mFourier_re m i x]
    exact (Complex.continuous_re.comp
      (continuous_const.mul
        (_root_.UnitAddTorus.mFourier m).continuous)).memLp_top_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)) volume

/-- The imaginary part of a Fourier mode, packaged as an admissible real weak-coordinate test
function. -/
@[expose]
def mFourierImCoordinateTest (m : d → ℤ) (i : d) : CoordinateTestFunction d i where
  toFun := fun x ↦ (_root_.UnitAddTorus.mFourier m x).im
  contDiffAlongCoordinate := contDiffAlongCoordinate_mFourier_im m i
  memLp_top :=
    (Complex.continuous_im.comp
      (_root_.UnitAddTorus.mFourier m).continuous).memLp_top_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)) volume
  coordinateDerivative_memLp_top := by
    rw [show coordinateDerivative
        (fun x : _root_.UnitAddTorus d ↦ (_root_.UnitAddTorus.mFourier m x).im) i =
      fun x ↦ (2 * Real.pi * Complex.I * (m i) *
        _root_.UnitAddTorus.mFourier m x).im by
          funext x
          exact coordinateDerivative_mFourier_im m i x]
    exact (Complex.continuous_im.comp
      (continuous_const.mul
        (_root_.UnitAddTorus.mFourier m).continuous)).memLp_top_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)) volume

@[simp]
theorem mFourierReCoordinateTest_apply (m : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) :
    mFourierReCoordinateTest m i x = (_root_.UnitAddTorus.mFourier m x).re :=
  rfl

@[simp]
theorem mFourierImCoordinateTest_apply (m : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) :
    mFourierImCoordinateTest m i x = (_root_.UnitAddTorus.mFourier m x).im :=
  rfl

@[simp]
theorem coordinateDerivative_mFourierReCoordinateTest (m : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) :
    coordinateDerivative (mFourierReCoordinateTest m i) i x =
      (2 * Real.pi * Complex.I * (m i) * _root_.UnitAddTorus.mFourier m x).re :=
  coordinateDerivative_mFourier_re m i x

@[simp]
theorem coordinateDerivative_mFourierImCoordinateTest (m : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) :
    coordinateDerivative (mFourierImCoordinateTest m i) i x =
      (2 * Real.pi * Complex.I * (m i) * _root_.UnitAddTorus.mFourier m x).im :=
  coordinateDerivative_mFourier_im m i x

end UnitAddTorus
