/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.Galerkin
public import TauCeti.Analysis.VectorField.Flat.Weak

/-!
# Smooth representatives for periodic Galerkin fields

Finite real Fourier synthesis in periodic vector `W¹,²` has an explicit trigonometric
representative.  This file proves that the representative is coordinatewise `C¹`, computes its
classical derivatives with the same positive `2π I kᵢ` multiplier as the weak derivative, and
identifies it almost everywhere with the quotient-level synthesized field.

This is the smooth-representative bridge needed before weak divergence constraints and smooth
transport cancellation can be transferred to finite Galerkin syntheses.  Pointwise
incompressibility, nonlinear energy cancellation for these representatives, a quotient-level
quadratic nonlinearity, and the finite-dimensional Galerkin ODE are not yet proved here.

## Main declarations

* `PeriodicW12.realMFourierAtomRepresentative`: an explicit real Fourier atom representative.
* `PeriodicW12.coordinateDerivative_realMFourierAtomRepresentative`: its exact derivative.
* `PeriodicVectorW12.realTrigonometricRepresentative`: the explicit finite synthesis.
* `PeriodicVectorW12.contDiffVectorField_realTrigonometricRepresentative`: coordinatewise `C¹`.
* `PeriodicVectorW12.componentDerivative_realTrigonometricRepresentative`: its exact derivative.
* `PeriodicVectorW12.realTrigonometricRepresentative_ae`: agreement with `W¹,²` synthesis.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped BigOperators

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq
attribute [local instance] unitAddTorusIsProbabilityMeasure

namespace PeriodicW12

/-- The explicit real-valued representative of one complex-amplitude Fourier atom. -/
def realMFourierAtomRepresentative (a : ℂ) (k : d → ℤ) : ScalarField d :=
  fun x ↦ (a * _root_.UnitAddTorus.mFourier k x).re

@[simp]
theorem realMFourierAtomRepresentative_apply (a : ℂ) (k : d → ℤ)
    (x : _root_.UnitAddTorus d) :
    realMFourierAtomRepresentative a k x =
      (a * _root_.UnitAddTorus.mFourier k x).re := by
  rfl

/-- A real Fourier atom representative is continuous. -/
theorem continuous_realMFourierAtomRepresentative (a : ℂ) (k : d → ℤ) :
    Continuous (realMFourierAtomRepresentative a k) :=
  Complex.continuous_re.comp
    (continuous_const.mul (_root_.UnitAddTorus.mFourier k).continuous)

/-- A real Fourier atom representative is `C¹` along every coordinate. -/
theorem contDiffAlongCoordinate_realMFourierAtomRepresentative
    (a : ℂ) (k : d → ℤ) (i : d) :
    ContDiffAlongCoordinate (realMFourierAtomRepresentative a k) i := by
  rw [show realMFourierAtomRepresentative a k = fun x ↦
      a.re * (_root_.UnitAddTorus.mFourier k x).re -
        a.im * (_root_.UnitAddTorus.mFourier k x).im by
    funext x
    rw [realMFourierAtomRepresentative_apply, Complex.mul_re]]
  exact ((contDiffAlongCoordinate_mFourier_re k i).const_smul a.re).sub
    ((contDiffAlongCoordinate_mFourier_im k i).const_smul a.im)

/-- The classical coordinate derivative of a real Fourier atom has the exact positive
`2π I kᵢ` multiplier. -/
theorem coordinateDerivative_realMFourierAtomRepresentative
    (a : ℂ) (k : d → ℤ) (i : d) :
    coordinateDerivative (realMFourierAtomRepresentative a k) i =
      fun x ↦ (2 * Real.pi * Complex.I * (k i) * a *
        _root_.UnitAddTorus.mFourier k x).re := by
  have hre := contDiffAlongCoordinate_mFourier_re k i
  have him := contDiffAlongCoordinate_mFourier_im k i
  rw [show realMFourierAtomRepresentative a k = fun x ↦
      a.re * (_root_.UnitAddTorus.mFourier k x).re -
        a.im * (_root_.UnitAddTorus.mFourier k x).im by
    funext x
    rw [realMFourierAtomRepresentative_apply, Complex.mul_re],
    coordinateDerivative_sub _ _ i (hre.const_smul a.re) (him.const_smul a.im),
    coordinateDerivative_const_smul _ a.re i hre,
    coordinateDerivative_const_smul _ a.im i him]
  funext x
  change a.re * coordinateDerivative (fun x ↦
      (_root_.UnitAddTorus.mFourier k x).re) i x -
    a.im * coordinateDerivative (fun x ↦
      (_root_.UnitAddTorus.mFourier k x).im) i x = _
  rw [coordinateDerivative_mFourier_re, coordinateDerivative_mFourier_im]
  rw [show 2 * Real.pi * Complex.I * (k i) * a *
      _root_.UnitAddTorus.mFourier k x =
        a * (2 * Real.pi * Complex.I * (k i) *
          _root_.UnitAddTorus.mFourier k x) by ring]
  let z := 2 * Real.pi * Complex.I * (k i) * _root_.UnitAddTorus.mFourier k x
  change a.re * z.re - a.im * z.im = (a * z).re
  exact (Complex.mul_re a z).symm

end PeriodicW12

namespace PeriodicVectorW12

/-- The explicit smooth vector field associated with finite real Fourier coefficients. -/
def realTrigonometricRepresentative (S : Finset (d → ℤ)) (a : d → S → ℂ) :
    VectorField d :=
  fun x j ↦ ∑ k : S, PeriodicW12.realMFourierAtomRepresentative (a j k) k.1 x

@[simp]
theorem realTrigonometricRepresentative_apply (S : Finset (d → ℤ)) (a : d → S → ℂ)
    (x : _root_.UnitAddTorus d) (j : d) :
    realTrigonometricRepresentative S a x j =
      ∑ k : S, PeriodicW12.realMFourierAtomRepresentative (a j k) k.1 x := by
  rfl

/-- Every component of an explicit finite real Fourier representative is continuous. -/
theorem continuous_realTrigonometricRepresentative_component
    (S : Finset (d → ℤ)) (a : d → S → ℂ) (j : d) :
    Continuous (fun x ↦ realTrigonometricRepresentative S a x j) := by
  apply continuous_finsetSum
  intro k _
  exact PeriodicW12.continuous_realMFourierAtomRepresentative (a j k) k.1

/-- An explicit finite real Fourier representative is coordinatewise `C¹`. -/
theorem contDiffVectorField_realTrigonometricRepresentative
    (S : Finset (d → ℤ)) (a : d → S → ℂ) :
    ContDiffVectorField (realTrigonometricRepresentative S a) := by
  apply contDiffVectorField_of_components
  intro i j
  simpa only [realTrigonometricRepresentative_apply] using
    (ContDiffAlongCoordinate.finsetSum Finset.univ
      (fun k : S ↦ PeriodicW12.realMFourierAtomRepresentative (a j k) k.1) i
      (fun k _ ↦
        PeriodicW12.contDiffAlongCoordinate_realMFourierAtomRepresentative (a j k) k.1 i))

/-- Exact classical derivative formula for an explicit finite Fourier representative. -/
theorem componentDerivative_realTrigonometricRepresentative
    (S : Finset (d → ℤ)) (a : d → S → ℂ) (i j : d) :
    componentDerivative (realTrigonometricRepresentative S a) i j =
      fun x ↦ ∑ k : S, (2 * Real.pi * Complex.I * (k.1 i) * a j k *
        _root_.UnitAddTorus.mFourier k.1 x).re := by
  rw [componentDerivative_eq]
  simpa only [realTrigonometricRepresentative_apply] using
    (coordinateDerivative_finsetSum Finset.univ
      (fun k : S ↦ PeriodicW12.realMFourierAtomRepresentative (a j k) k.1) i
      (fun k _ ↦
        PeriodicW12.contDiffAlongCoordinate_realMFourierAtomRepresentative (a j k) k.1 i)).trans
      (by
        funext x
        apply Finset.sum_congr rfl
        intro k _
        exact congrFun
          (PeriodicW12.coordinateDerivative_realMFourierAtomRepresentative (a j k) k.1 i) x)

/-- Each synthesized `W¹,²` component has the corresponding explicit trigonometric
representative. -/
theorem value_component_realTrigonometricSynthesis_ae
    (S : Finset (d → ℤ)) (a : d → S → ℂ) (j : d) :
    PeriodicW12.value (component (realTrigonometricSynthesis S a) j) =ᵐ[volume]
      fun x ↦ realTrigonometricRepresentative S a x j := by
  rw [component_realTrigonometricSynthesis]
  rw [← PeriodicW12.valueL_apply, map_sum]
  simp_rw [PeriodicW12.valueL_apply]
  have hall : ∀ᵐ x ∂volume, ∀ k : S,
      PeriodicW12.value (PeriodicW12.realMFourierAtom (a j k) k.1) x =
        PeriodicW12.realMFourierAtomRepresentative (a j k) k.1 x := by
    simpa only [Set.mem_univ, forall_const,
      PeriodicW12.realMFourierAtomRepresentative] using
      (Filter.eventually_all_finite Set.finite_univ).2 fun k _ ↦
        PeriodicW12.value_realMFourierAtom_ae (a j k) k.1
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun k : S ↦ PeriodicW12.value (PeriodicW12.realMFourierAtom (a j k) k.1)),
    hall] with x hsum hx
  rw [hsum]
  simp only [Finset.sum_apply, realTrigonometricRepresentative_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact hx k

/-- The canonical vector `W¹,²` representative of finite Fourier synthesis agrees almost
everywhere with the explicit smooth trigonometric representative. -/
theorem realTrigonometricRepresentative_ae
    (S : Finset (d → ℤ)) (a : d → S → ℂ) :
    representative (realTrigonometricSynthesis S a) =ᵐ[volume]
      realTrigonometricRepresentative S a := by
  have hall : ∀ᵐ x ∂volume, ∀ j : d,
      PeriodicW12.value (component (realTrigonometricSynthesis S a) j) x =
        realTrigonometricRepresentative S a x j := by
    simpa only [Set.mem_univ, forall_const] using
      (Filter.eventually_all_finite Set.finite_univ).2 fun j _ ↦
        value_component_realTrigonometricSynthesis_ae S a j
  filter_upwards [hall] with x hx
  funext j
  rw [representative_apply]
  exact hx j

end PeriodicVectorW12

end UnitAddTorus
