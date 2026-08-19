/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.EnergySpace
public import TauCeti.Analysis.Sobolev.Periodic.WeakDerivUniqueness

/-!
# Fourier symbol of periodic weak divergence

This file gives the quotient-native Fourier symbol of weak divergence on
`PeriodicVectorW12`.  A vector Fourier coefficient is assembled componentwise from the scalar
real `L²` quotient classes, and its frequency pairing is

`sum i, (k i : ℂ) * uHat i`.

The weak-derivative multiplier proves that the Fourier coefficient of weak divergence is exactly
`(2 * π * I)` times this pairing.  Conversely, vanishing of every pairing forces the quotient
weak divergence to vanish: the proof uses the existing full `L¹` Fourier-separation theorem on
its `L²` representative, not a density assertion or a pointwise representative choice.

No Galerkin truncation or Fourier-multiplier Leray formula is constructed here.

## Main declarations

* `realL2MFourierCoeff`: a Fourier coefficient of a real scalar `L²` quotient class.
* `PeriodicVectorW12.mFourierCoeff`: the componentwise vector Fourier coefficient.
* `PeriodicVectorW12.fourierDivergencePairing`: the frequency/divergence pairing.
* `PeriodicVectorW12.mFourierCoeff_weakDivergence`: the exact `2 * π * I` symbol formula.
* `mem_periodicDivergenceFreeW12Submodule_iff_forall_fourierDivergencePairing_eq_zero`:
  spectral characterization of the weak-divergence kernel.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped ENNReal

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

/- Mathlib keeps the normalized circle probability instance local to its Fourier module. -/
attribute [local instance] unitAddTorusIsProbabilityMeasure

/-- The `k`-th complex Fourier coefficient of a real scalar `L²` quotient class. -/
def realL2MFourierCoeff
    (f : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) (k : d → ℤ) : ℂ :=
  _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k

private theorem integrable_mFourier_mul_realL2
    (f : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) (k : d → ℤ) :
    Integrable (fun x ↦ _root_.UnitAddTorus.mFourier k x * (f x : ℂ)) := by
  have hk : MemLp (fun x ↦ _root_.UnitAddTorus.mFourier k x) ∞ :=
    (_root_.UnitAddTorus.mFourier k).continuous.memLp_top_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace (_root_.UnitAddTorus.mFourier k)) volume
  change Integrable
    ((fun x ↦ _root_.UnitAddTorus.mFourier k x) * fun x ↦ (f x : ℂ))
  rw [mul_comm]
  exact ((Lp.memLp f).integrable one_le_two).ofReal.mul_of_top_left hk

@[simp]
theorem realL2MFourierCoeff_zero (k : d → ℤ) :
    realL2MFourierCoeff
      (0 : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) k = 0 := by
  unfold realL2MFourierCoeff _root_.UnitAddTorus.mFourierCoeff
  apply integral_eq_zero_of_ae
  have hzero : (0 : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) =ᵐ[volume]
      (0 : _root_.UnitAddTorus d → ℝ) := Lp.coeFn_zero ℝ 2 volume
  have hzero' : (0 : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) =ᵐ[
      Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)]
      (0 : _root_.UnitAddTorus d → ℝ) := by
    simpa only [← volume_eq_pi_haarAddCircle] using hzero
  filter_upwards [hzero'] with x hx
  rw [hx]
  simp

/-- Fourier coefficients commute with finite sums of real scalar `L²` quotient classes. -/
theorem realL2MFourierCoeff_finsetSum {I : Type*} (s : Finset I)
    (f : I → Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) (k : d → ℤ) :
    realL2MFourierCoeff (∑ i ∈ s, f i) k =
      ∑ i ∈ s, realL2MFourierCoeff (f i) k := by
  unfold realL2MFourierCoeff _root_.UnitAddTorus.mFourierCoeff
  have hcoe := Lp.coeFn_finsetSum s f
  have hcoe0 : (fun x ↦ (∑ i ∈ s, f i) x) =ᵐ[volume]
      fun x ↦ ∑ i ∈ s, f i x := by
    filter_upwards [hcoe] with x hx
    simpa only [Finset.sum_apply] using hx
  have hcoe' : (fun x ↦ (∑ i ∈ s, f i) x) =ᵐ[
      Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)]
      fun x ↦ ∑ i ∈ s, f i x := by
    simpa only [← volume_eq_pi_haarAddCircle] using hcoe0
  calc
    (∫ x, _root_.UnitAddTorus.mFourier (-k) x •
        ((∑ i ∈ s, f i) x : ℂ)
        ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)) =
        ∫ x, ∑ i ∈ s,
          _root_.UnitAddTorus.mFourier (-k) x * (f i x : ℂ)
          ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [hcoe'] with x hx
      rw [hx]
      simp only [smul_eq_mul]
      push_cast
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∫ x,
        _root_.UnitAddTorus.mFourier (-k) x * (f i x : ℂ)
        ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle) := by
      apply integral_finsetSum
      intro i hi
      have hint := integrable_mFourier_mul_realL2 (f i) (-k)
      simpa only [← volume_eq_pi_haarAddCircle] using hint

/-- Fourier coefficients commute with a full finite-type sum. -/
theorem realL2MFourierCoeff_sum
    (f : d → Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) (k : d → ℤ) :
    realL2MFourierCoeff (∑ i, f i) k = ∑ i, realL2MFourierCoeff (f i) k := by
  simpa only [Finset.sum_const_zero] using
    realL2MFourierCoeff_finsetSum (d := d) Finset.univ f k

/-- The zero Fourier mode of a real scalar `L²` class is its normalized spatial mean. -/
@[simp]
theorem realL2MFourierCoeff_at_zero
    (f : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) :
    realL2MFourierCoeff f 0 = ((mean (fun x ↦ f x) : ℝ) : ℂ) := by
  rw [realL2MFourierCoeff, mFourierCoeff_zero_eq_mean]
  exact mean_complex_ofReal f ((Lp.memLp f).integrable one_le_two)

/-- Full Fourier separation for real scalar `L²` quotient classes.  The nontrivial direction
uses the `L¹` separation theorem on the canonical quotient representative. -/
theorem realL2_eq_zero_iff_forall_mFourierCoeff_eq_zero
    (f : Lp ℝ 2 (volume : Measure (_root_.UnitAddTorus d))) :
    f = 0 ↔ ∀ k : d → ℤ, realL2MFourierCoeff f k = 0 := by
  constructor
  · rintro rfl k
    exact realL2MFourierCoeff_zero k
  · intro hcoeff
    have hfint : Integrable f := (Lp.memLp f).integrable one_le_two
    have hmode : ∀ m : d → ℤ,
        (∫ x, _root_.UnitAddTorus.mFourier m x * (f x : ℂ)) = 0 := by
      intro m
      have hm := hcoeff (-m)
      unfold realL2MFourierCoeff _root_.UnitAddTorus.mFourierCoeff at hm
      change (∫ x, _root_.UnitAddTorus.mFourier (-(-m)) x * (f x : ℂ)
        ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)) = 0 at hm
      simp only [neg_neg] at hm
      have hvol : (volume : Measure (_root_.UnitAddTorus d)) =
          Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle) := by
        rw [MeasureTheory.volume_pi]
        congr 1
        funext i
        simp [AddCircle.volume_eq_smul_haarAddCircle]
      calc
        (∫ x, _root_.UnitAddTorus.mFourier m x * (f x : ℂ)) =
            ∫ x, _root_.UnitAddTorus.mFourier m x * (f x : ℂ)
              ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle) :=
          congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦
            ∫ x, _root_.UnitAddTorus.mFourier m x * (f x : ℂ) ∂μ) hvol
        _ = 0 := hm
    have hzero : f =ᵐ[volume] (0 : _root_.UnitAddTorus d → ℝ) :=
      ae_eq_zero_of_integral_mFourier_mul_eq_zero hfint hmode
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℝ 2 volume).symm

namespace PeriodicW12

/-- The Fourier coefficient of a scalar weak derivative has the exact positive multiplier. -/
theorem realL2MFourierCoeff_weakDeriv (u : PeriodicW12 d) (i : d) (k : d → ℤ) :
    realL2MFourierCoeff (weakDeriv u i) k =
      (2 * Real.pi * Complex.I * (k i)) * realL2MFourierCoeff (value u) k := by
  exact (hasWeakCoordinateDerivative u i).mFourierCoeff_ofReal k

end PeriodicW12

namespace PeriodicVectorW12

/-- The quotient-safe componentwise complex Fourier coefficient of a vector `W¹,²` class. -/
def mFourierCoeff (u : PeriodicVectorW12 d) (k : d → ℤ) : EuclideanSpace ℂ d :=
  WithLp.toLp 2 fun j ↦ realL2MFourierCoeff (PeriodicW12.value (component u j)) k

@[simp]
theorem mFourierCoeff_apply (u : PeriodicVectorW12 d) (k : d → ℤ) (j : d) :
    mFourierCoeff u k j = realL2MFourierCoeff (PeriodicW12.value (component u j)) k := by
  rfl

/-- Expanded evaluator formula for the vector Fourier coefficient.  This wrapper keeps the
underlying scalar quotient definition usable across module boundaries. -/
theorem mFourierCoeff_apply_eq_mFourierCoeff
    (u : PeriodicVectorW12 d) (k : d → ℤ) (j : d) :
    mFourierCoeff u k j = _root_.UnitAddTorus.mFourierCoeff
      (fun x ↦ (PeriodicW12.value (component u j) x : ℂ)) k := by
  rfl

/-- Pair frequency `k` with the componentwise Fourier coefficient of `u`. -/
def fourierDivergencePairing (u : PeriodicVectorW12 d) (k : d → ℤ) : ℂ :=
  ∑ i, (k i : ℂ) * mFourierCoeff u k i

/-- Expanded finite-sum formula for the Fourier divergence pairing. -/
theorem fourierDivergencePairing_eq_sum (u : PeriodicVectorW12 d) (k : d → ℤ) :
    fourierDivergencePairing u k = ∑ i, (k i : ℂ) * mFourierCoeff u k i := by
  rfl

/-- The weak-divergence Fourier coefficient is exactly `(2 * π * I)` times the frequency
pairing. -/
theorem mFourierCoeff_weakDivergence (u : PeriodicVectorW12 d) (k : d → ℤ) :
    realL2MFourierCoeff (weakDivergence u) k =
      (2 * Real.pi * Complex.I) * fourierDivergencePairing u k := by
  rw [weakDivergence_eq_sum, realL2MFourierCoeff_sum]
  rw [fourierDivergencePairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weakJacobianEntry_eq, PeriodicW12.realL2MFourierCoeff_weakDeriv,
    mFourierCoeff_apply]
  ring

/-- Any vector `W¹,²` class with zero componentwise mean has zero vector Fourier mode. -/
theorem mFourierCoeff_zero_of_mean_eq_zero (u : PeriodicVectorW12 d)
    (hu : mean u = 0) : mFourierCoeff u 0 = 0 := by
  apply PiLp.ext
  intro j
  rw [mFourierCoeff_apply, realL2MFourierCoeff_at_zero]
  have hj := congrArg (fun v : EuclideanSpace ℝ d ↦ v j) hu
  rw [mean_apply] at hj
  simp only [PiLp.zero_apply]
  rw [hj]
  norm_num

end PeriodicVectorW12

/-- A periodic vector `W¹,²` class is weakly divergence-free exactly when every frequency is
orthogonal to its vector Fourier coefficient. -/
theorem mem_periodicDivergenceFreeW12Submodule_iff_forall_fourierDivergencePairing_eq_zero
    (u : PeriodicVectorW12 d) :
    u ∈ periodicDivergenceFreeW12Submodule d ↔
      ∀ k : d → ℤ, PeriodicVectorW12.fourierDivergencePairing u k = 0 := by
  rw [mem_periodicDivergenceFreeW12Submodule_iff]
  constructor
  · intro hdiv k
    have hsymbol := PeriodicVectorW12.mFourierCoeff_weakDivergence u k
    rw [hdiv, realL2MFourierCoeff_zero] at hsymbol
    have hfactor : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    exact (mul_eq_zero.mp hsymbol.symm).resolve_left hfactor
  · intro hpair
    apply (realL2_eq_zero_iff_forall_mFourierCoeff_eq_zero
      (PeriodicVectorW12.weakDivergence u)).mpr
    intro k
    rw [PeriodicVectorW12.mFourierCoeff_weakDivergence, hpair k, mul_zero]

namespace PeriodicMeanZeroDivergenceFreeW12

/-- Every mean-zero incompressible energy field has vanishing vector zero mode. -/
@[simp]
theorem mFourierCoeff_zero (u : PeriodicMeanZeroDivergenceFreeW12 d) :
    PeriodicVectorW12.mFourierCoeff (u : PeriodicVectorW12 d) 0 = 0 :=
  PeriodicVectorW12.mFourierCoeff_zero_of_mean_eq_zero
    (u : PeriodicVectorW12 d) (mean_eq_zero u)

end PeriodicMeanZeroDivergenceFreeW12

end UnitAddTorus
