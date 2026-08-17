/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.W12Fourier

/-!
# Real Fourier atoms in periodic W¹,²

This file packages the real part of one complex Fourier monomial as an element of the scalar
periodic graph space `PeriodicW12`.  For `a : ℂ` and frequency `k`, the value representative is

`x ↦ re (a * mFourier k x)`,

and coordinate `i` of its weak gradient is

`x ↦ re ((2 * π * I * k i) * a * mFourier k x)`.

The positive multiplier sign is explicit and agrees with Mathlib's Fourier-coefficient
normalization.  The construction is genuinely real: it is the corresponding real linear
combination of the real and imaginary parts of a mode, not an unproved real-form assertion about
a complex `L²` class.

This supplies the finite-mode atoms used for trigonometric density in Layer 0, item 3 of the
`IncompressibleFlows` roadmap.

## Main declarations

* `PeriodicW12.realMFourierAtom`: the real `W¹,²` atom with amplitude `a` and frequency `k`.
* `PeriodicW12.value_realMFourierAtom_ae`: its value representative.
* `PeriodicW12.weakDeriv_realMFourierAtom_ae`: its sign-normalized coordinate weak derivative.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

namespace PeriodicW12

private def mkOfRepresentatives
    (f : _root_.UnitAddTorus d → ℝ) (D : d → _root_.UnitAddTorus d → ℝ)
    (hf : MemLp f 2) (hD : ∀ i, MemLp (D i) 2)
    (hweak : ∀ i, HasWeakCoordinateDerivative f (D i) i) : PeriodicW12 d := by
  let Gfun (x : _root_.UnitAddTorus d) : EuclideanSpace ℝ d :=
    WithLp.toLp 2 (fun i ↦ D i x)
  have hG : MemLp Gfun 2 := by
    apply MemLp.of_eval_piLp
    intro i
    change MemLp (D i) 2
    exact hD i
  let G : Lp (EuclideanSpace ℝ d) 2
      (volume : Measure (_root_.UnitAddTorus d)) := hG.toLp Gfun
  have hproj (i : d) :
      HasWeakCoordinateDerivative (hf.toLp f)
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) i := by
    apply ((hweak i).congr_ae (MemLp.coeFn_toLp hf).symm).congr_ae_deriv
    filter_upwards [MemLp.coeFn_toLp hG,
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).coeFn_compLp G] with x hGx hprojx
    calc
      D i x = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i) (Gfun x) := rfl
      _ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i) (G x) := by rw [hGx]
      _ = ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) x := hprojx.symm
  exact PeriodicW12.mk (hf.toLp f) G hproj

@[simp]
private theorem value_mkOfRepresentatives
    (f : _root_.UnitAddTorus d → ℝ) (D : d → _root_.UnitAddTorus d → ℝ)
    (hf : MemLp f 2) (hD : ∀ i, MemLp (D i) 2)
    (hweak : ∀ i, HasWeakCoordinateDerivative f (D i) i) :
    value (mkOfRepresentatives f D hf hD hweak) = hf.toLp f := by
  rw [mkOfRepresentatives]
  exact value_mk _ _ _

private theorem weakDeriv_mkOfRepresentatives_ae
    (f : _root_.UnitAddTorus d → ℝ) (D : d → _root_.UnitAddTorus d → ℝ)
    (hf : MemLp f 2) (hD : ∀ i, MemLp (D i) 2)
    (hweak : ∀ i, HasWeakCoordinateDerivative f (D i) i) (i : d) :
    weakDeriv (mkOfRepresentatives f D hf hD hweak) i =ᵐ[volume] D i := by
  exact (hasWeakCoordinateDerivative _ i).ae_eq_deriv <|
    (hweak i).congr_ae (by simpa using (MemLp.coeFn_toLp hf).symm)

private def mFourierReMode (k : d → ℤ) (x : _root_.UnitAddTorus d) : ℝ :=
  (_root_.UnitAddTorus.mFourier k x).re

private def mFourierReModeDeriv (k : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) : ℝ :=
  (2 * Real.pi * Complex.I * (k i) * _root_.UnitAddTorus.mFourier k x).re

private theorem mFourierReMode_memLp (k : d → ℤ) : MemLp (mFourierReMode k) 2 :=
  ((Complex.continuous_re.comp
      (_root_.UnitAddTorus.mFourier k).continuous).memLp_top_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
        volume).mono_exponent
    (by simp)

private theorem mFourierReModeDeriv_memLp (k : d → ℤ) (i : d) :
    MemLp (mFourierReModeDeriv k i) 2 :=
  ((Complex.continuous_re.comp
      (continuous_const.mul
        (_root_.UnitAddTorus.mFourier k).continuous)).memLp_top_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
          volume).mono_exponent
    (by simp)

private theorem hasWeakCoordinateDerivative_mFourierReMode (k : d → ℤ) (i : d) :
    HasWeakCoordinateDerivative (mFourierReMode k) (mFourierReModeDeriv k i) i := by
  have hcoord : coordinateDerivative (mFourierReMode k) i = mFourierReModeDeriv k i := by
    funext x
    exact coordinateDerivative_mFourier_re k i x
  have h := hasWeakCoordinateDerivative_coordinateDerivative
    (mFourierReMode k) i (contDiffAlongCoordinate_mFourier_re k i)
      ((mFourierReMode_memLp k).integrable one_le_two) (by
        rw [hcoord]
        exact (mFourierReModeDeriv_memLp k i).integrable one_le_two)
  rwa [hcoord] at h

private def mFourierReW12 (k : d → ℤ) : PeriodicW12 d :=
  mkOfRepresentatives (mFourierReMode k) (mFourierReModeDeriv k)
    (mFourierReMode_memLp k) (mFourierReModeDeriv_memLp k)
      (hasWeakCoordinateDerivative_mFourierReMode k)

@[simp]
private theorem value_mFourierReW12 (k : d → ℤ) :
    value (mFourierReW12 k) = (mFourierReMode_memLp k).toLp (mFourierReMode k) :=
  value_mkOfRepresentatives _ _ _ _ _

private theorem weakDeriv_mFourierReW12_ae (k : d → ℤ) (i : d) :
    weakDeriv (mFourierReW12 k) i =ᵐ[volume] mFourierReModeDeriv k i :=
  weakDeriv_mkOfRepresentatives_ae _ _ _ _ _ i

private def mFourierImMode (k : d → ℤ) (x : _root_.UnitAddTorus d) : ℝ :=
  (_root_.UnitAddTorus.mFourier k x).im

private def mFourierImModeDeriv (k : d → ℤ) (i : d)
    (x : _root_.UnitAddTorus d) : ℝ :=
  (2 * Real.pi * Complex.I * (k i) * _root_.UnitAddTorus.mFourier k x).im

private theorem mFourierImMode_memLp (k : d → ℤ) : MemLp (mFourierImMode k) 2 :=
  ((Complex.continuous_im.comp
      (_root_.UnitAddTorus.mFourier k).continuous).memLp_top_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
        volume).mono_exponent
    (by simp)

private theorem mFourierImModeDeriv_memLp (k : d → ℤ) (i : d) :
    MemLp (mFourierImModeDeriv k i) 2 :=
  ((Complex.continuous_im.comp
      (continuous_const.mul
        (_root_.UnitAddTorus.mFourier k).continuous)).memLp_top_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
          volume).mono_exponent
    (by simp)

private theorem hasWeakCoordinateDerivative_mFourierImMode (k : d → ℤ) (i : d) :
    HasWeakCoordinateDerivative (mFourierImMode k) (mFourierImModeDeriv k i) i := by
  have hcoord : coordinateDerivative (mFourierImMode k) i = mFourierImModeDeriv k i := by
    funext x
    exact coordinateDerivative_mFourier_im k i x
  have h := hasWeakCoordinateDerivative_coordinateDerivative
    (mFourierImMode k) i (contDiffAlongCoordinate_mFourier_im k i)
      ((mFourierImMode_memLp k).integrable one_le_two) (by
        rw [hcoord]
        exact (mFourierImModeDeriv_memLp k i).integrable one_le_two)
  rwa [hcoord] at h

private def mFourierImW12 (k : d → ℤ) : PeriodicW12 d :=
  mkOfRepresentatives (mFourierImMode k) (mFourierImModeDeriv k)
    (mFourierImMode_memLp k) (mFourierImModeDeriv_memLp k)
      (hasWeakCoordinateDerivative_mFourierImMode k)

@[simp]
private theorem value_mFourierImW12 (k : d → ℤ) :
    value (mFourierImW12 k) = (mFourierImMode_memLp k).toLp (mFourierImMode k) :=
  value_mkOfRepresentatives _ _ _ _ _

private theorem weakDeriv_mFourierImW12_ae (k : d → ℤ) (i : d) :
    weakDeriv (mFourierImW12 k) i =ᵐ[volume] mFourierImModeDeriv k i :=
  weakDeriv_mkOfRepresentatives_ae _ _ _ _ _ i

/-- The real periodic `W¹,²` Fourier atom with complex amplitude `a` and frequency `k`.
Its value is `re (a * mFourier k)` and its weak gradient carries the multiplier
`2 * π * I * k`. -/
def realMFourierAtom (a : ℂ) (k : d → ℤ) : PeriodicW12 d :=
  a.re • mFourierReW12 k - a.im • mFourierImW12 k

/-- The real Fourier atom with zero amplitude is the zero Sobolev class. -/
@[simp]
theorem realMFourierAtom_zero (k : d → ℤ) :
    realMFourierAtom (0 : ℂ) k = 0 := by
  rw [realMFourierAtom]
  simp

/-- The value class of a real Fourier atom has the expected real trigonometric representative. -/
theorem value_realMFourierAtom_ae (a : ℂ) (k : d → ℤ) :
    value (realMFourierAtom a k) =ᵐ[volume]
      fun x ↦ (a * _root_.UnitAddTorus.mFourier k x).re := by
  rw [realMFourierAtom]
  rw [← valueL_apply]
  rw [map_sub, map_smul, map_smul]
  simp only [valueL_apply]
  filter_upwards [MemLp.coeFn_toLp (mFourierReMode_memLp k),
    MemLp.coeFn_toLp (mFourierImMode_memLp k),
    Lp.coeFn_sub (a.re • value (mFourierReW12 k)) (a.im • value (mFourierImW12 k)),
    Lp.coeFn_smul a.re (value (mFourierReW12 k)),
    Lp.coeFn_smul a.im (value (mFourierImW12 k))] with x hre him hsub hsre hsim
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsre, hsim, value_mFourierReW12, value_mFourierImW12]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hre, him]
  simp only [mFourierReMode, mFourierImMode]
  rw [Complex.mul_re]

/-- Coordinate `i` of a real Fourier atom's weak gradient has the exact positive-sign multiplier
`2 * π * I * k i`.  The equality is almost everywhere because both sides represent `L²`
classes. -/
theorem weakDeriv_realMFourierAtom_ae (a : ℂ) (k : d → ℤ) (i : d) :
    weakDeriv (realMFourierAtom a k) i =ᵐ[volume]
      fun x ↦ (2 * Real.pi * Complex.I * (k i) * a *
        _root_.UnitAddTorus.mFourier k x).re := by
  rw [realMFourierAtom]
  rw [← weakDerivL_apply]
  rw [map_sub, map_smul, map_smul]
  simp only [weakDerivL_apply]
  filter_upwards [weakDeriv_mFourierReW12_ae k i, weakDeriv_mFourierImW12_ae k i,
    Lp.coeFn_sub (a.re • weakDeriv (mFourierReW12 k) i)
      (a.im • weakDeriv (mFourierImW12 k) i),
    Lp.coeFn_smul a.re (weakDeriv (mFourierReW12 k) i),
    Lp.coeFn_smul a.im (weakDeriv (mFourierImW12 k) i)] with x hre him hsub hsre hsim
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsre, hsim]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hre, him]
  simp only [mFourierReModeDeriv, mFourierImModeDeriv]
  rw [show 2 * Real.pi * Complex.I * (k i) * a * _root_.UnitAddTorus.mFourier k x =
      a * (2 * Real.pi * Complex.I * (k i) * _root_.UnitAddTorus.mFourier k x) by ring,
    Complex.mul_re]
  simp only [Complex.mul_re, Complex.mul_im]

end PeriodicW12

end TauCeti.UnitAddTorus
