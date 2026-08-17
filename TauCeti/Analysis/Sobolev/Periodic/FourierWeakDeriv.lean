/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.FourierTest
public import TauCeti.Analysis.Sobolev.Periodic.Poincare

/-!
# Fourier characterization of periodic weak coordinate derivatives

This file connects the real weak coordinate derivative from `Periodic.WeakDeriv` to Mathlib's
complex multivariate Fourier coefficients.  Testing the weak identity against the real and
imaginary parts of a Fourier mode gives the unit-period multiplier

`hat(∂ᵢ f)(k) = 2 * π * I * k i * hat(f)(k)`.

Parseval applied to each real weak derivative then identifies the Fourier Dirichlet series with
the full weak-gradient energy.  In particular, the series is proved summable rather than merely
assigned the totalized value of a divergent `tsum`.  Combining this identity with the sharp
Fourier Poincare theorem gives the real mean-zero estimate with constant `1 / (4π²)`.

No smooth-density theorem or full Sobolev-space definition is used: the Fourier modes themselves
belong to the bounded coordinate test class.  Pointwise representatives enter only through
explicit `MemLp.toLp` constructions and are compared almost everywhere.

This completes the Fourier/weak-derivative bridge and the periodic mean-zero Poincare acceptance
check in Layer 0 of the `IncompressibleFlows` roadmap.

## Main declarations

* `HasWeakCoordinateDerivative.mFourierCoeff_ofReal`: the exact Fourier multiplier formula.
* `HasWeakCoordinateDerivative.mFourierCoeff_ofReal_single`: a positive-sign unit-mode
  normalization regression.
* `hasSum_mFourierDirichletTerm_of_weakCoordinateDerivatives`: the Fourier Dirichlet series has
  sum equal to the real weak-gradient energy.
* `norm_sq_toLp_le_inv_four_pi_sq_mul_sum_weakGradient`: the sharp real mean-zero periodic
  Poincare inequality in weak-gradient form.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory
open scoped ENNReal

variable {d : Type*} [Fintype d]

private theorem integrable_mFourier_mul_of_integrable
    (m : d → ℤ) {f : _root_.UnitAddTorus d → ℝ} (hf : Integrable f) :
    Integrable (fun x ↦ _root_.UnitAddTorus.mFourier m x * (f x : ℂ)) := by
  have hm : MemLp (fun x ↦ _root_.UnitAddTorus.mFourier m x) ∞ :=
    (_root_.UnitAddTorus.mFourier m).continuous.memLp_top_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)) volume
  change Integrable
    ((fun x ↦ _root_.UnitAddTorus.mFourier m x) * fun x ↦ (f x : ℂ))
  rw [mul_comm]
  exact hf.ofReal.mul_of_top_left hm

private theorem mFourierCoeff_ofReal_eq_re_add_im
    (f : _root_.UnitAddTorus d → ℝ) (hf : Integrable f) (k : d → ℤ) :
    _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k =
      ((∫ x, (_root_.UnitAddTorus.mFourier (-k) x).re * f x : ℝ) : ℂ) +
        ((∫ x, (_root_.UnitAddTorus.mFourier (-k) x).im * f x : ℝ) : ℂ) *
          Complex.I := by
  have hint := integrable_mFourier_mul_of_integrable (-k) hf
  unfold _root_.UnitAddTorus.mFourierCoeff
  change (∫ x, _root_.UnitAddTorus.mFourier (-k) x * (f x : ℂ)
    ∂Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)) = _
  rw [← volume_eq_pi_haarAddCircle]
  have hdecomp := integral_re_add_im hint
  change ((∫ x, (_root_.UnitAddTorus.mFourier (-k) x * (f x : ℂ)).re : ℝ) : ℂ) +
      ((∫ x, (_root_.UnitAddTorus.mFourier (-k) x * (f x : ℂ)).im : ℝ) : ℂ) *
          Complex.I =
        ∫ x, _root_.UnitAddTorus.mFourier (-k) x * (f x : ℂ) at hdecomp
  simpa only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.mul_im, zero_add, add_zero, integral_ofReal] using hdecomp.symm

/-- Complexification preserves the `L²` norm of a real representative. -/
theorem norm_toLp_complexification_eq
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2) :
    ‖hf.ofReal.toLp (fun x ↦ (f x : ℂ))‖ = ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  apply eLpNorm_congr_enorm_ae
  filter_upwards with x
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_inj]
  exact NNReal.eq
    ((RCLike.norm_ofReal (K := ℂ) (f x)).trans (Real.norm_eq_abs (f x)).symm)

/-- The Fourier coefficient of an `L²` complexification agrees with that of its chosen real
representative.  The representative comparison is almost everywhere. -/
theorem mFourierCoeff_toLp_complexification
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2) (k : d → ℤ) :
    _root_.UnitAddTorus.mFourierCoeff
        (hf.ofReal.toLp (fun x ↦ (f x : ℂ))) k =
      _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  unfold _root_.UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  have hcoe : hf.ofReal.toLp (fun x ↦ (f x : ℂ)) =ᵐ[volume]
      fun x ↦ (f x : ℂ) :=
    MemLp.coeFn_toLp hf.ofReal
  have hcoe' : hf.ofReal.toLp (fun x ↦ (f x : ℂ)) =ᵐ[
      Measure.pi (fun _ : d ↦ AddCircle.haarAddCircle)] fun x ↦ (f x : ℂ) := by
    simpa only [← volume_eq_pi_haarAddCircle] using hcoe
  filter_upwards [hcoe'] with x hx
  rw [hx]

private theorem mFourierCoeff_toLp_pi {g : _root_.UnitAddTorus d → ℂ}
    (hg : MemLp g 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle)) (k : d → ℤ) :
    _root_.UnitAddTorus.mFourierCoeff (hg.toLp g) k =
      _root_.UnitAddTorus.mFourierCoeff g k := by
  unfold _root_.UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hg] with x hx
  rw [hx]

/-- For a real `L²` representative, the squared quotient norm is its honest square integral. -/
theorem norm_sq_toLp_eq_integral_sq
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx]
  simp

variable [DecidableEq d]

/-- A real periodic weak coordinate derivative has the expected complex Fourier multiplier.

The positive sign is the one compatible with Mathlib's convention that `mFourierCoeff f k`
integrates `mFourier (-k) * f`. -/
theorem HasWeakCoordinateDerivative.mFourierCoeff_ofReal
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i) (k : d → ℤ) :
    _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f' x : ℂ)) k =
      (2 * Real.pi * Complex.I * (k i)) *
        _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  let q : ℝ := 2 * Real.pi * (k i : ℝ)
  let A : ℝ := ∫ x, (_root_.UnitAddTorus.mFourier (-k) x).re * f x
  let B : ℝ := ∫ x, (_root_.UnitAddTorus.mFourier (-k) x).im * f x
  let A' : ℝ := ∫ x, (_root_.UnitAddTorus.mFourier (-k) x).re * f' x
  let B' : ℝ := ∫ x, (_root_.UnitAddTorus.mFourier (-k) x).im * f' x
  have hDre (x : _root_.UnitAddTorus d) :
      (2 * Real.pi * Complex.I * ((-k) i) *
        _root_.UnitAddTorus.mFourier (-k) x).re =
        q * (_root_.UnitAddTorus.mFourier (-k) x).im := by
    simp only [Pi.neg_apply, Int.cast_neg, q]
    norm_num [Complex.mul_re, Complex.mul_im]
  have hDim (x : _root_.UnitAddTorus d) :
      (2 * Real.pi * Complex.I * ((-k) i) *
        _root_.UnitAddTorus.mFourier (-k) x).im =
        -q * (_root_.UnitAddTorus.mFourier (-k) x).re := by
    simp only [Pi.neg_apply, Int.cast_neg, q]
    norm_num [Complex.mul_re, Complex.mul_im]
  have hre := h.integral_coordinateDerivative_mul_eq_neg_integral_mul
    (mFourierReCoordinateTest (-k) i)
  have him := h.integral_coordinateDerivative_mul_eq_neg_integral_mul
    (mFourierImCoordinateTest (-k) i)
  have hre' : q * B = -A' := by
    simp only [coordinateDerivative_mFourierReCoordinateTest, hDre,
      mFourierReCoordinateTest_apply] at hre
    rw [show (fun x : _root_.UnitAddTorus d ↦
      q * (_root_.UnitAddTorus.mFourier (-k) x).im * f x) =
        fun x ↦ q * ((_root_.UnitAddTorus.mFourier (-k) x).im * f x) by
          funext x
          ring, integral_const_mul] at hre
    exact hre
  have him' : -q * A = -B' := by
    simp only [coordinateDerivative_mFourierImCoordinateTest, hDim,
      mFourierImCoordinateTest_apply] at him
    rw [show (fun x : _root_.UnitAddTorus d ↦
      -q * (_root_.UnitAddTorus.mFourier (-k) x).re * f x) =
        fun x ↦ -q * ((_root_.UnitAddTorus.mFourier (-k) x).re * f x) by
          funext x
          ring, integral_const_mul] at him
    exact him
  rw [mFourierCoeff_ofReal_eq_re_add_im f' h.integrable_deriv k,
    mFourierCoeff_ofReal_eq_re_add_im f h.integrable k]
  change (A' : ℂ) + (B' : ℂ) * Complex.I =
    (2 * Real.pi * Complex.I * (k i)) * ((A : ℂ) + (B : ℂ) * Complex.I)
  rw [show A' = -q * B by linarith [hre'], show B' = q * A by linarith [him']]
  simp only [q, Complex.ofReal_mul, Complex.ofReal_neg]
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

/-- Unit-frequency regression for the sign and normalization of the weak Fourier multiplier. -/
theorem HasWeakCoordinateDerivative.mFourierCoeff_ofReal_single
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i) :
    _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f' x : ℂ)) (Pi.single i 1) =
      (2 * Real.pi * Complex.I) *
        _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) (Pi.single i 1) := by
  simpa using h.mFourierCoeff_ofReal (Pi.single i 1)

/-- **Fourier Dirichlet energy equals real weak-gradient energy.**

If `D i` is an `L²` weak derivative of `f` in every coordinate, the Fourier Dirichlet terms of
the complexification of `f` have sum `∑ i, ∫ (D i)²`.  The `HasSum` conclusion includes the
required summability and rules out reliance on the junk value of a divergent `tsum`. -/
theorem hasSum_mFourierDirichletTerm_of_weakCoordinateDerivatives
    (f : _root_.UnitAddTorus d → ℝ) (D : d → _root_.UnitAddTorus d → ℝ)
    (hf : MemLp f 2) (hD : ∀ i, MemLp (D i) 2)
    (hweak : ∀ i, HasWeakCoordinateDerivative f (D i) i) :
    HasSum
      (mFourierDirichletTerm (hf.ofReal.toLp (fun x ↦ (f x : ℂ))))
      (∑ i, ∫ x, (D i x) ^ 2) := by
  let F : Lp ℂ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
    hf.ofReal.toLp (fun x ↦ (f x : ℂ))
  let μF : Measure (_root_.UnitAddTorus d) :=
    Measure.pi fun _ : d ↦ AddCircle.haarAddCircle
  have hDπ (i : d) : MemLp (fun x ↦ (D i x : ℂ)) 2 μF := by
    change MemLp (fun x ↦ (D i x : ℂ)) 2
      (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle)
    have hcomplex : MemLp (fun x ↦ (D i x : ℂ)) 2
        (volume : Measure (_root_.UnitAddTorus d)) := (hD i).ofReal
    exact Eq.mp
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦
        MemLp (fun x ↦ (D i x : ℂ)) 2 μ) volume_eq_pi_haarAddCircle)
      hcomplex
  let G (i : d) : Lp ℂ 2 μF := (hDπ i).toLp (fun x ↦ (D i x : ℂ))
  have hcoeff (i : d) (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff (G i) k =
        (2 * Real.pi * Complex.I * (k i)) *
          _root_.UnitAddTorus.mFourierCoeff F k := by
    calc
      _ = _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (D i x : ℂ)) k :=
        mFourierCoeff_toLp_pi (hDπ i) k
      _ = (2 * Real.pi * Complex.I * (k i)) *
          _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k :=
        (hweak i).mFourierCoeff_ofReal k
      _ = _ := by rw [mFourierCoeff_toLp_complexification f hf k]
  have hterm (i : d) (k : d → ℤ) :
      ‖_root_.UnitAddTorus.mFourierCoeff (G i) k‖ ^ 2 =
        (2 * Real.pi) ^ 2 * (k i : ℝ) ^ 2 *
          ‖_root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2 := by
    rw [hcoeff]
    rw [norm_mul, mul_pow]
    congr 1
    rw [norm_mul, norm_mul,
      show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Complex.norm_I, Complex.norm_intCast, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos), mul_one, mul_pow, sq_abs]
  have hnorm (i : d) :
      (∫ x, ‖G i x‖ ^ 2 ∂μF) = ∫ x, (D i x) ^ 2 := by
    have hcoe : G i =ᵐ[μF] fun x ↦ (D i x : ℂ) := MemLp.coeFn_toLp (hDπ i)
    calc
      (∫ x, ‖G i x‖ ^ 2 ∂μF) = ∫ x, (D i x) ^ 2 ∂μF := by
        apply integral_congr_ae
        filter_upwards [hcoe] with x hx
        rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = ∫ x, (D i x) ^ 2 := by
        rw [volume_eq_pi_haarAddCircle]
  have hcoord (i : d) : HasSum
      (fun k : d → ℤ ↦ (2 * Real.pi) ^ 2 * (k i : ℝ) ^ 2 *
        ‖_root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2)
      (∫ x, (D i x) ^ 2) := by
    have hparse := _root_.UnitAddTorus.hasSum_sq_mFourierCoeff (G i)
    change HasSum
      (fun k ↦ ‖_root_.UnitAddTorus.mFourierCoeff (G i) k‖ ^ 2)
      (∫ x, ‖G i x‖ ^ 2 ∂μF) at hparse
    rw [hnorm i] at hparse
    exact hparse.congr_fun fun k ↦ (hterm i k).symm
  have hpoint (k : d → ℤ) :
      (∑ i, (2 * Real.pi) ^ 2 * (k i : ℝ) ^ 2 *
        ‖_root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2) =
        mFourierDirichletTerm F k := by
    rw [mFourierDirichletTerm_eq_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [show hf.ofReal.toLp (fun x ↦ (f x : ℂ)) = F from rfl]
  have htotal : HasSum
      (fun k : d → ℤ ↦ ∑ i, (2 * Real.pi) ^ 2 * (k i : ℝ) ^ 2 *
        ‖_root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2)
      (∑ i, ∫ x, (D i x) ^ 2) := by
    exact hasSum_sum fun i _ ↦ hcoord i
  exact htotal.congr_fun fun k ↦ (hpoint k).symm

/-- **Sharp mean-zero periodic Poincare inequality for real weak derivatives.**

The hypotheses give explicit `L²` representatives and a real weak derivative in every coordinate.
Zero normalized mean removes the constant Fourier mode, and the first nonzero frequency gives the
sharp coefficient `((2 * π)²)⁻¹`. -/
theorem norm_sq_toLp_le_inv_four_pi_sq_mul_sum_weakGradient
    (f : _root_.UnitAddTorus d → ℝ) (D : d → _root_.UnitAddTorus d → ℝ)
    (hf : MemLp f 2) (hD : ∀ i, MemLp (D i) 2)
    (hweak : ∀ i, HasWeakCoordinateDerivative f (D i) i)
    (hmean : mean f = 0) :
    ‖hf.toLp f‖ ^ 2 ≤ ((2 * Real.pi) ^ 2)⁻¹ *
      ∑ i, ‖(hD i).toLp (D i)‖ ^ 2 := by
  let F : Lp ℂ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
    hf.ofReal.toLp (fun x ↦ (f x : ℂ))
  have henergy :=
    hasSum_mFourierDirichletTerm_of_weakCoordinateDerivatives f D hf hD hweak
  have hzero : _root_.UnitAddTorus.mFourierCoeff F 0 = 0 := by
    rw [show F = hf.ofReal.toLp (fun x ↦ (f x : ℂ)) from rfl,
      mFourierCoeff_toLp_complexification f hf 0, mFourierCoeff_zero_eq_mean]
    rw [mean_complex_ofReal f (hf.integrable one_le_two), hmean]
    simp
  have hp := norm_sq_le_inv_four_pi_sq_mul_tsum_mFourierDirichletTerm
    F hzero henergy.summable
  rw [henergy.tsum_eq] at hp
  rw [show ‖F‖ = ‖hf.toLp f‖ by
    rw [show F = hf.ofReal.toLp (fun x ↦ (f x : ℂ)) from rfl]
    exact norm_toLp_complexification_eq f hf] at hp
  have hcoord (i : d) : ‖(hD i).toLp (D i)‖ ^ 2 = ∫ x, (D i x) ^ 2 :=
    norm_sq_toLp_eq_integral_sq (D i) (hD i)
  simpa only [hcoord] using hp

end TauCeti.UnitAddTorus
