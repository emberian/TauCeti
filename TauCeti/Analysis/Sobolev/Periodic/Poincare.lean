/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.Sobolev.Periodic.Mean

/-!
# Fourier Poincare inequality on the normalized flat torus

This file identifies the spectral gap of the normalized torus and proves the corresponding sharp
Poincare estimate directly from Mathlib's multivariate Fourier Hilbert basis.  With the unit-period
Fourier convention, a frequency `k : d → ℤ` has squared gradient multiplier
`(2 * π)² * ∑ i, k i ^ 2`; every nonzero frequency therefore has multiplier at least `(2 * π)²`.

The main theorem is deliberately phrased in terms of the summable Fourier Dirichlet series.  It
does not yet identify that series with a weak-gradient norm: that requires the independent weak
derivative and Fourier differentiation/density developments.  The explicit summability hypothesis
also prevents the totalized value of a divergent `tsum` from yielding a vacuous analytic statement.

This advances Layer 0, item 4 and the periodic Poincare acceptance check in the
`IncompressibleFlows` roadmap.

## Main declarations

* `UnitAddTorus.frequencyNormSq`: squared Euclidean norm of an integer frequency.
* `UnitAddTorus.one_le_frequencyNormSq`: the unit spectral gap away from zero.
* `UnitAddTorus.mFourierDirichletTerm`: one term of the Fourier Dirichlet energy.
* `UnitAddTorus.norm_sq_le_inv_four_pi_sq_mul_tsum_mFourierDirichletTerm`: the sharp
  Fourier-form Poincare estimate on mean-zero complex `L²`.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped BigOperators

variable {d : Type*} [Fintype d]

/-- Squared Euclidean norm of an integer-valued torus frequency. -/
@[expose]
def frequencyNormSq (k : d → ℤ) : ℝ :=
  ∑ i, (k i : ℝ) ^ 2

@[simp]
theorem frequencyNormSq_zero : frequencyNormSq (0 : d → ℤ) = 0 := by
  simp [frequencyNormSq]

theorem frequencyNormSq_nonneg (k : d → ℤ) : 0 ≤ frequencyNormSq k := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Every nonzero integer frequency has squared Euclidean norm at least one. -/
theorem one_le_frequencyNormSq {k : d → ℤ} (hk : k ≠ 0) :
    1 ≤ frequencyNormSq k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have hi' : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    exact_mod_cast (show (1 : ℤ) ≤ (k i) ^ 2 by
      rw [one_le_sq_iff_one_le_abs]
      exact Int.one_le_abs hi)
  exact hi'.trans
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg (k j : ℝ)) (Finset.mem_univ i))

@[simp]
theorem frequencyNormSq_eq_zero_iff (k : d → ℤ) : frequencyNormSq k = 0 ↔ k = 0 := by
  constructor
  · intro hkzero
    by_contra hk
    have hgap := one_le_frequencyNormSq hk
    linarith
  · rintro rfl
    exact frequencyNormSq_zero

/-- A coordinate unit frequency attains the first nonzero eigenvalue. -/
@[simp]
theorem frequencyNormSq_single [DecidableEq d] (i : d) :
    frequencyNormSq (Pi.single i 1) = 1 := by
  rw [frequencyNormSq, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- One frequency's contribution to the Dirichlet energy in Mathlib's unit-period Fourier
normalization. -/
@[expose]
def mFourierDirichletTerm (f : _root_.UnitAddTorus d → ℂ) (k : d → ℤ) : ℝ :=
  (2 * Real.pi) ^ 2 * frequencyNormSq k *
    ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2

/-- Expanded coordinate-sum form of one Fourier Dirichlet-energy term. -/
theorem mFourierDirichletTerm_eq_sum
    (f : _root_.UnitAddTorus d → ℂ) (k : d → ℤ) :
    mFourierDirichletTerm f k =
      (2 * Real.pi) ^ 2 * (∑ i, (k i : ℝ) ^ 2) *
        ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 :=
  rfl

theorem mFourierDirichletTerm_nonneg (f : _root_.UnitAddTorus d → ℂ) (k : d → ℤ) :
    0 ≤ mFourierDirichletTerm f k := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (frequencyNormSq_nonneg k)) (sq_nonneg _)

local notation "TorusL²" =>
  Lp ℂ 2 (volume : Measure (_root_.UnitAddTorus d))

/-- **Sharp Fourier-form Poincare inequality on the normalized torus.**

The zero Fourier coefficient removes the constant mode.  Parseval and the integer-frequency gap
then control the `L²` norm by `1 / (4π²)` times the summable Fourier Dirichlet series.  The
coefficient is normalized sharply: `frequencyNormSq_single` shows that coordinate unit frequencies
attain the gap.

This theorem does not identify the series with a weak-gradient integral; consumers must supply
that bridge separately. -/
theorem norm_sq_le_inv_four_pi_sq_mul_tsum_mFourierDirichletTerm
    (f : TorusL²)
    (hzero : _root_.UnitAddTorus.mFourierCoeff f 0 = 0)
    (henergy : Summable (mFourierDirichletTerm (d := d) f)) :
    ‖f‖ ^ 2 ≤ ((2 * Real.pi) ^ 2)⁻¹ *
      ∑' k : d → ℤ, mFourierDirichletTerm f k := by
  -- Mathlib's Fourier basis locally installs normalized Haar measure on each circle.  Rewrite the
  -- proposition before introducing its dependent `Lp` data so the basis and the public default
  -- volume API are definitionally aligned throughout the proof.
  revert f
  rw [volume_eq_pi_haarAddCircle]
  intro f hzero henergy
  let C : ℝ := (2 * Real.pi) ^ 2
  have hC : 0 < C := by positivity
  have hscoeff : Summable fun k : d → ℤ ↦
      ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
    simpa only [← _root_.UnitAddTorus.mFourierBasis_repr,
      HilbertBasis.repr_apply_apply] using
      (_root_.UnitAddTorus.mFourierBasis (d := d)).summable_norm_sq_inner f
  have hscaled : Summable fun k : d → ℤ ↦
      C⁻¹ * (C * frequencyNormSq k *
        ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2) := by
    exact henergy.mul_left C⁻¹
  have hterm (k : d → ℤ) :
      ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤
        C⁻¹ * (C * frequencyNormSq k *
          ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2) := by
    by_cases hk : k = 0
    · subst k
      simp [hzero]
    · have hfreq := one_le_frequencyNormSq hk
      have hsq : 0 ≤ ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 := sq_nonneg _
      calc
        _ ≤ frequencyNormSq k *
            ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
          nlinarith
        _ = C⁻¹ * (C * frequencyNormSq k *
            ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2) := by
          field_simp
  calc
    ‖f‖ ^ 2 = ∑' k : d → ℤ,
        ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
      simpa only [← _root_.UnitAddTorus.mFourierBasis_repr,
        HilbertBasis.repr_apply_apply] using
        (_root_.UnitAddTorus.mFourierBasis (d := d)).tsum_norm_sq_inner f |>.symm
    _ ≤ ∑' k : d → ℤ,
        C⁻¹ * (C * frequencyNormSq k *
          ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2) :=
      hscoeff.tsum_le_tsum hterm hscaled
    _ = C⁻¹ * ∑' k : d → ℤ,
        C * frequencyNormSq k *
          ‖_root_.UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = _ := rfl

end UnitAddTorus
