/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.EnergySpace
public import TauCeti.Analysis.Sobolev.Periodic.W12Density

/-!
# Vector trigonometric density in periodic W¹,²

This file lifts scalar Fourier synthesis and trigonometric density componentwise to
`PeriodicVectorW12`.  Every vector Fourier term is assembled from the scalar real Fourier term
at the same frequency.  Arbitrary finite-frequency truncations therefore have exact component,
value, and weak-Jacobian formulas, and their Finset net converges in the full vector graph norm.

The finite trigonometric-polynomial predicate uses one common finite frequency set for every
component.  Density is graph-norm density and makes no pointwise-convergence assertion.
Mean-zero preservation is stated using the canonical continuous vector mean from `EnergySpace`.
No divergence-preservation result is asserted here.

This advances Layer 0, item 3 of the `IncompressibleFlows` roadmap.

## Main declarations

* `PeriodicVectorW12.fourierTerm` and `.fourierTruncation`: componentwise vector Fourier sums.
* `PeriodicVectorW12.hasSum_fourierTerm`: unconditional synthesis in the vector graph norm.
* `PeriodicVectorW12.IsRealTrigonometricPolynomial`: finite real vector trigonometric fields.
* `PeriodicVectorW12.dense_realTrigonometricPolynomial`: graph-norm density.
* `PeriodicVectorW12.mean_fourierTerm_eq_zero` and `.mean_fourierTruncation_eq_zero`:
  preservation of the canonical zero-mean condition.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory Filter Topology

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq
attribute [local instance] unitAddTorusIsProbabilityMeasure

namespace PeriodicW12

private theorem mean_value_realMFourierAtom_eq_zero_of_ne
    (a : ℂ) {k : d → ℤ} (hk : k ≠ 0) :
    mean (value (realMFourierAtom a k)) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  let q : ℂ := 2 * Real.pi * Complex.I * (k i)
  have hq : q ≠ 0 := by
    dsimp only [q]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
      · exact Complex.I_ne_zero
    · exact_mod_cast hi
  let b : ℂ := q⁻¹ * a
  let w : PeriodicW12 d := realMFourierAtom b k
  have hqb : q * b = a := by
    dsimp only [b]
    rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  have hae : weakDeriv w i =ᵐ[volume] value (realMFourierAtom a k) := by
    filter_upwards [weakDeriv_realMFourierAtom_ae b k i,
      value_realMFourierAtom_ae a k] with x hderiv hvalue
    rw [hderiv, hvalue]
    change (q * b * _root_.UnitAddTorus.mFourier k x).re = _
    rw [hqb]
  calc
    mean (value (realMFourierAtom a k)) = ∫ x, weakDeriv w i x := by
      rw [mean_eq_average, average_eq_integral]
      exact (integral_congr_ae hae).symm
    _ = 0 := (hasWeakCoordinateDerivative w i).integral_deriv_eq_zero

/-- Every real Fourier term of a mean-zero scalar periodic Sobolev class has zero mean.  At the
zero frequency this uses the vanishing zero Fourier coefficient; at a nonzero frequency the
mode has a periodic weak antiderivative. -/
theorem mean_value_fourierTerm_eq_zero
    (u : PeriodicW12 d) (hmean : mean (value u) = 0) (k : d → ℤ) :
    mean (value (fourierTerm u k)) = 0 := by
  by_cases hk : k = 0
  · subst k
    have hf : Integrable (fun x ↦ value u x) :=
      (Lp.memLp (value u)).integrable one_le_two
    have hcoeff : _root_.UnitAddTorus.mFourierCoeff
        (fun x ↦ (value u x : ℂ)) 0 = 0 := by
      rw [mFourierCoeff_zero_eq_mean, mean_complex_ofReal _ hf, hmean]
      simp
    rw [fourierTerm_eq_realMFourierAtom, hcoeff, realMFourierAtom_zero]
    rw [← meanL_apply, map_zero]
  · rw [fourierTerm_eq_realMFourierAtom]
    exact mean_value_realMFourierAtom_eq_zero_of_ne _ hk

/-- Every finite Fourier truncation of a mean-zero scalar periodic Sobolev class has zero mean. -/
theorem mean_value_fourierTruncation_eq_zero
    (u : PeriodicW12 d) (hmean : mean (value u) = 0) (S : Finset (d → ℤ)) :
    mean (value (fourierTruncation u S)) = 0 := by
  rw [← meanL_apply, fourierTruncation_eq_sum, map_sum]
  simp only [meanL_apply, mean_value_fourierTerm_eq_zero u hmean,
    Finset.sum_const_zero]

end PeriodicW12

namespace PeriodicVectorW12

/-- The vector Fourier term at `k`, assembled from the scalar real Fourier term of every
component. -/
def fourierTerm (u : PeriodicVectorW12 d) (k : d → ℤ) :
    PeriodicVectorW12 d :=
  ofComponents fun j ↦ PeriodicW12.fourierTerm (component u j) k

/-- Taking a component of a vector Fourier term recovers the corresponding scalar term. -/
@[simp]
theorem component_fourierTerm (u : PeriodicVectorW12 d) (k : d → ℤ) (j : d) :
    component (fourierTerm u k) j =
      PeriodicW12.fourierTerm (component u j) k := by
  rw [fourierTerm, component_ofComponents]

/-- Component `j` of the vector value class of a Fourier term. -/
@[simp]
theorem value_fourierTerm_apply (u : PeriodicVectorW12 d) (k : d → ℤ) (j : d) :
    value (fourierTerm u k) j =
      PeriodicW12.value (PeriodicW12.fourierTerm (component u j) k) := by
  rw [value_apply, component_fourierTerm]

/-- Weak-Jacobian entry `(i,j)` of a vector Fourier term. -/
@[simp]
theorem weakJacobianEntry_fourierTerm (u : PeriodicVectorW12 d)
    (k : d → ℤ) (i j : d) :
    weakJacobianEntry (fourierTerm u k) i j =
      PeriodicW12.weakDeriv (PeriodicW12.fourierTerm (component u j) k) i := by
  rw [weakJacobianEntry_eq, component_fourierTerm]

/-- Truncate every component of a vector Fourier expansion to the same finite frequency set. -/
def fourierTruncation (u : PeriodicVectorW12 d) (S : Finset (d → ℤ)) :
    PeriodicVectorW12 d :=
  ∑ k ∈ S, fourierTerm u k

/-- Taking a component commutes with finite vector Fourier truncation. -/
@[simp]
theorem component_fourierTruncation (u : PeriodicVectorW12 d)
    (S : Finset (d → ℤ)) (j : d) :
    component (fourierTruncation u S) j =
      PeriodicW12.fourierTruncation (component u j) S := by
  rw [fourierTruncation, PeriodicW12.fourierTruncation_eq_sum]
  rw [← componentL_apply, map_sum]
  simp only [componentL_apply, component_fourierTerm]

/-- Component `j` of the vector value class of a finite Fourier truncation. -/
@[simp]
theorem value_fourierTruncation_apply (u : PeriodicVectorW12 d)
    (S : Finset (d → ℤ)) (j : d) :
    value (fourierTruncation u S) j =
      PeriodicW12.value (PeriodicW12.fourierTruncation (component u j) S) := by
  rw [value_apply, component_fourierTruncation]

/-- Weak-Jacobian entry `(i,j)` of a finite vector Fourier truncation. -/
@[simp]
theorem weakJacobianEntry_fourierTruncation (u : PeriodicVectorW12 d)
    (S : Finset (d → ℤ)) (i j : d) :
    weakJacobianEntry (fourierTruncation u S) i j =
      PeriodicW12.weakDeriv
        (PeriodicW12.fourierTruncation (component u j) S) i := by
  rw [weakJacobianEntry_eq, component_fourierTruncation]

/-- Weak-Jacobian entry `(i,j)` of a finite vector Fourier truncation has the exact positive
Fourier multiplier `2 * π * I * k i`, almost everywhere. -/
theorem weakJacobianEntry_fourierTruncation_ae
    (u : PeriodicVectorW12 d) (S : Finset (d → ℤ)) (i j : d) :
    weakJacobianEntry (fourierTruncation u S) i j =ᵐ[volume]
      fun x ↦ ∑ k ∈ S,
        (2 * Real.pi * Complex.I * (k i) *
          _root_.UnitAddTorus.mFourierCoeff
            (fun y ↦ (PeriodicW12.value (component u j) y : ℂ)) k *
          _root_.UnitAddTorus.mFourier k x).re := by
  rw [weakJacobianEntry_fourierTruncation]
  exact PeriodicW12.weakDeriv_fourierTruncation_ae (component u j) S i

/-- The canonical value representative of a finite vector Fourier truncation is the expected
finite real trigonometric sum, almost everywhere and simultaneously in every component. -/
theorem representative_fourierTruncation_ae
    (u : PeriodicVectorW12 d) (S : Finset (d → ℤ)) :
    representative (fourierTruncation u S) =ᵐ[volume]
      fun x j ↦ ∑ k ∈ S,
        (_root_.UnitAddTorus.mFourierCoeff
            (fun y ↦ (PeriodicW12.value (component u j) y : ℂ)) k *
          _root_.UnitAddTorus.mFourier k x).re := by
  have hcomponents : ∀ᵐ x ∂volume, ∀ j : d,
      PeriodicW12.value (PeriodicW12.fourierTruncation (component u j) S) x =
        ∑ k ∈ S,
          (_root_.UnitAddTorus.mFourierCoeff
              (fun y ↦ (PeriodicW12.value (component u j) y : ℂ)) k *
            _root_.UnitAddTorus.mFourier k x).re := by
    simpa only [Set.mem_univ, forall_const] using
      (Filter.eventually_all_finite Set.finite_univ).2 fun j _ ↦
        PeriodicW12.value_fourierTruncation_ae (component u j) S
  filter_upwards [hcomponents] with x hx
  funext j
  rw [representative_apply, component_fourierTruncation]
  exact hx j

/-- Lift unconditional convergence in every scalar component to unconditional convergence in the
finite vector Hilbert product. -/
theorem hasSum_of_component {ι : Type*}
    (f : ι → PeriodicVectorW12 d) (u : PeriodicVectorW12 d)
    (h : ∀ j : d, HasSum (fun n ↦ component (f n) j) (component u j)) :
    HasSum f u := by
  change ∀ j : d, Tendsto (fun s : Finset ι ↦ ∑ n ∈ s, component (f n) j)
    atTop (nhds (component u j)) at h
  change Tendsto (fun s : Finset ι ↦ ∑ n ∈ s, f n) atTop (nhds u)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcomponent (j : d) : Tendsto
      (fun s : Finset ι ↦ ‖(∑ n ∈ s, component (f n) j) - component u j‖ ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp (h j)).pow 2
  have hsq : Tendsto
      (fun s : Finset ι ↦
        ∑ j : d, ‖(∑ n ∈ s, component (f n) j) - component u j‖ ^ 2)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ ↦ hcomponent j)
  have hsq' : Tendsto
      (fun s : Finset ι ↦ ‖(∑ n ∈ s, f n) - u‖ ^ 2) atTop (nhds 0) := by
    convert hsq using 1
    funext s
    rw [norm_sq_eq_sum_norm_component_sq]
    apply Finset.sum_congr rfl
    intro j _
    rw [← componentL_apply, map_sub, map_sum]
    simp only [componentL_apply]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq'
  change Tendsto (fun s : Finset ι ↦ Real.sqrt (‖(∑ n ∈ s, f n) - u‖ ^ 2))
    atTop (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The vector Fourier terms sum unconditionally to `u` in the full vector `W¹,²` graph norm. -/
theorem hasSum_fourierTerm (u : PeriodicVectorW12 d) :
    HasSum (fourierTerm u) u := by
  apply hasSum_of_component
  intro j
  simpa only [component_fourierTerm] using
    PeriodicW12.hasSum_fourierTerm (component u j)

/-- The Finset net of vector Fourier truncations converges in the full vector graph norm.  No
pointwise convergence is asserted. -/
theorem tendsto_fourierTruncation (u : PeriodicVectorW12 d) :
    Tendsto (fourierTruncation u) atTop (nhds u) := by
  exact hasSum_fourierTerm u

/-- A real vector trigonometric polynomial: all components are finite real-mode sums supported
on one common finite frequency set. -/
def IsRealTrigonometricPolynomial (v : PeriodicVectorW12 d) : Prop :=
  ∃ (S : Finset (d → ℤ)) (a : d → (d → ℤ) → ℂ),
    v = ofComponents fun j ↦
      ∑ k ∈ S, PeriodicW12.realMFourierAtom (a j k) k

/-- Every finite vector Fourier truncation is a real vector trigonometric polynomial. -/
theorem isRealTrigonometricPolynomial_fourierTruncation
    (u : PeriodicVectorW12 d) (S : Finset (d → ℤ)) :
    IsRealTrigonometricPolynomial (fourierTruncation u S) := by
  refine ⟨S, fun j k ↦ _root_.UnitAddTorus.mFourierCoeff
    (fun x ↦ (PeriodicW12.value (component u j) x : ℂ)) k, ?_⟩
  apply ext_component
  intro j
  rw [component_fourierTruncation, component_ofComponents]
  rw [PeriodicW12.fourierTruncation_eq_sum]
  simp only [PeriodicW12.fourierTerm_eq_realMFourierAtom]

/-- Real vector trigonometric polynomials are dense in `PeriodicVectorW12`. -/
theorem dense_realTrigonometricPolynomial :
    Dense {v : PeriodicVectorW12 d | IsRealTrigonometricPolynomial v} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro u
  exact mem_closure_of_tendsto (tendsto_fourierTruncation u)
    (Filter.Eventually.of_forall fun S ↦
      isRealTrigonometricPolynomial_fourierTruncation u S)

/-- Every vector periodic `W¹,²` class admits a real trigonometric-polynomial approximation
within any positive graph-norm tolerance. -/
theorem exists_realTrigonometricPolynomial_norm_sub_lt
    (u : PeriodicVectorW12 d) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : PeriodicVectorW12 d,
      IsRealTrigonometricPolynomial v ∧ ‖u - v‖ < ε := by
  obtain ⟨v, hv, hdist⟩ :=
    dense_realTrigonometricPolynomial.exists_dist_lt u hε
  exact ⟨v, hv, by simpa only [dist_eq_norm] using hdist⟩

/-- Every vector Fourier term preserves the canonical componentwise zero-mean condition. -/
theorem mean_fourierTerm_eq_zero (u : PeriodicVectorW12 d)
    (hmean : mean u = 0) (k : d → ℤ) :
    mean (fourierTerm u k) = 0 := by
  apply PiLp.ext
  intro j
  rw [mean_apply, component_fourierTerm]
  apply PeriodicW12.mean_value_fourierTerm_eq_zero
  have hj := congrArg (fun v : EuclideanSpace ℝ d ↦ v j) hmean
  simpa only [mean_apply, PiLp.zero_apply] using hj

/-- Every finite vector Fourier truncation preserves the canonical componentwise zero-mean
condition. -/
theorem mean_fourierTruncation_eq_zero (u : PeriodicVectorW12 d)
    (hmean : mean u = 0) (S : Finset (d → ℤ)) :
    mean (fourierTruncation u S) = 0 := by
  rw [← meanL_apply, fourierTruncation, map_sum]
  simp only [meanL_apply, mean_fourierTerm_eq_zero u hmean,
    Finset.sum_const_zero]

end PeriodicVectorW12

end TauCeti.UnitAddTorus
