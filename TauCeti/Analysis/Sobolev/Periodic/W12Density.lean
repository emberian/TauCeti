/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.W12Trigonometric

/-!
# Trigonometric density in periodic W¹,²

This file synthesizes the real Fourier atoms from `W12Trigonometric` into the scalar periodic
graph space.  For `u : PeriodicW12 d`, `fourierTerm u k` uses the complex Fourier coefficient of
the real value representative as the amplitude of the real mode at `k`.  The unordered sum of
these terms converges to `u` in the full `W¹,²` graph norm.

The proof separately reconstructs the value and every weak coordinate derivative by Mathlib's
normalized-Haar `L²` Fourier basis, transports those quotient classes to the propositionally
equal public volume measure, and then uses the exact weak-derivative Fourier multiplier.  Thus no
smooth-density theorem and no pointwise convergence assertion is involved.

## Main declarations

* `PeriodicW12.fourierTerm`: one real Fourier term of a periodic Sobolev class.
* `PeriodicW12.fourierTruncation`: its truncation to an arbitrary finite frequency set.
* `PeriodicW12.hasSum_fourierTerm`: full graph-norm Fourier synthesis.
* `PeriodicW12.tendsto_fourierTruncation`: convergence of the Finset net in `PeriodicW12`.
* `PeriodicW12.IsRealTrigonometricPolynomial`: the finite real-mode class.
* `PeriodicW12.dense_realTrigonometricPolynomial`: density in the graph norm.
* `PeriodicW12.exists_realTrigonometricPolynomial_norm_sub_lt`: the corresponding explicit
  `ε`-approximation statement.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

local notation "μT" =>
  (Measure.pi fun _ : d ↦ (AddCircle.haarAddCircle : Measure _root_.UnitAddCircle))

namespace PeriodicW12

private def normalizedHaarToVolumeL
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E (2 : ℝ≥0∞) μT →L[ℝ]
      Lp E (2 : ℝ≥0∞) (volume : Measure (_root_.UnitAddTorus d)) :=
  Lp.LpToLpOfMeasureLeSMul (p := 2) (c := 1) (by simp) (by
    rw [one_smul, volume_eq_pi_haarAddCircle])

private theorem normalizedHaarToVolumeL_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E (2 : ℝ≥0∞) μT) :
    normalizedHaarToVolumeL E f =ᵐ[volume] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1) (by simp) (by
    rw [one_smul, volume_eq_pi_haarAddCircle]) f

private def complexValue (u : PeriodicW12 d) :
    Lp ℂ (2 : ℝ≥0∞) μT := by
  let f : _root_.UnitAddTorus d → ℂ := fun x ↦ (value u x : ℂ)
  have hfVolume : MemLp f 2 (volume : Measure (_root_.UnitAddTorus d)) :=
    (Lp.memLp (value u)).ofReal
  have hf : MemLp f 2 μT :=
    Eq.mp
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦ MemLp f 2 μ)
        volume_eq_pi_haarAddCircle)
      hfVolume
  exact hf.toLp f

private theorem complexValue_ae (u : PeriodicW12 d) :
    complexValue u =ᵐ[μT]
      fun x ↦ (value u x : ℂ) := by
  rw [complexValue]
  exact MemLp.coeFn_toLp _

/-- The real Fourier term of `u` at frequency `k`.  Its amplitude is the complex Fourier
coefficient of the real `L²` value representative. -/
def fourierTerm (u : PeriodicW12 d) (k : d → ℤ) : PeriodicW12 d :=
  realMFourierAtom
    (_root_.UnitAddTorus.mFourierCoeff (fun x ↦ (value u x : ℂ)) k) k

/-- Unfolding formula for one real Fourier term. -/
theorem fourierTerm_eq_realMFourierAtom (u : PeriodicW12 d) (k : d → ℤ) :
    fourierTerm u k = realMFourierAtom
      (_root_.UnitAddTorus.mFourierCoeff (fun x ↦ (value u x : ℂ)) k) k := by
  rfl

/-- The values of the real Fourier terms sum unconditionally to the value of `u` in `L²`.

This is quotient-level convergence, not pointwise convergence. -/
theorem hasSum_value_fourierTerm (u : PeriodicW12 d) :
    HasSum (fun k ↦ value (fourierTerm u k)) (value u) := by
  let reL := Complex.reCLM.compLpL (2 : ℝ≥0∞) μT
  have hcomplex := _root_.UnitAddTorus.hasSum_mFourier_series_L2 (complexValue u)
  have hreal := reL.hasSum hcomplex
  have hvolume := (normalizedHaarToVolumeL ℝ).hasSum hreal
  have hterm (k : d → ℤ) : value (fourierTerm u k) =
      normalizedHaarToVolumeL ℝ
        (reL (_root_.UnitAddTorus.mFourierCoeff (complexValue u) k •
          _root_.UnitAddTorus.mFourierLp 2 k)) := by
    rw [fourierTerm]
    apply Lp.ext
    let c := _root_.UnitAddTorus.mFourierCoeff (complexValue u) k
    let a := _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (value u x : ℂ)) k
    let z : Lp ℂ 2 μT := c • _root_.UnitAddTorus.mFourierLp 2 k
    have hatom := value_realMFourierAtom_ae
      a k
    have hcoeff : c = a := by
      dsimp only [c, a]
      unfold _root_.UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      filter_upwards [complexValue_ae u] with x hx
      rw [hx]
    have hmode : (_root_.UnitAddTorus.mFourierLp 2 k : Lp ℂ 2 μT) =ᵐ[μT]
        _root_.UnitAddTorus.mFourier k :=
      ContinuousMap.coeFn_toLp μT (_root_.UnitAddTorus.mFourier k)
    have hz : z =ᵐ[μT] fun x ↦ c * _root_.UnitAddTorus.mFourier k x := by
      filter_upwards [Lp.coeFn_smul c (_root_.UnitAddTorus.mFourierLp 2 k), hmode]
        with x hx hm
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hm]
    have hre : reL z =ᵐ[μT] fun x ↦ Complex.reCLM (z x) := by
      change Complex.reCLM.compLp z =ᵐ[μT] fun x ↦ Complex.reCLM (z x)
      exact Complex.reCLM.coeFn_compLp z
    have hright : reL z =ᵐ[volume]
        fun x ↦ (c * _root_.UnitAddTorus.mFourier k x).re := by
      have hπ : reL z =ᵐ[μT] fun x ↦ (c * _root_.UnitAddTorus.mFourier k x).re := by
        filter_upwards [hre, hz] with x hx hy
        rw [hx, hy]
        simp only [Complex.reCLM_apply]
      simpa only [volume_eq_pi_haarAddCircle] using hπ
    filter_upwards [hatom, normalizedHaarToVolumeL_ae (reL z), hright]
      with x hleft htransfer hrightx
    rw [hleft, htransfer, hrightx, hcoeff]
  have hseries : HasSum (fun k ↦ value (fourierTerm u k))
      (normalizedHaarToVolumeL ℝ (reL (complexValue u))) :=
    hvolume.congr_fun hterm
  have hlimit : normalizedHaarToVolumeL ℝ (reL (complexValue u)) = value u := by
    apply Lp.ext
    filter_upwards [normalizedHaarToVolumeL_ae (reL (complexValue u)),
      show reL (complexValue u) =ᵐ[volume] fun x ↦ value u x by
        filter_upwards [show reL (complexValue u) =ᵐ[volume]
            fun x ↦ Complex.reCLM (complexValue u x) by
              have hre : reL (complexValue u) =ᵐ[μT]
                  fun x ↦ Complex.reCLM (complexValue u x) := by
                change Complex.reCLM.compLp (complexValue u) =ᵐ[μT]
                  fun x ↦ Complex.reCLM (complexValue u x)
                exact Complex.reCLM.coeFn_compLp (complexValue u)
              simpa only [volume_eq_pi_haarAddCircle] using hre,
          show complexValue u =ᵐ[volume] fun x ↦ (value u x : ℂ) by
              simpa only [volume_eq_pi_haarAddCircle] using complexValue_ae u] with x hx hu
        rw [hx, hu]
        simp only [Complex.reCLM_apply, Complex.ofReal_re]] with x hx hy
    rw [hx, hy]
  rw [hlimit] at hseries
  exact hseries

private def complexWeakDeriv (u : PeriodicW12 d) (i : d) :
    Lp ℂ (2 : ℝ≥0∞) μT := by
  let f : _root_.UnitAddTorus d → ℂ := fun x ↦ (weakDeriv u i x : ℂ)
  have hfVolume : MemLp f 2 (volume : Measure (_root_.UnitAddTorus d)) :=
    (Lp.memLp (weakDeriv u i)).ofReal
  have hf : MemLp f 2 μT :=
    Eq.mp
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦ MemLp f 2 μ)
        volume_eq_pi_haarAddCircle)
      hfVolume
  exact hf.toLp f

private theorem complexWeakDeriv_ae (u : PeriodicW12 d) (i : d) :
    complexWeakDeriv u i =ᵐ[μT]
      fun x ↦ (weakDeriv u i x : ℂ) := by
  rw [complexWeakDeriv]
  exact MemLp.coeFn_toLp _

/-- At every coordinate, the weak derivatives of the real Fourier terms sum unconditionally to
the weak derivative of `u` in `L²`.  The coefficient calculation uses the positive multiplier
`2 * π * I * k i`. -/
theorem hasSum_weakDeriv_fourierTerm (u : PeriodicW12 d) (i : d) :
    HasSum (fun k ↦ weakDeriv (fourierTerm u k) i) (weakDeriv u i) := by
  let reL := Complex.reCLM.compLpL (2 : ℝ≥0∞) μT
  have hcomplex :=
    _root_.UnitAddTorus.hasSum_mFourier_series_L2 (complexWeakDeriv u i)
  have hreal := reL.hasSum hcomplex
  have hvolume := (normalizedHaarToVolumeL ℝ).hasSum hreal
  have hterm (k : d → ℤ) : weakDeriv (fourierTerm u k) i =
      normalizedHaarToVolumeL ℝ
        (reL (_root_.UnitAddTorus.mFourierCoeff (complexWeakDeriv u i) k •
          _root_.UnitAddTorus.mFourierLp 2 k)) := by
    rw [fourierTerm]
    apply Lp.ext
    let c := _root_.UnitAddTorus.mFourierCoeff (complexWeakDeriv u i) k
    let a := _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (value u x : ℂ)) k
    let q : ℂ := 2 * Real.pi * Complex.I * (k i)
    let z : Lp ℂ 2 μT := c • _root_.UnitAddTorus.mFourierLp 2 k
    have hatom := weakDeriv_realMFourierAtom_ae a k i
    have hcoeffDerivative : c = q * a := by
      dsimp only [c, q, a]
      calc
        _root_.UnitAddTorus.mFourierCoeff (complexWeakDeriv u i) k =
            _root_.UnitAddTorus.mFourierCoeff
              (fun x ↦ (weakDeriv u i x : ℂ)) k := by
          unfold _root_.UnitAddTorus.mFourierCoeff
          apply integral_congr_ae
          filter_upwards [complexWeakDeriv_ae u i] with x hx
          rw [hx]
        _ = (2 * Real.pi * Complex.I * (k i)) *
            _root_.UnitAddTorus.mFourierCoeff
              (fun x ↦ (value u x : ℂ)) k :=
          (hasWeakCoordinateDerivative u i).mFourierCoeff_ofReal k
    have hmode : (_root_.UnitAddTorus.mFourierLp 2 k : Lp ℂ 2 μT) =ᵐ[μT]
        _root_.UnitAddTorus.mFourier k :=
      ContinuousMap.coeFn_toLp μT (_root_.UnitAddTorus.mFourier k)
    have hz : z =ᵐ[μT] fun x ↦ c * _root_.UnitAddTorus.mFourier k x := by
      filter_upwards [Lp.coeFn_smul c (_root_.UnitAddTorus.mFourierLp 2 k), hmode]
        with x hx hm
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hm]
    have hre : reL z =ᵐ[μT] fun x ↦ Complex.reCLM (z x) := by
      change Complex.reCLM.compLp z =ᵐ[μT] fun x ↦ Complex.reCLM (z x)
      exact Complex.reCLM.coeFn_compLp z
    have hright : reL z =ᵐ[volume]
        fun x ↦ (q * a * _root_.UnitAddTorus.mFourier k x).re := by
      have hπ : reL z =ᵐ[μT]
          fun x ↦ (q * a * _root_.UnitAddTorus.mFourier k x).re := by
        filter_upwards [hre, hz] with x hx hy
        rw [hx, hy, hcoeffDerivative]
        simp only [Complex.reCLM_apply]
      simpa only [volume_eq_pi_haarAddCircle] using hπ
    filter_upwards [hatom, normalizedHaarToVolumeL_ae (reL z), hright]
      with x hleft htransfer hrightx
    rw [hleft, htransfer, hrightx]
  have hseries : HasSum (fun k ↦ weakDeriv (fourierTerm u k) i)
      (normalizedHaarToVolumeL ℝ (reL (complexWeakDeriv u i))) :=
    hvolume.congr_fun hterm
  have hlimit : normalizedHaarToVolumeL ℝ (reL (complexWeakDeriv u i)) =
      weakDeriv u i := by
    apply Lp.ext
    filter_upwards [normalizedHaarToVolumeL_ae (reL (complexWeakDeriv u i)),
      show reL (complexWeakDeriv u i) =ᵐ[volume] fun x ↦ weakDeriv u i x by
        filter_upwards [show reL (complexWeakDeriv u i) =ᵐ[volume]
            fun x ↦ Complex.reCLM (complexWeakDeriv u i x) by
              have hre : reL (complexWeakDeriv u i) =ᵐ[μT]
                  fun x ↦ Complex.reCLM (complexWeakDeriv u i x) := by
                change Complex.reCLM.compLp (complexWeakDeriv u i) =ᵐ[μT]
                  fun x ↦ Complex.reCLM (complexWeakDeriv u i x)
                exact Complex.reCLM.coeFn_compLp (complexWeakDeriv u i)
              simpa only [volume_eq_pi_haarAddCircle] using hre,
          show complexWeakDeriv u i =ᵐ[volume]
              fun x ↦ (weakDeriv u i x : ℂ) by
            simpa only [volume_eq_pi_haarAddCircle] using complexWeakDeriv_ae u i]
            with x hx hu
        rw [hx, hu]
        simp only [Complex.reCLM_apply, Complex.ofReal_re]] with x hx hy
    rw [hx, hy]
  rw [hlimit] at hseries
  exact hseries

/-- Lift unconditional convergence of values and all weak coordinate derivatives to convergence
in the full `PeriodicW12` graph norm. -/
theorem hasSum_of_value_weakDeriv {ι : Type*}
    (f : ι → PeriodicW12 d) (u : PeriodicW12 d)
    (hvalue : HasSum (fun n ↦ value (f n)) (value u))
    (hderiv : ∀ i : d, HasSum (fun n ↦ weakDeriv (f n) i) (weakDeriv u i)) :
    HasSum f u := by
  change Tendsto (fun s : Finset ι ↦ ∑ n ∈ s, value (f n))
    atTop (nhds (value u)) at hvalue
  change ∀ i : d, Tendsto (fun s : Finset ι ↦ ∑ n ∈ s, weakDeriv (f n) i)
    atTop (nhds (weakDeriv u i)) at hderiv
  change Tendsto (fun s : Finset ι ↦ ∑ n ∈ s, f n) atTop (nhds u)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hvalueNorm : Tendsto
      (fun s : Finset ι ↦ ‖(∑ n ∈ s, value (f n)) - value u‖ ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hvalue).pow 2
  have hderivNorm (i : d) : Tendsto
      (fun s : Finset ι ↦ ‖(∑ n ∈ s, weakDeriv (f n) i) - weakDeriv u i‖ ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp (hderiv i)).pow 2
  have hderivSum : Tendsto
      (fun s : Finset ι ↦
        ∑ i : d, ‖(∑ n ∈ s, weakDeriv (f n) i) - weakDeriv u i‖ ^ 2)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ hderivNorm i)
  have hsq := hvalueNorm.add hderivSum
  have hsq' : Tendsto
      (fun s : Finset ι ↦ ‖(∑ n ∈ s, f n) - u‖ ^ 2) atTop (nhds 0) := by
    convert hsq using 1
    · funext s
      rw [norm_sq_eq_norm_value_sq_add_sum_norm_weakDeriv_sq]
      congr 1
      · rw [← valueL_apply, map_sub, map_sum]
        simp only [valueL_apply]
      · apply Finset.sum_congr rfl
        intro i _
        rw [← weakDerivL_apply, map_sub, map_sum]
        simp only [weakDerivL_apply]
    · simp
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq'
  change Tendsto (fun s : Finset ι ↦ Real.sqrt (‖(∑ n ∈ s, f n) - u‖ ^ 2))
    atTop (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The real Fourier terms of `u` sum unconditionally to `u` in the full periodic `W¹,²` graph
norm. -/
theorem hasSum_fourierTerm (u : PeriodicW12 d) :
    HasSum (fourierTerm u) u :=
  hasSum_of_value_weakDeriv _ _ (hasSum_value_fourierTerm u)
    (hasSum_weakDeriv_fourierTerm u)

/-- Truncate the real Fourier expansion of `u` to an arbitrary finite set of frequencies. -/
def fourierTruncation (u : PeriodicW12 d) (S : Finset (d → ℤ)) :
    PeriodicW12 d :=
  ∑ k ∈ S, fourierTerm u k

/-- Unfolding formula for a finite real Fourier truncation. -/
theorem fourierTruncation_eq_sum (u : PeriodicW12 d) (S : Finset (d → ℤ)) :
    fourierTruncation u S = ∑ k ∈ S, fourierTerm u k := by
  rfl

/-- A periodic `W¹,²` class is a real trigonometric polynomial when it is a finite sum of the
real Fourier atoms.  Complex amplitudes are allowed because `realMFourierAtom` takes the real
part explicitly, so this predicate contains only real-valued Sobolev classes. -/
def IsRealTrigonometricPolynomial (v : PeriodicW12 d) : Prop :=
  ∃ (S : Finset (d → ℤ)) (a : (d → ℤ) → ℂ),
    v = ∑ k ∈ S, realMFourierAtom (a k) k

/-- Every finite Fourier truncation is a real trigonometric polynomial. -/
theorem isRealTrigonometricPolynomial_fourierTruncation
    (u : PeriodicW12 d) (S : Finset (d → ℤ)) :
    IsRealTrigonometricPolynomial (fourierTruncation u S) := by
  exact ⟨S, fun k ↦ _root_.UnitAddTorus.mFourierCoeff
    (fun x ↦ (value u x : ℂ)) k, rfl⟩

private theorem value_sum_realMFourierAtom_ae
    (a : (d → ℤ) → ℂ) (S : Finset (d → ℤ)) :
    value (∑ k ∈ S, realMFourierAtom (a k) k) =ᵐ[volume]
      fun x ↦ ∑ k ∈ S, (a k * _root_.UnitAddTorus.mFourier k x).re := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [← valueL_apply, map_zero]
      exact Lp.coeFn_zero ℝ 2 volume
  | @insert k S hk ih =>
      rw [Finset.sum_insert hk]
      rw [← valueL_apply, map_add]
      simp only [valueL_apply]
      filter_upwards [Lp.coeFn_add
          (value (realMFourierAtom (a k) k))
          (value (∑ n ∈ S, realMFourierAtom (a n) n)),
        value_realMFourierAtom_ae (a k) k, ih] with x hadd hmode htail
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hmode, htail, Finset.sum_insert hk]

private theorem weakDeriv_sum_realMFourierAtom_ae
    (a : (d → ℤ) → ℂ) (S : Finset (d → ℤ)) (i : d) :
    weakDeriv (∑ k ∈ S, realMFourierAtom (a k) k) i =ᵐ[volume]
      fun x ↦ ∑ k ∈ S, (2 * Real.pi * Complex.I * (k i) * a k *
        _root_.UnitAddTorus.mFourier k x).re := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [← weakDerivL_apply, map_zero]
      exact Lp.coeFn_zero ℝ 2 volume
  | @insert k S hk ih =>
      rw [Finset.sum_insert hk]
      rw [← weakDerivL_apply, map_add]
      simp only [weakDerivL_apply]
      filter_upwards [Lp.coeFn_add
          (weakDeriv (realMFourierAtom (a k) k) i)
          (weakDeriv (∑ n ∈ S, realMFourierAtom (a n) n) i),
        weakDeriv_realMFourierAtom_ae (a k) k i, ih] with x hadd hmode htail
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hmode, htail, Finset.sum_insert hk]

/-- The value representative of a finite Fourier truncation is the expected finite real
trigonometric sum, almost everywhere. -/
theorem value_fourierTruncation_ae
    (u : PeriodicW12 d) (S : Finset (d → ℤ)) :
    value (fourierTruncation u S) =ᵐ[volume]
      fun x ↦ ∑ k ∈ S,
        (_root_.UnitAddTorus.mFourierCoeff (fun y ↦ (value u y : ℂ)) k *
          _root_.UnitAddTorus.mFourier k x).re := by
  exact value_sum_realMFourierAtom_ae _ S

/-- Coordinate `i` of a finite Fourier truncation's weak gradient carries the exact positive
multiplier `2 * π * I * k i`, almost everywhere. -/
theorem weakDeriv_fourierTruncation_ae
    (u : PeriodicW12 d) (S : Finset (d → ℤ)) (i : d) :
    weakDeriv (fourierTruncation u S) i =ᵐ[volume]
      fun x ↦ ∑ k ∈ S,
        (2 * Real.pi * Complex.I * (k i) *
          _root_.UnitAddTorus.mFourierCoeff (fun y ↦ (value u y : ℂ)) k *
          _root_.UnitAddTorus.mFourier k x).re := by
  exact weakDeriv_sum_realMFourierAtom_ae _ S i

/-- The net of arbitrary finite Fourier truncations converges to `u` in the full `PeriodicW12`
graph norm.  This theorem deliberately makes no pointwise-convergence claim. -/
theorem tendsto_fourierTruncation (u : PeriodicW12 d) :
    Tendsto (fourierTruncation u) atTop (nhds u) := by
  exact hasSum_fourierTerm u

/-- Real trigonometric polynomials are dense in the scalar periodic `W¹,²` graph norm. -/
theorem dense_realTrigonometricPolynomial :
    Dense {v : PeriodicW12 d | IsRealTrigonometricPolynomial v} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro u
  exact mem_closure_of_tendsto (tendsto_fourierTruncation u)
    (Filter.Eventually.of_forall fun S ↦
      isRealTrigonometricPolynomial_fourierTruncation u S)

/-- Consumer-facing graph-norm approximation: every periodic `W¹,²` class is within any positive
`ε` of a real trigonometric polynomial. -/
theorem exists_realTrigonometricPolynomial_norm_sub_lt
    (u : PeriodicW12 d) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : PeriodicW12 d,
      IsRealTrigonometricPolynomial v ∧ ‖u - v‖ < ε := by
  obtain ⟨v, hv, hdist⟩ :=
    dense_realTrigonometricPolynomial.exists_dist_lt u hε
  exact ⟨v, hv, by simpa only [dist_eq_norm] using hdist⟩

end PeriodicW12

end UnitAddTorus
