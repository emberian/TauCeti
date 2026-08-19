/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.FourierTest
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Uniqueness of periodic weak coordinate derivatives

This file proves the `L¹` fundamental lemma needed to make periodic weak coordinate derivatives
unique almost everywhere. Mathlib's multivariate Fourier monomials are uniformly dense in the
complex continuous functions on a finite unit torus. Pairing an integrable real field with a
continuous function defines a continuous linear functional, so annihilating every Fourier mode
forces the functional to annihilate every continuous function.

The final passage from continuous test fields to almost-everywhere equality is measure-theoretic,
not a choice of an `L¹` representative. The positive and negative density measures of the field
agree on every compactly supported continuous function, hence agree by regular-measure
extensionality.
The injectivity of vector-measure density then gives almost-everywhere vanishing.

Real and imaginary Fourier modes are admissible coordinate tests by
`TauCeti.Analysis.Sobolev.Periodic.FourierTest`. Subtracting two weak-derivative relations therefore
annihilates every complex Fourier mode, and the fundamental lemma gives uniqueness for the original
`L¹` candidates. This advances Layer 0, item 3 of the `IncompressibleFlows` roadmap.

## Main declarations

* `UnitAddTorus.ae_eq_zero_of_integral_mFourier_mul_eq_zero`: `L¹` Fourier separation for
  real fields on a finite unit torus.
* `UnitAddTorus.HasWeakCoordinateDerivative.ae_eq_deriv`: almost-everywhere uniqueness of
  periodic weak coordinate derivatives.
* `UnitAddTorus.HasWeakCoordinateDerivative.ae_eq_coordinateDerivative`: agreement with an
  integrable classical coordinate derivative.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory Set Algebra Submodule TopologicalSpace
open scoped ENNReal ComplexConjugate

variable {d : Type*} [Fintype d]

/-- Pair a complex continuous field with a fixed real `L¹` density. -/
private def continuousIntegralPairing (h : _root_.UnitAddTorus d → ℝ)
    (hh : Integrable h) : C(_root_.UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ ↦ ∫ x, φ x * (h x : ℂ)
      map_add' := by
        intro φ ψ
        simp only [ContinuousMap.add_apply, add_mul]
        rw [integral_add]
        · exact hh.ofReal.mul_of_top_right
            (φ.continuous.memLp_top_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace φ) volume)
        · exact hh.ofReal.mul_of_top_right
            (ψ.continuous.memLp_top_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace ψ) volume)
      map_smul' := by
        intro c φ
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
          integral_const_mul] }
    (∫ x, ‖h x‖)
    (by
      intro φ
      calc
        ‖∫ x, φ x * (h x : ℂ)‖ ≤ ∫ x, ‖φ x * (h x : ℂ)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖φ‖ * ‖h x‖ := by
          refine integral_mono ?_ (hh.norm.const_mul ‖φ‖) fun x ↦ ?_
          · exact hh.ofReal.mul_of_top_right
              (φ.continuous.memLp_top_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace φ) volume) |>.norm
          rw [norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)
        _ = ‖φ‖ * ∫ x, ‖h x‖ := by rw [integral_const_mul]
        _ ≤ (∫ x, ‖h x‖) * ‖φ‖ := by rw [mul_comm])

/-- An integrable real field whose pairing with every Fourier monomial vanishes is zero almost
everywhere. This is the `L¹` Fourier-separation theorem on a finite unit torus. -/
theorem ae_eq_zero_of_integral_mFourier_mul_eq_zero
    {h : _root_.UnitAddTorus d → ℝ} (hh : Integrable h)
    (hmode : ∀ m : d → ℤ,
      (∫ x, _root_.UnitAddTorus.mFourier m x * (h x : ℂ)) = 0) :
    h =ᵐ[volume] 0 := by
  let L := continuousIntegralPairing h hh
  have hrange : range (_root_.UnitAddTorus.mFourier (d := d)) ⊆ L.ker := by
    rintro φ ⟨m, rfl⟩
    change L (_root_.UnitAddTorus.mFourier m) = 0
    exact hmode m
  have hspan : span ℂ (range (_root_.UnitAddTorus.mFourier (d := d))) ≤ L.ker :=
    span_le.2 hrange
  have hclosure :
      (span ℂ (range (_root_.UnitAddTorus.mFourier (d := d)))).topologicalClosure ≤ L.ker :=
    (span ℂ (range (_root_.UnitAddTorus.mFourier (d := d)))).topologicalClosure_minimal
      hspan L.isClosed_ker
  rw [_root_.UnitAddTorus.span_mFourier_closure_eq_top] at hclosure
  have hall : ∀ φ : C(_root_.UnitAddTorus d, ℂ), L φ = 0 := by
    intro φ
    exact hclosure Submodule.mem_top
  have hall_real : ∀ φ : C(_root_.UnitAddTorus d, ℝ), ∫ x, φ x * h x = 0 := by
    intro φ
    let φc : C(_root_.UnitAddTorus d, ℂ) :=
      ⟨fun x ↦ (φ x : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩
    have hpair := hall φc
    change (∫ x, φc x * (h x : ℂ)) = 0 at hpair
    have hint : Integrable (fun x ↦ φc x * (h x : ℂ)) :=
      hh.ofReal.mul_of_top_right
        (φc.continuous.memLp_top_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace φc) volume)
    have hre : ∫ x, (φc x * (h x : ℂ)).re = 0 := by
      calc
        (∫ x, (φc x * (h x : ℂ)).re) = (∫ x, φc x * (h x : ℂ)).re :=
          integral_re hint
        _ = 0 := by rw [hpair]; rfl
    simpa [φc] using hre
  let μpos : Measure (_root_.UnitAddTorus d) :=
    volume.withDensity fun x ↦ ENNReal.ofReal (h x)
  let μneg : Measure (_root_.UnitAddTorus d) :=
    volume.withDensity fun x ↦ ENNReal.ofReal (-h x)
  let _ : IsFiniteMeasure μpos := isFiniteMeasure_withDensity_ofReal hh.2
  let _ : IsFiniteMeasure μneg := isFiniteMeasure_withDensity_ofReal hh.neg.2
  have hμ : μpos = μneg := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro φ
    have hmeas : AEMeasurable h volume := hh.aestronglyMeasurable.aemeasurable
    have hφtop : MemLp (φ : _root_.UnitAddTorus d → ℝ) ∞ :=
      φ.continuous.memLp_top_of_hasCompactSupport φ.hasCompactSupport volume
    have hpos : Integrable (fun x ↦ max (h x) 0 * φ x) := by
      exact (hh.pos_part.mul_of_top_right hφtop).congr <|
        Filter.Eventually.of_forall fun x ↦ by simp only [Pi.mul_apply, mul_comm]
    have hneg : Integrable (fun x ↦ max (-h x) 0 * φ x) := by
      exact (hh.neg_part.mul_of_top_right hφtop).congr <|
        Filter.Eventually.of_forall fun x ↦ by simp only [Pi.mul_apply, mul_comm]
    change (∫ x, φ x ∂volume.withDensity fun x ↦ ENNReal.ofReal (h x)) =
      ∫ x, φ x ∂volume.withDensity fun x ↦ ENNReal.ofReal (-h x)
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) φ,
      integral_withDensity_eq_integral_toReal_smul₀ hmeas.fun_neg.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) φ]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    rw [← sub_eq_zero, ← integral_sub hpos hneg]
    convert hall_real φ.toContinuousMap using 1
    exact integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ by
      change max (h x) 0 * φ x - max (-h x) 0 * φ x = φ x * h x
      rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      exact mul_comm _ _
  have hdensity : volume.withDensityᵥ h = 0 := by
    rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hh]
    change μpos.toSignedMeasure - μneg.toSignedMeasure = 0
    rw [Measure.toSignedMeasure_congr hμ, sub_self]
  rw [← (hh.withDensityᵥ_eq_iff (integrable_zero _ _ _))]
  rw [withDensityᵥ_zero]
  exact hdensity

/-- A real integrable field has at most one weak derivative in a fixed torus coordinate. -/
theorem HasWeakCoordinateDerivative.ae_eq_deriv [DecidableEq d]
    {f f' g' : _root_.UnitAddTorus d → ℝ} {i : d}
    (hf : HasWeakCoordinateDerivative f f' i)
    (hg : HasWeakCoordinateDerivative f g' i) :
    f' =ᵐ[volume] g' := by
  let h : _root_.UnitAddTorus d → ℝ := f' - g'
  have hweak : HasWeakCoordinateDerivative (f - f) h i := hf.sub hg
  have hint : Integrable h := hweak.integrable_deriv
  have hmode : ∀ m : d → ℤ,
      (∫ x, _root_.UnitAddTorus.mFourier m x * (h x : ℂ)) = 0 := by
    intro m
    have hre_relation := hweak.integral_coordinateDerivative_mul_eq_neg_integral_mul
      (mFourierReCoordinateTest m i)
    have him_relation := hweak.integral_coordinateDerivative_mul_eq_neg_integral_mul
      (mFourierImCoordinateTest m i)
    have hre : ∫ x, (_root_.UnitAddTorus.mFourier m x).re * h x = 0 := by
      have hzero : 0 = -∫ x, (_root_.UnitAddTorus.mFourier m x).re * h x := by
        simpa only [Pi.sub_apply, sub_self, mul_zero, integral_zero,
          mFourierReCoordinateTest_apply] using hre_relation
      linarith
    have him : ∫ x, (_root_.UnitAddTorus.mFourier m x).im * h x = 0 := by
      have hzero : 0 = -∫ x, (_root_.UnitAddTorus.mFourier m x).im * h x := by
        simpa only [Pi.sub_apply, sub_self, mul_zero, integral_zero,
          mFourierImCoordinateTest_apply] using him_relation
      linarith
    have hpair_int : Integrable
        (fun x ↦ _root_.UnitAddTorus.mFourier m x * (h x : ℂ)) :=
      hint.ofReal.mul_of_top_right <|
        (_root_.UnitAddTorus.mFourier m).continuous.memLp_top_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace (_root_.UnitAddTorus.mFourier m)) volume
    apply Complex.ext
    · calc
        (∫ x, _root_.UnitAddTorus.mFourier m x * (h x : ℂ)).re =
            ∫ x, (_root_.UnitAddTorus.mFourier m x * (h x : ℂ)).re :=
          (integral_re hpair_int).symm
        _ = ∫ x, (_root_.UnitAddTorus.mFourier m x).re * h x := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        _ = 0 := hre
        _ = (0 : ℂ).re := rfl
    · calc
        (∫ x, _root_.UnitAddTorus.mFourier m x * (h x : ℂ)).im =
            ∫ x, (_root_.UnitAddTorus.mFourier m x * (h x : ℂ)).im :=
          (integral_im hpair_int).symm
        _ = ∫ x, (_root_.UnitAddTorus.mFourier m x).im * h x := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
        _ = 0 := him
        _ = (0 : ℂ).im := rfl
  have hzero : h =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_mFourier_mul_eq_zero hint hmode
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

/-- A weak derivative agrees almost everywhere with the integrable classical coordinate
derivative whenever the original field is classically `C¹` along that coordinate. -/
theorem HasWeakCoordinateDerivative.ae_eq_coordinateDerivative [DecidableEq d]
    {f f' : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative f f' i)
    (hf : ContDiffAlongCoordinate f i)
    (hdf : Integrable (coordinateDerivative f i)) :
    f' =ᵐ[volume] coordinateDerivative f i :=
  h.ae_eq_deriv <| hasWeakCoordinateDerivative_coordinateDerivative
    f i hf h.integrable hdf

/-- A weak coordinate derivative of a constant field vanishes almost everywhere. This is a
nontrivial check that uniqueness specializes to the zero Fourier-gradient mode. -/
theorem HasWeakCoordinateDerivative.ae_eq_zero_deriv_of_const [DecidableEq d]
    {c : ℝ} {g : _root_.UnitAddTorus d → ℝ} {i : d}
    (h : HasWeakCoordinateDerivative (fun _ ↦ c) g i) :
    g =ᵐ[volume] 0 :=
  h.ae_eq_deriv (hasWeakCoordinateDerivative_const c i)

end UnitAddTorus
