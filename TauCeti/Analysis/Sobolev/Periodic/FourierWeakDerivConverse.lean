/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx, Codex
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.FourierWeakDeriv

/-!
# Converse Fourier characterization of periodic weak derivatives

This file proves the converse to the Fourier-energy theorem in `Periodic.FourierWeakDeriv`.
Starting from a real `L²` field with summable Fourier Dirichlet energy, it constructs each
coordinate derivative by applying `UnitAddTorus.mFourierBasis.repr.symm` to the square-summable
coefficient family

`k ↦ 2 * π * I * k i * hat(f)(k)`.

The construction remains genuinely real.  Fourier coefficients of a real field have conjugate
symmetry, which the derivative multiplier preserves.  Fourier-coefficient uniqueness therefore
shows that the synthesized complex `L²` class is fixed by conjugation; its real part supplies the
required real representative.

No smooth-density result is assumed.  For an arbitrary existing coordinate test `φ`, both `φ` and
`∂ᵢφ` are in `L²` by their `L∞` hypotheses.  The already-proved classical multiplier formula
for `φ`, together with polarized Parseval for the pairs `(∂ᵢφ, f)` and `(φ, ∂ᵢf)`, proves the
full weak integration-by-parts identity term by term.

Together with the forward energy identity, this gives the existence half of the periodic `W¹²`
Fourier characterization requested by Layer 0 of the `IncompressibleFlows` roadmap, without yet
introducing a full Sobolev-space structure.

## Main declarations

* `mFourierCoeff_ofReal_neg`: conjugate symmetry for an integrable real field.
* `exists_weakCoordinateDerivatives_of_summable_mFourierDirichletTerm`: synthesis of real `L²`
  weak coordinate derivatives from finite Fourier Dirichlet energy.
* `summable_mFourierDirichletTerm_iff_exists_weakCoordinateDerivatives`: the resulting
  Fourier/weak-derivative characterization.
-/

public section

noncomputable section

namespace UnitAddTorus

open MeasureTheory
open scoped ComplexConjugate ENNReal lp

variable {d : Type*} [Fintype d]

/-- Fourier coefficients of an integrable real field have conjugate symmetry. -/
theorem mFourierCoeff_ofReal_neg
    (f : _root_.UnitAddTorus d → ℝ) (_hf : Integrable f) (k : d → ℤ) :
    _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) (-k) =
      conj (_root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k) := by
  unfold _root_.UnitAddTorus.mFourierCoeff
  simp only [neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [_root_.UnitAddTorus.mFourier_neg]
  simp

private theorem norm_sq_mFourierMultiplier
    (F : _root_.UnitAddTorus d → ℂ) (i : d) (k : d → ℤ) :
    ‖(2 * Real.pi * Complex.I * (k i)) *
        _root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (k i : ℝ) ^ 2 *
        ‖_root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  congr 1
  rw [norm_mul, norm_mul,
    show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num,
    Complex.norm_real, Complex.norm_I, Complex.norm_intCast, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos), mul_one, mul_pow, sq_abs]

private theorem mFourierCoeff_star
    (G : Lp ℂ 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle)) (k : d → ℤ) :
    _root_.UnitAddTorus.mFourierCoeff
        ((star G : Lp ℂ 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle)) :
          _root_.UnitAddTorus d → ℂ) k =
      conj (_root_.UnitAddTorus.mFourierCoeff G (-k)) := by
  unfold _root_.UnitAddTorus.mFourierCoeff
  simp only [neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star G] with x hx
  rw [hx]
  simp only [_root_.UnitAddTorus.mFourier_neg]
  simp

variable [DecidableEq d]

omit [DecidableEq d] in
private theorem exists_complex_fourierCoordinateDerivative
    (F : Lp ℂ 2 (volume : Measure (_root_.UnitAddTorus d)))
    (henergy : Summable (mFourierDirichletTerm F)) (i : d) :
    ∃ G : Lp ℂ 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle),
      ∀ k : d → ℤ, _root_.UnitAddTorus.mFourierCoeff G k =
        (2 * Real.pi * Complex.I * (k i)) *
          _root_.UnitAddTorus.mFourierCoeff F k := by
  classical
  let c (k : d → ℤ) : ℂ := (2 * Real.pi * Complex.I * (k i)) *
    _root_.UnitAddTorus.mFourierCoeff F k
  have hle (k : d → ℤ) : ‖c k‖ ^ 2 ≤ mFourierDirichletTerm F k := by
    rw [show ‖c k‖ ^ 2 = (2 * Real.pi) ^ 2 * (k i : ℝ) ^ 2 *
      ‖_root_.UnitAddTorus.mFourierCoeff F k‖ ^ 2 from norm_sq_mFourierMultiplier F i k,
      mFourierDirichletTerm_eq_sum]
    gcongr
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  have hcsq : Summable fun k : d → ℤ ↦ ‖c k‖ ^ 2 :=
    henergy.of_nonneg_of_le (fun k ↦ sq_nonneg ‖c k‖) hle
  have hc : Memℓp c 2 := by
    apply memℓp_gen
    simpa using hcsq
  let C : ℓ²(d → ℤ, ℂ) := ⟨c, hc⟩
  let G : Lp ℂ 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle) :=
    (_root_.UnitAddTorus.mFourierBasis (d := d)).repr.symm C
  refine ⟨G, ?_⟩
  intro k
  rw [← _root_.UnitAddTorus.mFourierBasis_repr]
  change ((_root_.UnitAddTorus.mFourierBasis (d := d)).repr G) k = c k
  rw [show G = (_root_.UnitAddTorus.mFourierBasis (d := d)).repr.symm C from rfl,
    LinearIsometryEquiv.apply_symm_apply]

omit [DecidableEq d] in
private theorem exists_real_complex_fourierCoordinateDerivative
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2)
    (henergy : Summable (mFourierDirichletTerm
      (hf.ofReal.toLp (fun x ↦ (f x : ℂ))))) (i : d) :
    ∃ G : Lp ℂ 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle),
      (∀ k : d → ℤ, _root_.UnitAddTorus.mFourierCoeff G k =
        (2 * Real.pi * Complex.I * (k i)) *
          _root_.UnitAddTorus.mFourierCoeff
            (hf.ofReal.toLp (fun x ↦ (f x : ℂ))) k) ∧
      (fun x ↦ ((G x).re : ℂ)) =ᵐ[
        Measure.pi fun _ : d ↦ AddCircle.haarAddCircle] G := by
  classical
  let F : Lp ℂ 2 (volume : Measure (_root_.UnitAddTorus d)) :=
    hf.ofReal.toLp (fun x ↦ (f x : ℂ))
  obtain ⟨G, hG⟩ := exists_complex_fourierCoordinateDerivative F henergy i
  have hFneg (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff F (-k) =
        conj (_root_.UnitAddTorus.mFourierCoeff F k) := by
    rw [show F = hf.ofReal.toLp (fun x ↦ (f x : ℂ)) from rfl,
      mFourierCoeff_toLp_complexification f hf (-k),
      mFourierCoeff_toLp_complexification f hf k]
    exact mFourierCoeff_ofReal_neg f (hf.integrable one_le_two) k
  have hGneg (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff G (-k) =
        conj (_root_.UnitAddTorus.mFourierCoeff G k) := by
    rw [hG, hG, hFneg]
    simp only [Pi.neg_apply, Int.cast_neg]
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hstar : star G = G := by
    apply (_root_.UnitAddTorus.mFourierBasis (d := d)).repr.injective
    ext k
    rw [_root_.UnitAddTorus.mFourierBasis_repr,
      _root_.UnitAddTorus.mFourierBasis_repr, mFourierCoeff_star, hGneg]
    simp
  refine ⟨G, ?_, ?_⟩
  · intro k
    exact hG k
  · have hcoe := Lp.coeFn_star G
    rw [hstar] at hcoe
    filter_upwards [hcoe] with x hx
    apply Complex.ext
    · simp
    · have him := congrArg Complex.im hx
      change (G x).im = -(G x).im at him
      simp only [Complex.ofReal_im]
      linarith

private theorem hasWeakCoordinateDerivative_of_complexSynthesis
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2) (i : d)
    (G : Lp ℂ 2 (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle))
    (hG : ∀ k : d → ℤ, _root_.UnitAddTorus.mFourierCoeff G k =
      (2 * Real.pi * Complex.I * (k i)) *
        _root_.UnitAddTorus.mFourierCoeff
          (hf.ofReal.toLp (fun x ↦ (f x : ℂ))) k)
    (hreal : (fun x ↦ ((G x).re : ℂ)) =ᵐ[
      Measure.pi fun _ : d ↦ AddCircle.haarAddCircle] G) :
    HasWeakCoordinateDerivative f (fun x ↦ (G x).re) i := by
  let μF : Measure (_root_.UnitAddTorus d) :=
    Measure.pi fun _ : d ↦ AddCircle.haarAddCircle
  let g : _root_.UnitAddTorus d → ℝ := fun x ↦ (G x).re
  have hgπ : MemLp g 2 μF := (Lp.memLp G).re
  have hg : MemLp g 2 (volume : Measure (_root_.UnitAddTorus d)) := by
    exact Eq.mpr
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦ MemLp g 2 μ)
        volume_eq_pi_haarAddCircle)
      hgπ
  rw [hasWeakCoordinateDerivative_iff]
  refine ⟨hf.integrable one_le_two, hg.integrable one_le_two, ?_⟩
  intro φ
  have hfπ : MemLp (fun x ↦ (f x : ℂ)) 2 μF := by
    have hfC : MemLp (fun x ↦ (f x : ℂ)) 2
        (volume : Measure (_root_.UnitAddTorus d)) := hf.ofReal
    exact Eq.mp
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦
        MemLp (fun x ↦ (f x : ℂ)) 2 μ) volume_eq_pi_haarAddCircle)
      hfC
  have hφtopπ : MemLp (φ : _root_.UnitAddTorus d → ℝ) ∞ μF := by
    exact Eq.mp
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦
        MemLp (φ : _root_.UnitAddTorus d → ℝ) ∞ μ) volume_eq_pi_haarAddCircle)
      φ.memLp_top
  have hDφtopπ : MemLp (coordinateDerivative φ i) ∞ μF := by
    exact Eq.mp
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦
        MemLp (coordinateDerivative φ i) ∞ μ) volume_eq_pi_haarAddCircle)
      φ.coordinateDerivative_memLp_top
  have hφπ : MemLp (fun x ↦ (φ x : ℂ)) 2 μF :=
    (hφtopπ.mono_exponent (by simp)).ofReal
  have hDφπ : MemLp (fun x ↦ (coordinateDerivative φ i x : ℂ)) 2 μF :=
    (hDφtopπ.mono_exponent (by simp)).ofReal
  let FLp : Lp ℂ 2 μF := hfπ.toLp (fun x ↦ (f x : ℂ))
  let Phi : Lp ℂ 2 μF := hφπ.toLp (fun x ↦ (φ x : ℂ))
  let DPhi : Lp ℂ 2 μF :=
    hDφπ.toLp (fun x ↦ (coordinateDerivative φ i x : ℂ))
  have hφweak : HasWeakCoordinateDerivative
      (φ : _root_.UnitAddTorus d → ℝ) (coordinateDerivative φ i) i :=
    hasWeakCoordinateDerivative_coordinateDerivative φ i φ.contDiffAlongCoordinate
      (φ.memLp_top.integrable (by simp))
      (φ.coordinateDerivative_memLp_top.integrable (by simp))
  have hFLp (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff FLp k =
        _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k :=
    mFourierCoeff_toLp_normalizedHaar hfπ k
  have hPhi (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff Phi k =
        _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (φ x : ℂ)) k :=
    mFourierCoeff_toLp_normalizedHaar hφπ k
  have hDPhi (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff DPhi k =
        _root_.UnitAddTorus.mFourierCoeff
          (fun x ↦ (coordinateDerivative φ i x : ℂ)) k :=
    mFourierCoeff_toLp_normalizedHaar hDφπ k
  have hG' (k : d → ℤ) :
      _root_.UnitAddTorus.mFourierCoeff G k =
        (2 * Real.pi * Complex.I * (k i)) *
          _root_.UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
    rw [hG, mFourierCoeff_toLp_complexification f hf k]
  have hfactor (k : d → ℤ) :
      conj (2 * Real.pi * Complex.I * (k i)) =
        -(2 * Real.pi * Complex.I * (k i)) := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hterm (k : d → ℤ) :
      conj (_root_.UnitAddTorus.mFourierCoeff DPhi k) *
          _root_.UnitAddTorus.mFourierCoeff FLp k =
        -(conj (_root_.UnitAddTorus.mFourierCoeff Phi k) *
          _root_.UnitAddTorus.mFourierCoeff G k) := by
    rw [hDPhi, hFLp, hPhi, hG', hφweak.mFourierCoeff_ofReal k, map_mul, hfactor]
    ring
  have hleft := _root_.UnitAddTorus.hasSum_prod_mFourierCoeff DPhi FLp
  have hright := _root_.UnitAddTorus.hasSum_prod_mFourierCoeff Phi G
  change HasSum
    (fun k ↦ conj (_root_.UnitAddTorus.mFourierCoeff DPhi k) *
      _root_.UnitAddTorus.mFourierCoeff FLp k)
    (∫ x, conj (DPhi x) * FLp x ∂μF) at hleft
  change HasSum
    (fun k ↦ conj (_root_.UnitAddTorus.mFourierCoeff Phi k) *
      _root_.UnitAddTorus.mFourierCoeff G k)
    (∫ x, conj (Phi x) * G x ∂μF) at hright
  have hend :
      (∫ x, conj (DPhi x) * FLp x ∂μF) =
        -(∫ x, conj (Phi x) * G x ∂μF) :=
    hleft.unique (hright.neg.congr_fun hterm)
  let L : ℝ := ∫ x, coordinateDerivative φ i x * f x ∂μF
  let R : ℝ := ∫ x, φ x * g x ∂μF
  have hleftEq : (∫ x, conj (DPhi x) * FLp x ∂μF) = (L : ℂ) := by
    calc
      _ = ∫ x, ((coordinateDerivative φ i x * f x : ℝ) : ℂ) ∂μF := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hDφπ, MemLp.coeFn_toLp hfπ] with x hDx hfx
        rw [hDx, hfx]
        simp
      _ = (L : ℂ) := by
        dsimp only [L]
        exact integral_complex_ofReal
  have hrightEq : (∫ x, conj (Phi x) * G x ∂μF) = (R : ℂ) := by
    calc
      _ = ∫ x, ((φ x * g x : ℝ) : ℂ) ∂μF := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hφπ, hreal] with x hφx hGx
        rw [hφx, ← hGx]
        simp [g]
      _ = (R : ℂ) := by
        dsimp only [R]
        exact integral_complex_ofReal
  rw [hleftEq, hrightEq] at hend
  have hrealEnd := congrArg Complex.re hend
  change L = -R at hrealEnd
  change (∫ x, coordinateDerivative φ i x * f x) = -∫ x, φ x * g x
  rw [volume_eq_pi_haarAddCircle]
  exact hrealEnd

/-- **Synthesis of periodic weak derivatives from finite Fourier Dirichlet energy.**

The returned real representatives are in `L²` and satisfy the full coordinate-test weak relation.
Their Fourier coefficients therefore have multiplier `2 * π * I * k i` by
`HasWeakCoordinateDerivative.mFourierCoeff_ofReal`. -/
theorem exists_weakCoordinateDerivatives_of_summable_mFourierDirichletTerm
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2)
    (henergy : Summable (mFourierDirichletTerm
      (hf.ofReal.toLp (fun x ↦ (f x : ℂ))))) :
    ∃ D : d → _root_.UnitAddTorus d → ℝ,
      (∀ i, MemLp (D i) 2) ∧
        ∀ i, HasWeakCoordinateDerivative f (D i) i := by
  choose G hG hreal using fun i ↦
    exists_real_complex_fourierCoordinateDerivative f hf henergy i
  let D (i : d) (x : _root_.UnitAddTorus d) : ℝ := (G i x).re
  have hD (i : d) : MemLp (D i) 2 := by
    have hDπ : MemLp (D i) 2
        (Measure.pi fun _ : d ↦ AddCircle.haarAddCircle) := (Lp.memLp (G i)).re
    exact Eq.mpr
      (congrArg (fun μ : Measure (_root_.UnitAddTorus d) ↦ MemLp (D i) 2 μ)
        volume_eq_pi_haarAddCircle)
      hDπ
  refine ⟨D, hD, ?_⟩
  intro i
  exact hasWeakCoordinateDerivative_of_complexSynthesis f hf i (G i) (hG i) (hreal i)

/-- A real periodic `L²` field has summable Fourier Dirichlet energy exactly when it has an `L²`
weak derivative in every coordinate.  This is the representative-level core of the periodic
`W¹²` Fourier characterization. -/
theorem summable_mFourierDirichletTerm_iff_exists_weakCoordinateDerivatives
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2) :
    Summable (mFourierDirichletTerm
      (hf.ofReal.toLp (fun x ↦ (f x : ℂ)))) ↔
      ∃ D : d → _root_.UnitAddTorus d → ℝ,
        (∀ i, MemLp (D i) 2) ∧
          ∀ i, HasWeakCoordinateDerivative f (D i) i := by
  constructor
  · exact exists_weakCoordinateDerivatives_of_summable_mFourierDirichletTerm f hf
  · rintro ⟨D, hD, hweak⟩
    exact (hasSum_mFourierDirichletTerm_of_weakCoordinateDerivatives
      f D hf hD hweak).summable

end UnitAddTorus
