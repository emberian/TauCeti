/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Sobolev.Periodic.W12
public import TauCeti.Analysis.Sobolev.Periodic.FourierWeakDerivConverse

/-!
# Fourier characterization of periodic W¹,²

This file identifies the scalar periodic graph space `PeriodicW12` with finite Fourier
Dirichlet energy.  For a periodic Sobolev class, the Dirichlet series has sum exactly the
squared `L²` norm of its weak gradient.  Conversely, an `L²` representative with summable
Dirichlet series determines a `PeriodicW12` class with the prescribed value class.

The converse assembles the coordinate weak derivatives synthesized by Fourier series into an
`L²` Euclidean gradient.  Its passage from representatives to `Lp` classes is explicit, so the
result does not rely on a smooth-density theorem or on a choice of representatives.

This advances Layer 0, items 3 and 4 of the `IncompressibleFlows` roadmap: it gives the
order-one Fourier/weak-derivative agreement before the full periodic Hilbert scale is defined.

## Main declarations

* `PeriodicW12.hasSum_mFourierDirichletTerm`: Fourier Dirichlet energy equals the squared weak
  gradient norm.
* `PeriodicW12.summable_mFourierDirichletTerm`: every periodic `W¹,²` class has finite Fourier
  Dirichlet energy.
* `exists_periodicW12_of_summable_mFourierDirichletTerm`: finite Dirichlet energy constructs a
  periodic `W¹,²` class with the prescribed value.
* `summable_mFourierDirichletTerm_iff_exists_periodicW12_value_eq`: the representative-safe
  Fourier characterization.
-/

public section

noncomputable section

namespace TauCeti.UnitAddTorus

open MeasureTheory

variable {d : Type*} [Fintype d]

attribute [local instance] Classical.decEq

namespace PeriodicW12

/-- The Fourier Dirichlet series of a periodic `W¹,²` class sums to the squared `L²` norm of
its weak gradient. -/
theorem hasSum_mFourierDirichletTerm (u : PeriodicW12 d) :
    HasSum
      (mFourierDirichletTerm
        ((Lp.memLp (value u)).ofReal.toLp (fun x ↦ (value u x : ℂ))))
      (‖gradient u‖ ^ 2) := by
  let D : d → _root_.UnitAddTorus d → ℝ := fun i x ↦ weakDeriv u i x
  have hD (i : d) : MemLp (D i) 2 := Lp.memLp (weakDeriv u i)
  have hweak (i : d) : HasWeakCoordinateDerivative (value u) (D i) i :=
    hasWeakCoordinateDerivative u i
  have hsum := hasSum_mFourierDirichletTerm_of_weakCoordinateDerivatives
    (value u) D (Lp.memLp (value u)) hD hweak
  have hcoord (i : d) : ∫ x, (D i x) ^ 2 = ‖weakDeriv u i‖ ^ 2 := by
    rw [← norm_sq_toLp_eq_integral_sq (D i) (hD i)]
    change ‖(hD i).toLp (weakDeriv u i)‖ ^ 2 = ‖weakDeriv u i‖ ^ 2
    rw [Lp.toLp_coeFn]
  rw [show ‖gradient u‖ ^ 2 = ∑ i, ‖weakDeriv u i‖ ^ 2 from
    norm_gradient_sq_eq_sum_norm_weakDeriv_sq u]
  simpa only [hcoord] using hsum

/-- The Fourier Dirichlet series of a periodic `W¹,²` class is summable. -/
theorem summable_mFourierDirichletTerm (u : PeriodicW12 d) :
    Summable
      (mFourierDirichletTerm
        ((Lp.memLp (value u)).ofReal.toLp (fun x ↦ (value u x : ℂ)))) :=
  (hasSum_mFourierDirichletTerm u).summable

end PeriodicW12

/-- Finite Fourier Dirichlet energy of a real `L²` representative constructs a periodic
`W¹,²` class whose value is the corresponding `Lp` class. -/
theorem exists_periodicW12_of_summable_mFourierDirichletTerm
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2)
    (henergy : Summable (mFourierDirichletTerm
      (hf.ofReal.toLp (fun x ↦ (f x : ℂ))))) :
    ∃ u : PeriodicW12 d, PeriodicW12.value u = hf.toLp f := by
  obtain ⟨D, hD, hweak⟩ :=
    exists_weakCoordinateDerivatives_of_summable_mFourierDirichletTerm f hf henergy
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
    have hvalue := (hweak i).congr_ae (MemLp.coeFn_toLp hf).symm
    apply hvalue.congr_ae_deriv
    filter_upwards [MemLp.coeFn_toLp hG,
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).coeFn_compLp G] with x hGx hprojx
    calc
      D i x = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i) (Gfun x) := rfl
      _ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i) (G x) := by rw [hGx]
      _ = ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d ↦ ℝ) i).compLp G) x := hprojx.symm
  let u : PeriodicW12 d := PeriodicW12.mk (hf.toLp f) G hproj
  exact ⟨u, PeriodicW12.value_mk (hf.toLp f) G hproj⟩

/-- A real periodic `L²` representative has summable Fourier Dirichlet energy exactly when its
`Lp` value class belongs to `PeriodicW12`. -/
theorem summable_mFourierDirichletTerm_iff_exists_periodicW12_value_eq
    (f : _root_.UnitAddTorus d → ℝ) (hf : MemLp f 2) :
    Summable (mFourierDirichletTerm
      (hf.ofReal.toLp (fun x ↦ (f x : ℂ)))) ↔
      ∃ u : PeriodicW12 d, PeriodicW12.value u = hf.toLp f := by
  constructor
  · exact exists_periodicW12_of_summable_mFourierDirichletTerm f hf
  · rintro ⟨u, hu⟩
    let D : d → _root_.UnitAddTorus d → ℝ := fun i x ↦ PeriodicW12.weakDeriv u i x
    have hD (i : d) : MemLp (D i) 2 := Lp.memLp (PeriodicW12.weakDeriv u i)
    have hvf : PeriodicW12.value u =ᵐ[volume] f := by
      rw [hu]
      exact MemLp.coeFn_toLp hf
    have hweak (i : d) : HasWeakCoordinateDerivative f (D i) i :=
      (PeriodicW12.hasWeakCoordinateDerivative u i).congr_ae hvf
    exact (hasSum_mFourierDirichletTerm_of_weakCoordinateDerivatives
      f D hf hD hweak).summable

end TauCeti.UnitAddTorus
