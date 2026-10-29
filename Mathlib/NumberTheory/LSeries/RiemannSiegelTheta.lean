/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Lince
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.NumberTheory.LSeries.HardyZ

/-!
# The Riemann–Siegel theta function

The Riemann–Siegel theta function `ϑ` is the argument of the archimedean factor `Γ_ℝ` on
the critical line. This file defines it as the imaginary part of a continuous logarithm of
`t ↦ Γ_ℝ (1/2 + it)`, which exists because `ℝ` is simply connected and `Γ_ℝ` does not
vanish on the critical line, and proves the relation asked for by the TODO in
`Mathlib.NumberTheory.LSeries.HardyZ`:

$$ Z(t) = e^{i\vartheta(t)}\,\zeta(1/2 + it). $$

The definition fixes no normalisation at `t = 0`: any two continuous arguments differ by a
constant multiple of `2π`, which drops out of `exp (I * ϑ t)`.

## Main results

* `riemannSiegelTheta`: the function `ℝ → ℝ`.
* `exp_I_riemannSiegelTheta`: `exp (I * ϑ t) = Γ_ℝ (1/2 + it) / ‖Γ_ℝ (1/2 + it)‖`.
* `hardyZ_eq_riemannZeta_mul_exp`: `Z t = ζ (1/2 + it) * exp (I * ϑ t)`.
-/

@[expose] public section

open Complex

namespace Complex

/-- `t ↦ Γ_ℝ (1/2 + it)` is continuous. -/
theorem continuousAt_Gammaℝ_half_add_mul_I (t : ℝ) :
    ContinuousAt (fun t : ℝ => Gammaℝ (1 / 2 + t * I)) t := by
  have hs : DifferentiableAt ℂ (fun s : ℂ => Gammaℝ s) (1 / 2 + t * I) := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) (1 / 2 + t * I) :=
      differentiable_Gammaℝ_inv.differentiableAt
    have hne : Gammaℝ (1 / 2 + t * I) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp)
    have h2 := h1.inv (inv_ne_zero hne)
    convert h2 using 2
    simp
  have hg : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t := by fun_prop
  have hcomp : ContinuousAt
      ((fun s : ℂ => Gammaℝ s) ∘ (fun t : ℝ => (1 / 2 : ℂ) + t * I)) t :=
    ContinuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + t * I)
      (g := fun s : ℂ => Gammaℝ s) hs.continuousAt hg
  simpa [Function.comp_def] using hcomp

theorem continuous_Gammaℝ_half_add_mul_I :
    Continuous (fun t : ℝ => Gammaℝ (1 / 2 + t * I)) :=
  continuous_iff_continuousAt.mpr continuousAt_Gammaℝ_half_add_mul_I

/-- `ℝ` is simply connected. -/
theorem isSimplyConnected_univ_real : IsSimplyConnected (Set.univ : Set ℝ) := by
  haveI : ContractibleSpace (Set.univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).contractibleSpace_iff.mpr inferInstance
  exact SimplyConnectedSpace.ofContractible _

theorem Gammaℝ_half_add_mul_I_ne_zero' (t : ℝ) : Gammaℝ (1 / 2 + t * I) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (by simp)

theorem exists_gammaRLogBranch :
    ∃ f : ℝ → ℂ, Continuous f ∧ ∀ t : ℝ, exp (f t) = Gammaℝ (1 / 2 + t * I) := by
  obtain ⟨f, hfc, hfe⟩ :=
    exists_continuousOn_eqOn_exp_comp (U := Set.univ) isSimplyConnected_univ_real
      isOpen_univ (g := fun t : ℝ => Gammaℝ (1 / 2 + t * I))
      continuous_Gammaℝ_half_add_mul_I.continuousOn
      (by
        rintro ⟨t, -, h0⟩
        exact Gammaℝ_half_add_mul_I_ne_zero' t h0)
  refine ⟨f, ?_, ?_⟩
  · simpa [continuousOn_univ] using hfc
  · intro t
    simpa [Function.comp_def] using hfe (Set.mem_univ t)

/-- A continuous choice of logarithm of `t ↦ Γ_ℝ (1/2 + it)` on the real line. -/
noncomputable def gammaRLogBranch : ℝ → ℂ := Classical.choose exists_gammaRLogBranch

theorem gammaRLogBranch_continuous : Continuous gammaRLogBranch :=
  (Classical.choose_spec exists_gammaRLogBranch).1

theorem exp_gammaRLogBranch (t : ℝ) :
    exp (gammaRLogBranch t) = Gammaℝ (1 / 2 + t * I) :=
  (Classical.choose_spec exists_gammaRLogBranch).2 t

/-- **The Riemann–Siegel theta function**: the argument of `Γ_ℝ` on the critical line,
as the imaginary part of the continuous logarithm. -/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ := (gammaRLogBranch t).im

theorem continuous_riemannSiegelTheta : Continuous riemannSiegelTheta := by
  have h := Complex.continuous_im.comp gammaRLogBranch_continuous
  change Continuous (fun t : ℝ => (gammaRLogBranch t).im)
  exact h

/-- `exp (I * ϑ t)` is the unit-modulus part of `Γ_ℝ (1/2 + it)`. -/
theorem exp_I_riemannSiegelTheta (t : ℝ) :
    Complex.exp (I * riemannSiegelTheta t) =
      Gammaℝ (1 / 2 + t * I) / (‖Gammaℝ (1 / 2 + t * I)‖ : ℂ) := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hΓ : Gammaℝ s = Complex.exp (gammaRLogBranch t) := (exp_gammaRLogBranch t).symm
  have hre_ne : Complex.exp ((gammaRLogBranch t).re : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hsum : Complex.exp (((gammaRLogBranch t).re : ℂ) + ((gammaRLogBranch t).im : ℂ) * I)
      = Complex.exp (gammaRLogBranch t) := by rw [Complex.re_add_im]
  have hphase : Complex.exp (((gammaRLogBranch t).im : ℂ) * I)
      = Complex.exp (gammaRLogBranch t) / Complex.exp ((gammaRLogBranch t).re) := by
    have hprod : Complex.exp (((gammaRLogBranch t).re : ℂ) + ((gammaRLogBranch t).im : ℂ) * I)
        = Complex.exp ((gammaRLogBranch t).re) *
          Complex.exp (((gammaRLogBranch t).im : ℂ) * I) := by
      rw [Complex.exp_add]
    have hmul : Complex.exp ((gammaRLogBranch t).re) *
        Complex.exp (((gammaRLogBranch t).im : ℂ) * I) = Complex.exp (gammaRLogBranch t) := by
      rw [← hprod, hsum]
    rw [eq_div_iff hre_ne, mul_comm, hmul]
  calc Complex.exp (I * riemannSiegelTheta t)
      = Complex.exp (((gammaRLogBranch t).im : ℂ) * I) := by
        rw [riemannSiegelTheta, mul_comm]
    _ = Complex.exp (gammaRLogBranch t) / Complex.exp ((gammaRLogBranch t).re) := hphase
    _ = Gammaℝ s / (‖Gammaℝ s‖ : ℂ) := by
        rw [hΓ, Complex.norm_exp, Complex.ofReal_exp]

/-- **The Riemann–Siegel relation**, the TODO in `Mathlib.NumberTheory.LSeries.HardyZ`:
`Z t = ζ (1/2 + it) * exp (I * ϑ t)`. -/
theorem hardyZ_eq_riemannZeta_mul_exp (t : ℝ) :
    (hardyZ t : ℂ) =
      riemannZeta (1 / 2 + t * I) * Complex.exp (I * riemannSiegelTheta t) := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hsne : s ≠ 0 := by
    intro h
    have hre : s.re = 0 := by rw [h]; simp
    simp [hs] at hre
  have hΓne : Gammaℝ s ≠ 0 := Gammaℝ_half_add_mul_I_ne_zero' t
  have hL : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hsne, div_mul_cancel₀ _ hΓne]
  have him : (completedRiemannZeta s).im = 0 := completedRiemannZeta_half_add_mul_I_im t
  have hΛ : (completedRiemannZeta s : ℂ) = ((completedRiemannZeta s).re : ℂ) := by
    have h := Complex.re_add_im (completedRiemannZeta s)
    rw [him] at h
    simpa using h.symm
  have hZ : (hardyZ t : ℂ) = completedRiemannZeta s / (‖Gammaℝ s‖ : ℂ) := by
    rw [hardyZ, ← hs, hΛ]
    push_cast
    simp
  calc (hardyZ t : ℂ) = completedRiemannZeta s / (‖Gammaℝ s‖ : ℂ) := hZ
    _ = (riemannZeta s * Gammaℝ s) / (‖Gammaℝ s‖ : ℂ) := by rw [hL]
    _ = riemannZeta s * (Gammaℝ s / (‖Gammaℝ s‖ : ℂ)) := by ring
    _ = riemannZeta s * Complex.exp (I * riemannSiegelTheta t) := by
        rw [exp_I_riemannSiegelTheta]

end Complex
