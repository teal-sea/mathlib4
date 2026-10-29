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

The Riemann–Siegel theta function `ϑ` is the continuous argument of the archimedean factor
`Γ_ℝ` on the critical line, normalised by `ϑ 0 = 0`.

This file defines `ϑ` as the imaginary part of a continuous logarithm of
`t ↦ Γ_ℝ (1/2 + it)` (which exists because `ℝ` is simply connected and `Γ_ℝ` does not
vanish on the critical line), normalised so that `ϑ 0 = 0`.

## Main definitions and results

* `riemannSiegelTheta`: the function `ℝ → ℝ`.
* `riemannSiegelTheta_zero`: `ϑ 0 = 0`.
* `continuous_riemannSiegelTheta`: `ϑ` is continuous.

## TODO

* Prove `hardyZ t = ζ (1/2 + it) * exp (I * riemannSiegelTheta t)`, the relation the
  TODO in `Mathlib.NumberTheory.LSeries.HardyZ` asks for.
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

/-- **The Riemann–Siegel theta function**, normalised by `ϑ 0 = 0`: the continuous
argument of `Γ_ℝ` on the critical line. -/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
  (gammaRLogBranch t).im - (gammaRLogBranch 0).im

@[simp]
theorem riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 := by
  simp [riemannSiegelTheta]

theorem continuous_riemannSiegelTheta : Continuous riemannSiegelTheta := by
  have h := Complex.continuous_im.comp gammaRLogBranch_continuous
  exact h.sub continuous_const

end Complex
