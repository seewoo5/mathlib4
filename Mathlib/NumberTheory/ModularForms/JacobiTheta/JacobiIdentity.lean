/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee, Sidharth Hariharan, Gareth Ma, Christopher Birkbeck
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The Jacobi theta identity `Θ₂⁴ + Θ₄⁴ = Θ₃⁴`

This file proves the **Jacobi identity**

$$\theta_2(\tau)^4 + \theta_4(\tau)^4 = \theta_3(\tau)^4,$$

for the Jacobi theta constants `Θ₂`, `Θ₃`, `Θ₄` defined in
`Mathlib/NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`.

## Strategy

Writing `Hᵢ := Θᵢ ^ 4` (local abbreviations), the weight-`2` slash-action laws for `Hᵢ` follow by
taking fourth powers of the weight-`1/2` transformation laws `Θᵢ_S_smul` and `Θᵢ_add_one`: the
square-root automorphy factor `(-I τ) ^ (1 / 2)` becomes `(-I τ) ^ 2 = -τ ^ 2`. One then shows that
`g := H₂ + H₄ - H₃` satisfies `g ∣[2] S = -g` and `g ∣[2] T = -g`, hence `f := g ^ 2` is a
slash-invariant form of weight `4` for `SL(2, ℤ)`. Since `g → 0` at `i∞`, so does `f`, making `f`
a weight-`4` cusp form. The space of weight-`4` cusp forms for `SL(2, ℤ)` is zero-dimensional
(`CuspForm.rank_eq_zero_of_weight_lt_twelve`), so `f = 0`, hence `g = 0`, which is the Jacobi
identity.

## Main results

* `jacobi_identity`: `Θ₂ τ ^ 4 + Θ₄ τ ^ 4 = Θ₃ τ ^ 4`.

This is a migration of the proof from the *Sphere Packing in dimension 8* formalization project.
-/

@[expose] public section

open scoped Real ModularForm MatrixGroups Manifold Topology
open UpperHalfPlane hiding I
open Complex Asymptotics Filter ModularForm SlashInvariantForm ModularGroup

noncomputable section

/-! ## Auxiliary lemmas -/

private lemma norm_cexp_mul_I (z : ℂ) : ‖cexp (z * I)‖ = Real.exp (-z.im) := by
  simp [norm_exp]

private lemma eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ z in atImInfty, p z) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z := by
  simp only [Filter.eventually_iff, atImInfty_mem, Set.mem_setOf_eq]

/-- The slash action of the translation `T` on a function evaluates to a shift by `1`. -/
private lemma slash_T_apply (f : ℍ → ℂ) (k : ℤ) (z : ℍ) :
    (f ∣[k] ModularGroup.T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul]
  simp [ModularGroup.T, denom]

private lemma tendsto_im_atImInfty : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap

/-- The fourth power of the weight-`1/2` automorphy factor: `((-I z) ^ (1/2)) ^ 4 = -z ^ 2`. -/
private lemma cpow_half_four (z : ℍ) : ((-I * (z : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -(z : ℂ) ^ 2 := by
  rw [← cpow_mul_nat]
  norm_num
  rw [mul_pow, I_sq]
  ring

/-! ## The functions `Hᵢ := Θᵢ ^ 4` -/

/-- Fourth power of `Θ₂` (local abbreviation). -/
abbrev H₂ : ℍ → ℂ := fun τ ↦ Θ₂ τ ^ 4

/-- Fourth power of `Θ₃` (local abbreviation). -/
abbrev H₃ : ℍ → ℂ := fun τ ↦ Θ₃ τ ^ 4

/-- Fourth power of `Θ₄` (local abbreviation). -/
abbrev H₄ : ℍ → ℂ := fun τ ↦ Θ₄ τ ^ 4

/-! ## Holomorphy -/

lemma H₂_MDifferentiable : MDiff H₂ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (fun z : ℂ ↦ Θ₂ z ^ 4) {z : ℂ | 0 < z.im} := fun x hx ↦
    ((differentiableAt_Θ₂ hx).pow 4).differentiableWithinAt
  apply h.congr
  intro z hz
  simp [H₂, ofComplex_apply_of_im_pos hz]

lemma H₃_MDifferentiable : MDiff H₃ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (fun z : ℂ ↦ Θ₃ z ^ 4) {z : ℂ | 0 < z.im} := fun x hx ↦
    ((differentiableAt_Θ₃ hx).pow 4).differentiableWithinAt
  apply h.congr
  intro z hz
  simp [H₃, ofComplex_apply_of_im_pos hz]

lemma H₄_MDifferentiable : MDiff H₄ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (fun z : ℂ ↦ Θ₄ z ^ 4) {z : ℂ | 0 < z.im} := fun x hx ↦
    ((differentiableAt_Θ₄ hx).pow 4).differentiableWithinAt
  apply h.congr
  intro z hz
  simp [H₄, ofComplex_apply_of_im_pos hz]

/-! ## Transformation laws

The weight-`2` slash-action laws for `Hᵢ` follow by taking fourth powers of the corresponding
weight-`1/2` laws for `Θᵢ` proved in `OneVariable.lean`.
-/

lemma H₂_T_action : (H₂ ∣[(2 : ℤ)] ModularGroup.T) = -H₂ := by
  ext z
  simp_rw [slash_T_apply, Pi.neg_apply, H₂, UpperHalfPlane.coe_vadd, ofReal_one, Θ₂_add_one,
    mul_pow, ← Complex.exp_nat_mul, mul_comm ((4 : ℕ) : ℂ), Nat.cast_ofNat,
    div_mul_cancel₀ (b := (4 : ℂ)) _ (by norm_num), Complex.exp_pi_mul_I, neg_one_mul]

lemma H₃_T_action : (H₃ ∣[(2 : ℤ)] ModularGroup.T) = H₄ := by
  ext z
  simp_rw [slash_T_apply, H₃, H₄, UpperHalfPlane.coe_vadd, ofReal_one, Θ₃_add_one]

lemma H₄_T_action : (H₄ ∣[(2 : ℤ)] ModularGroup.T) = H₃ := by
  ext z
  simp_rw [slash_T_apply, H₄, H₃, UpperHalfPlane.coe_vadd, ofReal_one, Θ₄_add_one]

lemma H₂_S_action : (H₂ ∣[(2 : ℤ)] ModularGroup.S) = -H₄ := by
  ext z
  have hz : (z : ℂ) ≠ 0 := ne_of_apply_ne Complex.im (zero_im.symm ▸ ne_of_gt z.2)
  rw [slash_S_apply, ← UpperHalfPlane.modular_S_smul, Pi.neg_apply]
  simp only [H₂, H₄]
  rw [Θ₂_S_smul z, mul_pow, cpow_half_four z]
  field_simp

lemma H₃_S_action : (H₃ ∣[(2 : ℤ)] ModularGroup.S) = -H₃ := by
  ext z
  have hz : (z : ℂ) ≠ 0 := ne_of_apply_ne Complex.im (zero_im.symm ▸ ne_of_gt z.2)
  rw [slash_S_apply, ← UpperHalfPlane.modular_S_smul, Pi.neg_apply]
  simp only [H₃]
  rw [Θ₃_S_smul z, mul_pow, cpow_half_four z]
  field_simp

lemma H₄_S_action : (H₄ ∣[(2 : ℤ)] ModularGroup.S) = -H₂ := by
  ext z
  have hz : (z : ℂ) ≠ 0 := ne_of_apply_ne Complex.im (zero_im.symm ▸ ne_of_gt z.2)
  rw [slash_S_apply, ← UpperHalfPlane.modular_S_smul, Pi.neg_apply]
  simp only [H₄, H₂]
  rw [Θ₄_S_smul z, mul_pow, cpow_half_four z]
  field_simp

/-! ## Limits at `i∞` -/

private lemma jacobiTheta₂_term_half_apply (n : ℤ) (z : ℂ) :
    jacobiTheta₂_term n (z / 2) z = cexp (π * I * (n ^ 2 + n) * z) := by
  rw [jacobiTheta₂_term]
  ring_nf

private lemma jacobiTheta₂_rel_aux (n : ℤ) (t : ℝ) :
    Real.exp (-π * (n + 1 / 2) ^ 2 * t)
      = Real.exp (-π * t / 4) * jacobiTheta₂_term n (I * t / 2) (I * t) := by
  rw [jacobiTheta₂_term_half_apply, ofReal_exp, ofReal_exp, ← Complex.exp_add, ofReal_mul]
  congr
  ring_nf
  simp
  ring_nf!

theorem jacobiTheta₂_half_mul_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (x / 2) x) atImInfty (𝓝 2) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun z (n : ℤ) ↦ cexp (2 * π * I * n * (z / 2) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := Set.indicator {-1, 0} 1)
    (bound := fun n : ℤ ↦ Real.exp (π / 4) * Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2)) ?_ ?_ ?_
  · simp [← tsum_subtype]
  · apply summable_ofReal.mp
    have (n : ℤ) := jacobiTheta₂_rel_aux n 1
    simp_rw [mul_one] at this
    simp_rw [ofReal_mul, this, ← smul_eq_mul]
    apply Summable.const_smul
    apply Summable.const_smul
    rw [summable_jacobiTheta₂_term_iff]
    simp
  · intro n
    have : n = -1 ∨ n = 0 ∨ n ∉ ({-1, 0} : Set ℤ) := by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rcases this with (rfl | rfl | hn) <;> ring_nf
    · simp
    · simp
    · simp only [hn, not_false_eq_true, Set.indicator_of_notMem]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have h₁ (n : ℤ) (z : ℂ) : (π * I * n * z + π * I * n ^ 2 * z) = π * (n + n ^ 2) * z * I := by
        ring_nf
      have h_base' : Real.exp (-π) ^ ((n : ℝ) + n ^ 2) < 1 := by
        apply Real.rpow_lt_one
        · positivity
        · exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
        convert_to 0 < ((n * (n + 1) : ℤ) : ℝ)
        · push_cast
          ring_nf
        · apply Int.cast_pos.mpr
          by_cases hn' : 0 < n
          · apply mul_pos hn' (by omega)
          · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
            exact mul_pos_of_neg_of_neg (by omega) (by omega)
      simp_rw [h₁, norm_cexp_mul_I, mul_assoc, im_ofReal_mul, ← Int.cast_pow, ← Int.cast_add,
        ← ofReal_intCast, im_ofReal_mul, ← mul_assoc, Int.cast_add, Int.cast_pow, ← neg_mul,
        Real.exp_mul, coe_im]
      refine (tendsto_rpow_atTop_of_base_lt_one _ ?_ h_base').comp tendsto_im_atImInfty
      exact neg_one_lt_zero.trans (by positivity)
  · rw [eventually_atImInfty]
    use 1
    intro z hz k
    simp_rw [← Real.exp_add]
    ring_nf
    trans ‖cexp (((π * k + π * k ^ 2 : ℝ) * z) * I)‖
    · apply le_of_eq
      simpa [add_mul] using by ring_nf
    · rw [norm_cexp_mul_I, im_ofReal_mul]
      have (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
        nth_rw 2 [← mul_one n]
        rw [sq, Int.cast_mul, Int.cast_one, ← mul_add]
        rcases lt_trichotomy (-1) n with (hn | rfl | hn)
        · apply mul_nonneg <;> norm_cast; omega
        · norm_num
        · apply mul_nonneg_of_nonpos_of_nonpos <;> norm_cast <;> omega
      simpa using le_mul_of_one_le_right
        (by rw [← mul_add, add_comm]; exact mul_nonneg Real.pi_nonneg (this k)) hz

theorem jacobiTheta₂_zero_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ 0 x) atImInfty (𝓝 1) := by
  simp_rw [jacobiTheta₂, jacobiTheta₂_term, mul_zero, zero_add]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ cexp (π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ Real.exp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    split_ifs with hk
    · subst hk
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [mul_right_comm _ I, norm_cexp_mul_I, mul_assoc, im_ofReal_mul, ← ofReal_intCast,
        ← ofReal_pow, im_ofReal_mul, ← mul_assoc]
      simpa using tendsto_im_atImInfty.const_mul_atTop (by positivity)
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    simp_rw [mul_right_comm _ I, norm_cexp_mul_I]
    simpa [← ofReal_intCast, ← ofReal_pow] using le_mul_of_one_le_right (by positivity) hz

theorem jacobiTheta₂_half_apply_tendsto_atImInfty :
    Tendsto (fun x : ℍ ↦ jacobiTheta₂ (1 / 2 : ℂ) x) atImInfty (𝓝 1) := by
  have hnorm (z : ℍ) (k : ℤ) :
      ‖cexp (2 * π * I * k * (1 / 2 : ℂ) + π * I * k ^ 2 * z)‖ = Real.exp (-π * k ^ 2 * z.im) := by
    simpa [jacobiTheta₂_term, coe_im] using
      (norm_jacobiTheta₂_term k (1 / 2 : ℂ) (z : ℂ))
  simp_rw [jacobiTheta₂, jacobiTheta₂_term]
  convert tendsto_tsum_of_dominated_convergence
    (f := fun (z : ℍ) (n : ℤ) ↦ cexp (2 * π * I * n * (1 / 2 : ℂ) + π * I * n ^ 2 * z))
    (𝓕 := atImInfty)
    (g := fun k ↦ if k = 0 then 1 else 0)
    (bound := fun n : ℤ ↦ Real.exp (-π * n ^ 2)) ?_ ?_ ?_
  · simp
  · apply summable_ofReal.mp
    have := (summable_jacobiTheta₂_term_iff 0 I).mpr (by simp)
    rw [← summable_norm_iff, ← summable_ofReal] at this
    simp_rw [jacobiTheta₂_term, mul_zero, zero_add, mul_right_comm _ I, mul_assoc, ← sq, I_sq,
      mul_neg_one, norm_exp, re_ofReal_mul, neg_re, mul_neg, ← neg_mul, ← ofReal_intCast,
      ← ofReal_pow, ofReal_re] at this
    exact this
  · intro k
    split_ifs with hk
    · subst hk
      simp
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hnorm]
      have hk2_pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)
      exact (Real.tendsto_exp_atBot).comp
        (tendsto_im_atImInfty.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos, hk2_pos]))
  · rw [eventually_atImInfty]
    use 1, fun z hz k ↦ ?_
    rw [hnorm]
    have hcoef_nonpos : (-π * (k : ℝ) ^ 2) ≤ 0 := by
      nlinarith [Real.pi_pos, sq_nonneg (k : ℝ)]
    simpa using Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz hcoef_nonpos)

theorem Θ₂_tendsto_atImInfty : Tendsto (fun τ : ℍ ↦ Θ₂ ↑τ) atImInfty (𝓝 0) := by
  simp_rw [Θ₂_eq_jacobiTheta₂]
  rw [← zero_mul (2 : ℂ)]
  refine Tendsto.mul ?_ jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have (z : ℍ) : ‖cexp (π * I * z / 4)‖ = Real.exp (-π * z.im / 4) := by
    rw [mul_right_comm, mul_div_right_comm, norm_cexp_mul_I]
    simp [neg_div]
  simp_rw [this]
  exact (Real.tendsto_exp_atBot).comp <|
    (tendsto_div_const_atBot_of_pos zero_lt_four).mpr
      (tendsto_im_atImInfty.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos))

theorem Θ₃_tendsto_atImInfty : Tendsto (fun τ : ℍ ↦ Θ₃ ↑τ) atImInfty (𝓝 1) := by
  simp_rw [Θ₃_eq_jacobiTheta₂]
  exact jacobiTheta₂_zero_apply_tendsto_atImInfty

theorem Θ₄_tendsto_atImInfty : Tendsto (fun τ : ℍ ↦ Θ₄ ↑τ) atImInfty (𝓝 1) := by
  simp_rw [Θ₄_eq_jacobiTheta₂]
  exact jacobiTheta₂_half_apply_tendsto_atImInfty

theorem H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0) := by
  convert Θ₂_tendsto_atImInfty.pow 4
  norm_num

theorem H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1) := by
  convert Θ₃_tendsto_atImInfty.pow 4
  norm_num

theorem H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1) := by
  convert Θ₄_tendsto_atImInfty.pow 4
  norm_num

/-! ## The Jacobi identity -/

/-- The difference `g := H₂ + H₄ - H₃`. -/
private def jacobi_g : ℍ → ℂ := H₂ + H₄ - H₃

/-- The square `f := g²`. -/
private def jacobi_f : ℍ → ℂ := jacobi_g ^ 2

private lemma jacobi_g_S_action : (jacobi_g ∣[(2 : ℤ)] ModularGroup.S) = -jacobi_g := by
  change ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] ModularGroup.S) = -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_S_action, H₃_S_action, H₄_S_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

private lemma jacobi_g_T_action : (jacobi_g ∣[(2 : ℤ)] ModularGroup.T) = -jacobi_g := by
  change ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] ModularGroup.T) = -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    H₂_T_action, H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

private lemma jacobi_f_eq_mul : jacobi_f = jacobi_g * jacobi_g := by
  ext; simp [jacobi_f, sq]

private lemma jacobi_f_S_action : (jacobi_f ∣[(4 : ℤ)] ModularGroup.S) = jacobi_f := by
  simp only [jacobi_f_eq_mul, show (4 : ℤ) = 2 + 2 by norm_num,
    mul_slash_SL2 2 2 ModularGroup.S _ _, jacobi_g_S_action, neg_mul_neg]

private lemma jacobi_f_T_action : (jacobi_f ∣[(4 : ℤ)] ModularGroup.T) = jacobi_f := by
  simp only [jacobi_f_eq_mul, show (4 : ℤ) = 2 + 2 by norm_num,
    mul_slash_SL2 2 2 ModularGroup.T _ _, jacobi_g_T_action, neg_mul_neg]

private lemma jacobi_g_MDifferentiable : MDiff jacobi_g :=
  (H₂_MDifferentiable.add H₄_MDifferentiable).sub H₃_MDifferentiable

private lemma jacobi_f_MDifferentiable : MDiff jacobi_f := by
  rw [jacobi_f_eq_mul]
  exact jacobi_g_MDifferentiable.mul jacobi_g_MDifferentiable

private theorem jacobi_g_tendsto_atImInfty : Tendsto jacobi_g atImInfty (𝓝 0) := by
  have h := (H₂_tendsto_atImInfty.add H₄_tendsto_atImInfty).sub H₃_tendsto_atImInfty
  simp only [zero_add, sub_self] at h
  exact h

private theorem jacobi_f_tendsto_atImInfty : Tendsto jacobi_f atImInfty (𝓝 0) := by
  have h := jacobi_g_tendsto_atImInfty.pow 2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  exact h

/-- The weight-`4` cusp form `f := (H₂ + H₄ - H₃)²` for `SL(2, ℤ)`. -/
private def jacobi_f_CF : CuspForm 𝒮ℒ 4 where
  toFun := jacobi_f
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z jacobi_f_S_action jacobi_f_T_action A
  holo' := jacobi_f_MDifferentiable
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z jacobi_f_S_action jacobi_f_T_action]
    exact jacobi_f_tendsto_atImInfty

@[simp] private lemma jacobi_f_CF_apply (z : ℍ) : jacobi_f_CF z = jacobi_f z := rfl

/-- `f = 0` by the dimension argument: weight-`4` cusp forms for `SL(2, ℤ)` vanish. -/
private theorem jacobi_f_eq_zero : jacobi_f = 0 := by
  have h : jacobi_f_CF = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) jacobi_f_CF
  ext z
  simpa using DFunLike.congr_fun h z

private theorem jacobi_g_eq_zero : jacobi_g = 0 := by
  ext z
  simpa [jacobi_f] using congr_fun jacobi_f_eq_zero z

/-- The Jacobi identity in terms of the fourth powers: `H₂ + H₄ = H₃`. -/
theorem jacobi_identity_pow : H₂ + H₄ = H₃ := by
  ext z
  simpa [jacobi_g, sub_eq_zero] using congr_fun jacobi_g_eq_zero z

/-- **The Jacobi theta identity**: `Θ₂ τ ^ 4 + Θ₄ τ ^ 4 = Θ₃ τ ^ 4`. -/
theorem jacobi_identity (τ : ℍ) : Θ₂ ↑τ ^ 4 + Θ₄ ↑τ ^ 4 = Θ₃ ↑τ ^ 4 := by
  simpa using congr_fun jacobi_identity_pow τ

end
