/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! # Jacobi's theta function

This file defines the one-variable Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.
-/

@[expose] public section

open Complex Real Asymptotics Filter Topology

open scoped Real UpperHalfPlane

/-- Jacobi's one-variable theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobiTheta (τ : ℂ) : ℂ := ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ)

lemma jacobiTheta_eq_jacobiTheta₂ (τ : ℂ) : jacobiTheta τ = jacobiTheta₂ 0 τ :=
  tsum_congr (by simp [jacobiTheta₂_term])

theorem jacobiTheta_two_add (τ : ℂ) : jacobiTheta (2 + τ) = jacobiTheta τ := by
  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]

theorem jacobiTheta_T_sq_smul (τ : ℍ) : jacobiTheta (ModularGroup.T ^ 2 • τ :) = jacobiTheta τ := by
  suffices (ModularGroup.T ^ 2 • τ :) = (2 : ℂ) + ↑τ by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : ℕ) = ModularGroup.T ^ (2 : ℤ) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast

theorem jacobiTheta_S_smul (τ : ℍ) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  have h0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  have h1 : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_eq_jacobiTheta₂, ← ofReal_zero]
  norm_cast
  simp_rw [jacobiTheta₂_functional_equation 0 τ, zero_pow two_ne_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one, ← mul_assoc, mul_one_div, div_self h1, one_mul,
    inv_neg, neg_div, one_div]

theorem norm_exp_mul_sq_le {τ : ℂ} (hτ : 0 < τ.im) (n : ℤ) :
    ‖cexp (π * I * (n : ℂ) ^ 2 * τ)‖ ≤ rexp (-π * τ.im) ^ n.natAbs := by
  let y := rexp (-π * τ.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  refine (le_of_eq ?_).trans (?_ : y ^ n ^ 2 ≤ _)
  · rw [norm_exp]
    have : (π * I * n ^ 2 * τ : ℂ).re = -π * τ.im * (n : ℝ) ^ 2 := by
      rw [(by push_cast; ring : (π * I * n ^ 2 * τ : ℂ) = (π * n ^ 2 : ℝ) * (τ * I)),
        re_ofReal_mul, mul_I_re]
      ring
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
    rw [this, exp_mul, ← Int.cast_pow, rpow_intCast, hm, zpow_natCast]
  · have : n ^ 2 = (n.natAbs ^ 2 :) := by rw [Nat.cast_pow, Int.natAbs_sq]
    rw [this, zpow_natCast]
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.natAbs).symm ▸ n.natAbs.le_mul_self)

theorem hasSum_nat_jacobiTheta {τ : ℂ} (hτ : 0 < im τ) :
    HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)) ((jacobiTheta τ - 1) / 2) := by
  have := hasSum_jacobiTheta₂_term 0 hτ
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
  have := this.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_natCast, Nat.cast_zero, neg_zero,
    Int.cast_zero, sq (0 : ℂ), mul_zero, zero_mul, neg_sq, ← mul_two,
    Complex.exp_zero, add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ← sub_eq_add_neg,
    Nat.cast_add, Nat.cast_one] at this
  convert! this.div_const 2 using 1
  simp_rw [mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

theorem jacobiTheta_eq_tsum_nat {τ : ℂ} (hτ : 0 < im τ) :
    jacobiTheta τ = ↑1 + ↑2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ) := by
  rw [(hasSum_nat_jacobiTheta hτ).tsum_eq, mul_div_cancel₀ _ (two_ne_zero' ℂ), ← add_sub_assoc,
    add_sub_cancel_left]

/-- An explicit upper bound for `‖jacobiTheta τ - 1‖`. -/
theorem norm_jacobiTheta_sub_one_le {τ : ℂ} (hτ : 0 < im τ) :
    ‖jacobiTheta τ - 1‖ ≤ 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by
  suffices ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ ≤
      rexp (-π * τ.im) / (1 - rexp (-π * τ.im)) by
    calc
      ‖jacobiTheta τ - 1‖ = ↑2 * ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ), norm_mul, Complex.norm_two]
      _ ≤ 2 * (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by gcongr
      _ = 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by rw [div_mul_comm, mul_comm]
  have : ∀ n : ℕ, ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ ≤ rexp (-π * τ.im) ^ (n + 1) := by
    intro n
    simpa only [Int.cast_add, Int.cast_one] using! norm_exp_mul_sq_le hτ (n + 1)
  have s : HasSum (fun n : ℕ =>
      rexp (-π * τ.im) ^ (n + 1)) (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
    exact hasSum_geometric_of_lt_one (exp_pos (-π * τ.im)).le
      (exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  have aux : Summable fun n : ℕ => ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) this s.summable
  exact (norm_tsum_le_tsum_norm aux).trans ((aux.tsum_mono s.summable this).trans_eq s.tsum_eq)

/-- The norm of `jacobiTheta τ - 1` decays exponentially as `im τ → ∞`. -/
theorem isBigO_at_im_infty_jacobiTheta_sub_one :
    (fun τ => jacobiTheta τ - 1) =O[comap im atTop] fun τ => rexp (-π * τ.im) := by
  simp_rw [IsBigO, IsBigOWith, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨2 / (1 - rexp (-(π * 1))), 1, fun y hy τ hτ =>
    (norm_jacobiTheta_sub_one_le (hτ.symm ▸ zero_lt_one.trans_le hy : 0 < im τ)).trans ?_⟩
  rw [Real.norm_eq_abs, Real.abs_exp, hτ, neg_mul]
  gcongr
  simp [pi_pos]

theorem differentiableAt_jacobiTheta {τ : ℂ} (hτ : 0 < im τ) :
    DifferentiableAt ℂ jacobiTheta τ := by
  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτ

theorem continuousAt_jacobiTheta {τ : ℂ} (hτ : 0 < im τ) : ContinuousAt jacobiTheta τ :=
  (differentiableAt_jacobiTheta hτ).continuousAt

/-! ## The Jacobi theta constants `Θ₂`, `Θ₃`, `Θ₄`

We define the three classical Jacobi theta constants (theta nullwerte) as specializations of the
two-variable theta function `jacobiTheta₂`. Note that `Θ₃` coincides with `jacobiTheta`
(see `Θ₃_eq_jacobiTheta`); it is kept as a separate name for symmetry with `Θ₂` and `Θ₄`.
We prove their transformation laws under `τ ↦ τ + 1` and `τ ↦ -1/τ` (the latter involving the
square-root automorphy factor `(-I * τ) ^ (1 / 2)`) and their holomorphy on the upper half-plane.
-/

/-- Summand of the Jacobi theta constant `Θ₂`. -/
noncomputable def Θ₂Term (n : ℤ) (τ : ℂ) : ℂ := cexp (π * I * (n + 1 / 2 : ℂ) ^ 2 * τ)

/-- Summand of the Jacobi theta constant `Θ₃`. -/
noncomputable def Θ₃Term (n : ℤ) (τ : ℂ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)

/-- Summand of the Jacobi theta constant `Θ₄`. -/
noncomputable def Θ₄Term (n : ℤ) (τ : ℂ) : ℂ := (-1) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)

/-- The Jacobi theta constant `Θ₂ τ = ∑ₙ exp(π i (n + 1/2)² τ)`. -/
noncomputable def Θ₂ (τ : ℂ) : ℂ := ∑' n : ℤ, Θ₂Term n τ

/-- The Jacobi theta constant `Θ₃ τ = ∑ₙ exp(π i n² τ)`; this equals `jacobiTheta τ`. -/
noncomputable def Θ₃ (τ : ℂ) : ℂ := ∑' n : ℤ, Θ₃Term n τ

/-- The Jacobi theta constant `Θ₄ τ = ∑ₙ (-1)ⁿ exp(π i n² τ)`. -/
noncomputable def Θ₄ (τ : ℂ) : ℂ := ∑' n : ℤ, Θ₄Term n τ

theorem Θ₂Term_eq_jacobiTheta₂_term (τ : ℂ) (n : ℤ) :
    Θ₂Term n τ = cexp (π * I * τ / 4) * jacobiTheta₂_term n (τ / 2) τ := by
  rw [Θ₂Term, jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

theorem Θ₂_eq_jacobiTheta₂ (τ : ℂ) : Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  simp_rw [Θ₂, Θ₂Term_eq_jacobiTheta₂_term, tsum_mul_left, jacobiTheta₂]

theorem Θ₃Term_eq_jacobiTheta₂_term (τ : ℂ) (n : ℤ) : Θ₃Term n τ = jacobiTheta₂_term n 0 τ := by
  simp [Θ₃Term, jacobiTheta₂_term]

theorem Θ₃_eq_jacobiTheta₂ (τ : ℂ) : Θ₃ τ = jacobiTheta₂ (0 : ℂ) τ := by
  simp_rw [Θ₃, Θ₃Term_eq_jacobiTheta₂_term, jacobiTheta₂]

theorem Θ₃_eq_jacobiTheta (τ : ℂ) : Θ₃ τ = jacobiTheta τ := by
  rw [Θ₃_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂]

theorem Θ₄Term_eq_jacobiTheta₂_term (τ : ℂ) (n : ℤ) :
    Θ₄Term n τ = jacobiTheta₂_term n (1 / 2 : ℂ) τ := by
  rw [Θ₄Term, jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
  ring_nf

theorem Θ₄_eq_jacobiTheta₂ (τ : ℂ) : Θ₄ τ = jacobiTheta₂ (1 / 2 : ℂ) τ := by
  simp_rw [Θ₄, Θ₄Term_eq_jacobiTheta₂_term, jacobiTheta₂]

/-! ### Transformation laws under `τ ↦ τ + 1` -/

theorem Θ₂_add_one (τ : ℂ) : Θ₂ (1 + τ) = cexp (π * I / 4) * Θ₂ τ := by
  calc
  _ = ∑' (n : ℤ), cexp (π * I * (n + 1 / 2) ^ 2 * (1 + τ)) := by simp_rw [Θ₂, Θ₂Term]
  _ = ∑' (n : ℤ), cexp (π * I / 4) * cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * τ) := by
    apply tsum_congr fun b ↦ ?_
    rw [← Complex.exp_add]
    congr 1
    ring
  _ = cexp (π * I / 4) * ∑' (n : ℤ), cexp (π * I * (n ^ 2 + n) + π * I * (n + 1 / 2) ^ 2 * τ) := by
    rw [tsum_mul_left]
  _ = _ := by
    simp_rw [Θ₂, Θ₂Term]
    congr 1
    apply tsum_congr fun b ↦ ?_
    have : Even (b ^ 2 + b) := by convert Int.even_mul_succ_self b using 1; ring_nf
    norm_cast
    rw [Complex.exp_add, mul_comm (π * I), Complex.exp_int_mul, Complex.exp_pi_mul_I,
      this.neg_one_zpow, one_mul]

theorem Θ₃_add_one (τ : ℂ) : Θ₃ (1 + τ) = Θ₄ τ := by
  simp_rw [Θ₃, Θ₄, Θ₃Term, Θ₄Term]
  apply tsum_congr fun b ↦ ?_
  rw [mul_add, Complex.exp_add, mul_one, mul_comm (π * I), ← Int.cast_pow, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]
  congr 1
  rcases Int.even_or_odd b with (hb | hb)
  · rw [hb.neg_one_zpow, Even.neg_one_zpow]
    simp [sq, hb]
  · rw [hb.neg_one_zpow, Odd.neg_one_zpow]
    simp [sq, hb]

theorem Θ₄_add_one (τ : ℂ) : Θ₄ (1 + τ) = Θ₃ τ := by
  simp_rw [Θ₃, Θ₄, Θ₃Term, Θ₄Term]
  apply tsum_congr fun b ↦ ?_
  rw [mul_add, Complex.exp_add, mul_one, mul_comm (π * I), ← Int.cast_pow, Complex.exp_int_mul,
    Complex.exp_pi_mul_I, ← mul_assoc, ← zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num),
    show b + b ^ 2 = b * (b + 1) by ring, (Int.even_mul_succ_self b).neg_one_zpow, one_mul]

/-! ### Transformation laws under `τ ↦ -1/τ` (weight `1/2`) -/

private lemma negI_mul_ne_zero (τ : ℍ) : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
  have h0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0

/-- The `S`-transformation of `Θ₃` (equal to `jacobiTheta_S_smul` since `Θ₃ = jacobiTheta`). -/
theorem Θ₃_S_smul (τ : ℍ) : Θ₃ ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * Θ₃ τ := by
  simp_rw [Θ₃_eq_jacobiTheta]
  exact jacobiTheta_S_smul τ

/-- The `S`-transformation `Θ₄(-1/τ) = (-I τ)^{1/2} Θ₂ τ`. -/
theorem Θ₄_S_smul (τ : ℍ) : Θ₄ ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * Θ₂ τ := by
  have h0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  rw [Θ₄_eq_jacobiTheta₂, Θ₂_eq_jacobiTheta₂, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    jacobiTheta₂_functional_equation (↑τ / 2) τ]
  rw [show ((τ : ℂ) / 2) / τ = 1 / 2 by rw [div_div, mul_comm, ← div_div, div_self h0],
    show -π * I * (↑τ / 2) ^ 2 / ↑τ = -(π * I * ↑τ / 4) by field_simp; ring,
    show (-1 / (τ : ℂ)) = -(↑τ)⁻¹ by rw [neg_div, one_div]]
  rw [Complex.exp_neg]
  field_simp [negI_mul_ne_zero τ]

/-- The `S`-transformation `Θ₂(-1/τ) = (-I τ)^{1/2} Θ₄ τ`. -/
theorem Θ₂_S_smul (τ : ℍ) :
    Θ₂ ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * Θ₄ τ := by
  have h0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.2)
  rw [Θ₂_eq_jacobiTheta₂, Θ₄_eq_jacobiTheta₂, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    jacobiTheta₂_functional_equation (1 / 2 : ℂ) τ,
    show ((-↑τ)⁻¹ : ℂ) = -1 / ↑τ by rw [inv_neg, neg_div, one_div],
    show ((-1 / (↑τ : ℂ)) / 2) = -(1 / 2 / ↑τ) by ring, jacobiTheta₂_neg_left,
    show ((π : ℂ) * I * (-1 / ↑τ) / 4) = -(π : ℂ) * I * (1 / 2) ^ 2 / ↑τ by ring]
  field_simp [negI_mul_ne_zero τ]

/-! ### Holomorphy -/

/-- Differentiability of `t ↦ jacobiTheta₂ (t / 2) t` at points of the upper half-plane. -/
private lemma differentiableAt_jacobiTheta₂_half {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ := by
  let f : ℂ → ℂ × ℂ := fun t : ℂ => (t / 2, t)
  let g : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
  have hg : DifferentiableAt ℂ g (f τ) := by
    simpa [f] using (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
  have hf : DifferentiableAt ℂ f τ :=
    (differentiableAt_id.div_const 2).prodMk differentiableAt_id
  simpa [f, g] using DifferentiableAt.fun_comp' τ hg hf

theorem differentiableAt_Θ₂ {τ : ℂ} (hτ : 0 < im τ) : DifferentiableAt ℂ Θ₂ τ := by
  simp_rw [funext Θ₂_eq_jacobiTheta₂]
  have h_exp : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) τ :=
    ((differentiableAt_id.const_mul (π * I)).div_const 4).cexp
  exact h_exp.mul (differentiableAt_jacobiTheta₂_half hτ)

theorem differentiableAt_Θ₃ {τ : ℂ} (hτ : 0 < im τ) : DifferentiableAt ℂ Θ₃ τ := by
  simp_rw [funext Θ₃_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτ

theorem differentiableAt_Θ₄ {τ : ℂ} (hτ : 0 < im τ) : DifferentiableAt ℂ Θ₄ τ := by
  simp_rw [funext Θ₄_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd (1 / 2) hτ
