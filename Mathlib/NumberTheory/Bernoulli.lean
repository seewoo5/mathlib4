/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

This result is formalised in Lean: `riemannZeta_two_mul_nat`.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* and need not concern the mathematician).

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli := (-1)^n * bernoulli'`.

## Main theorems

`sum_bernoulli : ∑ k ∈ Finset.range n, (n.choose k : ℚ) * bernoulli k =
  if n = 1 then 1 else 0`
-/


@[expose] public section


open Nat Finset Finset.Nat PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-! ### Definitions -/


/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli' (n : ℕ) : ℚ :=
  1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k

theorem bernoulli'_def' (n : ℕ) :
    bernoulli' n = 1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli']

theorem bernoulli'_def (n : ℕ) :
    bernoulli' n = 1 - ∑ k ∈ range n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli'_def', ← Fin.sum_univ_eq_sum_range]

theorem bernoulli'_spec (n : ℕ) :
    (∑ k ∈ range n.succ, (n.choose (n - k) : ℚ) / (n - k + 1) * bernoulli' k) = 1 := by
  rw [sum_range_succ_comm, bernoulli'_def n, tsub_self, choose_zero_right, sub_self, zero_add,
    div_one, cast_one, one_mul, sub_add, ← sum_sub_distrib, ← sub_eq_zero, sub_sub_cancel_left,
    neg_eq_zero]
  exact Finset.sum_eq_zero (fun x hx => by rw [choose_symm (le_of_lt (mem_range.1 hx)), sub_self])

theorem bernoulli'_spec' (n : ℕ) :
    (∑ k ∈ antidiagonal n, ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli' k.1) = 1 := by
  refine ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans ?_).trans (bernoulli'_spec n)
  refine sum_congr rfl fun x hx => ?_
  simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]

/-! ### Examples -/


section Examples

@[simp]
theorem bernoulli'_zero : bernoulli' 0 = 1 := by
  rw [bernoulli'_def]
  simp

@[simp]
theorem bernoulli'_one : bernoulli' 1 = 1 / 2 := by
  rw [bernoulli'_def]
  norm_num

@[simp]
theorem bernoulli'_two : bernoulli' 2 = 1 / 6 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
theorem bernoulli'_three : bernoulli' 3 = 0 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
theorem bernoulli'_four : bernoulli' 4 = -1 / 30 := by
  have : Nat.choose 4 2 = 6 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero, this]

end Examples

@[simp]
theorem sum_bernoulli' (n : ℕ) : (∑ k ∈ range n, (n.choose k : ℚ) * bernoulli' k) = n := by
  cases n with | zero => simp | succ n =>
  suffices
    ((n + 1 : ℚ) * ∑ k ∈ range n, ↑(n.choose k) / (n - k + 1) * bernoulli' k) =
      ∑ x ∈ range n, ↑(n.succ.choose x) * bernoulli' x by
    rw_mod_cast [sum_range_succ, bernoulli'_def, ← this, choose_succ_self_right]
    ring
  simp_rw [mul_sum, ← mul_assoc]
  refine sum_congr rfl fun k hk => ?_
  congr
  have : ((n - k : ℕ) : ℚ) + 1 ≠ 0 := by norm_cast
  simp only [← cast_sub (mem_range.1 hk).le, succ_eq_add_one, field, mul_comm]
  rw_mod_cast [tsub_add_eq_add_tsub (mem_range.1 hk).le, choose_mul_succ_eq]

/-- The exponential generating function for the Bernoulli numbers `bernoulli' n`. -/
def bernoulli'PowerSeries :=
  mk fun n => algebraMap ℚ A (bernoulli' n / n !)

theorem bernoulli'PowerSeries_mul_exp_sub_one :
    bernoulli'PowerSeries A * (exp A - 1) = X * exp A := by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  rw [bernoulli'PowerSeries, coeff_mul, mul_comm X, sum_antidiagonal_succ']
  suffices (∑ p ∈ antidiagonal n,
      bernoulli' p.1 / p.1! * ((p.2 + 1) * p.2! : ℚ)⁻¹) = (n ! : ℚ)⁻¹ by
    simpa [map_sum, Nat.factorial] using congr_arg (algebraMap ℚ A) this
  apply eq_inv_of_mul_eq_one_left
  rw [sum_mul]
  convert bernoulli'_spec' n using 1
  apply sum_congr rfl
  simp_rw [mem_antidiagonal]
  rintro ⟨i, j⟩ rfl
  have := factorial_mul_factorial_dvd_factorial_add i j
  simp [field, add_choose, *]

/-- Odd Bernoulli numbers (greater than 1) are zero. -/
theorem bernoulli'_eq_zero_of_odd {n : ℕ} (h_odd : Odd n) (hlt : 1 < n) : bernoulli' n = 0 := by
  let B := mk fun n => bernoulli' n / (n ! : ℚ)
  suffices (B - evalNegHom B) * (exp ℚ - 1) = X * (exp ℚ - 1) by
    rcases mul_eq_mul_right_iff.mp this with h | h <;>
      simp only [PowerSeries.ext_iff, evalNegHom, coeff_X] at h
    · apply eq_zero_of_neg_eq
      specialize h n
      split_ifs at h <;> simp_all [B, h_odd.neg_one_pow, factorial_ne_zero]
    · simpa +decide [Nat.factorial] using h 1
  have h : B * (exp ℚ - 1) = X * exp ℚ := by
    simpa [bernoulli'PowerSeries] using bernoulli'PowerSeries_mul_exp_sub_one ℚ
  rw [sub_mul, h, mul_sub X, sub_right_inj, ← neg_sub, mul_neg, neg_eq_iff_eq_neg]
  suffices evalNegHom (B * (exp ℚ - 1)) * exp ℚ = evalNegHom (X * exp ℚ) * exp ℚ by
    simpa [mul_assoc, sub_mul, mul_comm (evalNegHom (exp ℚ)), exp_mul_exp_neg_eq_one]
  congr

@[deprecated (since := "2025-12-09")]
alias bernoulli'_odd_eq_zero := bernoulli'_eq_zero_of_odd

/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli (n : ℕ) : ℚ :=
  (-1) ^ n * bernoulli' n

theorem bernoulli'_eq_bernoulli (n : ℕ) : bernoulli' n = (-1) ^ n * bernoulli n := by
  simp [bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

@[simp]
theorem bernoulli_zero : bernoulli 0 = 1 := by simp [bernoulli]

@[simp]
theorem bernoulli_one : bernoulli 1 = -1 / 2 := by norm_num [bernoulli]

@[simp]
theorem bernoulli_two : bernoulli 2 = 6⁻¹ := by
  simp [bernoulli]

@[simp]
theorem bernoulli_eq_zero_of_odd {n : ℕ} (h_odd : Odd n) (hlt : 1 < n) : bernoulli n = 0 := by
  rw [bernoulli, bernoulli'_eq_zero_of_odd h_odd hlt, mul_zero]

theorem bernoulli_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli n = bernoulli' n := by
  cases hn.lt_or_gt with
  | inl hlt => simp [lt_one_iff.mp hlt]
  | inr hgt =>
    cases n.even_or_odd with
    | inl heven => rw [bernoulli, heven.neg_one_pow, one_mul]
    | inr hodd => rw [bernoulli'_eq_zero_of_odd hodd hgt, bernoulli_eq_zero_of_odd hodd hgt]

@[simp]
theorem sum_bernoulli (n : ℕ) :
    (∑ k ∈ range n, (n.choose k : ℚ) * bernoulli k) = if n = 1 then 1 else 0 := by
  cases n with | zero => simp | succ n =>
  cases n with
  | zero => simp
  | succ n =>
  suffices (∑ i ∈ range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2)) = n / 2 by
    simp only [this, sum_range_succ', cast_succ, bernoulli_one, bernoulli_zero, choose_one_right,
      mul_one, choose_zero_right, cast_zero, if_false, zero_add, succ_succ_ne_one]
    ring
  have f := sum_bernoulli' n.succ.succ
  simp_rw [sum_range_succ', cast_succ, ← eq_sub_iff_add_eq] at f
  refine Eq.trans ?_ (Eq.trans f ?_)
  · congr
    funext x
    rw [bernoulli_eq_bernoulli'_of_ne_one (succ_ne_zero x ∘ succ.inj)]
  · simp only [one_div, mul_one, bernoulli'_zero, choose_zero_right,
      zero_add, choose_one_right, cast_succ, bernoulli'_one, one_div]
    ring

theorem bernoulli_spec' (n : ℕ) :
    (∑ k ∈ antidiagonal n, ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli k.1) =
      if n = 0 then 1 else 0 := by
  cases n with | zero => simp | succ n =>
  rw [if_neg (succ_ne_zero _)]
  -- algebra facts
  have h₁ : (1, n) ∈ antidiagonal n.succ := by simp [mem_antidiagonal, add_comm]
  have h₃ : (1 + n).choose n = n + 1 := by simp [add_comm]
  -- key equation: the corresponding fact for `bernoulli'`
  have H := bernoulli'_spec' n.succ
  -- massage it to match the structure of the goal, then convert piece by piece
  rw [sum_eq_add_sum_diff_singleton h₁] at H ⊢
  apply add_eq_of_eq_sub'
  convert eq_sub_of_add_eq' H using 1
  · refine sum_congr rfl fun p h => ?_
    obtain ⟨h', h''⟩ : p ∈ _ ∧ p ≠ _ := by rwa [mem_sdiff, mem_singleton] at h
    simp [bernoulli_eq_bernoulli'_of_ne_one ((not_congr (antidiagonal_congr h' h₁)).mp h'')]
  · simp [field, h₃]
    norm_num

/-- The exponential generating function for the Bernoulli numbers `bernoulli n`. -/
def bernoulliPowerSeries :=
  mk fun n => algebraMap ℚ A (bernoulli n / n !)

theorem bernoulliPowerSeries_mul_exp_sub_one : bernoulliPowerSeries A * (exp A - 1) = X := by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  simp only [bernoulliPowerSeries, coeff_mul, coeff_X, sum_antidiagonal_succ', one_div, coeff_mk,
    coeff_one, coeff_exp, map_sub, factorial, if_pos, cast_succ, cast_mul,
    sub_zero, add_eq_zero, if_false, one_ne_zero, and_false, ← map_mul, ← map_sum]
  cases n with | zero => simp | succ n =>
  rw [if_neg n.succ_succ_ne_one]
  have hfact : ∀ m, (m ! : ℚ) ≠ 0 := fun m => mod_cast factorial_ne_zero m
  have hite2 : ite (n.succ = 0) 1 0 = (0 : ℚ) := if_neg n.succ_ne_zero
  simp only [CharP.cast_eq_zero, zero_add, inv_one, map_one, sub_self, mul_zero]
  rw [← map_zero (algebraMap ℚ A), ← zero_div (n.succ ! : ℚ), ← hite2, ← bernoulli_spec', sum_div]
  refine congr_arg (algebraMap ℚ A) (sum_congr rfl fun x h => eq_div_of_mul_eq (hfact n.succ) ?_)
  rw [mem_antidiagonal] at h
  rw [← h, add_choose, cast_div_charZero (factorial_mul_factorial_dvd_factorial_add _ _)]
  simp [field, mul_comm _ (bernoulli x.1), mul_assoc]

section Faulhaber

/-- **Faulhaber's theorem** relating the **sum of p-th powers** to the Bernoulli numbers:
$$\sum_{k=0}^{n-1} k^p = \sum_{i=0}^p B_i\binom{p+1}{i}\frac{n^{p+1-i}}{p+1}.$$
See https://proofwiki.org/wiki/Faulhaber%27s_Formula and [orosi2018faulhaber] for
the proof provided here. -/
theorem sum_range_pow (n p : ℕ) :
    (∑ k ∈ range n, (k : ℚ) ^ p) =
      ∑ i ∈ range (p + 1), bernoulli i * ((p + 1).choose i) * (n : ℚ) ^ (p + 1 - i) / (p + 1) := by
  have hne : ∀ m : ℕ, (m ! : ℚ) ≠ 0 := fun m => mod_cast factorial_ne_zero m
  -- compute the Cauchy product of two power series
  have h_cauchy :
    ((mk fun p => bernoulli p / p !) * mk fun q => coeff (q + 1) (exp ℚ ^ n)) =
      mk fun p => ∑ i ∈ range (p + 1),
          bernoulli i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1)! := by
    ext q : 1
    let f a b := bernoulli a / a ! * coeff (b + 1) (exp ℚ ^ n)
    -- key step: use `PowerSeries.coeff_mul` and then rewrite sums
    simp only [f, coeff_mul, coeff_mk, sum_antidiagonal_eq_sum_range_succ f]
    apply sum_congr rfl
    intro m h
    simp only [exp_pow_eq_rescale_exp, rescale, RingHom.coe_mk]
    -- manipulate factorials and binomial coefficients
    have h : m < q + 1 := by simpa using h
    rw [choose_eq_factorial_div_factorial h.le, eq_comm, div_eq_iff (hne q.succ), succ_eq_add_one,
      mul_assoc _ _ (q.succ ! : ℚ), mul_comm _ (q.succ ! : ℚ), ← mul_assoc, div_mul_eq_mul_div]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, coeff_exp, Algebra.algebraMap_self, one_div,
      map_inv₀, map_natCast, coeff_mk]
    rw [mul_comm ((n : ℚ) ^ (q - m + 1)), ← mul_assoc _ _ ((n : ℚ) ^ (q - m + 1)), ← one_div,
      mul_one_div, div_div, tsub_add_eq_add_tsub (le_of_lt_succ h), cast_div, cast_mul]
    · ring
    · exact factorial_mul_factorial_dvd_factorial h.le
    · simp [factorial_ne_zero]
  -- same as our goal except we pull out `p!` for convenience
  have hps :
    (∑ k ∈ range n, (k : ℚ) ^ p) =
      (∑ i ∈ range (p + 1),
          bernoulli i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1)!) * p ! := by
    suffices
      (mk fun p => ∑ k ∈ range n, (k : ℚ) ^ p * algebraMap ℚ ℚ p !⁻¹) =
        mk fun p =>
          ∑ i ∈ range (p + 1), bernoulli i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1)! by
      rw [← div_eq_iff (hne p), div_eq_mul_inv, sum_mul]
      rw [PowerSeries.ext_iff] at this
      simpa using this p
    -- the power series `exp ℚ - 1` is non-zero, a fact we need in order to use `mul_right_inj'`
    have hexp : exp ℚ - 1 ≠ 0 := by
      simp only [exp, PowerSeries.ext_iff, Ne, not_forall]
      use 1
      simp
    have h_r : exp ℚ ^ n - 1 = X * mk fun p => coeff (p + 1) (exp ℚ ^ n) := by
      have h_const : C (constantCoeff (exp ℚ ^ n)) = 1 := by simp
      rw [← h_const, sub_const_eq_X_mul_shift]
    -- key step: a chain of equalities of power series
    rw [← mul_right_inj' hexp, mul_comm]
    rw [← exp_pow_sum, geom_sum_mul, h_r, ← bernoulliPowerSeries_mul_exp_sub_one,
      bernoulliPowerSeries, mul_right_comm]
    simp only [mul_comm, mul_eq_mul_left_iff, hexp, or_false]
    refine Eq.trans (mul_eq_mul_right_iff.mpr ?_) (Eq.trans h_cauchy ?_)
    · left
      congr
    · simp only [mul_comm, factorial]
  -- massage `hps` into our goal
  rw [hps, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  simp [field, factorial]

/-- Alternate form of **Faulhaber's theorem**, relating the sum of p-th powers to the Bernoulli
numbers:
$$\sum_{k=1}^{n} k^p = \sum_{i=0}^p (-1)^iB_i\binom{p+1}{i}\frac{n^{p+1-i}}{p+1}.$$
Deduced from `sum_range_pow`. -/
theorem sum_Ico_pow (n p : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ p) =
      ∑ i ∈ range (p + 1), bernoulli' i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1) := by
  rw [← Nat.cast_succ]
  -- dispose of the trivial case
  cases p with | zero => simp | succ p =>
  let f i := bernoulli i * p.succ.succ.choose i * (n : ℚ) ^ (p.succ.succ - i) / p.succ.succ
  let f' i := bernoulli' i * p.succ.succ.choose i * (n : ℚ) ^ (p.succ.succ - i) / p.succ.succ
  suffices (∑ k ∈ Ico 1 n.succ, (k : ℚ) ^ p.succ) = ∑ i ∈ range p.succ.succ, f' i by convert this
  -- prove some algebraic facts that will make things easier for us later on
  have hle := Nat.le_add_left 1 n
  have hne : (p + 1 + 1 : ℚ) ≠ 0 := by norm_cast
  have h1 : ∀ r : ℚ, r * (p + 1 + 1) * (n : ℚ) ^ p.succ / (p + 1 + 1 : ℚ) = r * (n : ℚ) ^ p.succ :=
      fun r => by rw [mul_div_right_comm, mul_div_cancel_right₀ _ hne]
  have h2 : f 1 + (n : ℚ) ^ p.succ = 1 / 2 * (n : ℚ) ^ p.succ := by
    simp_rw [f, bernoulli_one, choose_one_right, succ_sub_succ_eq_sub, cast_succ, tsub_zero, h1]
    ring
  have :
    (∑ i ∈ range p, bernoulli (i + 2) * (p + 2).choose (i + 2) * (n : ℚ) ^ (p - i) / ↑(p + 2)) =
      ∑ i ∈ range p, bernoulli' (i + 2) * (p + 2).choose (i + 2) * (n : ℚ) ^ (p - i) / ↑(p + 2) :=
    sum_congr rfl fun i _ => by rw [bernoulli_eq_bernoulli'_of_ne_one (succ_succ_ne_one i)]
  calc
    (-- replace sum over `Ico` with sum over `range` and simplify
        ∑ k ∈ Ico 1 n.succ, (k : ℚ) ^ p.succ)
    _ = ∑ k ∈ range n.succ, (k : ℚ) ^ p.succ := by simp [sum_Ico_eq_sub _ hle]
    -- extract the last term of the sum
    _ = (∑ k ∈ range n, (k : ℚ) ^ p.succ) + (n : ℚ) ^ p.succ := by rw [sum_range_succ]
    -- apply the key lemma, `sum_range_pow`
    _ = (∑ i ∈ range p.succ.succ, f i) + (n : ℚ) ^ p.succ := by simp [f, sum_range_pow]
    -- extract the first two terms of the sum
    _ = (∑ i ∈ range p, f i.succ.succ) + f 1 + f 0 + (n : ℚ) ^ p.succ := by
      simp_rw [sum_range_succ']
    _ = (∑ i ∈ range p, f i.succ.succ) + (f 1 + (n : ℚ) ^ p.succ) + f 0 := by ring
    _ = (∑ i ∈ range p, f i.succ.succ) + 1 / 2 * (n : ℚ) ^ p.succ + f 0 := by rw [h2]
    -- convert from `bernoulli` to `bernoulli'`
    _ = (∑ i ∈ range p, f' i.succ.succ) + f' 1 + f' 0 := by
      simpa [f, f', h1, fun i => show i + 2 = i + 1 + 1 from rfl]
    -- rejoin the first two terms of the sum
    _ = ∑ i ∈ range p.succ.succ, f' i := by simp_rw [sum_range_succ']

end Faulhaber

section vonStaudtClausen

/-- Indicator function that is `1` if `(p - 1) ∣ k` and `0` otherwise. -/
noncomputable def vonStaudtIndicator (k p : ℕ) : ℚ :=
  if (p - 1 : ℕ) ∣ k then 1 else 0

lemma zmod_pow_eq_one_of_dvd (p l : ℕ) (hp : p.Prime) (hdvd : (p - 1) ∣ l)
    (a : ZMod p) (ha : a ≠ 0) : a ^ l = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hdvd
  simp only [hk, pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow]

lemma card_filter_range_ne_zero (p : ℕ) (_hp : p.Prime) :
    (Finset.range p |>.filter (· ≠ 0)).card = p - 1 := by
  simp only [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_range.mpr _hp.pos),
    Finset.card_range]

lemma cast_ne_zero_of_mem_filter (p : ℕ) (v : ℕ)
    (hv : v ∈ (Finset.range p).filter (· ≠ 0)) : (v : ZMod p) ≠ 0 := by
  simp only [Finset.mem_filter, Finset.mem_range] at hv
  intro h
  have h1 : (p : ℕ) ∣ v := by simpa [ZMod.natCast_eq_zero_iff] using h
  exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)

lemma power_sum_eq_neg_one_mod_of_dvd (p l : ℕ) (hp : p.Prime) (hdvd : (p - 1) ∣ l) :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ZMod p) ^ l) = -1 := by
  have h1 : ∀ v ∈ (Finset.range p).filter (· ≠ 0), (v : ZMod p) ^ l = 1 := fun v hv =>
    zmod_pow_eq_one_of_dvd p l hp hdvd (v : ZMod p) (cast_ne_zero_of_mem_filter p v hv)
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_filter_range_ne_zero p hp,
      nsmul_eq_mul, mul_one]
  simp [Nat.cast_sub hp.pos]

lemma sum_pow_eq_sum_units_pow (p l : ℕ) [Fact p.Prime] :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l := by
  have hcast := cast_ne_zero_of_mem_filter p
  refine Finset.sum_bij' (fun v hv => ⟨(v : ZMod p), (v : ZMod p)⁻¹,
      mul_inv_cancel₀ (hcast v hv), inv_mul_cancel₀ (hcast v hv)⟩)
    (fun u _ => (u : ZMod p).val) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    exact Finset.mem_univ _
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact ZMod.val_lt (u : ZMod p)
    · intro h
      have hu : (u : ZMod p) ≠ 0 := Units.ne_zero u
      simp only [ZMod.val_eq_zero] at h
      exact hu h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    have : (v : ZMod p).val = v := ZMod.val_cast_of_lt hv.1
    simp only [this]
  · intro u _
    ext
    simp only [ZMod.natCast_zmod_val]
  · intro v _
    simp

lemma generator_orderOf_eq (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ)
    (_hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) : orderOf g = p - 1 := by
  have h1 : Fintype.card (Subgroup.zpowers g) = orderOf g := Fintype.card_zpowers
  have h3 : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  aesop

lemma pow_injective_on_range (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    Set.InjOn (fun i => g ^ i) (Finset.range (p - 1) : Set ℕ) := by
  intro i hi j hj heq
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hord : orderOf g = p - 1 := generator_orderOf_eq p g hg
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  rw [IsOfFinOrder.pow_eq_pow_iff_modEq hfin, hord] at heq
  exact Nat.ModEq.eq_of_lt_of_lt heq hi hj

lemma sum_units_eq_sum_range (p l : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    (∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l) =
    ∑ i ∈ Finset.range (p - 1), ((g : ZMod p) ^ l) ^ i := by
  have hord : orderOf g = p - 1 := generator_orderOf_eq p g hg
  have himg : Finset.image (fun i => g ^ i) (Finset.range (orderOf g)) = Finset.univ :=
    IsCyclic.image_range_orderOf hg
  rw [hord] at himg
  conv_lhs => rw [← himg]
  rw [Finset.sum_image (pow_injective_on_range p g hg)]
  congr 1
  ext i
  simp [← pow_mul, mul_comm]

lemma generator_pow_ne_one (p l : ℕ) [hp : Fact p.Prime]
    (hndvd : ¬(p - 1) ∣ l) (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    (g : ZMod p) ^ l ≠ 1 := by
  have h_order : orderOf g = p - 1 := by
    simp only [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  intro h
  exact hndvd (h_order ▸ orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h)))

lemma sum_units_pow_eq_zero_of_not_dvd (p l : ℕ) [hp : Fact p.Prime]
    (hndvd : ¬(p - 1) ∣ l) :
    (∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l) = 0 := by
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  rw [sum_units_eq_sum_range p l g hg]
  have hx1 := generator_pow_ne_one p l hndvd g hg
  have hxp := ZMod.pow_card_sub_one_eq_one (pow_ne_zero l (Units.ne_zero g))
  have := geom_sum_eq hx1 (p - 1)
  aesop

lemma power_sum_eq_zero_mod_of_not_dvd (p l : ℕ) (hp : p.Prime) (hndvd : ¬(p - 1) ∣ l) :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ZMod p) ^ l) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_pow_eq_sum_units_pow p l]
  exact sum_units_pow_eq_zero_of_not_dvd p l hndvd

lemma power_sum_add_indicator_eq_zero (p l : ℕ) (hp : p.Prime) :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ZMod p) ^ l) +
    (if (p - 1 : ℕ) ∣ l then (1 : ZMod p) else 0) = 0 := by
  by_cases h : (p - 1) ∣ l
  · simp only [h, ↓reduceIte]
    rw [power_sum_eq_neg_one_mod_of_dvd p l hp h]
    ring
  · simp only [h, ↓reduceIte, add_zero]
    exact power_sum_eq_zero_mod_of_not_dvd p l hp h

lemma mem_range_int_cast_iff (q : ℚ) :
    q ∈ Set.range Int.cast ↔ q.den = 1 := by
  constructor
  · intro ⟨z, hz⟩
    simp only [← hz]
    norm_cast
  · intro h
    use q.num
    have hq : (q.num : ℚ) / q.den = q := Rat.num_div_den q
    rw [← hq, h]
    simp

lemma is_integer_of_coprime_all_primes (q : ℚ)
    (h : ∀ p : ℕ, p.Prime → q.den.Coprime p) :
    q ∈ Set.range Int.cast := by
  have h1 : q.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : q.den ≠ 1)
    have hcop := h p hp
    have : p ∣ Nat.gcd q.den p := Nat.dvd_gcd hpdvd (dvd_refl p)
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at this
    have : p ≤ 1 := Nat.le_of_dvd (by norm_num) this
    linarith [hp.two_le]
  use q.num
  have hq : (q.num : ℚ) / q.den = q := Rat.num_div_den q
  rw [← hq, h1]
  simp

/-- A rational number `x` is `p`-integral if `p` does not divide its denominator. -/
def pIntegral (p : ℕ) (x : ℚ) : Prop := x.den.Coprime p

lemma sum_den_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has]
    exact dvd_trans (Rat.add_den_dvd (f a) (∑ x ∈ s, f x)) (mul_dvd_mul_left _ ih)

lemma pIntegral_sum {ι : Type*} (p : ℕ) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, pIntegral p (f i)) : pIntegral p (∑ i ∈ s, f i) :=
  Nat.Coprime.coprime_dvd_left (sum_den_dvd_prod_den s f)
    (Nat.Coprime.prod_left fun i hi => hf i hi)

lemma pIntegral_of_int (p : ℕ) (z : ℤ) : pIntegral p z := by simp_all [pIntegral]

lemma pIntegral_mul (p : ℕ) (x y : ℚ) (hx : pIntegral p x) (hy : pIntegral p y) :
    pIntegral p (x * y) :=
  Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y) (Nat.Coprime.mul_left hx hy)

lemma pIntegral_int_mul (p : ℕ) (x : ℚ) (z : ℤ) (hx : pIntegral p x) : pIntegral p (z * x) := by
  have _ := Rat.mul_den_dvd z x
  have h1 : (z * x : ℚ).den ∣ x.den := by aesop
  have h2 := Nat.Coprime.coprime_dvd_left h1 hx
  aesop

lemma pIntegral_sub (p : ℕ) (x y : ℚ) (hx : pIntegral p x) (hy : pIntegral p y) :
    pIntegral p (x - y) :=
  Nat.Coprime.coprime_dvd_left (Rat.sub_den_dvd x y) (Nat.Coprime.mul_left hx hy)

lemma prod_den_coprime_p (k p : ℕ) (hp : p.Prime) :
    (∏ q ∈ Finset.range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k ∧ q ≠ p,
      ((1 : ℚ) / q).den).Coprime p := by
  apply Nat.Coprime.prod_left
  intro q hq
  have h1 : q.Prime := (Finset.mem_filter.mp hq).2.1
  have h2 : ((1 : ℚ) / q).den = q := by have := Nat.Prime.ne_zero h1; simp_all
  rw [h2]
  exact (Nat.coprime_primes h1 hp).mpr (Finset.mem_filter.mp hq).2.2.2

lemma sum_primes_eq_indicator_add_rest (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    (∑ q ∈ Finset.range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q) =
    vonStaudtIndicator (2 * k) p / p + ∑ q ∈ Finset.range (2 * k + 2) with
      q.Prime ∧ (q - 1) ∣ 2 * k ∧ q ≠ p, (1 : ℚ) / q := by
  by_cases hdvd : (p - 1 : ℕ) ∣ 2 * k
  · -- p is in the filtered set; extract its term
    have hp_mem : p ∈ (Finset.range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := Nat.le_of_dvd (by omega) hdvd; omega, hp, hdvd⟩
    rw [← Finset.add_sum_erase _ _ hp_mem]
    simp only [vonStaudtIndicator, if_pos hdvd]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext q; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]; tauto
  · -- p is not in the filtered set; indicator is 0, filter sets are equal
    simp only [vonStaudtIndicator, if_neg hdvd, zero_div, zero_add]
    exact Finset.sum_congr (Finset.filter_congr fun q _ =>
      ⟨fun ⟨hpr, hd⟩ => ⟨hpr, hd, fun h => hdvd (h ▸ hd)⟩,
       fun ⟨hpr, hd, _⟩ => ⟨hpr, hd⟩⟩) fun _ _ => rfl

lemma pow_div_eq_pow_sub_div_ordCompl (p M N : ℕ) (hp : p.Prime) (hM : M ≠ 0)
    (hv : M.factorization p ≤ N) :
    (p : ℚ)^N / M = (p : ℚ) ^ (N - M.factorization p) / (M / p ^ M.factorization p) := by
  set e := M.factorization p with he
  set M' := M / p ^ e with hM'
  have hdecomp : p ^ e * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hM'_ne : M' ≠ 0 := (Nat.ordCompl_pos p hM).ne'
  have hM_cast : (M : ℚ) = (p ^ e : ℕ) * (M' : ℕ) := by rw [← hdecomp]; simp
  rw [hM_cast]
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpe_ne : (p : ℚ) ^ e ≠ 0 := pow_ne_zero e hp_ne
  rw [div_mul_eq_div_div]
  congr 1
  · rw [Nat.cast_pow, div_eq_iff hpe_ne, ← pow_add, Nat.sub_add_cancel hv]
  · field_simp; simp

lemma den_pow_div_dvd (p M' k : ℕ) : ((p : ℚ)^k / M').den ∣ M' := by
  have h1 : ((p : ℚ) ^ k / M') = Rat.divInt (p ^ k : ℤ) (M' : ℤ) := by norm_cast; simp
  rw [h1]
  have h2 : ↑(Rat.divInt (p ^ k : ℤ) (M' : ℤ)).den ∣ (M' : ℤ) := by apply Rat.den_dvd
  norm_cast at h2 ⊢

lemma pIntegral_pow_div (p M N : ℕ) (hp : p.Prime) (hM : M ≠ 0)
    (hv : M.factorization p ≤ N) : pIntegral p ((p : ℚ)^N / M) := by
  set M' := M / p ^ M.factorization p with hM'_def
  have hM'_ne : M' ≠ 0 := (Nat.ordCompl_pos p hM).ne'
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl hp hM).symm
  rw [pow_div_eq_pow_sub_div_ordCompl p M N hp hM hv]
  have hcast : (M : ℚ) / (p : ℚ) ^ M.factorization p = (M' : ℚ) := by
    rw [hM'_def]
    simp only [← Nat.cast_pow]
    rw [Nat.cast_div_charZero (Nat.ordProj_dvd M p)]
  rw [hcast]
  have hdvd : ((p : ℚ) ^ (N - M.factorization p) / M').den ∣ M' :=
    den_pow_div_dvd p M' (N - M.factorization p)
  exact hM'_cop.coprime_dvd_left hdvd

lemma valuation_bound (p n : ℕ) (hp : p.Prime) : (n + 1).factorization p ≤ n :=
  Nat.factorization_le_of_le_pow <|
    calc n + 1 = (n + 1).choose 1 := by simp
      _ ≤ 2 ^ n := Nat.choose_succ_le_two_pow n 1
      _ ≤ p ^ n := Nat.pow_le_pow_left hp.two_le n

lemma pIntegral_i0_term (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    pIntegral p ((p : ℚ) ^ (2 * k) / (2 * k + 1)) := by
  have h : (2 * k + 1 : ℚ) = ↑(2 * k + 1) := by push_cast; ring
  rw [h]
  apply pIntegral_pow_div p (2 * k + 1) (2 * k) hp
  · omega
  · exact valuation_bound p (2 * k) hp

lemma pIntegral_i1_term_p_eq_two (k : ℕ) (hk : k > 0) :
    pIntegral 2 (bernoulli 1 * (2 * k) * (2 : ℚ) ^ (2 * k - 1) / (2 * k)) := by
  rw [show bernoulli 1 = -1 / 2 from by norm_num [bernoulli_one]]
  have h : ((-1 / 2 : ℚ) * (2 * k) * (2 : ℚ) ^ (2 * k - 1) / (2 * k)) =
      (-(2 : ℤ) ^ (2 * k - 2) : ℤ) := by
    have hpow : (2 : ℚ) ^ (2 * k - 1) = (2 : ℚ) ^ (2 * k - 2) * 2 := by
      rw [show 2 * k - 1 = (2 * k - 2) + 1 from by omega, pow_succ]
    rw [hpow]; push_cast; field_simp [show (2 * k : ℚ) ≠ 0 from by positivity]
  rw [h]
  norm_num [pIntegral]

lemma den_neg_pow_div_two_dvd_two (k p : ℕ) : (-(p : ℚ) ^ (2 * k - 1) / 2).den ∣ 2 := by
  rw [neg_div, Rat.den_neg_eq_den, ← Nat.cast_pow]
  conv_lhs => rw [show (2 : ℚ) = (2 : ℕ) from rfl, Rat.natCast_div_eq_divInt]
  have h := Rat.den_dvd (p ^ (2 * k - 1)) 2
  exact Int.natCast_dvd_natCast.mp h

lemma pIntegral_i1_term_p_odd (k p : ℕ) (hk : k > 0) (hp : p.Prime) (hp2 : p ≠ 2) :
    pIntegral p (bernoulli 1 * (2 * k) * (p : ℚ) ^ (2 * k - 1) / (2 * k)) := by
  rw [show bernoulli 1 = (-1 : ℚ) / 2 from by norm_num [bernoulli]]
  have h2 : ((2 * k : ℕ) : ℚ) ≠ 0 := by norm_cast; omega
  field_simp [h2]
  rw [show -(↑↑p ^ (2 * k - 1) / (2 : ℚ)) = -↑↑p ^ (2 * k - 1) / 2 from by ring]
  unfold pIntegral
  exact Nat.Coprime.of_dvd_left (den_neg_pow_div_two_dvd_two k p)
    (Odd.coprime_two_left (hp.odd_of_ne_two hp2))

lemma pIntegral_i1_term (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    pIntegral p (bernoulli 1 * (2 * k) * (p : ℚ) ^ (2 * k - 1) / (2 * k)) := by
  obtain rfl | hp2 := eq_or_ne p 2
  · exact pIntegral_i1_term_p_eq_two k hk
  · exact pIntegral_i1_term_p_odd k p hk hp hp2

lemma valuation_bound_d_plus_1_p2_d2 : (2 + 1).factorization 2 ≤ 2 - 1 := by
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬(2 ∣ 3) by decide)]

lemma pow_two_ge_succ_of_ge_three (d : ℕ) (hd : d ≥ 3) : d + 1 ≤ 2 ^ (d - 1) := by
  have h : ∀ n : ℕ, n ≥ 3 → n + 1 ≤ 2 ^ (n - 1) := by
    intro n hn
    induction hn with
    | refl => norm_num
    | @step m hm IH =>
      have hm : (3 : ℕ) ≤ m := hm
      have h1 : 2 ^ (m - 1) ≥ 1 := Nat.one_le_pow _ _ (by omega)
      calc m + 1 + 1 ≤ 2 ^ (m - 1) + 1 := by omega
        _ ≤ 2 ^ (m - 1) * 2 := by nlinarith
        _ = 2 ^ m := by conv_rhs => rw [show m = m - 1 + 1 from by omega]; exact pow_succ ..
  exact h d hd

lemma pow_ge_succ_of_ge_three (p d : ℕ) (hp : 3 ≤ p) (hd : d ≥ 2) : d + 1 ≤ p ^ (d - 1) := by
  have h2 : ∀ d : ℕ, d ≥ 2 → d + 1 ≤ p ^ (d - 1) := by
    intro d hd
    induction hd with
    | refl => norm_num; omega
    | @step m hm IH =>
      have hm : (2 : ℕ) ≤ m := hm
      calc m + 1 + 1 ≤ p ^ (m - 1) + 1 := by omega
        _ ≤ p ^ (m - 1) * p := by
          have : p ^ (m - 1) ≥ 1 := Nat.one_le_pow _ _ (by omega)
          nlinarith
        _ = p ^ m := by
          conv_rhs => rw [show m = m - 1 + 1 from by omega]; exact pow_succ ..
  exact h2 d hd

lemma pIntegral_pow_div_factor (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime) :
    pIntegral p ((p : ℚ) ^ (2*(k-m)) / (2*(↑k - ↑m) + 1)) := by
  set d := k - m with hd
  have hd_pos : d ≥ 1 := by omega
  have hcast : (↑k : ℚ) - ↑m = ↑d := by rw [hd, Nat.cast_sub (le_of_lt hm_lt)]
  rw [hcast]
  have hcast2 : (2 : ℚ) * ↑d + 1 = ↑(2 * d + 1) := by push_cast; ring
  rw [hcast2]
  apply pIntegral_pow_div p (2 * d + 1) (2 * d) hp
  · omega
  · exact valuation_bound p (2 * d) hp

lemma pIntegral_T1 (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime)
    (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p ((bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) * ((2 * k).choose (2 * m)) *
                 (p : ℚ) ^ (2*(k-m)) / (2*(k-m) + 1)) := by
  have h_eq : (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) * ((2 * k).choose (2 * m)) *
              (p : ℚ) ^ (2*(k-m)) / (2*(k-m) + 1) =
              ((bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) * ((2 * k).choose (2 * m))) *
              ((p : ℚ) ^ (2*(k-m)) / (2*(k-m) + 1)) := by ring
  rw [h_eq]
  apply pIntegral_mul
  · apply pIntegral_mul
    · exact ih
    · exact pIntegral_of_int p ((2 * k).choose (2 * m))
  · exact pIntegral_pow_div_factor k m p hm_lt hp

lemma valuation_three_le_one (p : ℕ) (hp : p.Prime) : (3 : ℕ).factorization p ≤ 1 := by
  rcases hp.eq_two_or_odd with rfl | hp_odd
  · exact valuation_bound_d_plus_1_p2_d2
  · rcases eq_or_ne p 3 with rfl | hp_ne_3
    · simp [Nat.Prime.factorization_self hp]
    · have h : ¬ p ∣ 3 := by
        intro hdvd
        have hp_le_3 : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
        have hp_ge_2 : p ≥ 2 := hp.two_le
        interval_cases p <;> simp_all
      simp [Nat.factorization_eq_zero_of_not_dvd h]

lemma two_d_plus_one_le_pow_two (d : ℕ) (hd : d ≥ 2) : 2 * d + 1 ≤ 2 ^ (2 * d - 1) := by
  have := pow_two_ge_succ_of_ge_three (2 * d) (by omega)
  omega

lemma valuation_bound_2d_plus_1 (p d : ℕ) (hp : p.Prime) (hd : d ≥ 1) :
    (2 * d + 1).factorization p ≤ 2 * d - 1 := by
  rcases eq_or_lt_of_le hd with rfl | hd'
  · simp only [mul_one]
    exact valuation_three_le_one p hp
  · have hd2 : d ≥ 2 := hd'
    apply Nat.factorization_le_of_le_pow
    calc 2 * d + 1 ≤ 2 ^ (2 * d - 1) := two_d_plus_one_le_pow_two d hd2
      _ ≤ p ^ (2 * d - 1) := Nat.pow_le_pow_left hp.two_le _

lemma pIntegral_T2 (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime) :
    pIntegral p (vonStaudtIndicator (2 * m) p * ((2 * k).choose (2 * m)) * (p : ℚ) ^ (2*(k-m) - 1) /
                 (2*(k-m) + 1)) := by
  set d := k - m with hd_def
  have hd_pos : d ≥ 1 := by omega
  unfold vonStaudtIndicator
  split_ifs with he
  · simp only [one_mul]
    have hd_eq : (2 : ℚ) * (↑k - ↑m) + 1 = ↑(2 * d + 1) := by
      simp only [hd_def]
      have hkm : m ≤ k := le_of_lt hm_lt
      rw [← Nat.cast_sub hkm]
      push_cast
      ring
    rw [hd_eq]
    have hN_ne_zero : (2 * d + 1 : ℕ) ≠ 0 := by omega
    have hvaluation : (2 * d + 1).factorization p ≤ 2 * d - 1 :=
      valuation_bound_2d_plus_1 p d hp hd_pos
    have h_pow_pIntegral : pIntegral p ((p : ℚ) ^ (2 * d - 1) / ↑(2 * d + 1)) :=
      pIntegral_pow_div p (2 * d + 1) (2 * d - 1) hp hN_ne_zero hvaluation
    have h_rw :
        (↑((2 * k).choose (2 * m)) : ℚ) * ↑p ^ (2 * d - 1) / ↑(2 * d + 1) =
        (↑((2 * k).choose (2 * m)) : ℚ) *
          (↑p ^ (2 * d - 1) / ↑(2 * d + 1)) := by ring
    rw [h_rw]
    exact pIntegral_int_mul p ((p : ℚ) ^ (2 * d - 1) / ↑(2 * d + 1))
      ((2 * k).choose (2 * m)) h_pow_pIntegral
  · simp only [zero_mul, zero_div]
    exact pIntegral_of_int p 0

lemma core_algebraic_identity (B I : ℚ) (p d : ℕ) (hd : d ≥ 1) :
    B * (p : ℚ) ^ (2*d) = (B + I / p) * (p : ℚ) ^ (2*d) - I * (p : ℚ) ^ (2*d - 1) := by
  have hpow : (p : ℚ) ^ (2*d) = (p : ℚ) ^ (2*d - 1) * p := by
    conv_lhs => rw [show 2 * d = (2 * d - 1) + 1 from by omega, pow_succ]
  rcases eq_or_ne (p : ℚ) 0 with hp | hp
  · simp [hp, zero_pow (show 2 * d - 1 ≠ 0 from by omega)]
  · rw [hpow]; field_simp [hp]; ring

lemma even_term_eq_T1_sub_T2 (k m p : ℕ) (hm_lt : m < k) :
    (bernoulli (2 * m) * ((2 * k).choose (2 * m)) * (p : ℚ) ^ (2*(k-m)) / (2*(k-m) + 1) : ℚ) =
    (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) * ((2 * k).choose (2 * m)) *
                 (p : ℚ) ^ (2*(k-m)) / (2*(k-m) + 1) -
    vonStaudtIndicator (2 * m) p * ((2 * k).choose (2 * m)) *
      (p : ℚ) ^ (2*(k-m) - 1) / (2*(k-m) + 1) := by
  have h := core_algebraic_identity (bernoulli (2 * m)) (vonStaudtIndicator (2 * m) p) p (k - m)
    (by omega)
  set C := ((2 * k).choose (2 * m) : ℚ)
  set N := (2 * (k - m) + 1 : ℚ)
  calc bernoulli (2 * m) * C * (p : ℚ) ^ (2*(k-m)) / N
      = (bernoulli (2 * m) * (p : ℚ) ^ (2*(k-m))) * C / N := by ring
    _ = ((bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) * (p : ℚ) ^ (2*(k-m)) -
         vonStaudtIndicator (2 * m) p * (p : ℚ) ^ (2*(k-m) - 1)) * C / N := by rw [h]
    _ = (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) * C * (p : ℚ) ^ (2*(k-m)) / N -
        vonStaudtIndicator (2 * m) p * C * (p : ℚ) ^ (2*(k-m) - 1) / N := by ring

theorem i1_term_forms_eq (k p : ℕ) (hk : k > 0) :
    bernoulli 1 * (2 * ↑k) * (p : ℚ) ^ (2 * k - 1) / (2 * ↑k) =
    bernoulli 1 * ↑(2 * k + 1) * (p : ℚ) ^ (2 * k - 1) / (2 * ↑k + 1) := by
  have h1 : (2 : ℚ) * k ≠ 0 := by positivity
  have h2 : (2 : ℚ) * k + 1 ≠ 0 := by positivity
  simp only [show (↑(2 * k + 1) : ℚ) = 2 * ↑k + 1 by norm_cast]
  field_simp [h1, h2]

lemma pIntegral_i1_term_in_sum (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    pIntegral p (bernoulli 1 * ((2 * k + 1).choose 1) * (p : ℚ) ^ (2 * k - 1) / (2 * k + 1)) := by
  simp only [Nat.choose_one_right]
  rw [← i1_term_forms_eq k p hk]
  exact pIntegral_i1_term k p hk hp

lemma valuation_bound_d_plus_1 (p d : ℕ) (hp : p.Prime) (hd : d ≥ 2) :
    (d + 1).factorization p ≤ d - 1 := by
  obtain hp2 | hp3 := hp.eq_two_or_odd
  · subst hp2
    obtain rfl | hd3 := eq_or_lt_of_le hd
    · exact valuation_bound_d_plus_1_p2_d2
    · apply Nat.factorization_le_of_le_pow
      exact pow_two_ge_succ_of_ge_three _ hd3
  · apply Nat.factorization_le_of_le_pow
    apply pow_ge_succ_of_ge_three
    · have hne2 : p ≠ 2 := fun h => by simp [h] at hp3
      have h1lt : 1 < p := hp.one_lt
      omega
    · exact hd

lemma choose_div_core (k m : ℕ) (hm_lt : m < k) :
    ((2 * k + 1).choose (2 * m) : ℚ) / (2 * k + 1) =
    ((2 * k).choose (2 * m) : ℚ) / (2 * k - 2 * m + 1) := by
  have h_denom : (2 * (k : ℚ) - 2 * m + 1) = ((2 * k - 2 * m + 1 : ℕ) : ℚ) := by
    simp only [Nat.cast_sub (by omega : 2 * m ≤ 2 * k), Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  conv_rhs => rw [h_denom]
  have h_nat : 2 * k + 1 - 2 * m = 2 * k - 2 * m + 1 := by grind
  simp only [h_nat.symm]
  have h_lhs_denom : (2 * (k : ℚ) + 1) = ((2 * k + 1 : ℕ) : ℚ) := by push_cast; ring
  conv_lhs => rw [h_lhs_denom]
  have hk_pos : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hd_pos : ((2 * k + 1 - 2 * m : ℕ) : ℚ) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  rw [div_eq_div_iff hk_pos hd_pos]
  exact_mod_cast (Nat.choose_mul_succ_eq (2 * k) (2 * m)).symm

lemma choose_div_simplify (k m : ℕ) (x : ℚ) (hm_lt : m < k) :
    ((2 * k + 1).choose (2 * m) : ℚ) * x / (2 * k + 1) =
    ((2 * k).choose (2 * m) : ℚ) * x / (2 * k - 2 * m + 1) := by
  have h := choose_div_core k m hm_lt
  rw [mul_comm ((2 * k + 1).choose (2 * m) : ℚ) x, mul_div_assoc,
      mul_comm ((2 * k).choose (2 * m) : ℚ) x, mul_div_assoc, h]

lemma pIntegral_case_one (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime) (hd : 2 * k - 2 * m ≥ 2) :
    pIntegral p (((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m - 1) /
      (2 * k - 2 * m + 1)) := by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_ne_zero, hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d ≠ 0 ∧ d + 1 ≠ 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m ≤ 2 * k := by omega
  have h_denom_rat : (2 * (k : ℚ) - 2 * m + 1) = ((d + 1 : ℕ) : ℚ) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h_exp, h_denom_rat]
  have h_pow_integral : pIntegral p ((p : ℚ) ^ (d - 1) / ((d + 1 : ℕ) : ℚ)) := by
    apply pIntegral_pow_div p (d + 1) (d - 1) hp hd_plus_one_ne_zero
    exact valuation_bound_d_plus_1 p d hp hd
  have h_eq : ((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (d - 1) / ((d + 1 : ℕ) : ℚ) =
      ((2 * k).choose (2 * m) : ℕ) * ((p : ℚ) ^ (d - 1) / ((d + 1 : ℕ) : ℚ)) := by ring
  rw [h_eq]
  exact pIntegral_int_mul p _ _ h_pow_integral

lemma pIntegral_second_term (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime) :
    pIntegral p (vonStaudtIndicator (2 * m) p * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m - 1) / (2 * k + 1)) := by
  unfold vonStaudtIndicator
  split_ifs with h
  · simp only [one_mul]
    rw [choose_div_simplify k m _ hm_lt]
    exact pIntegral_case_one k m p hm_lt hp (by omega)
  · simp only [zero_mul, zero_div]
    unfold pIntegral
    rw [Rat.den_zero]
    exact Nat.coprime_one_left_iff p |>.mpr trivial

lemma even_term_decomposition_identity (k m p : ℕ) (hm_lt : m < k) :
    (bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) : ℚ) =
    (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) -
    vonStaudtIndicator (2 * m) p * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m - 1) / (2 * k + 1) := by
  simp only [show 2 * k - 2 * m = 2 * (k - m) from by omega]
  have h := core_algebraic_identity (bernoulli (2 * m))
    (vonStaudtIndicator (2 * m) p) p (k - m) (by omega)
  set C := ((2 * k + 1).choose (2 * m) : ℚ)
  set N := (2 * k + 1 : ℚ)
  calc bernoulli (2 * m) * C * (p : ℚ) ^ (2 * (k - m)) / N
      = (bernoulli (2 * m) * (p : ℚ) ^ (2 * (k - m))) * C / N := by ring
    _ = ((bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / ↑p) *
         (p : ℚ) ^ (2 * (k - m)) -
         vonStaudtIndicator (2 * m) p * (p : ℚ) ^ (2 * (k - m) - 1)) *
         C / N := by rw [h]
    _ = _ := by ring

lemma pIntegral_coeff_term (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime) :
    pIntegral p (((2 * k + 1).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  have hsimp := choose_div_simplify k m ((p : ℚ) ^ (2 * k - 2 * m)) hm_lt
  rw [hsimp]
  have hp_factor : ((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) / (2 * k - 2 * m + 1) =
                   (p : ℚ) * (((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m - 1) /
                   (2 * k - 2 * m + 1)) := by
    have hpow : (p : ℚ) ^ (2 * k - 2 * m) = (p : ℚ) * (p : ℚ) ^ (2 * k - 2 * m - 1) := by
      conv_lhs =>
        rw [show (2 * k - 2 * m : ℕ) = (2 * k - 2 * m - 1) + 1 from by omega]
      exact pow_succ' _ _
    rw [hpow]
    ring
  rw [hp_factor]
  apply pIntegral_mul
  · exact pIntegral_of_int p p
  · exact pIntegral_case_one k m p hm_lt hp (by omega)

lemma pIntegral_first_term (k m p : ℕ) (hm_lt : m < k) (hp : p.Prime)
    (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p ((bernoulli (2 * m) +
      vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  rw [show (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) =
      (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      (((2 * k + 1).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) by ring]
  exact pIntegral_mul p _ _ ih (pIntegral_coeff_term k m p hm_lt hp)

lemma pIntegral_even_term_in_sum (k m p : ℕ) (hm_lt : m < k)
    (hp : p.Prime) (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  rw [even_term_decomposition_identity k m p hm_lt]
  exact pIntegral_sub p _ _ (pIntegral_first_term k m p hm_lt hp ih)
    (pIntegral_second_term k m p hm_lt hp)

lemma pIntegral_remainder (k p : ℕ) (hk : k > 0) (hp : p.Prime)
    (ih : ∀ m, 0 < m → m < k → pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (∑ i ∈ Finset.range (2 * k),
      bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
  apply pIntegral_sum
  intro i hi
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact pIntegral_i0_term k p hk hp
  · simp only [zero_add]
    exact pIntegral_i1_term_in_sum k p hk hp
  · set j := i + 2 with hj_def
    have hj_lt : j < 2 * k := by omega
    rcases Nat.even_or_odd j with ⟨m, hm⟩ | hodd
    · have ⟨_, hm_lt, hj_eq⟩ : m ≥ 1 ∧ m < k ∧ j = 2 * m := by omega
      simp only [hj_eq]
      exact pIntegral_even_term_in_sum k m p hm_lt hp (ih m (by omega) hm_lt)
    · simp only [bernoulli_eq_zero_of_odd hodd (by rcases hodd with ⟨r, hr⟩; omega),
        zero_mul, zero_div]
      unfold pIntegral
      simp only [Rat.den_zero]
      exact Nat.coprime_one_left_iff p |>.mpr trivial

lemma faulhaber_top_term (k p : ℕ) :
    bernoulli (2 * k) * ((2 * k + 1).choose (2 * k)) * (p : ℚ) ^ (2 * k + 1 - 2 * k) / (2 * k + 1) =
    p * bernoulli (2 * k) := by
  have h1 : (2 * k + 1).choose (2 * k) = 2 * k + 1 := by
    rw [← Nat.choose_symm_of_eq_add (by omega : 2 * k + 1 = 1 + 2 * k), Nat.choose_one_right]
  rw [h1, show (2 * k + 1 - 2 * k : ℕ) = 1 from by omega, pow_one]
  have h4 : (2 * k + 1 : ℚ) ≠ 0 := by positivity
  field_simp [h4]
  ring_nf
  field_simp [h4]
  norm_cast
  ring_nf

lemma power_sum_indicator_divisible_by_p (k p : ℕ) (hp : p.Prime) :
    ∃ T : ℤ, (∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) +
    (if (p - 1 : ℕ) ∣ (2 * k) then 1 else 0) = p * T := by
  have h_cast : (↑((∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) +
      (if (p - 1 : ℕ) ∣ (2 * k) then 1 else 0)) : ZMod p) = 0 := by
    push_cast
    exact power_sum_add_indicator_eq_zero p (2 * k) hp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_cast
  exact h_cast

lemma faulhaber_split_top_term (k p : ℕ) :
    (∑ i ∈ Finset.range (2 * k + 1),
      bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) =
    (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k + 1 - i) /
      (2 * k + 1)) + bernoulli (2 * k) * ((2 * k + 1).choose (2 * k)) *
      (p : ℚ) ^ (2 * k + 1 - 2 * k) / (2 * k + 1) := by
  have h3 : Finset.range (2 * k + 1) = Finset.range (2 * k) ∪ {2 * k} := by
    ext x; simp [Finset.mem_range]; omega
  have h4 : Disjoint (Finset.range (2 * k)) ({2 * k} : Finset ℕ) := by
    simp [Finset.disjoint_left]; omega
  rw [h3, Finset.sum_union h4, Finset.sum_singleton]

lemma rat_power_sum_eq_filter_ne_zero (k p : ℕ) (hk : k > 0) :
    (∑ v ∈ Finset.range p, (v : ℚ) ^ (2 * k)) =
      ∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k) := by
  conv_lhs =>
    arg 2; ext v
    rw [show (v : ℚ) ^ (2 * k) = if v ≠ 0 then (v : ℚ) ^ (2 * k) else 0 by
      split_ifs with h
      · rfl
      · simp [show v = 0 by omega, show 2 * k ≠ 0 from by omega]]
  rw [Finset.sum_filter]

lemma remainder_div_p (k p : ℕ) (hp : p.Prime) :
    (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k + 1 - i) /
      (2 * k + 1)) / p =
    (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) /
      (2 * k + 1)) := by
  have h0 : (∑ i ∈ Finset.range (2 * k), (bernoulli i : ℚ) * ((2 * k + 1).choose i : ℚ) *
      (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1 : ℚ)) / (p : ℚ) =
      ∑ i ∈ Finset.range (2 * k), (bernoulli i : ℚ) * ((2 * k + 1).choose i : ℚ) *
      (p : ℚ) ^ (2 * k - i) / (2 * k + 1 : ℚ) := by
    have h1 : ∀ i ∈ Finset.range (2 * k), ((bernoulli i : ℚ) * ((2 * k + 1).choose i : ℚ) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1 : ℚ)) / (p : ℚ) =
        (bernoulli i : ℚ) * ((2 * k + 1).choose i : ℚ) * (p : ℚ) ^ (2 * k - i) /
        (2 * k + 1 : ℚ) := by
      intro i hi
      have h2 : i < 2 * k := Finset.mem_range.mp hi
      have h5 : (p : ℚ) ≠ 0 := by norm_cast; exact Nat.Prime.ne_zero hp
      rw [show (2 * k + 1 - i : ℕ) = (2 * k - i : ℕ) + 1 from by omega, pow_succ]
      field_simp [h5]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => h1 i hi
  exact_mod_cast h0

lemma algebraic_rearrangement (k p : ℕ) (T : ℤ) (hp : p.Prime)
    (hT' : (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) + vonStaudtIndicator (2 * k) p =
      (p : ℚ) * (T : ℚ))
    (hFaul : (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) =
      (∑ i ∈ Finset.range (2 * k), bernoulli i *
      ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) + p * bernoulli (2 * k)) :
    bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p = T - (∑ i ∈ Finset.range (2 * k),
      bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) / p := by
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp_ne]
  linarith

lemma divisibility_to_rat_eq (k p : ℕ) (T : ℤ)
    (hT : (∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) +
          (if (p - 1 : ℕ) ∣ (2 * k) then 1 else 0) = p * T) :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) +
      vonStaudtIndicator (2 * k) p = p * T := by
  have h1 : ((∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) : ℚ) =
      ∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k) := by norm_cast
  have h2 : ((if (p - 1 : ℕ) ∣ (2 * k) then (1 : ℤ) else (0 : ℤ)) : ℚ) =
      vonStaudtIndicator (2 * k) p := by
    split_ifs at * <;> simp_all [vonStaudtIndicator]
  have h4 : ((∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) : ℚ) +
      ((if (p - 1 : ℕ) ∣ (2 * k) then (1 : ℤ) else (0 : ℤ)) : ℚ) = (p : ℚ) * T := by
    norm_cast at hT ⊢
  calc (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) + vonStaudtIndicator (2 * k) p =
      ((∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) : ℚ) +
      ((if (p - 1 : ℕ) ∣ (2 * k) then (1 : ℤ) else (0 : ℤ)) : ℚ) := by rw [h1, h2]
    _ = (p : ℚ) * T := by rw [h4]
    _ = p * T := by simp

lemma bernoulli_plus_indicator_rearrangement (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    ∃ T : ℤ, bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ Finset.range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
  obtain ⟨T, hT⟩ := power_sum_indicator_divisible_by_p k p hp
  use T
  have hT' : (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) + vonStaudtIndicator (2 * k) p =
      p * T := divisibility_to_rat_eq k p T hT
  have hFaul : (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) =
               (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
                (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) + p * bernoulli (2 * k) := by
    rw [← rat_power_sum_eq_filter_ne_zero k p hk]
    simp only [sum_range_pow]; push_cast
    rw [faulhaber_split_top_term, faulhaber_top_term]
  have hAlg := algebraic_rearrangement k p T hp hT' hFaul
  rw [hAlg, remainder_div_p k p hp]

lemma bernoulli_plus_indicator_coprime_p_pos (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    (bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p).den.Coprime p := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨T, hT⟩ := bernoulli_plus_indicator_rearrangement k p hk hp
    rw [hT]
    have hT_int : pIntegral p (T : ℚ) := pIntegral_of_int p T
    have hR : pIntegral p (∑ i ∈ Finset.range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
      apply pIntegral_remainder k p hk hp
      intro m hm_pos hm_lt
      exact ih m hm_lt hm_pos
    exact pIntegral_sub p T _ hT_int hR

lemma sum_other_primes_coprime_p_pos (k p : ℕ) (hp : p.Prime) :
    (∑ q ∈ Finset.range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k ∧ q ≠ p,
      (1 : ℚ) / q).den.Coprime p := by
  apply Nat.Coprime.of_dvd_left
  · exact sum_den_dvd_prod_den _ _
  · exact prod_den_coprime_p k p hp

lemma von_staudt_coprime_all_primes_pos (k p : ℕ) (hk : k > 0) (hp : p.Prime) :
    (bernoulli (2 * k) + ∑ q ∈ Finset.range (2 * k + 2) with
      q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q).den.Coprime p := by
  rw [sum_primes_eq_indicator_add_rest k p hk hp]
  rw [← add_assoc]
  exact Nat.Coprime.of_dvd_left (Rat.add_den_dvd _ _)
    ((bernoulli_plus_indicator_coprime_p_pos k p hk hp).mul_left
      (sum_other_primes_coprime_p_pos k p hp))

theorem von_staudt_clausen (k : ℕ) :
    bernoulli (2 * k) + ∑ p ∈ Finset.range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
      (1 : ℚ) / p ∈ Set.range Int.cast := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : bernoulli (2 * 0) = 1 := by norm_num [bernoulli_zero]
    have h2 : ∑ p ∈ Finset.range (2 * 0 + 2) with
        p.Prime ∧ (p - 1) ∣ 2 * 0, (1 : ℚ) / p = 0 := by norm_num; decide
    rw [h1, h2]
    exact ⟨1, by norm_num⟩
  · exact is_integer_of_coprime_all_primes _
      (fun p hp => von_staudt_coprime_all_primes_pos k p hk hp)

end vonStaudtClausen
