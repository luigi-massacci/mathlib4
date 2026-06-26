import Mathlib

open SchwartzMap Filter Nat NNReal ContDiff Topology

-- set_option trace.Meta.synthInstance true

noncomputable def bumpAux (x : ℝ) : ℂ :=
 if x ∈ Set.Ioo (-1 : ℝ) 1  then Complex.exp (-1 / (1 - x^2)) else 0

theorem smooth_bumpAux : ContDiff ℝ ∞ bumpAux := by
  have heq : bumpAux = Complex.ofRealCLM ∘ expNegInvGlue ∘ (fun x : ℝ => 1 - x ^ 2) := by
    funext x; simp only [Function.comp, Complex.ofRealCLM_apply, bumpAux]
    split_ifs with hx
    · have h1 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
      simp only [expNegInvGlue, if_neg (not_le.mpr h1), Complex.ofReal_exp]
      congr 1; push_cast; ring
    · have h2 : 1 - x ^ 2 ≤ 0 := by
        simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
        rcases hx with h | h <;> nlinarith [sq_nonneg x]
      simp [expNegInvGlue, h2]
  rw [heq]; fun_prop

theorem bumpAux_hasCompactSupport : HasCompactSupport bumpAux := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  simp only [Function.mem_support, bumpAux] at hx
  exact Set.Ioo_subset_Icc_self (not_not.mp fun h => hx (if_neg h))


noncomputable def bump : 𝓢(ℝ, ℂ) := bumpAux_hasCompactSupport.toSchwartzMap smooth_bumpAux

/-!
### Non-analyticity of the bump function

The real part of `bumpAux` is `g := expNegInvGlue ∘ (1 - ·²)`.

**Proof that `‖D^n bumpAux‖_∞ / n! → ∞`**:
- `g(x) = 0` for all `x ≥ 1`, so all iterated derivatives `D^k g(1) = 0` (the function is
  flat at 1). This follows from `iteratedFDerivWithin_congr` (within-derivatives on `Ici 1` agree
  with those of the zero function) combined with `iteratedDerivWithin_eq_iteratedDeriv`
  (using `UniqueDiffOn ℝ (Ici 1)`).
- By Taylor's theorem with Lagrange remainder for `g`, centered at `x₀ = 1` and evaluated at
  `x = 1/2` to order `n-1`, the polynomial part vanishes (all coefficients are zero), giving
  `g(1/2) = D^n g(ξₙ) · (-1/2)^n / n!` for some `ξₙ ∈ (1/2, 1)`.
- Since `g(1/2) = exp(-4/3) > 0`, we get `|D^n g(ξₙ)| / n! = 2^n · exp(-4/3)`.
- Since `bumpAux = ↑ ∘ g`, `‖D^n bumpAux(ξₙ)‖ = |D^n g(ξₙ)|`, so
  `sup_x ‖D^n bumpAux(x)‖ / n! ≥ 2^n · ‖bumpAux(1/2)‖ → ∞`.
-/

private noncomputable def g : ℝ → ℝ := expNegInvGlue ∘ (fun x : ℝ => 1 - x ^ 2)

private lemma smooth_g : ContDiff ℝ ∞ g := by unfold g; fun_prop

private lemma g_eq_bumpAux : bumpAux = Complex.ofRealCLM ∘ g := by
  funext x; simp only [Function.comp, Complex.ofRealCLM_apply, bumpAux, g]
  split_ifs with hx
  · have h1 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
    simp only [expNegInvGlue, if_neg (not_le.mpr h1), Complex.ofReal_exp]
    congr 1; push_cast; ring
  · have h2 : 1 - x ^ 2 ≤ 0 := by
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with h | h <;> nlinarith [sq_nonneg x]
    simp [expNegInvGlue, h2]

private lemma g_zero_on_Ici (x : ℝ) (hx : 1 ≤ x) : g x = 0 := by
  simp [g, expNegInvGlue, le_abs.2 (.inl hx)]

/-- All iterated derivatives of `g` vanish at `x = 1`. -/
lemma g_iteratedDeriv_one_eq_zero (k : ℕ) : iteratedDeriv k g 1 = 0 := by
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 1) smooth_g.contDiffAt
      (Set.self_mem_Ici (le_rfl _))]
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_congr (fun x hx => g_zero_on_Ici x hx)
        (Set.left_mem_Ici.mpr le_rfl) k,
      iteratedFDerivWithin_fun_zero]
  rfl

/-- The iterated derivatives of `bumpAux` are the complex embedding of those of `g`. -/
lemma iteratedDeriv_bumpAux_ofReal (n : ℕ) (x : ℝ) :
    iteratedDeriv ℝ n bumpAux x = (iteratedDeriv ℝ n g x : ℂ) := by
  have h : iteratedFDeriv ℝ n bumpAux x =
      Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ n g x) := by
    conv_lhs => rw [g_eq_bumpAux]
    exact Complex.ofRealCLM.iteratedFDeriv_comp_left smooth_g le_top
  simp only [iteratedDeriv_eq_iteratedFDeriv, h,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, Complex.ofRealCLM_apply]

/-- **Key bound**: there exists `ξ ∈ (1/2, 1)` with
`‖bumpAux(1/2)‖ · 2^n ≤ n!⁻¹ · ‖D^n bumpAux(ξ)‖`.

Proof: Taylor's theorem centered at `1` (where all derivatives of `g` vanish) evaluated at `1/2`
gives `g(1/2) = D^n g(ξ) · (-1/2)^n / n!`, hence `|D^n g(ξ)| / n! = 2^n · g(1/2)`. -/
lemma bumpAux_taylor_lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ ξ ∈ Set.Ioo (1/2 : ℝ) 1,
      ‖bumpAux (1/2 : ℝ)‖ * 2 ^ n ≤ (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv ℝ n bumpAux ξ‖ := by
  sorry

/-- The sup norm of the `n`-th derivative of `bumpAux`, divided by `n!`, tends to `+∞`. -/
theorem bumpAux_itDeriv_div_factorial_tendsto_atTop :
    Filter.Tendsto
      (fun n : ℕ => (⨆ x : ℝ, ‖iteratedDeriv ℝ n bumpAux x‖) / (n.factorial : ℝ))
      Filter.atTop Filter.atTop := by
  apply Filter.Tendsto.atTop_div_const (eventually_of_forall fun n => le_ciSup_of_le ⟨0, 0⟩ 0 le_rfl)
  sorry

example (hExp : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • ((SchwartzMap.derivCLM ℂ ℂ) ^ n))))
  : False := by

  have tendstoZero := Summable.tendsto_cofinite_zero hExp

  have H := WithSeminorms.tendsto_nhds_atTop (schwartz_withSeminorms ℂ ..)
    ((fun n => ((n.factorial : ℂ)⁻¹ • ((SchwartzMap.derivCLM ℂ ℂ) ^ n)) bump))
    ((0 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) bump)

  have hcont : Continuous (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T bump) :=
    ContinuousLinearMap.instContinuousEvalConst.continuous_eval_const _

  have h1 : Tendsto (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • (SchwartzMap.derivCLM ℂ ℂ) ^ n) bump)
    cofinite (nhds ((0 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) bump)) := by
    have := (hcont.tendsto 0).comp tendstoZero
    rw [show ((fun T => T bump) ∘ fun n => (n.factorial : ℂ)⁻¹ • derivCLM ℂ ℂ ^ n) =
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • (SchwartzMap.derivCLM ℂ ℂ) ^ n) bump) by congr] at this
    assumption

  rw [Nat.cofinite_eq_atTop, H] at h1
  -- Use ε = ‖bumpAux(1/2)‖ > 0 as threshold (using 1 would fail for N = 0)
  have hε_pos : 0 < ‖bumpAux (1/2 : ℝ)‖ :=
    norm_pos_iff.mpr (by simp [bumpAux, show (1/2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num,
                               Complex.exp_ne_zero])
  specialize h1 ⟨0, 0⟩ ‖bumpAux (1/2 : ℝ)‖ hε_pos
  rcases h1 with ⟨N, hN⟩
  contrapose! hN
  use N + 1
  simp
  set f : 𝓢(ℝ, ℂ) :=
    (((N + 1).factorial : ℂ)⁻¹ • (⇑(derivCLM ℂ ℂ))^[N] ((derivCLM ℂ ℂ) bump)) with f_def
  have hbound := (le_seminorm ℂ 0 0 f)
  simp at hbound
  nth_rewrite 1 [f_def] at hbound
  simp at hbound
  -- Need: ∃ x, ‖bumpAux(1/2)‖ ≤ (N+1)!⁻¹ · ‖D^{N+1} bumpAux(x)‖
  -- From Taylor: (N+1)!⁻¹ · ‖D^{N+1} bumpAux(ξ)‖ = 2^{N+1} · ‖bumpAux(1/2)‖ ≥ ‖bumpAux(1/2)‖
  have :
    ∃ x : ℝ, ‖bumpAux (1/2 : ℝ)‖ ≤
      ((N + 1).factorial : ℝ)⁻¹ * ‖((⇑(derivCLM ℂ ℂ))^[N] ((derivCLM ℂ ℂ) bump)) x‖ := by
    sorry
  rcases this with ⟨x, hx⟩
  exact le_trans hx (hbound x)
