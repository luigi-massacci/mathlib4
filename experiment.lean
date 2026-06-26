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

  have hε_pos : 0 < ‖bump (1/2 : ℝ)‖ := sorry

  specialize h1 ⟨0, 0⟩ ‖bump (1/2 : ℝ)‖ hε_pos
  rcases h1 with ⟨N, hN⟩
  contrapose! hN
  use N + 1
  simp [-one_div]
  set f : 𝓢(ℝ, ℂ) :=
    (((N + 1).factorial : ℂ)⁻¹ • (⇑(derivCLM ℂ ℂ))^[N] ((derivCLM ℂ ℂ) bump)) with f_def
  have hbound := (le_seminorm ℂ 0 0 f)
  simp at hbound
  nth_rewrite 1 [f_def] at hbound
  simp at hbound
  have :
    ∃ x : ℝ, ‖bump (1/2 : ℝ)‖ ≤
      ((N + 1).factorial : ℝ)⁻¹ * ‖((⇑(derivCLM ℂ ℂ))^[N] ((derivCLM ℂ ℂ) bump)) x‖ := by
    sorry
  rcases this with ⟨x, hx⟩
  exact le_trans hx (hbound x)
