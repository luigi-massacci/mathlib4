import Mathlib

open SchwartzMap Filter

-- set_option trace.Meta.synthInstance true

noncomputable instance : TopologicalSpace (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  infer_instance

noncomputable def bump (x : ℝ) : ℂ :=
 if x ∈ Set.Ioo (-1 : ℝ) 1  then Complex.exp (-1 / (1 - x^2)) else 0


example (hExp : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • ((SchwartzMap.derivCLM ℂ ℂ) ^ n))))
  : False := by
  have tendstoZero := Summable.tendsto_cofinite_zero hExp
  let bump : 𝓢(ℝ, ℂ) := sorry

  have := WithSeminorms.tendsto_nhds_atTop (schwartz_withSeminorms ℂ ..)
    ((fun n => ((n.factorial : ℂ)⁻¹ • ((SchwartzMap.derivCLM ℂ ℂ) ^ n)) bump))
    ((0 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) bump)

  have hcont : Continuous (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T bump) := ContinuousLinearMap.instContinuousEvalConst.continuous_eval_const _
  have h1 : Tendsto (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • (SchwartzMap.derivCLM ℂ ℂ) ^ n) bump) cofinite (nhds ((0 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) bump)) := by
    have h := (hcont.tendsto 0).comp tendstoZero
    have : ((fun T => T bump) ∘ fun n => (n.factorial : ℂ)⁻¹ • derivCLM ℂ ℂ ^ n) = (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • (SchwartzMap.derivCLM ℂ ℂ) ^ n) bump) := by
      congr
    rw [this] at h
    exact h
  rw [Nat.cofinite_eq_atTop] at h1
  rw [this] at h1
  simp at h1
  specialize h1 0 0 1 (zero_lt_one)
  rcases h1 with ⟨N, hN⟩
  contrapose! hN
  use N+1
  simp
  set f  : 𝓢(ℝ, ℂ) := (((N + 1).factorial : ℂ)⁻¹ • (⇑(derivCLM ℂ ℂ))^[N] ((derivCLM ℂ ℂ) bump)) with f_def

  have hbound := (le_seminorm ℂ 0 0 f)
  simp at hbound
  nth_rewrite 1 [f_def] at hbound
  simp at hbound
  have :
    ∃ x : ℝ, 1 ≤ ((N + 1).factorial : ℝ)⁻¹ * ‖((⇑(derivCLM ℂ ℂ))^[N] ((derivCLM ℂ ℂ) bump)) x‖ := by
    sorry
  rcases this with ⟨x, hx⟩
  exact le_trans hx (hbound x)







  sorry
