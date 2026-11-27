/-
  ColumnAnalysis.lean — 실수·초월수(e, π)가 필요한 명제. Lean 4 + Mathlib 필요.
  ※ 이 파일은 작업 환경에서 Mathlib을 받을 수 없어 컴파일 확인을 하지 못했다.
    Mathlib 프로젝트에서 `lake env lean ColumnAnalysis.lean`으로 확인할 것.
  P ≠ NP 자체는 증명하지 않는다(미해결 문제). 칼럼이 그 결론을 세우는 데 쓰는
  구조적 명제(역이 없는 축약, 확인은 유한 걸음 등)만 증명한다.
-/
import Mathlib

open Real

namespace ColumnAnalysis

/-! ## 1. 전역 상수: 이항 계수 1, 2, 1 (염색체 T1) -/
theorem binom_121 (a b : ℝ) : (a + b) ^ 2 = 1 * a ^ 2 + 2 * (a * b) + 1 * b ^ 2 := by ring

theorem pascal_row2 : (List.range 3).map (fun k => Nat.choose 2 k) = [1, 2, 1] := by decide

/-! ## 2. 한 방향 흐름: x ∨ True 축약에는 역이 없다 -/
theorem or_true_no_inverse : ¬ ∃ g : Bool → Bool, ∀ x, g (x || true) = x := by
  rintro ⟨g, hg⟩
  have h1 := hg true
  have h2 := hg false
  simp at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ## 3. 오일러 항등식과 분해 -/
theorem euler_identity : Complex.exp (↑π * Complex.I) + 1 = 0 := by
  rw [Complex.exp_pi_mul_I]; ring

/-- 지수가 곱으로 갈라진다: 변수분리의 근거 -/
theorem exp_split (a b : ℂ) : Complex.exp (a + b) = Complex.exp a * Complex.exp b :=
  Complex.exp_add a b

/-- 평면파 e^(i(kx − ωt)) = e^(ikx)·e^(−iωt) -/
theorem plane_wave_split (k x ω t : ℝ) :
    Complex.exp (Complex.I * (k * x - ω * t)) =
      Complex.exp (Complex.I * (k * x)) * Complex.exp (-(Complex.I * (ω * t))) := by
  rw [← Complex.exp_add]; ring_nf

/-- 패턴 e^(λt)는 미분해도 자기 자신에 상수 λ가 곱해질 뿐이다 -/
theorem exp_pattern_deriv (lam t : ℝ) :
    HasDerivAt (fun s => Real.exp (lam * s)) (lam * Real.exp (lam * t)) t := by
  have h := ((hasDerivAt_id t).const_mul lam).exp
  simpa [mul_comm] using h

/-! ## 4. 유리수 매개변수와 초월 상수는 등식으로 만나지 못한다 -/
theorem rational_ne_pi (q : ℚ) : (q : ℝ) ≠ π := by
  intro h; exact irrational_pi ⟨q, h⟩

/-- 유리수 걸음은 π의 0이 아닌 정수배에 정확히 닿지 못한다(한 바퀴를 온전히 돌지 못한다) -/
theorem rational_ne_int_mul_pi (q : ℚ) (n : ℤ) (hn : n ≠ 0) : (q : ℝ) ≠ n * π := by
  intro h
  apply irrational_pi
  refine ⟨q / n, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  rw [h]; field_simp

/-! ## 5. 부등식이 패턴의 순서를 정한다 -/
/-- 실수부가 작은 패턴이 더 빨리 사라진다 -/
theorem pattern_order_real_part {a₁ a₂ t : ℝ} (ha : a₁ < a₂) (ht : 0 < t) :
    Real.exp (a₁ * t) < Real.exp (a₂ * t) :=
  Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right ha ht)

/-- 실수부가 같으면 t의 차수가 높은 쪽이 더 오래 남는다(t > 1) -/
theorem pattern_order_degree {k₁ k₂ : ℕ} {a t : ℝ} (hk : k₁ < k₂) (ht : 1 < t) :
    t ^ k₁ * Real.exp (a * t) < t ^ k₂ * Real.exp (a * t) :=
  mul_lt_mul_of_pos_right (pow_lt_pow_right₀ ht hk) (Real.exp_pos _)

/-! ## 6. 국소화 항등식: 몫을 더하면 전체와 정확히 같다 -/
theorem shares_split {ι : Type*} [DecidableEq ι] (s t : Finset ι) (h : Disjoint s t)
    (share : ι → ℝ) : (∑ i ∈ s ∪ t, share i) = (∑ i ∈ s, share i) + ∑ i ∈ t, share i :=
  Finset.sum_union h

/-! ## 7. 시간 점화식의 영점 -/
/-- 점화식 D_(n+1) = ρ·D_n 의 해 -/
def orbit (ρ D₀ : ℝ) : ℕ → ℝ
  | 0 => D₀
  | n + 1 => ρ * orbit ρ D₀ n

theorem orbit_eq (ρ D₀ : ℝ) (n : ℕ) : orbit ρ D₀ n = ρ ^ n * D₀ := by
  induction n with
  | zero => simp [orbit]
  | succ n ih => simp [orbit, ih, pow_succ]; ring

/-- 영점 0은 고정점이다(매개변수와 무관) -/
theorem zero_fixed (ρ : ℝ) : ρ * 0 = 0 := mul_zero ρ

/-- 수축률 0이면 한 걸음 만에 정확히 영점에 닿는다 -/
theorem reach_if_rho_zero (D₀ : ℝ) : orbit 0 D₀ 1 = 0 := by simp [orbit]

/-- 수축률이 0과 1 사이면 어떤 유한 걸음에서도 영점에 닿지 못한다 -/
theorem never_reach {ρ D₀ : ℝ} (hρ : 0 < ρ) (hD : D₀ ≠ 0) (n : ℕ) : orbit ρ D₀ n ≠ 0 := by
  rw [orbit_eq]; exact mul_ne_zero (pow_ne_zero n hρ.ne') hD

/-- 그러나 다가가기는 한다: D_n → 0 -/
theorem approaches {ρ D₀ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Filter.Tendsto (orbit ρ D₀) Filter.atTop (nhds 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const D₀
  simpa [funext (orbit_eq ρ D₀)] using this

/-- '도달했다'는 부등식으로만: 충분히 큰 걸음 뒤에는 |D_n| < ε -/
theorem reached_by_inequality {ρ D₀ ε : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, |orbit ρ D₀ n| < ε := by
  have h := (approaches (D₀ := D₀) h0 h1)
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

/-! ## 8. 염색체: D′ = (1−r)D, d′ = −d/2 -/
theorem chromo_T4 (r D₀ : ℝ) (n : ℕ) : orbit (1 - r) D₀ n = (1 - r) ^ n * D₀ := orbit_eq _ _ _

theorem chromo_T5 (d₀ : ℝ) (n : ℕ) : orbit (-1/2) d₀ n = (-1/2) ^ n * d₀ := orbit_eq _ _ _

/-! ## 9. 확인은 유한 걸음: 구간 판정은 결정 가능하다 -/
/-- 유리수 값이 유리수 구간 [L, U] 안에 드는지는 계산으로 판정된다 -/
instance inInterval_decidable (x L U : ℚ) : Decidable (L ≤ x ∧ x ≤ U) := inferInstance

example : (1 : ℚ) / 3 ∈ Set.Icc (333 / 1000 : ℚ) (334 / 1000) := by
  constructor <;> norm_num

end ColumnAnalysis
