/-
  ColumnCore.lean — 「변하지 않는 것과 고르는 것」 핵심 명제의 Lean 4 검증 (Mathlib 없이 코어만)
  확인 방법:  lean ColumnCore.lean   (Lean 4.37.0-rc1에서 오류 없이 통과)

  여기서 증명하는 것은 칼럼이 P ≠ NP라는 결론을 세우는 데 쓰는 구조적 명제들이다.
  P ≠ NP 자체는 미해결 문제이므로 정리로 증명하지 않는다.
  실수·초월수(e, π)가 필요한 명제는 ColumnAnalysis.lean(Mathlib 필요)에 따로 있다.
-/

namespace ColumnCore

/-! ## 1. 전역 상수: 이항 계수 1, 2, 1 (염색체 T1, 파스칼 삼각형) -/

theorem binom_121 (a b : Int) : (a + b) ^ 2 = 1 * a ^ 2 + 2 * (a * b) + 1 * b ^ 2 := by grind

def pascal : Nat → List Nat
  | 0 => [1]
  | n + 1 => List.zipWith (· + ·) (0 :: pascal n) (pascal n ++ [0])

theorem pascal_row2 : pascal 2 = [1, 2, 1] := by decide
theorem pascal_row4 : pascal 4 = [1, 4, 6, 4, 1] := by decide

/-! ## 2. 한 방향 흐름: x ∨ True 축약에는 역이 없다 -/

theorem or_true_collapses (x : Bool) : (x || true) = true := by cases x <;> rfl

theorem or_true_no_inverse : ¬ ∃ g : Bool → Bool, ∀ x, g (x || true) = x := by
  intro ⟨g, hg⟩
  have h1 := hg true
  have h2 := hg false
  simp at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ## 3. 점화식 A: a_n = n·a_(n−1) + 1  (1, 2, 5, 16, 65, 326, … = ⌊n!·e⌋, n ≥ 1) -/

def recA : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * recA n + 1

theorem recA_values : (List.range 8).map recA = [1, 2, 5, 16, 65, 326, 1957, 13700] := by decide

/-! ## 4. 국소화 항등식: 몫을 더하면 전체와 정확히 같다 -/

theorem shares_split (l₁ l₂ : List Int) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  simp [List.sum_append]

/-! ## 5. 시간 점화식 D_(n+1) = ρ·D_n 과 영점 -/

def orbit (ρ D₀ : Rat) : Nat → Rat
  | 0 => D₀
  | n + 1 => ρ * orbit ρ D₀ n

/-- 영점 0은 매개변수 ρ와 무관한 고정점이다 -/
theorem zero_fixed (ρ : Rat) (n : Nat) : orbit ρ 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit, ih]

/-- 수축률이 0이면 한 걸음 만에 정확히 영점에 닿는다 -/
theorem reach_if_rho_zero (D₀ : Rat) : orbit 0 D₀ 1 = 0 := by simp [orbit]

/-- 수축률이 0이 아니면 어떤 유한 걸음에서도 영점에 닿지 못한다 -/
theorem never_reach {ρ D₀ : Rat} (hρ : ρ ≠ 0) (hD : D₀ ≠ 0) (n : Nat) : orbit ρ D₀ n ≠ 0 := by
  induction n with
  | zero => exact hD
  | succ n ih =>
    simp only [orbit]
    intro h
    rcases Rat.mul_eq_zero.mp h with h | h
    · exact hρ h
    · exact ih h

/-- 수축률과 시작값이 양수면 궤도는 계속 양수다 -/
theorem orbit_pos {ρ D₀ : Rat} (h0 : 0 < ρ) (hD : 0 < D₀) (n : Nat) : 0 < orbit ρ D₀ n := by
  induction n with
  | zero => exact hD
  | succ n ih => exact Rat.mul_pos h0 ih

/-- 수축하면 걸음마다 작아진다: 0 < ρ < 1, D₀ > 0 이면 D_(n+1) < D_n -/
theorem strictly_shrinks {ρ D₀ : Rat} (h0 : 0 < ρ) (h1 : ρ < 1) (hD : 0 < D₀) (n : Nat) :
    orbit ρ D₀ (n + 1) < orbit ρ D₀ n := by
  have h := Rat.mul_lt_mul_of_pos_right h1 (orbit_pos h0 hD n)
  rw [Rat.one_mul] at h
  exact h

/-- '도달했다'는 부등식으로만 말한다: ρ = 1/2, D₀ = 1, ε = 1/1000 → 10걸음 뒤 -/
def reached (ρ D₀ ε : Rat) (n : Nat) : Bool := decide (orbit ρ D₀ n < ε)

theorem reached_at_10 : reached (1/2) 1 (1/1000) 10 = true := by native_decide
theorem not_reached_at_9 : reached (1/2) 1 (1/1000) 9 = false := by native_decide

/-! ## 6. 부등식이 패턴의 순서를 정한다
  패턴 e^(λt)를 걸음 h로 이산화하면 걸음마다 ρ = |e^(λh)|를 곱한다.
  실수부 a가 작을수록 ρ가 작다. 아래는 ρ가 작은 패턴이 매 걸음 더 작다는 것,
  곧 먼저 사라진다는 것을 보인다. -/

theorem pattern_order {ρ₁ ρ₂ D₀ : Rat} (h0 : 0 < ρ₁) (h12 : ρ₁ < ρ₂) (hD : 0 < D₀) (n : Nat) :
    orbit ρ₁ D₀ (n + 1) < orbit ρ₂ D₀ (n + 1) := by
  have h2 : 0 < ρ₂ := Std.lt_trans h0 h12
  induction n with
  | zero => exact Rat.mul_lt_mul_of_pos_right h12 hD
  | succ n ih =>
    show ρ₁ * orbit ρ₁ D₀ (n + 1) < ρ₂ * orbit ρ₂ D₀ (n + 1)
    exact Std.lt_trans (Rat.mul_lt_mul_of_pos_right h12 (orbit_pos h0 hD (n + 1)))
      (Rat.mul_lt_mul_of_pos_left ih h2)

/-- 같은 기준 ε에 먼저 닿는 쪽이 먼저 사라지는 패턴이다 (ρ = 1/2 은 10걸음, ρ = 9/10 은 66걸음) -/
theorem order_by_steps :
    reached (1/2) 1 (1/1000) 10 = true ∧ reached (9/10) 1 (1/1000) 65 = false ∧
    reached (9/10) 1 (1/1000) 66 = true := by native_decide

/-! ## 7. 염색체: D′ = (1−r)D, d′ = −d/2 -/

theorem chromo_T5_sign : orbit (-1/2) 1 1 = -1/2 ∧ orbit (-1/2) 1 2 = 1/4 := by native_decide

/-! ## 8. 확인은 유한 걸음: 구간 판정은 계산으로 끝난다 -/

def inInterval (x L U : Rat) : Bool := decide (L ≤ x) && decide (x ≤ U)

theorem check_one_third : inInterval (1/3) (333/1000) (334/1000) = true := by native_decide

end ColumnCore
