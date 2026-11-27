#!/usr/bin/env python3
"""column_verify.py — 칼럼 「변하지 않는 것과 고르는 것」의 개념을 수식과 코드로 검증한다.

표준 라이브러리만 쓴다. 실행: python3 column_verify.py
각 검사는 증명(정확 산술의 등식·부등식), 반례, 정의(구간 판정) 가운데 하나로 끝난다.
하나라도 실패하면 종료 코드 1을 돌려준다.

장 구성
  1장  미분의 알맹이는 조합론이다        (전역 상수 nCr, 유한 간격 몫, b^1 계수)
  2·4장 세 층과 만나지 못하는 이유      (읽기 전용 상수, 복사되는 매개변수, 불리언 수축)
  5장  계산은 유리수로, 초월수는 구간으로 (점화식 A·B, 이항계수에서 오일러 분해로)
  6장  식과 값이 어긋날 때 — 검증기      (구현 검사, 정확도 구간, 육하원칙, 국소화 항등식)
  5·6장 오일러 분해의 패턴               (길이·각도 오차, 허수축 안정, i^n mod 4, 한 바퀴 닫힘)
  5장  함수로 옮기면 · 변수분리           (그래프 상수, 반이산 열방정식의 고유모드)
  8장  확인과 찾기                       (확인 비용과 탐색 비용의 비대칭 — 대응, 증명 아님)
  9장  과거·현재·미래의 점화식            (씨앗 하나로 재생성, 위조 거부, 다대일 수축)
  11장 OSI 7계층                         (ping 표본 수, RTO 합, 리틀의 법칙, 창/RTT 한계)
  12장 염색체 한 쌍                      (T1·T3·T4·T5·T7, t*(ε), 호에프딩)
  13장 달을 0점으로 둔 우주               (광행시간, 조석력, 시차, 25/12 일치)
"""
from __future__ import annotations

import cmath
import hashlib
import hmac
import math
import random
import struct
import sys
import types
from fractions import Fraction as Fr
from math import comb, factorial

RESULTS: list[tuple[str, str, bool, str]] = []   # (장, 검사, 통과, 근거)


def check(chapter: str, name: str, cond: bool, note: str = "") -> bool:
    RESULTS.append((chapter, name, bool(cond), note))
    return bool(cond)


# ═════════════════════════════════════════ 1장. 미분의 알맹이는 조합론이다
def pascal_row(n: int) -> list[int]:
    """전역 상수: 덧셈 점화식 C(n,r) = C(n-1,r-1) + C(n-1,r)만으로 만든 이항계수 행."""
    row = [1]
    for _ in range(n):
        row = [1] + [row[i] + row[i + 1] for i in range(len(row) - 1)] + [1]
    return row


def chapter1() -> None:
    ch = "1장"
    # (가) 점화식으로 만든 계수 = 조합 수
    check(ch, "파스칼 점화식 행 = C(n,r) (n ≤ 30)",
          all(pascal_row(n) == [comb(n, r) for r in range(n + 1)] for n in range(31)))
    # (나) 불변: 같은 계수표가 모든 a, b에서 (a+b)^n을 정확히 만든다
    R = random.Random(1)
    ok = True
    for _ in range(300):
        a, b = Fr(R.randint(-50, 50), R.randint(1, 20)), Fr(R.randint(-50, 50), R.randint(1, 20))
        n = R.randint(0, 15)
        row = pascal_row(n)
        ok &= (a + b) ** n == sum(row[r] * a ** (n - r) * b ** r for r in range(n + 1))
    check(ch, "불변: 한 계수표가 무작위 유리수 a, b 300쌍에서 (a+b)^n과 정확히 같다", ok)
    # (다) 유한 간격 몫 = Σ_{r≥1} C(n,r) a^(n-r) b^(r-1), 앞 항 n·a^(n-1)이 변화율
    ok = True
    for n in range(1, 13):
        for a, b in ((Fr(3, 2), Fr(1, 10)), (Fr(-2), Fr(1, 1000)), (Fr(5, 7), Fr(-1, 3))):
            q = ((a + b) ** n - a ** n) / b
            ok &= q == sum(comb(n, r) * a ** (n - r) * b ** (r - 1) for r in range(1, n + 1))
            # 고차항의 크기는 간격 b가 정하는 상한 안에 갇힌다
            tail = abs(q - n * a ** (n - 1))
            bound = sum(comb(n, r) * abs(a) ** (n - r) * abs(b) ** (r - 1) for r in range(2, n + 1))
            ok &= tail <= bound
    check(ch, "유한 간격 몫의 전개와 고차항 상한 (극한 대신 구간)", ok)
    # (라) b → 0으로 몫이 n·a^(n-1)에 수렴: 상한이 b에 비례해 줄어든다
    a, n = Fr(3, 2), 7
    gaps = [abs(((a + b) ** n - a ** n) / b - n * a ** (n - 1)) for b in (Fr(1, 10 ** k) for k in range(1, 7))]
    ratios = [float(gaps[i] / gaps[i + 1]) for i in range(len(gaps) - 1)]
    # 간격이 클 때는 b^2 이상의 항이 남아 비가 10에서 벗어나고(11.06), 간격이 작아질수록 10에 붙는다
    check(ch, "b를 1/10씩 줄이면 몫과 n·a^(n-1)의 차이가 10배씩 준다 — 간격이 클수록 고차항 때문에 어긋난다",
          all(ratios[i] > ratios[i + 1] > 10 for i in range(len(ratios) - 1)) and abs(ratios[-1] - 10) < 1e-3,
          "비 " + ", ".join(f"{r:.4f}" for r in ratios))


# ═════════════════════════════════════════ 2·4장. 세 층과 만나지 못하는 네 가지 이유
GLOBAL = types.MappingProxyType({"C7": tuple(pascal_row(7))})   # 읽기 전용 전역 상수


def call_with_parameter(p: list[int]) -> list[int]:
    """매개변수는 복사본이다. 안에서 바꿔도 바깥 원본과 전역 상수는 그대로다."""
    p = list(p)          # 호출 시점에 값이 묶인다 (복사)
    p[0] = 999
    return p


def chapter2_4() -> None:
    ch = "2·4장"
    try:
        GLOBAL["C7"] = (0,)          # type: ignore[index]
        locked = False
    except TypeError:
        locked = True
    check(ch, "전역 상수는 안쪽에서 바꿀 수 없다 (읽기 전용)", locked)
    original = list(GLOBAL["C7"])
    changed = call_with_parameter(original)
    check(ch, "매개변수를 바꿔도 원본과 전역 상수는 그대로다 (값은 한 방향으로만 흐른다)",
          original == list(GLOBAL["C7"]) and changed[0] == 999)
    # 종속변수: 계수(틀)는 그대로, 결과는 매개변수에 따라 변한다
    vals = {sum(c * a ** (7 - r) * 1 ** r for r, c in enumerate(GLOBAL["C7"])) for a in range(1, 6)}
    check(ch, "같은 틀에서 매개변수 a만 바꾸면 종속변수가 모두 다르다", len(vals) == 5)
    # 전제 4: 참거짓 수축은 되돌릴 수 없다 (x ∨ True 의 역상은 두 개)
    preimage = [x for x in (False, True) if (x or True) is True]
    check(ch, "x ∨ True 는 다대일이라 역연산이 없다 (역상 2개)", len(preimage) == 2)


# ═════════════════════════════════════════ 5장. 계산은 유리수로, 초월수는 구간으로
E_REF = sum(Fr(1, factorial(k)) for k in range(60))       # e의 고정밀 유리수 근사 (오차 < 1/60!)


def recurrence_A(N: int) -> list[int]:
    a = [1]
    for n in range(1, N + 1):
        a.append(n * a[-1] + 1)
    return a


def integral_B(lam: Fr, tau: Fr, N: int) -> list[tuple[Fr, Fr, Fr]]:
    """후보 I_n과 부등식 구간 [I_n + L, I_n + U] (0 < x < n+3)."""
    x = lam * tau
    c, I, out = tau, tau, []
    for n in range(N + 1):
        if n > 0:
            c = c * x / (n + 1)
            I += c
        c_next = c * x / (n + 2)
        upper = I + c_next * (n + 3) / (n + 3 - x) if x < n + 3 else None   # 상한은 0 < x < n+3 에서만
        out.append((I, I + c_next, upper))
    return out


def exp_enclosure(x: Fr, n: int = 30) -> tuple[Fr, Fr]:
    """e^x의 유리수 구간. x ≥ 0이면 테일러 부분합과 등비 꼬리, x < 0이면 역수."""
    ax = abs(x)
    S, term = Fr(0), Fr(1)
    for k in range(n + 1):
        if k:
            term = term * ax / k
        S += term
    nxt = term * ax / (n + 1)
    assert ax < n + 2
    lo, hi = S, S + nxt * (n + 2) / (n + 2 - ax)
    return (lo, hi) if x >= 0 else (1 / hi, 1 / lo)


def chapter5() -> None:
    ch = "5장"
    a = recurrence_A(12)
    check(ch, "점화식 A: a_n = n·a_(n-1) + 1 = 1, 2, 5, 16, 65, 326, 1957, 13700, 109601",
          a[:9] == [1, 2, 5, 16, 65, 326, 1957, 13700, 109601])
    check(ch, "점화식 A: a_n < n!·e < a_n + 1/n, 곧 a_n = ⌊n!·e⌋ (n = 1..12)",
          all(a[n] < factorial(n) * E_REF < a[n] + Fr(1, n) for n in range(1, 13)))
    r_prev, ok = E_REF - 1, True
    for n in range(1, 13):
        r = factorial(n) * E_REF - a[n]
        ok &= abs(r - (n * r_prev - 1)) < Fr(1, 10 ** 40) and 0 < r < Fr(1, n)
        r_prev = r
    check(ch, "나머지 사다리: r_n = n·r_(n-1) − 1, 0 < r_n < 1/n (0이 되지 않는다)", ok)
    B = integral_B(Fr(1), Fr(1), 6)
    check(ch, "점화식 B: I_n = 1, 3/2, 5/3, 41/24, 103/60, 1237/720, 433/252",
          [t[0] for t in B] == [Fr(1), Fr(3, 2), Fr(5, 3), Fr(41, 24), Fr(103, 60), Fr(1237, 720), Fr(433, 252)])
    check(ch, "점화식 B: 모든 n에서 I_n + L < e − 1 < I_n + U",
          all(lo < E_REF - 1 < hi for _, lo, hi in B))
    check(ch, "두 점화식의 연결: λ = τ = 1이면 I_n = a_(n+1)/(n+1)! − 1",
          all(B[n][0] == Fr(a[n + 1], factorial(n + 1)) - 1 for n in range(7)))
    R, ok = random.Random(2), True
    for _ in range(200):
        lam, tau = Fr(R.randint(1, 30), R.randint(1, 10)), Fr(R.randint(1, 30), R.randint(1, 10))
        N = R.randint(0, 12)
        if not lam * tau < N + 3:
            continue
        I, lo, hi = integral_B(lam, tau, N)[-1]
        elo, ehi = exp_enclosure(lam * tau, 60)
        true_lo, true_hi = (elo - 1) / lam, (ehi - 1) / lam
        ok &= lo < true_lo and true_hi < hi
    check(ch, "점화식 B 일반화: 무작위 유리수 λ, τ에서 참값 (e^(λτ)−1)/λ가 구간 안", ok)
    # 이항계수에서 오일러 분해로: Σ_{n≤N} (a+b)^n/n! = Σ_{i+j≤N} a^i/i! · b^j/j! (정확한 항등식)
    ok = True
    for a_, b_ in ((Fr(1, 2), Fr(1, 3)), (Fr(-2), Fr(5, 7)), (Fr(3), Fr(-1, 4))):
        for N in range(12):
            lhs = sum((a_ + b_) ** n / factorial(n) for n in range(N + 1))
            rhs = sum(a_ ** i / factorial(i) * b_ ** j / factorial(j)
                      for i in range(N + 1) for j in range(N + 1 - i))
            ok &= lhs == rhs
    check(ch, "이항계수가 지수함수를 곱으로 가른다: 차수별로 e^(a+b) = e^a·e^b", ok)
    # 유한 간격에서도 지수 패턴은 '자기 자신 × t와 무관한 상수'
    lam, h = complex(-0.3, 2.0), 0.05
    ratios = [(cmath.exp(lam * (t + h)) - cmath.exp(lam * t)) / h / cmath.exp(lam * t) for t in (0.0, 0.7, 3.1)]
    check(ch, "유한 간격 미분 몫 ÷ e^(λt) = (e^(λh)−1)/h 는 t와 무관한 상수",
          max(abs(r - ratios[0]) for r in ratios) < 1e-12
          and abs(ratios[0] - (cmath.exp(lam * h) - 1) / h) < 1e-12)
    # 그 상수 = Σ λ^k h^(k−1)/k! 이고 항비가 점화식 B와 같은 꼴 c_k = c_(k−1)·(λh)/(k+1)
    c, s = lam, lam
    for k in range(1, 30):
        c = c * (lam * h) / (k + 1)
        s += c
    check(ch, "(e^(λh)−1)/h = Σ λ^k h^(k−1)/k! (항비 λh/(k+1), 점화식 B와 같은 꼴)",
          abs(s - (cmath.exp(lam * h) - 1) / h) < 1e-12)


# ═════════════════════════════════════════ 5·6장. 오일러 분해의 패턴과 시간 스킴
def R_euler(z: complex) -> complex:
    return 1 + z


def R_rk4(z: complex) -> complex:
    return 1 + z + z ** 2 / 2 + z ** 3 / 6 + z ** 4 / 24


def length_angle_error(R, z: complex) -> tuple[float, float]:
    """한 걸음 오차를 길이(e: 증폭·감쇠)와 각도(π: 위상 어긋남)로 가른다."""
    ex = cmath.exp(z)
    return abs(R(z)) - abs(ex), cmath.phase(R(z) / ex)

def arctan_inv_enclosure(m: int, terms: int) -> tuple[Fr, Fr]:
    """arctan(1/m)의 교대급수: 짝수 개 항의 합은 아래, 홀수 개 항의 합은 위."""
    x = Fr(1, m)
    partial = [Fr(0)]
    for k in range(terms + 1):
        partial.append(partial[-1] + (-1) ** k * x ** (2 * k + 1) / (2 * k + 1))
    a, b = partial[-1], partial[-2]
    return (min(a, b), max(a, b))


def pi_enclosure(terms: int = 30) -> tuple[Fr, Fr]:
    """마친 공식 π = 16·arctan(1/5) − 4·arctan(1/239)을 유리수 구간으로."""
    l5, u5 = arctan_inv_enclosure(5, terms)
    l239, u239 = arctan_inv_enclosure(239, terms)
    return 16 * l5 - 4 * u239, 16 * u5 - 4 * l239


def convergents(cf: list[int]) -> list[Fr]:
    """연분수 수렴분수: p_n = a_n·p_(n−1) + p_(n−2), q_n도 같은 점화식."""
    p0, p1, q0, q1 = 0, 1, 1, 0
    out = []
    for a in cf:
        p0, p1 = p1, a * p1 + p0
        q0, q1 = q1, a * q1 + q0
        out.append(Fr(p1, q1))
    return out


def taylor_at_iy(p: int, y: Fr) -> tuple[Fr, Fr]:
    """p차에서 자른 e^z를 z = iy에서 정확히 계산 (실수부, 허수부)."""
    re = im = Fr(0)
    tr, ti = Fr(1), Fr(0)
    for k in range(p + 1):
        re += tr; im += ti
        tr, ti = -ti * y / (k + 1), tr * y / (k + 1)
    return re, im


def chapter_ladders() -> None:
    ch = "5장(세 사다리)"
    lo, hi = pi_enclosure()
    check(ch, "π를 마친 공식으로 유리수 구간에 가둔다 (폭 < 10⁻⁴⁰)", lo < hi and hi - lo < Fr(1, 10 ** 40),
          f"폭 {float(hi - lo):.1e}")
    cv = convergents([3, 7, 15, 1, 292, 1, 1])
    check(ch, "π 연분수 수렴분수 = 3, 22/7, 333/106, 355/113, 103993/33102",
          cv[:5] == [Fr(3), Fr(22, 7), Fr(333, 106), Fr(355, 113), Fr(103993, 33102)])
    check(ch, "수렴분수는 π의 아래(짝수 번째)와 위(홀수 번째)를 번갈아 짚는다",
          all((c < lo) if n % 2 == 0 else (c > hi) for n, c in enumerate(cv)))
    check(ch, "333/106 < π < 355/113, 폭 약 10⁻⁴",
          Fr(333, 106) < lo and hi < Fr(355, 113) and Fr(355, 113) - Fr(333, 106) < Fr(1, 10 ** 4))
    # i: 4걸음 주기 (가우스 정수 (a, b) = a + bi)
    z, powers = (1, 0), []
    for _ in range(8):
        z = (-z[1], z[0]); powers.append(z)
    check(ch, "i의 거듭제곱은 i, −1, −i, 1로 4걸음마다 닫힌다",
          powers[:4] == [(0, 1), (-1, 0), (0, -1), (1, 0)] and powers[4:] == powers[:4])
    # mod 4 규칙
    y = Fr(1, 10)
    stab = {p: (lambda r: r[0] ** 2 + r[1] ** 2 < 1)(taylor_at_iy(p, y)) for p in range(1, 13)}
    check(ch, "mod 4 규칙: p ≡ 3, 0 (mod 4)이면 안정, 1, 2면 증폭 (p = 1..12, y = 1/10)",
          all(stab[p] == (p % 4 in (0, 3)) for p in stab))
    ys = [Fr(1, 3), Fr(1, 7), Fr(2, 5)]
    m2 = lambda p, y: (lambda r: r[0] ** 2 + r[1] ** 2)(taylor_at_iy(p, y))
    check(ch, "|1+iy|² = 1+y², 2차 1+y⁴/4, 3차 1−y⁴/12+y⁶/36, RK4 1−y⁶/72+y⁸/576",
          all(m2(1, y) == 1 + y ** 2 and m2(2, y) == 1 + y ** 4 / 4
              and m2(3, y) == 1 - y ** 4 / 12 + y ** 6 / 36
              and m2(4, y) == 1 - y ** 6 / 72 + y ** 8 / 576 for y in ys))
    # ‖e‖² = 길이² + 각도²
    ok = True
    for z in (0.3j, 1.1j, -0.2 + 0.9j, 2.5j):
        R, E = 1 + z + z * z / 2, cmath.exp(z)
        rho, sig, d = abs(R), abs(E), cmath.phase(R) - cmath.phase(E)
        length2, angle2 = (rho - sig) ** 2, 4 * rho * sig * math.sin(d / 2) ** 2
        ok &= abs(abs(R - E) ** 2 - (length2 + angle2)) < 1e-12
    check(ch, "‖e‖² = 길이² + 각도², 길이² = (|R|−|e^z|)², 각도² = 4|R||e^z|·sin²(Δθ/2)", ok)


def chapter_euler() -> None:
    ch = "5·6장"
    # 시간 스킴 = e^z 전개를 자른 것: 전진 오일러 1차(1a+1b의 자리), RK4 4차
    z = 0.1 + 0.05j
    tay = [sum(z ** k / factorial(k) for k in range(m + 1)) for m in range(5)]
    check(ch, "전진 오일러 = e^z의 1차 절단, RK4 = 4차 절단",
          abs(R_euler(z) - tay[1]) < 1e-15 and abs(R_rk4(z) - tay[4]) < 1e-15)
    # 국소 오차 차수: 걸음을 반으로 줄이면 오차가 2^(p+1)배 준다
    def order(R):
        e1 = abs(R(z) - cmath.exp(z)); e2 = abs(R(z / 2) - cmath.exp(z / 2))
        return math.log2(e1 / e2) - 1
    check(ch, "국소 오차 차수: 오일러 ≈ 1, RK4 ≈ 4", abs(order(R_euler) - 1) < 0.1 and abs(order(R_rk4) - 4) < 0.1,
          f"오일러 {order(R_euler):.2f}, RK4 {order(R_rk4):.2f}")
    # 허수축(회전) 위의 안정: 오일러는 |1+iy| > 1로 늘 증폭, RK4는 |y| ≤ 2√2에서 증폭 없음
    ys = [k / 1000 for k in range(1, 2829)]
    check(ch, "i(회전) 판정: 전진 오일러는 허수축에서 항상 증폭한다", all(abs(R_euler(1j * y)) > 1 for y in ys))
    check(ch, "i(회전) 판정: RK4는 허수축 |y| ≤ 2√2 에서 증폭 없음, 그 밖에서 증폭",
          all(abs(R_rk4(1j * y)) <= 1 + 1e-15 for y in ys) and abs(R_rk4(1j * 2.84)) > 1)
    dl, da = length_angle_error(R_rk4, 0.5j)
    dle, dae = length_angle_error(R_euler, 0.5j)
    check(ch, "길이·각도 분해: 순수 회전에서 RK4는 각도 오차보다 길이 오차가 작다, 오일러는 길이(증폭) 오차가 크다",
          abs(dl) < abs(da) < 1e-3 and dle > 0.1, f"RK4 길이 {dl:.2e} 각도 {da:.2e} / 오일러 길이 {dle:.2e}")
    check(ch, "i^n mod 4: 1, i, −1, −i 로 4걸음에 닫힌다",
          [1j ** n for n in range(8)] == [1, 1j, -1, -1j] * 2)
    # 한 바퀴에서만 사는 항등식: ∫_0^{2π} e^{it} dt = 0 (사다리꼴 합도 정확히 0에 가깝다), e^{iπ}+1 = 0
    M = 1000
    s = sum(cmath.exp(1j * 2 * math.pi * k / M) for k in range(M)) * (2 * math.pi / M)
    check(ch, "한 바퀴 닫힘: ∫_0^{2π} e^{it} dt = 0, e^{iπ} + 1 = 0",
          abs(s) < 1e-12 and abs(cmath.exp(1j * math.pi) + 1) < 1e-15)
    # 구간 끝이 π의 유리수 배가 아니면 닫히지 않는다: 유리수 걸음 τ로는 한 바퀴를 정확히 못 돈다
    taus = [Fr(1, 10), Fr(1, 7), Fr(3, 11)]
    check(ch, "유리수 걸음 τ의 정수배는 2π가 아니다 (닫힘은 구간으로 판정)",
          all(min(abs(float(k * t) - 2 * math.pi) for k in range(1, 200)) > 0 for t in taus))


# ═════════════════════════════════════════ 6장. 식과 값이 어긋날 때 — 검증기
U = 2.0 ** -53


def stepper_rk4(lam: float, h: float, y: float, bug: bool = False) -> float:
    """검은 상자 대상. bug=True면 두 번째 단계에 h/2 대신 h를 쓴다 (선형에서도 드러나는 구현 오류)."""
    k1 = lam * y
    k2 = lam * (y + (h if bug else h / 2) * k1)
    k3 = lam * (y + h / 2 * k2)
    k4 = lam * (y + h * k3)
    return y + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)


def implementation_check(lam: float, h: float, ys: list[float]) -> dict:
    """구현 검사: 실제 출력이 주장한 관계식 y_{n+1} = R(λh)·y_n 을 걸음마다 만족하는가.
    허용치는 주장 자신에서 유도한 반올림 상한 (연산 수 × u × 크기의 합)."""
    z = lam * h
    R = 1 + z + z * z / 2 + z ** 3 / 6 + z ** 4 / 24
    for n in range(len(ys) - 1):
        resid = abs(ys[n + 1] - R * ys[n])
        bound = 40 * U * (abs(ys[n + 1]) + (1 + abs(z) + z * z / 2 + abs(z) ** 3 / 6 + z ** 4 / 24) * abs(ys[n]))
        if resid > bound:
            return {"판정": "반례", "누가": "RK4라고 주장한 대상", "무엇을": "관계식 y_(n+1) = R(λh)·y_n",
                    "언제": f"걸음 {n} (t = {n * h:g})", "어디서": "성분 0",
                    "왜": f"차이 {resid:.3e} > 반올림 상한 {bound:.3e}", "어떻게": "그 걸음의 단계 계산을 공식과 맞춘 뒤 다시 판정"}
    return {"판정": "증명", "누가": "RK4", "무엇을": "모든 걸음에서 관계식 만족", "언제": "전 구간",
            "어디서": "-", "왜": "모든 차이 ≤ 반올림 상한", "어떻게": "-"}


def accuracy_check(lam: Fr, h: Fr, N: int, y0: Fr, yN: float, eps: Fr) -> dict:
    """정확도 검사: 참 해 e^(λT)·y0 를 유리수 구간으로 가두고 오차 구간을 ε와 비교한다."""
    lo, hi = exp_enclosure(lam * h * N, 40)
    t_lo, t_hi = sorted((lo * y0, hi * y0))
    yN_q = Fr(yN)
    err_lo = max(Fr(0), max(yN_q - t_hi, t_lo - yN_q))
    err_hi = max(abs(yN_q - t_lo), abs(yN_q - t_hi))
    if err_hi <= eps:
        verdict = "증명"
    elif err_lo > eps:
        verdict = "반례"
    else:
        verdict = "해상도 안 (기준해를 세분해 다시)"
    return {"판정": verdict, "오차 구간": (float(err_lo), float(err_hi)), "ε": float(eps)}


def localization_shares(R: Fr, E: Fr, ys: list[Fr]) -> tuple[list[Fr], Fr]:
    """국소화: 전역 오차 e_N = Σ_k E^(N−1−k)·(R−E)·y_k (e_0 = 0). 몫의 합이 전체와 정확히 같다."""
    N = len(ys) - 1
    shares = [E ** (N - 1 - k) * (R - E) * ys[k] for k in range(N)]
    exact = [ys[0]]
    for _ in range(N):
        exact.append(E * exact[-1])
    return shares, ys[N] - exact[N]


def chapter6() -> None:
    ch = "6장"
    lam, h, N = -1.0, 0.1, 50
    good, bad = [1.0], [1.0]
    for _ in range(N):
        good.append(stepper_rk4(lam, h, good[-1]))
        bad.append(stepper_rk4(lam, h, bad[-1], bug=True))
    rg, rb = implementation_check(lam, h, good), implementation_check(lam, h, bad)
    check(ch, "구현 검사: 맞는 RK4는 증명, 틀린 RK4는 걸음 0에서 반례", rg["판정"] == "증명" and rb["판정"] == "반례",
          f"틀린 쪽 육하원칙: 언제 {rb.get('언제')}, 왜 {rb.get('왜')}")
    acc = accuracy_check(Fr(-1), Fr(1, 10), N, Fr(1), good[-1], Fr(1, 10 ** 6))
    check(ch, "정확도 검사: 참 해를 유리수 구간으로 가둬 오차 ≤ 10^-6 증명", acc["판정"] == "증명",
          f"오차 구간 [{acc['오차 구간'][0]:.2e}, {acc['오차 구간'][1]:.2e}]")
    acc2 = accuracy_check(Fr(-1), Fr(1, 10), N, Fr(1), good[-1], Fr(1, 10 ** 9))
    check(ch, "정확도 검사: 같은 출력에 ε = 10^-9 를 요구하면 반례 (구현은 맞지만 걸음이 거칠다)",
          acc2["판정"] == "반례")
    # 국소화 항등식: 유리수로 정확히
    Rq = Fr(R_rk4(-0.1)).limit_denominator(10 ** 12)
    Eq = Fr(1) - Fr(1, 10) + Fr(1, 200) - Fr(1, 6000) + Fr(1, 240000) - Fr(1, 12000000)   # e^(-0.1) 근사도 상관없다
    ys = [Fr(1)]
    for _ in range(20):
        ys.append(Rq * ys[-1])
    shares, total = localization_shares(Rq, Eq, ys)
    check(ch, "국소화: 걸음별 몫의 합 = 전역 오차 (근사가 아니라 항등식)", sum(shares) == total)


# ═════════════════════════════════════════ 5장. 변수분리와 그래프 상수
def heat_matrix(n: int) -> list[list[Fr]]:
    """[0, π]의 영 경계 열방정식 u_t = u_xx 의 중심 차분 L (n개 내부 마디, 정확한 유리수 h는 쓰지 않고 1/h² 인자를 뺀 그래프 꼴)."""
    L = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        L[i][i] = Fr(-2)
        if i: L[i][i - 1] = Fr(1)
        if i < n - 1: L[i][i + 1] = Fr(1)
    return L


def chapter_separation() -> None:
    ch = "5장(변수분리)"
    n = 12
    L = heat_matrix(n)
    check(ch, "그래프 상수: L은 대칭이고 비대각은 음이 아니다 (메츨러)",
          all(L[i][j] == L[j][i] for i in range(n) for j in range(n))
          and all(L[i][j] >= 0 for i in range(n) for j in range(n) if i != j))
    # 공간 고유모드 sin(k x_j)는 L의 고유벡터: 편미분이 상수 곱으로 바뀐다
    h = math.pi / (n + 1)
    ok = True
    for k in range(1, n + 1):
        v = [math.sin(k * (j + 1) * h) for j in range(n)]
        mu = -4 * math.sin(k * h / 2) ** 2
        Lv = [sum(float(L[i][j]) * v[j] for j in range(n)) for i in range(n)]
        ok &= max(abs(Lv[i] - mu * v[i]) for i in range(n)) < 1e-12
    check(ch, "공간 모드 sin(kx)는 L의 고유벡터: ∂²/∂x²가 상수 −(4/h²)sin²(kh/2) 곱으로 바뀐다", ok)
    # 반이산 해 = Σ c_k e^{μ_k t / h²} v_k 이고, h → 0 에서 연속 고유값 −k²에 수렴 (근사)
    conv = [abs(-4 * math.sin(1 * (math.pi / (m + 1)) / 2) ** 2 / (math.pi / (m + 1)) ** 2 + 1) for m in (10, 20, 40, 80)]
    check(ch, "이산 고유값 → 연속 고유값 −k²: 격자를 2배 세밀하게 하면 오차 약 1/4 (2차)",
          all(3.5 < conv[i] / conv[i + 1] < 4.5 for i in range(3)))
    # 평면파: ∂/∂x e^{i(kx−ωt)} = ik·u, ∂/∂t = −iω·u (복소 차분으로 확인)
    k_, w_, x0, t0, d = 3.0, 2.0, 0.4, 1.3, 1e-6
    u = lambda x, t: cmath.exp(1j * (k_ * x - w_ * t))
    dx = (u(x0 + d, t0) - u(x0 - d, t0)) / (2 * d) / u(x0, t0)
    dt = (u(x0, t0 + d) - u(x0, t0 - d)) / (2 * d) / u(x0, t0)
    check(ch, "평면파의 편미분은 상수 곱: ∂x → ik, ∂t → −iω", abs(dx - 1j * k_) < 1e-6 and abs(dt + 1j * w_) < 1e-6)


# ═════════════════════════════════════════ 8장. 확인과 찾기 (대응 — 증명 아님)
def chapter8() -> None:
    ch = "8장(대응)"
    R = random.Random(8)
    rows = []
    for n in (8, 12, 16):
        items = [R.randint(1, 10 ** 6) for _ in range(n)]
        cert = [i for i in range(n) if R.random() < 0.5]
        target = sum(items[i] for i in cert)
        verify_ops = len(cert)                    # 확인: 증거를 더해 한 번 비교
        search_ops = 0
        found = None
        for mask in range(1 << n):                # 찾기: 증거 없이 전수 탐색
            search_ops += 1
            if sum(items[i] for i in range(n) if mask >> i & 1) == target:
                found = mask
                break
        rows.append((n, verify_ops, search_ops, found is not None))
    check(ch, "부분합 문제: 확인 비용은 n에 비례, 전수 탐색 비용은 최악 2^n (모든 사례에서 해를 찾음)",
          all(r[3] for r in rows) and all(r[1] <= r[0] for r in rows),
          "; ".join(f"n={a}: 확인 {b}회, 탐색 {c}회" for a, b, c, _ in rows))


# ═════════════════════════════════════════ 9장. 과거·현재·미래의 점화식
def chapter9() -> None:
    ch = "9장"
    secret, ctx = b"demo-server-secret-32byte-string", b"user=alice|device=42"
    seed = hmac.new(secret, b"seed|" + ctx, hashlib.sha256).digest()
    term = lambda k: hmac.new(seed, b"term|" + struct.pack(">q", k), hashlib.sha256).digest()[:16]
    check(ch, "씨앗 하나로 같은 순서의 값을 다시 만든다 (표 저장 불필요)", term(100) == term(100) and term(99) != term(101))
    body = struct.pack(">q", 100) + term(99)
    sig = hmac.new(secret, b"cookie|" + body, hashlib.sha256).digest()[:16]
    cookie = body + sig
    def verify(c: bytes) -> bool:
        b, s = c[:-16], c[-16:]
        return hmac.compare_digest(s, hmac.new(secret, b"cookie|" + b, hashlib.sha256).digest()[:16]) \
            and hmac.compare_digest(b[8:], term(struct.unpack(">q", b[:8])[0] - 1))
    forged = bytearray(cookie); forged[-1] ^= 1
    check(ch, "과거값 쿠키: 정상은 통과, 1비트 위조는 거부", verify(cookie) and not verify(bytes(forged)))
    check(ch, "문서 실행 결과와 일치: 쿠키 앞부분 00000000000000646fc95864",
          cookie.hex()[:24] == "00000000000000646fc95864")
    # 다대일 수축: 16바이트로 자른 출력 공간이 입력보다 작으므로 역사상이 하나로 정해지지 않는다
    outs = {hmac.new(seed, b"x" + bytes([i]), hashlib.sha256).digest()[:1] for i in range(256)}
    check(ch, "출력을 1바이트로 자르면 256개 입력이 더 적은 값으로 모인다 (다대일, 역연산 없음)", len(outs) < 256,
          f"서로 다른 출력 {len(outs)}개")


# ═════════════════════════════════════════ 11장. OSI 7계층
def chapter11() -> None:
    ch = "11장"
    miss = {N: (1 - 0.1) ** N for N in (10, 20, 50, 100)}
    check(ch, "손실률 10%에서 ping N회가 손실을 못 볼 확률 0.3487, 0.1216, 0.0052, 0.0000",
          [round(miss[N], 4) for N in (10, 20, 50, 100)] == [0.3487, 0.1216, 0.0052, 0.0])
    check(ch, "놓칠 확률 1% 미만이 되는 최소 ping 수 = 44", math.ceil(math.log(0.01) / math.log(0.9)) == 44)
    t, rto = 0.0, 0.2
    for _ in range(16):
        t += rto; rto = min(2 * rto, 120.0)
    check(ch, "RTO 점화식 합 (첫 0.2초, 상한 120초, 재시도 15) = 924.6초", abs(t - 924.6) < 1e-9)
    check(ch, "리틀의 법칙 L = λW: 200 req/s × 0.5초 = 100", 200 * 0.5 == 100)
    check(ch, "창/RTT 한계: 수신창 64KB, RTT 50ms → 10.5 Mbps", round(65536 * 8 / 0.05 / 1e6, 1) == 10.5)
    check(ch, "대기열: 도착 105/s, 처리 100/s, 60초 → 300개, 대기 3.0초", (105 - 100) * 60 == 300)
    check(ch, "흐름 쏠림: 흐름 100개·경로 4개의 표준편차 4.33, 상대 17.3% (10,000개면 1.73%)",
          round(math.sqrt(100 * .25 * .75), 2) == 4.33 and round(math.sqrt(10000 * .25 * .75) / 2500 * 100, 2) == 1.73)
    hdr = bytes.fromhex("4500002800000000400666ce0a0000010a000002")
    def fold(b):
        s = sum((b[i] << 8) | b[i + 1] for i in range(0, len(b), 2))
        while s >> 16:
            s = (s & 0xFFFF) + (s >> 16)
        return s
    tt = bytearray(hdr); tt[8] = 0x50
    check(ch, "IP 헤더 접은 합 0xffff, TTL 1바이트 변경 → 0x1000", fold(hdr) == 0xFFFF and fold(bytes(tt)) == 0x1000)


# ═════════════════════════════════════════ 12장. 염색체 한 쌍
def chapter12() -> None:
    ch = "12장"
    ok = True
    for p in (0.1, 0.3, 0.5, 0.8):
        q = 1 - p
        coef = [comb(2, k) for k in range(3)]
        ok &= coef == [1, 2, 1] and abs(sum(coef[k] * p ** k * q ** (2 - k) for k in range(3)) - 1) < 1e-12
    check(ch, "T1 분리: 계수 (1,2,1)은 p와 무관, 빈도 합 1", ok)
    # T3 한 자리 사영: HW 사상을 두 번 적용해도 한 번과 같다
    def hw(f):
        AA, Aa, aa = f; p = AA + Aa / 2; return (p * p, 2 * p * (1 - p), (1 - p) ** 2)
    f0 = (Fr(3, 5), Fr(0), Fr(2, 5))
    check(ch, "T3 한 자리: 갱신 T는 사영 (T² = T, 1세대에 평형)", hw(hw(f0)) == hw(f0))
    # T4 두 자리 D' = (1−r)D, T5 X 연관 d' = −d/2
    R, ok4, ok5 = random.Random(4), True, True
    for _ in range(500):
        w = [Fr(R.randint(1, 100)) for _ in range(4)]; s = sum(w); AB, Ab, aB, ab = (x / s for x in w)
        r = Fr(R.randint(0, 100), 100)
        pA, pB = AB + Ab, AB + aB
        AB1 = (1 - r) * AB + r * pA * pB
        ok4 &= AB1 - pA * pB == (1 - r) * (AB - pA * pB)
        pf, pm = Fr(R.randint(0, 100), 100), Fr(R.randint(0, 100), 100)
        ok5 &= ((pf + pm) / 2 - pf) == -(pf - pm) / 2
    check(ch, "T4 두 자리: D_(t+1) = (1−r)·D_t (정확한 유리수 500건)", ok4)
    check(ch, "T5 X 연관: d_(t+1) = −d_t/2 (부호는 뒤집히고 크기는 절반)", ok5)
    def tstar(r, eps, D0=0.25):
        return math.ceil(math.log(D0 / eps) / (-math.log(1 - r)))
    table = [[tstar(r, e) for e in (1e-2, 1e-4, 1e-6)] for r in (0.5, 0.1, 0.01, 0.001)]
    check(ch, "T7 평형 부등식: t*(ε) 표 [5,12,18] [31,75,118] [321,779,1237] [3218,7821,12424]",
          table == [[5, 12, 18], [31, 75, 118], [321, 779, 1237], [3218, 7821, 12424]])
    D0 = Fr(1, 4)
    check(ch, "T7: ρ > 0이면 유한 t에서 D_t > 0 (등식 불가, r = 1/100, t ≤ 2000)",
          all(D0 * (1 - Fr(1, 100)) ** t > 0 for t in range(0, 2001, 250)))
    hoeff = [round(math.sqrt(math.log(2 / 0.01) / (2 * n)), 4) for n in (100, 1000, 10000, 100000)]
    check(ch, "호에프딩 99%: n = 100…100000 에서 ±0.1628, 0.0515, 0.0163, 0.0051",
          hoeff == [0.1628, 0.0515, 0.0163, 0.0051])
    n = math.ceil(math.log(2 / 0.01) / (2 * 1e-4 ** 2))
    check(ch, "실험 C: 도달 779세대, 확인 표본 264,915,869개 (서로 다른 변수에 의존)",
          tstar(0.01, 1e-4) == 779 and n == 264915869)


# ═════════════════════════════════════════ 13장. 달을 0점으로 둔 우주
def chapter13() -> None:
    ch = "13장"
    c = 299792.458
    t = {k: d / c for k, d in {"평균": 1.496e8, "근일점": 1.471e8, "원일점": 1.521e8, "화성": 2.28e8, "달": 3.844e5}.items()}
    check(ch, "광행시간: 평균 499초(8분 19초), 근일점 8분 11초, 원일점 8분 27초, 화성 약 12분 40초, 달 1.3초",
          round(t["평균"]) == 499 and divmod(round(t["근일점"]), 60) == (8, 11) and divmod(round(t["원일점"]), 60) == (8, 27)
          and abs(t["화성"] - 760) < 1 and round(t["달"], 1) == 1.3)
    check(ch, "500초(8분 20초)는 1년 변동 구간 [491, 507]초 안", 491 <= 500 <= 507 and 491 <= t["평균"] <= 507)
    check(ch, "499초의 표기: 60진법 8|19, 16진법 1F3, 0.139시간 (표기만 바뀐다)",
          divmod(499, 60) == (8, 19) and format(499, "X") == "1F3" and round(499 / 3600, 3) == 0.139)
    Ms, Mm, Me, rs, rm = 1.989e30, 7.342e22, 5.972e24, 1.496e11, 3.844e8
    grav, tide = (Ms / rs ** 2) / (Mm / rm ** 2), (Mm / rm ** 3) / (Ms / rs ** 3)
    check(ch, "중력은 태양이 달의 약 180배, 조석력(가속도의 거리 미분)은 달이 약 2.2배", 175 < grav < 182 and 2.1 < tide < 2.3,
          f"중력비 {grav:.0f}, 조석비 {tide:.2f}")
    check(ch, "지구–달 질량중심: 지구 중심에서 약 4,670km", 4600 < rm * Mm / (Mm + Me) / 1e3 < 4720)
    check(ch, "1 AU ÷ 태양 지름 ≈ 107", 107 <= 1.496e8 / 1.3927e6 < 108)
    check(ch, "1파섹 = 연주시차 1초각의 거리 ≈ 3.26광년",
          round((180 * 3600 / math.pi) * 1.495978707e11 / 9.4607e15, 2) == 3.26)
    check(ch, "블랙홀 지평선 r_s = 2GM/c²: 태양 질량이면 약 2.95km", abs(2 * 6.674e-11 * Ms / (c * 1e3) ** 2 - 2953) < 5)
    check(ch, "500초 동안 지구 자전각 = 1/480 Hz(mHz 단위) = 25/12 정확히 (86,400 = 480 × 180 때문)",
          Fr(360 * 500, 86400) == Fr(1000, 480) == Fr(25, 12) and 86400 == 480 * 180)
    check(ch, "자유낙하 점화식으로 원궤도가 닫힌다 (반지름 변동 1% 이하, 한 바퀴 위상 오차 작음)",
          _orbit_check())


def _orbit_check() -> bool:
    """v_(n+1) = v_n + g(x_n)h, x_(n+1) = x_n + v_(n+1)h 로 원궤도(GM = 1, r = 1)를 한 바퀴 돈다."""
    x, y, vx, vy, h = 1.0, 0.0, 0.0, 1.0, 2 * math.pi / 20000
    rmin = rmax = 1.0
    for _ in range(20000):
        r3 = (x * x + y * y) ** 1.5
        vx -= x / r3 * h; vy -= y / r3 * h
        x += vx * h; y += vy * h
        r = math.hypot(x, y); rmin, rmax = min(rmin, r), max(rmax, r)
    return rmax - rmin < 0.01 and math.hypot(x - 1, y) < 0.01


# ═════════════════════════════════════════ 실행
def main() -> int:
    for f in (chapter1, chapter2_4, chapter5, chapter_ladders, chapter_euler, chapter6, chapter_separation,
              chapter8, chapter9, chapter11, chapter12, chapter13):
        f()
    width = max(len(n) for _, n, _, _ in RESULTS)
    current = None
    for chap, name, ok, note in RESULTS:
        if chap != current:
            print(f"\n[{chap}]"); current = chap
        print(f"  {'통과' if ok else '실패'}  {name}" + (f"\n        └ {note}" if note else ""))
    fails = [r for r in RESULTS if not r[2]]
    print(f"\n검사 {len(RESULTS)}개 중 통과 {len(RESULTS) - len(fails)}개, 실패 {len(fails)}개")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
