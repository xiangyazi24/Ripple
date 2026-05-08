# Apéry ρ-branch ratio_bound 证明路线图

写于 2026-04-29 凌晨。3 个 ratio_bound sorries 的具体拆解：
`aperyFrobenius_{half,one,zero}_ratio_bound`。

每个 sorry 都需要拆成 7 个 sub-lemma，然后 chain 起来。

## 拆解（以 ρ=1/2 为例）

### sub-lemma 1: `aperyFrobenius_half_explicit_3step`

陈述：对 m ≥ 3，
```
c(m+1) = α(m)·c(m) + β(m)·c(m-1) + γ(m)·c(m-2)
```
其中（用现有的 Apéry-specific lemmas）：

**Denominator:**
```
denom(m+1) = (m+3/2)(m+1/2)(m+1)·P'(z₁)
```
（用 `aperyConifold_simpleZeroIndicialPoly_factor` at x = m+3/2，
ff(m+3/2, 2)·(m+1)·P'(z₁) = (m+3/2)(m+1/2)(m+1)·P'(z₁)）

**Weights** (用 `coeff_substLHSGen_one_explicit` + Taylor connectors):
```
w_m = -ff(m+1/2, 2)·Q'(z₁) - ff(m+1/2, 3)·P''(z₁)/2
w_{m-1} = ff(m-1/2, 2)·Q''(z₁)/2 + ff(m-1/2, 3)·P'''(z₁)/6
w_{m-2} = -ff(m-3/2, 2)·Q'''(z₁)/6 - ff(m-3/2, 3)·P^(4)(z₁)/24
```

**Coefficients α, β, γ:**
```
α(m) = -w_m/denom(m+1)
β(m) = -w_{m-1}/denom(m+1)
γ(m) = -w_{m-2}/denom(m+1)
```

代入 Apéry 数值（用 `aperyQconifold_deriv_eval_z1` 系列 + `aperyPconifold_deriv_eval_z1` 系列）后展开成具体有理函数 m 的形式。

**估计行数：** ~120 行（unfold frobeniusBuilder + substLHS + 大量 Apéry-specific simp）。

### sub-lemma 2: `aperyFrobenius_half_alpha_lim`

α(m) → α∞ 当 m → ∞。

**显式值:**
```
α∞ = -P''(z₁)/(2·P'(z₁))
   = -2·(1729 - 1224√2)/(2·(19584 - 13848√2))
   = -(1729 - 1224√2)/(19584 - 13848√2)
```

数值上 ≈ -12.2.

**证明：** 把 sub-lemma 1 的 α(m) 公式取极限。M·z₁ 等校正项的 m → ∞ 极限。

**估计行数：** ~40 行。

### sub-lemma 3: `aperyFrobenius_half_alpha_rate`

|α(m) - α∞| ≤ C/m for m ≥ M₀.

**估计行数：** ~30 行（bound 多项式分母里的 1/m 项）。

### sub-lemma 4: `aperyFrobenius_half_beta_lim` + 5: `aperyFrobenius_half_gamma_lim`

类似 sub-lemma 2，对 β 和 γ。需要更多 Apéry 数值代入。

**估计行数：** 各 ~40 行。

### sub-lemma 6: `aperyFrobenius_half_char_poly_identity`

```
α∞·z₁ + β∞·z₁² + γ∞·z₁³ = 1
```

这是 dominant eigenvalue 1/z₁ 满足 char poly 的具体计算。

**关键恒等式（已用过）：**
- Q(z₁) = (3/2)·P'(z₁)
- 2·Q'(z₁) = 3·P''(z₁)
- z₁² = 34·z₁ - 1
- P^(4)(z₁) = 24

代入这些后，`α∞·z₁ + β∞·z₁² + γ∞·z₁³` 应化简为 `1`。

**估计行数：** ~80 行（heavy nlinarith with sqrt 2 hints）。

### sub-lemma 7: ratio_bound（finale）

用 1-6 + 双 IH bootstrap (upper bound 和 lower bound 的 |c(m-1)|/|c(m)|) 闭合。

**关键要点：**
- IH 维护 `K_low·m·(1/z₁)^m ≤ |c(m)| ≤ K_high·m·(1/z₁)^m` 双侧。
- 比较 |c(m-1)|/|c(m)| ≤ K_high/(K_low·z₁)·(m-1)/m。
- 套入 ratio recurrence + 用 char poly identity 让 m·... 项相消。

**估计行数：** ~150 行 (bootstrap induction)。

## ρ=0 与 ρ=1 的对应

结构相同，区别仅在：
- `denom(m+1)` 的 ff 部分（ρ + m + 1 不同）
- ff(ρ + m, j) 的具体值

ρ=1: x = m+2，ff(m+2, 2) = (m+2)(m+1)，simpleZero(m+2) = ff(m+2, 2)·(m+2-1/2)·P'(z₁) = (m+2)(m+1)(m+3/2)·P'(z₁)。

ρ=0: x = m+1（仅 m ≥ 1 因为 ρ=0 在 m=0 处共振），simpleZero(m+1) = ff(m+1, 2)·(m+1/2)·P'(z₁) = (m+1)·m·(m+1/2)·P'(z₁)。

每个 case 单独走 7-step，但很多 sub-lemma 可以参数化一次写好。

## 总估计

- 单 case (ρ=1/2) 全部 7 sub-lemma： ~500 行
- 三个 case 复用结构后总计： ~900-1200 行

这是 4-6 个 dedicated session 的工作量。现状：基础设施已全部 in place（taylor coeff connectors, 显式 derivative values, simpleZeroIndicialPoly factorization, 3-step reduction），只缺 chain 起来 + 双 IH 收尾。

不需要 Birkhoff 渐近基或 Lyapunov，全是 Apéry 显式 algebra。
