import Mathlib

/-!
# 固定剩余类的二元哥德巴赫例外集

目标是把完整 Farey 证明接到 Mathlib。下文的 `DirichletGRH` 是显式假设，
`TwistEstimate`、`DyadicBound` 和 `Target` 是待证明命题的类型。
文件包含定义和有限集计数引理的证明草稿。解析节点的证明由以下依赖树指定。

```text
GRH → A1 尖截断显式公式与局部零点计数 → A2 平方根频率扭曲界
    → B0 素数幂转移和 q=1 的一阶矩
B0 + A2 + B1 特征展开 + B2 Farey 胞腔 → B3 余项 L∞ 与 L²
B2 + C1 Ramanujan 和 + C2 有限欧拉积 → C3 模型系数的正下界
B3 + C3 + D1 Fourier 卷积与 Bessel → D2 二进块例外计数
D2 + 余数类计数 + 几何级数 → E 全局 Target
```

## 坐标与模块边界

在二进块 `Y / 2 < n ≤ Y` 上，令 `H = Y / r + 1`（自然数除法），
`L = log(2Y)`，`Q = Nat.sqrt H`，`Q₀ = floor(Q / L)`，最后一个整除在实数中计算。
对两类均取 `0 ≤ j < H`、`p = r*j+b`，包括 `j=0`。于是当 `n ≥ b₁+b₂` 且
满足同余，`k=(n-b₁-b₂)/r` 是自然数，`k < H`，所有可能的两个素数都在截断内。
模型的完整 Fourier 系数因此出现 `k+1`。当 `r³ ≤ Y` 且 Y 足够大，
整块有 `n ≥ b₁+b₂` 和 `k+1 ≫ H`。小 Y 与 `r³ > Y` 在 D2 另有平凡计数分支。
固定奇素数 r 和两类 b₁,b₂，所有常数对这些参数一致。

## A. 定量解析输入

建议模块 `FareyGoldbach/TwistedExplicitFormula.lean`。

- [ ] `unitIntervalZeroCount`。对本原 χ，按重数计数，任一单位高度区间中临界
  带零点数 ≤ `C * log(2*d*(2+|T|))`。量化两侧高度。对复特征，关于实轴的共轭
  会把 χ 换成 `conj χ`。在同一 χ 的证明里直接分别估计正负高度。
- [ ] `sharpTwistedExplicitFormula`。选择 `T ≍ Y²` 的有效截断高度，或使用文献
  的等效截断约定。扣除极点主项之后，尖截断和等于有限零点积分之和加可控余项。
  每项为 `∫₂^Y u^(ρ-1) e(t*u) du`，把端点取整和跳跃纳入 `O(log²(2dY))`。把 `d=1` 的 ζ
  分支和非本原特征的导数修正写全。后者只涉及整除模数的素数幂，总权 `O(log d log Y)`。
- [ ] `twistEstimate_of_grh : DirichletGRH → TwistEstimate`。在 GRH 下，
  `|Im ρ| ≤ 1+4π|t|Y` 用二阶导给 `O(√Y / √(1+|Im ρ|))`，外面用一阶导给
  `O(√Y / |Im ρ|)`。用 A1 按单位高度求和。主特征扣掉的是离散几何和，
  要证明它与显式公式的连续主项至多差 `O(1)`，可直接积分每个单位段并用几何和。
  核对主特征 `t=0`、非本原特征和 `d=1` 三个分支。

解析依据为 Friedlander–Goldston, *Sums of Three or More Primes*, (7.1)–(7.5)。
https://doi.org/10.1090/S0002-9947-97-01652-8
Mathlib 已有 `DirichletCharacter.LFunction`、`LFunction_modOne_eq` 和
`DirichletCharacter.LSeries_twist_vonMangoldt_eq`。最后一个等式的收敛半平面
为 `1 < s.re`，它是显式公式的起点。GRH 要写在延拓的 `LFunction` 上。
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/DirichletContinuation.html

## B. 从逐特征界到全圆余项

建议模块 `FareyGoldbach/Cells.lean` 与 `FareyGoldbach/ProgressionSum.lean`。

- [ ] `primePowerMass`。`∑_{n≤Y} |Λ(n)-primeWeight(n)| ≪ √Y log²(2Y)`。写成
  `n=p^k`，`k≥2`，再用 `p≤√Y`、`k≤log₂ Y`。因此主圆法从一开始就可用真素数权。
- [ ] `rationalCharacterExpansion`。模 `rq` 的单位群上展开
  `1_{n≡b (mod r)} e(a*(n-b)/(rq))`。若 `(q,r)=1`，主系数是
  `e(-a*r⁻¹*b/q)*μ(q)/(φ(r)φ(q))`，系数 ℓ¹ ≤ `√q`。当 `q=1` 相位定义为 1。
  若 `r∣q`，用 `1+mq` 子群限制特征，主系数为 0，ℓ¹ ≤ `√(φ(q)/(r-1))`。
  证明时用群正交性和 Parseval。只为同一 r 的两个 b 构造两份和，共用胞腔。
  对 `r∤q` 用 CRT，`n` 与 `rq` 不互素的项另估 `O(log²(2Y))`。
  Mathlib 入口 `DirichletCharacter.sum_char_inv_mul_char_eq`。
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletCharacter/Orthogonality.html
- [ ] `fareyCellCover`。在 `AddCircle 1` 收集所有 `0≤a<q≤Q` 的约分中心。
  把 α 赋给使 `q*dist(α,a/q)` 最小的中心，平手按固定字典序决胜。
  这是有限个 Borel 比较。用 `Real.exists_rat_abs_sub_le_and_den_le` 证明外半径
  `|β|≤1/(qQ)`。若 α 到该中心距离 `<1/(2qQ)`，对任意另一中心 a'/q'，
  模 1 的有理间距 ≥ `1/(qq')` 给出 `q'*dist(α,a'/q') > 1/(2q) ≥ 1/(2Q)`，
  而本中心的加权距离 `<1/(2Q)`。故整个内弧归入本胞腔。
  q=1 的中心是 0/1，用圆周距离处理跨 0；开闭端点只影响零测集。
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DiophantineApproximation/Basic.html
- [ ] `remainder_sup`。在 `(q,r)=1`、`q≤Q₀` 处保留主特征模型 M，其他胞腔置零。
  模型取 `r/φ(r)` 乘 Ramanujan 相位系数 `μ(q)/φ(q)` 与 `V_H(β)`。
  将主特征几何和按长度 r 的块分组，换成 `r*V_H(β)`，差除以 r 后为 `O(1)`。
  使用 `q*|β|*H ≤ H/Q`、`Q ≍ √H` 把 A2 推成 `‖S-M‖∞≪√(YQ)L²`。
  舍弃的主项用 `H/φ(q)≪HL/Q₀`，这里 `Q₀≥1` 由大 Y、`r³≤Y` 得到。
- [ ] `model_and_prime_l2`。用 A2 的 `t=0`、B1 的 `q=1` 得 AP 素数权总重
  `O(H+√Y L²)=O(H)`，因为非平凡分支 `r³≤Y`。权值上界为 `L`，所以
  Parseval 给 `∫|S|²≪HL`。模型上逐胞腔用 `∫|V_H|²≤H` 和
  `∑_{q≤Q₀} μ²(q)/φ(q)≪log(2Q₀)` 得相同结论。算术平均可由
  `q/φ(q)=∑_{d∣q} μ²(d)/φ(d)` 与 `∑ μ²(d)/(dφ(d))<∞` 推出。

## C. 有限主项下界

建议模块 `FareyGoldbach/MainCoefficient.lean`。

- [ ] `ramanujanCoefficient`。两个模型相乘，再乘 `e(-k*(a/q+β))` 后，分子和为
  `c_q(n)`，其中 `n=r*k+b₁+b₂`。证明乘以 r 的逆元只置换约分分子。q=1 给 1。
- [ ] `completeCells`。每个胞腔的补弧误差 ≤ `C*q*Q`，由内半径以及
  `|V_H(β)|≤min(H, 1/(2|β|))` 得到。乘算术系数，累加 ≤ `C*Q*Q₀≤CH/L`。
  完整 Fourier 系数是 `k+1`，用 `Finset.range H`、`k < H` 数 `j₁+j₂=k`。
- [ ] `finiteSingularSeries_lower`。令 `A_q=1_{(q,r)=1} μ(q)²*c_q(n)/φ(q)²`。
  展开有限乘积 `∏_{p≤Q₀}(1+A_p)`。其中 `q≤Q₀` 的项恰给截断主项。
  其余项绝对值之和 ≤ `Q₀^(-1/2) * ∏_{p≤Q₀}(1+√p*|A_p|)`。
  `p∤n` 的因子用收敛 p 级数控制，`p∣n` 的因子对充分大 p ≤ `p^ε`。
  因此取 `ε=1/32` 即得一致的 `O(n^(1/32)/√Q₀)`。不用引入无限奇异级数。
  当 n 偶、r 奇、`Q₀≥2` 时，p=2 因子等于 2。其余 ≤1 的因子是
  `1-1/(p-1)²`。用 `∏_{j=2}^m(1-1/j²)=(m+1)/(2m)` 给有限乘积下界 1。
  验收要求 `Re(fourierCoeff (M₁*M₂) k) ≥ cH`，其中 c 为绝对常数。

## D. 有限 Fourier 系数与例外计数

建议模块 `FareyGoldbach/Dyadic.lean`。

- [ ] `primeConvolution_eq_fourierCoeff`。用 `AddCircle.fourier 1` 表示正指数基，
  用 `AddCircle.fourierCoeff_fourier` 取系数。通过 `p=r*j+b` 双射配到
  `primeRepresentations`，其系数为真素数对的 `log p₁*log p₂` 之和。
- [ ] `errorEnergy`。`F = (S₁-M₁)*S₂ + M₁*(S₂-M₂)`，所以
  `∫|F|²≪Y*Q*H*L⁵`。使用 `AddCircle.hasSum_sq_fourierCoeff` 取有限个系数的
  Bessel 上界，明确使用 `AddCircle.haarAddCircle`。其值与实坐标的单位长积分一致，
  使用 `AddCircle.fourierCoeff_eq_intervalIntegral` 对接 B/C。
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/AddCircle.html
- [ ] `dyadicBound_of_twistEstimate : TwistEstimate → DyadicBound`。
  例外目标的素数卷积为零，C 给误差系数的绝对值 ≥ `cH`。用下方
  `card_mul_sq_le_sum`，再除以 `(cH)²`，得 `O(√(Yr)*L⁵)`。
  若 `r³>Y` 且 `r≤Y`，同余计数 ≤ `Y/r+1≤2Y/r≤2√(Yr)`。
  若 Y 小于前面选好的绝对阈值，则扩大绝对常数。所有分支保留同一个 r。

## E. 全局组装与回归核查

建议模块 `FareyGoldbach/Main.lean`。

- [ ] `target_of_dyadicBound : DyadicBound → Target`。对 `Y_j=X/2^j` 取自然数除法。
  `(Y_j/2,Y_j]` 互不重叠。首次 `Y_j<r` 后，所有余下正整数在同余类中合计至多
  一个。其余块用 `∑√Y_j ≤ √X/(1-1/√2)`，不损失对数。独立使用同余计数
  `X/r+1≤2X/r`，再取两界的最小值。
- [ ] `exception_bound_of_dirichletGRH : DirichletGRH → Target`，依次接上 A、D、E。
  固定 mathlib 的提交和对应 `lean-toolchain` 后，用 `lake env lean` 验每个模块。
  最后 `#print axioms` 核查目标的依赖，GRH 明写为参数，解析缺口必须有证明。
- [ ] 回归例。`r=3,b₁=b₂=2,n=4` 检查下标 j=0。`r=5,b₁=1,b₂=4,n=30`
  用 `11+19` 检查 b₁+b₂ 可被 r 整除。`n=8,r=3,b₁=1,b₂=1` 应计为例外，
  高次幂 (4,4) 不属于素数对。用 `0/1` 胞腔测试跨 0，
  用 `r=X`、`r³=Y`、`Y=r-1` 测试计数分支。
- [ ] 若接入外部 GRH 库，单独增加适配模块、锁定提交并审计公理。
  接口可比较 `DirichletLZerosOnLine`，定量的 `TwistEstimate` 仍须单独导出。
  https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Challenge.lean
-/

open scoped BigOperators

namespace FareyGoldbachBlueprint

structure Progressions where
  r : ℕ
  prime_r : r.Prime
  odd_r : Odd r
  b₁ : ℕ
  b₂ : ℕ
  b₁_pos : 0 < b₁
  b₂_pos : 0 < b₂
  b₁_lt : b₁ < r
  b₂_lt : b₂ < r

noncomputable def primeRepresentations (P : Progressions) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 2 n).product (Finset.Icc 2 n)).filter fun pq =>
    pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = n ∧
      pq.1 % P.r = P.b₁ ∧ pq.2 % P.r = P.b₂

noncomputable def exceptions (P : Progressions) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n =>
    Even n ∧ n % P.r = (P.b₁ + P.b₂) % P.r ∧ (primeRepresentations P n).card = 0

noncomputable def dyadicExceptions (P : Progressions) (Y : ℕ) : Finset ℕ :=
  (exceptions P Y).filter fun n => Y / 2 < n

noncomputable def primeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)

noncomputable def primeSum (r b H : ℕ) (α : ℝ) : ℂ :=
  ∑ j ∈ Finset.range H, (primeWeight (r * j + b) : ℂ) * e (α * (j : ℝ))

structure RationalCenter where
  numerator : ℕ
  denominator : ℕ
  numerator_lt : numerator < denominator
  reduced : Nat.Coprime numerator denominator

noncomputable def kernel (H : ℕ) (β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range H, e (β * (j : ℝ))

noncomputable def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    e ((a : ℝ) * (n : ℝ) / (q : ℝ))

noncomputable def singularTrunc (r n cutoff : ℕ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 cutoff).filter (fun q => Nat.Coprime q r),
    (ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n /
      (q.totient : ℂ) ^ 2

def DirichletGRH : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2

noncomputable def tiltedRemainder {d : ℕ} (χ : DirichletCharacter ℂ d)
    (Y : ℕ) (t : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 Y,
    (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod d) -
      (if χ = 1 then (1 : ℂ) else 0)) * e (t * (n : ℝ))

def TwistEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖tiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) *
            (Real.log (2 * (d : ℝ) * Y)) ^ 2

noncomputable def dyadicBudget (Y r : ℕ) : ℝ :=
  Real.sqrt ((Y : ℝ) * r) * (Real.log (2 * (Y : ℝ))) ^ 5

def DyadicBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) (Y : ℕ), P.r ≤ Y →
    ((dyadicExceptions P Y).card : ℝ) ≤ C * dyadicBudget Y P.r

def Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) (X : ℕ), 3 ≤ X → P.r ≤ X →
    ((exceptions P X).card : ℝ) ≤
      C * min ((X : ℝ) / P.r) (dyadicBudget X P.r)

theorem card_mul_sq_le_sum {ι : Type*} {bad allTargets : Finset ι}
    (hsub : bad ⊆ allTargets) (err : ι → ℂ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) (hbad : ∀ i ∈ bad, threshold ≤ ‖err i‖) :
    (bad.card : ℝ) * threshold ^ 2 ≤ ∑ i ∈ allTargets, ‖err i‖ ^ 2 := by
  classical
  calc
    (bad.card : ℝ) * threshold ^ 2 = ∑ _i ∈ bad, threshold ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ bad, ‖err i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := mul_nonneg (sub_nonneg.mpr (hbad i hi))
        (add_nonneg (norm_nonneg (err i)) hthreshold)
      nlinarith
    _ ≤ ∑ i ∈ allTargets, ‖err i‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i _ _
        exact sq_nonneg ‖err i‖)

end FareyGoldbachBlueprint
