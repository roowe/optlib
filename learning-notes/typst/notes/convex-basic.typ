#block[
#block[
= Convex Basic 学习笔记
<convex-basic-学习笔记>
主题：`import Mathlib.Analysis.Convex.Basic`、 `Convex 𝕜 s`、标量域/半环
`𝕜`、非负线性组合、最优传输视角、线性映射与仿射映射。

#block[
#link(<module>)[1. 模块做什么] #link(<convex>)[2. Convex 𝕜 s 的含义]
#link(<scalar>)[3. 标量域/半环 𝕜] #link(<nonnegative>)[4. 非负线性组合]
#link(<ot>)[5. 最优传输中的例子]
#link(<linear-affine>)[6. 线性映射 vs 仿射映射]
#link(<lean>)[7. Lean 使用小抄]
]
]
#block[
== 1. `Mathlib.Analysis.Convex.Basic` 做什么？
<mathlib.analysis.convex.basic-做什么>
这个模块是 Mathlib 中关于#strong[凸集基础理论]的模块。
它主要不是研究凸函数，而是研究集合的凸性：

#block[
s 是凸集 ⇔ 任意 x, y ∈ s，连接 x 和 y 的线段仍然在 s 中。
]
Lean 中的主要对象是：

```
Convex 𝕜 s
```

其中 `s : Set E` 是某个空间 `E` 里的集合， `𝕜`
是标量类型，也就是凸组合的系数来自哪里。

#block[
一句话记忆： \ #strong[`Mathlib.Analysis.Convex.Basic` =
定义凸集，并证明凸集的基础封闭性质。]
]
] <module>
#block[
== 2. `Convex 𝕜 s` 的数学含义
<convex-𝕜-s-的数学含义>
数学上，凸集的常见定义是：

#block[
若 x ∈ s, y ∈ s, a ≥ 0, b ≥ 0, a + b = 1， \ 则 a • x + b • y ∈ s。
]
这里的

```
a • x + b • y
```

就是两个点 `x`、`y` 的凸组合。

=== 线段版本
<线段版本>
也可以理解为：

#block[
Convex 𝕜 s ⇔ 对任意 x, y ∈ s，segment 𝕜 x y ⊆ s。
]
Lean 里相关定理常见名称：

```
#check convex_iff_segment_subset
#check Convex.segment_subset
```

=== 凸组合版本
<凸组合版本>
Lean 里最常用的直观形式是：

```
example {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ s := by
  exact hs hx hy ha hb hab
```

#block[
这段代码表达的是：如果 `s` 是凸的，那么 `s` 对凸组合封闭。
]
] <convex>
#block[
== 3. 标量域/半环 `𝕜` 是什么？
<标量域半环-𝕜-是什么>
在 `Convex 𝕜 s` 中，`𝕜` 表示#strong[系数来自哪个数系]。 例如在表达

```
a • x + b • y
```

时，`a b : 𝕜`。

=== 常见选择
<常见选择>
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([𝕜], [含义], [几何直观],),
    table.hline(),
    [`ℝ`], [实数标量], [最常见的普通几何凸性],
    [`ℚ`], [有理数标量], [只允许有理系数凸组合],
    [`ℕ`], [自然数标量], [几何意义很弱，因为 a + b = 1 只给出端点],
    [`ℝ≥0`], [非负实数标量], [适合描述非负线性组合、锥、非负测度],
  )]
  , kind: table
  )

=== 为什么 `ℕ` 的凸性很弱？
<为什么-ℕ-的凸性很弱>
如果 `a b : ℕ` 且

#block[
a + b = 1
]
那么只能是：

#block[
a = 1, b = 0 \ 或者 \ a = 0, b = 1。
]
因此凸组合只能得到端点 `x` 或 `y`，不能得到真正的中间点。

#block[
学习时可以先把 `𝕜` 脑补成 `ℝ`。也就是说，先把 `Convex 𝕜 s` 理解成
`Convex ℝ s`。
]
=== 半环和域的区别
<半环和域的区别>
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([结构], [大致含义], [例子],),
    table.hline(),
    [半环 Semiring], [有 0, 1, +, \*，但不一定能减、能除], [`ℕ`, `ℝ≥0`],
    [域 Field], [有加减乘除，非零元素可除], [`ℚ`, `ℝ`],
  )]
  , kind: table
  )

凸性还需要写 `0 ≤ a`、`0 ≤ b`， 所以 `𝕜` 通常还要带有顺序结构。

] <scalar>
#block[
== 4. 非负线性组合、凸组合、锥
<非负线性组合凸组合锥>
=== 线性组合
<线性组合>
#block[
∑ᵢ aᵢ xᵢ
]
其中系数 `aᵢ` 可以正、可以负。

=== 非负线性组合
<非负线性组合>
#block[
∑ᵢ aᵢ xᵢ，且 aᵢ ≥ 0。
]
非负线性组合生成的对象通常叫#strong[锥]，也就是 cone。 例如：

#block[
2x + 3y
]
是非负线性组合。

=== 凸组合
<凸组合>
#block[
∑ᵢ aᵢ xᵢ，且 aᵢ ≥ 0，并且 ∑ᵢ aᵢ = 1。
]
例如：

#block[
0.3x + 0.7y
]
是凸组合。

#block[
#strong[核心关系：] \ 凸组合 = 非负线性组合 + 系数和为 1。
]
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([概念], [要求], [生成对象],),
    table.hline(),
    [线性组合], [系数任意], [线性子空间/span],
    [非负线性组合], [系数非负], [锥/cone],
    [凸组合], [系数非负，且系数和为 1], [凸包/convex hull],
  )]
  , kind: table
  )

] <nonnegative>
#block[
== 5. 最优传输中的非负线性组合
<最优传输中的非负线性组合>
你提到"非负线性组合在最优传输里面很常见"，这个理解很关键。
最优传输里的很多对象，本质上都是：

#block[
非负锥 + 线性约束 + 线性目标函数。
]
=== 离散概率测度
<离散概率测度>
一个离散概率测度可以写成 Dirac 测度的凸组合：

#block[
μ = ∑ᵢ aᵢ δ\_{xᵢ}，其中 aᵢ ≥ 0，∑ᵢ aᵢ = 1。
]
如果只要求 `aᵢ ≥ 0`，不要求总质量为 1，那么得到的是有限非负测度：

#block[
μ = ∑ᵢ aᵢ δ\_{xᵢ}，其中 aᵢ ≥ 0。
]
#block[
非负测度 = Dirac 测度的非负线性组合。 \ 概率测度 = Dirac 测度的凸组合。
]
=== 离散运输计划
<离散运输计划>
离散最优传输中，运输计划通常是一个矩阵：

#block[
π = (πᵢⱼ)，其中 πᵢⱼ ≥ 0。
]
边缘约束为：

#block[
∑ⱼ πᵢⱼ = μᵢ， \ ∑ᵢ πᵢⱼ = νⱼ。
]
运输计划集合可写成：

#block[
Π(μ, ν) = { π ≥ 0 | ∑ⱼ πᵢⱼ = μᵢ, ∑ᵢ πᵢⱼ = νⱼ }。
]
这个集合是凸的。原因是如果 `π₁` 和 `π₂` 都满足边缘约束， 那么对
`0 ≤ t ≤ 1`：

#block[
tπ₁ + (1 - t)π₂
]
仍然非负，并且仍然满足同样的边缘约束。

#block[
OT 中常见结构： \ 非负矩阵 / 非负测度 → 加上总质量或边缘约束 →
得到凸可行集 → 在线性目标下优化。
]
] <ot>
#block[
== 6. 线性映射和仿射映射的区别
<线性映射和仿射映射的区别>
#block[
#strong[一句话：] \ 线性映射必须保持原点；仿射映射允许整体平移。
]
=== 线性映射
<线性映射>
一个映射 `f` 是线性的，如果：

#block[
f(x + y) = f(x) + f(y)， \ f(a x) = a f(x)。
]
因此线性映射必然满足：

#block[
f(0) = 0。
]
例子：

#block[
f(x) = 2x
]
二维例子：

#block[
f(x, y) = (2x, 3y)
]
=== 仿射映射
<仿射映射>
仿射映射具有形式：

#block[
f(x) = L(x) + b
]
其中 `L` 是线性映射，`b` 是一个固定向量。

#block[
仿射映射 = 线性映射 + 平移。
]
例子：

#block[
g(x) = 2x + 1
]
它不是线性的，因为 `g(0) = 1 ≠ 0`； 但它是仿射的。

=== 为什么仿射映射保持凸性？
<为什么仿射映射保持凸性>
虽然仿射映射不保持一般线性组合，但它保持凸组合。

设 `f(x) = L(x) + c`，如果 `a + b = 1`，那么：

#block[
f(a x + b y) \ = L(a x + b y) + c \ = aL(x) + bL(y) + c \ = a(L(x) + c)
\+ b(L(y) + c) \ = a f(x) + b f(y)。
]
关键就是：

#block[
a + b = 1。
]
所以凸集在线性映射和仿射映射下的像仍然是凸的。

#figure(
  align(center)[#table(
    columns: 4,
    align: (auto,auto,auto,auto,),
    table.header([类型], [形式], [是否要求 f(0)=0], [例子],),
    table.hline(),
    [线性映射], [f(x) = Lx], [是], [f(x)=2x],
    [仿射映射], [f(x) = Lx + b], [否], [f(x)=2x+1],
  )]
  , kind: table
  )

] <linear-affine>
#block[
== 7. Lean 使用小抄
<lean-使用小抄>
=== 导入模块
<导入模块>
```
import Mathlib.Analysis.Convex.Basic
```

=== 检查核心对象
<检查核心对象>
```
#check Convex
#check convex_iff_segment_subset
#check convex_empty
#check convex_univ
#check Convex.inter
#check convex_iInter
#check convex_singleton
#check convex_segment
#check Convex.linear_image
#check Convex.linear_preimage
#check Convex.affine_image
#check Convex.affine_preimage
#check Convex.add
#check Convex.smul
#check Convex.translate
```

=== 闭区间是凸的
<闭区间是凸的>
```
import Mathlib.Analysis.Convex.Basic

example (a b : ℝ) : Convex ℝ (Set.Icc a b) := by
  exact convex_Icc a b
```

=== 两个凸集的交仍然凸
<两个凸集的交仍然凸>
```
import Mathlib.Analysis.Convex.Basic

example {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s t : Set E}
    (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ (s ∩ t) := by
  exact hs.inter ht
```

=== 凸集对凸组合封闭
<凸集对凸组合封闭>
```
import Mathlib.Analysis.Convex.Basic

example {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ s := by
  exact hs hx hy ha hb hab
```

=== 与凸包相关的模块
<与凸包相关的模块>
`Basic` 主要讲凸集本身。如果要用凸包，一般看：

```
import Mathlib.Analysis.Convex.Hull
```

其中核心对象通常是：

```
convexHull 𝕜 s
```

#block[
#strong[区分：] \ `Mathlib.Analysis.Convex.Basic`：凸集基础。 \
`Mathlib.Analysis.Convex.Hull`：凸包。 \
`Mathlib.Analysis.Convex.Function`：凸函数。
]
] <lean>
#block[
== 8. 总结图
<总结图>
#block[
Convex 𝕜 s \ ↓ \ s 对 𝕜 中的凸组合封闭
]
#block[
非负线性组合 \ = 系数非负 \ ↓ \ 锥 / 非负测度 / 非负矩阵
]
#block[
凸组合 \ = 非负线性组合 + 系数和为 1 \ ↓ \ 凸集 / 凸包 / 概率测度
]
#block[
线性映射：f(x) = Lx，保持原点 \ 仿射映射：f(x) = Lx + b，允许平移 \
二者都保持凸性
]
]
本笔记基于本次对话整理，可直接保存为 HTML 文件本地复习。

]
