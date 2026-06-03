#block[
#block[
Mathlib / Analysis / Normed / Lp
]
= PiLp 学习笔记
<pilp-学习笔记>
这份笔记介绍 `import Mathlib.Analysis.Normed.Lp.PiLp`：
它为有限坐标族提供 #strong[L#super[p]
风格的范数、距离、拓扑和常用定理]。

```
import Mathlib.Analysis.Normed.Lp.PiLp
```

]
#block[
== 1. 模块概览
<模块概览>
这个 import 引入的是 mathlib 中关于 #strong[有限乘积上的 L#super[p] 距离
\/ 范数结构] 的内容。

核心对象是：

```
PiLp p α
```

#block[
可以把 `PiLp p α` 理解成：有限多个坐标组成的对象，但 Lean 把它当成带有
L#super[p] 范数和 L#super[p] 距离的空间。
]
] <intro>
#block[
== 2. Pi 是什么？
<pi-是什么>
`Pi` 不是英文缩写，而是希腊字母 #strong[Π]，读作
pi。它在数学中表示"乘积"：

#block[
∏#sub[i : ι] α#sub[i]
]
在类型论中，#strong[Pi type] 指的是依赖乘积类型，也叫依赖函数类型。

```
(i : ι) → α i
```

可以理解成：

#block[
Π i : ι, α#sub[i]
]
意思是：对每个 `i : ι`，给出一个属于 `α i` 的值。

如果 `α i` 不依赖于 `i`，那么：

```
(i : ι) → α
```

就退化成普通函数类型：

```
ι → α
```

例如：

```
Fin 3 → ℝ
```

可以看成三维实向量：

#block[
\(x#sub[0], x#sub[1], x#sub[2])
]
] <pi>
#block[
== 3. 有限类型是什么意思？
<有限类型是什么意思>
"若 `ι` 是有限类型"指的是：`ι` 这个指标类型里只有有限多个元素。

Lean 中通常写作：

```
[Fintype ι]
```

意思是 Lean 知道 `ι` 可以被枚举完。

例如：

```
Fin 3
```

是有限类型，里面有三个元素：

```
0, 1, 2
```

因此：

```
Fin 3 → ℝ
```

可以理解成三维向量。

#block[
在 `PiLp p α` 中，`ι` 是坐标编号类型。若有
`[Fintype ι]`，就表示只有有限多个坐标，因此可以使用有限求和。
]
```
∑ i, ‖x.ofLp i‖
```

] <fintype>
#block[
== 4. `PiLp p α` 是什么？
<pilp-p-α-是什么>
普通的 Pi 类型：

```
(i : ι) → α i
```

只是"一组坐标"。

而：

```
PiLp p α
```

是同样的一组坐标，但 Lean 给它配上了 L#super[p] 风格的范数和距离。

#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([对象], [理解],),
    table.hline(),
    [`(i : ι) → α i`], [普通坐标族],
    [`PiLp p α`], [带有 L#super[p] 范数 / 距离结构的坐标族],
  )]
  , kind: table
  )

=== 常用转换
<常用转换>
```
WithLp.toLp p f  -- 把普通函数放进 PiLp
x.ofLp          -- 把 PiLp 元素取回普通函数
x.ofLp i        -- 取第 i 个坐标
```

] <pilp>
#block[
== 5. 有限乘积上的 L#super[p] 范数
<有限乘积上的-lp-范数>
设：

#block[
x = (x#sub[i])#sub[i ∈ ι]
]
当 1 ≤ p \< ∞ 时：

#block[
‖x‖#sub[p] = (∑#sub[i] ‖x#sub[i]‖#super[p])#super[1/p]
]
#block[
#block[
=== L#super[1] 范数
<l1-范数>
#block[
‖x‖#sub[1] = ∑#sub[i] ‖x#sub[i]‖
]
所有坐标大小的总和。

]
#block[
=== L#super[2] 范数
<l2-范数>
#block[
‖x‖#sub[2] = √(∑#sub[i] ‖x#sub[i]‖#super[2])
]
欧几里得风格的范数。

]
#block[
=== L#super[∞] 范数
<l-范数>
#block[
‖x‖#sub[∞] = max#sub[i] ‖x#sub[i]‖
]
最大坐标范数。

]
#block[
=== L#super[0] "范数"
<l0-范数>
#block[
‖x‖#sub[0] = \#{ i | x#sub[i] ≠ 0 }
]
非零坐标的个数。严格说它不是范数。

]
]
] <norm>
#block[
== 6. L#super[p] 距离
<lp-距离>
若：

#block[
x = (x#sub[i])#sub[i ∈ ι], ~ y = (y#sub[i])#sub[i ∈ ι]
]
则：

#block[
d#sub[p]\(x,y) = (∑#sub[i] d(x#sub[i], y#sub[i])#super[p])#super[1/p]
]
在实数向量中，就是：

#block[
d#sub[p]\(x,y) = (∑#sub[i] |x#sub[i] - y#sub[i]|#super[p])#super[1/p]
]
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([距离], [公式], [直觉],),
    table.hline(),
    [L#super[1]], [d#sub[1]\(x,y) = ∑#sub[i]
    d(x#sub[i],y#sub[i])], [曼哈顿距离],
    [L#super[2]], [d#sub[2]\(x,y) = √(∑#sub[i]
    d(x#sub[i],y#sub[i])#super[2])], [欧几里得距离],
    [L#super[∞]], [d#sub[∞]\(x,y) = max#sub[i]
    d(x#sub[i],y#sub[i])], [最大坐标距离],
    [L#super[0]], [d#sub[0]\(x,y) = \#{ i | x#sub[i] ≠ y#sub[i]
    }], [不同坐标的个数],
  )]
  , kind: table
  )

] <dist>
#block[
== 7. L#super[0] 与齐次性
<l0-与齐次性>
L#super[0] 范数和 L#super[0] 距离要区分：

```
L0 范数：非零坐标的个数
L0 距离：两个向量不同坐标的个数
```

因为：

#block[
‖x‖#sub[0] = d#sub[0]\(x,0)
]
#block[
L#super[0] 严格来说不是范数，因为它不满足范数的齐次性。
]
范数的齐次性要求：

#block[
‖a x‖ = |a| ‖x‖
]
但例如：

#block[
x = (1,0,2), ~ ‖x‖#sub[0] = 2
]
乘以 3 后：

#block[
3x = (3,0,6), ~ ‖3x‖#sub[0] = 2
]
而齐次性会要求：

#block[
‖3x‖#sub[0] = 3‖x‖#sub[0] = 6
]
这显然不成立。所以 L#super[0] 常用于衡量稀疏性，但不是严格意义的范数。

] <l0>
#block[
== 8. `PiLp` 中常用的定理
<pilp-中常用的定理>
公共环境：

```
import Mathlib.Analysis.Normed.Lp.PiLp

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {β : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (β i)]
```

常用结论包括：

```
PiLp.norm_eq_of_L1
PiLp.dist_eq_of_L1
PiLp.norm_eq_of_L2
PiLp.norm_sq_eq_of_L2
PiLp.dist_sq_eq_of_L2
PiLp.norm_apply_le
PiLp.dist_apply_le
PiLp.single
PiLp.norm_single
PiLp.ext
PiLp.continuous_apply
```

] <lemmas>
#block[
== 9. Lean 例子
<lean-例子>
=== 展开 L#super[1] 范数
<展开-l1-范数>
```
example (x : PiLp 1 β) :
    ‖x‖ = ∑ i, ‖x.ofLp i‖ :=
  PiLp.norm_eq_of_L1 x
```

#block[
‖x‖#sub[1] = ∑#sub[i] ‖x#sub[i]‖
]
=== 展开 L#super[1] 距离
<展开-l1-距离>
```
example (x y : PiLp 1 β) :
    dist x y = ∑ i, dist (x.ofLp i) (y.ofLp i) :=
  PiLp.dist_eq_of_L1 x y
```

#block[
d#sub[1]\(x,y) = ∑#sub[i] d(x#sub[i], y#sub[i])
]
=== 展开 L#super[2] 范数平方
<展开-l2-范数平方>
```
example (x : PiLp 2 β) :
    ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 β x
```

#block[
‖x‖#sub[2]#super[2] = ∑#sub[i] ‖x#sub[i]‖#super[2]
]
=== 展开 L#super[2] 距离平方
<展开-l2-距离平方>
```
example (x y : PiLp 2 β) :
    dist x y ^ 2 = ∑ i, dist (x.ofLp i) (y.ofLp i) ^ 2 :=
  PiLp.dist_sq_eq_of_L2 x y
```

#block[
d#sub[2]\(x,y)#super[2] = ∑#sub[i] d(x#sub[i], y#sub[i])#super[2]
]
=== 坐标范数小于整体范数
<坐标范数小于整体范数>
```
example {p : ENNReal} [Fact (1 ≤ p)] (x : PiLp p β) (i : ι) :
    ‖x.ofLp i‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le x i
```

#block[
‖x#sub[i]‖ ≤ ‖x‖#sub[p]
]
本质原因是：非负求和中，单项不超过总和。

#block[
‖x#sub[i]‖#super[p] ≤ ∑#sub[j] ‖x#sub[j]‖#super[p]
]
=== 坐标距离小于整体距离
<坐标距离小于整体距离>
```
example {p : ENNReal} [Fact (1 ≤ p)] (x y : PiLp p β) (i : ι) :
    dist (x.ofLp i) (y.ofLp i) ≤ dist x y :=
  PiLp.dist_apply_le x y i
```

#block[
d(x#sub[i],y#sub[i]) ≤ d#sub[p]\(x,y)
]
这说明取某个坐标的投影映射是 1-Lipschitz 的。

=== 构造单坐标向量
<构造单坐标向量>
```
variable [DecidableEq ι]

example (p : ENNReal) (i : ι) (a : β i) :
    (PiLp.single p i a).ofLp i = a :=
  PiLp.single_eq_same p i a
```

`PiLp.single p i a` 表示第 `i` 个坐标是 `a`，其他坐标都是 `0`。

=== 其他坐标为零
<其他坐标为零>
```
example (p : ENNReal) {i j : ι} (h : j ≠ i) (a : β i) :
    (PiLp.single p i a).ofLp j = 0 :=
  PiLp.single_eq_of_ne p h a
```

=== 单坐标向量的范数
<单坐标向量的范数>
```
example {p : ENNReal} [Fact (1 ≤ p)] (i : ι) (a : β i) :
    ‖PiLp.single p i a‖ = ‖a‖ :=
  PiLp.norm_single p β i a
```

#block[
‖(0, …, a, …, 0)‖#sub[p] = ‖a‖
]
=== 用 `PiLp.ext` 逐坐标证明相等
<用-pilp.ext-逐坐标证明相等>
```
example {p : ENNReal} {x y : PiLp p β}
    (h : ∀ i, x.ofLp i = y.ofLp i) :
    x = y :=
  PiLp.ext h
```

#block[
\(∀ i, x#sub[i] = y#sub[i]) ⇒ x = y
]
] <examples>
#block[
== 10. 取坐标是连续函数
<取坐标是连续函数>
```
example (p : ENNReal) (i : ι) :
    Continuous fun x : PiLp p β => x.ofLp i :=
  PiLp.continuous_apply p β i
```

数学含义是：

#block[
x ↦ x#sub[i]
]
是连续函数。

#block[
这最重要的用途是：整体收敛可以推出逐坐标收敛。
]
#block[
x#sub[n] → x ~ ⇒ ~ x#sub[n]\(i) → x(i)
]
在 Lean 中，如果有：

```
h : Tendsto u l (𝓝 x)
```

其中：

```
u : γ → PiLp p β
x : PiLp p β
```

那么可以得到第 `i` 个坐标也收敛：

```
Tendsto (fun n => (u n).ofLp i) l (𝓝 (x.ofLp i))
```

思路是使用：

```
(PiLp.continuous_apply p β i).tendsto x
```

=== 和距离估计的关系
<和距离估计的关系>
前面的定理：

```
PiLp.dist_apply_le
```

说的是：

#block[
d(x#sub[i],y#sub[i]) ≤ d#sub[p]\(x,y)
]
这说明坐标投影是 1-Lipschitz 的，而 1-Lipschitz 函数一定连续。

#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([定理], [含义],),
    table.hline(),
    [`PiLp.dist_apply_le`], [更强的定量估计],
    [`PiLp.continuous_apply`], [由估计导出的拓扑结论],
  )]
  , kind: table
  )

] <continuous>
#block[
== 11. `PiLp` 和其他类似对象的区别
<pilp-和其他类似对象的区别>
#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([对象], [用途],),
    table.hline(),
    [`PiLp p α`], [有限乘积上的 L#super[p] 结构],
    [`(i : ι) → α i`], [普通坐标族，默认不一定是想要的 L#super[p]
    范数结构],
    [`lp`], [可能无限指标集上的 l#super[p]
    空间，需要考虑可和性、收敛性],
    [`MeasureTheory.Lp`], [测度空间上的 L#super[p]
    函数空间，涉及几乎处处相等等测度论内容],
  )]
  , kind: table
  )

] <compare>
#block[
== 12. 总结
<总结>
`PiLp p α` 可以理解成：

#block[
有限维向量或有限坐标族的 L#super[p] 版本。
]
普通的：

```
(i : ι) → α i
```

只是坐标族。而：

```
PiLp p α
```

是同样的数据，但配上了 L#super[p] 范数、距离和拓扑结构。

=== 最常用的直觉
<最常用的直觉>
```
L1：坐标范数求和
L2：平方和开根号
L∞：最大坐标范数
L0：非零坐标个数，但严格来说不是范数
```

=== 最常用的估计
<最常用的估计>
#block[
‖x#sub[i]‖ ≤ ‖x‖#sub[p]
]
#block[
d(x#sub[i],y#sub[i]) ≤ d#sub[p]\(x,y)
]
=== 最常用的拓扑结论
<最常用的拓扑结论>
#block[
x#sub[n] → x ⇒ x#sub[n]\(i) → x(i)
]
一句话：

#block[
整体收敛推出逐坐标收敛。
]
] <summary>
#block[
Mathlib.Analysis.Normed.Lp.PiLp 学习笔记 · HTML 展示版
]
