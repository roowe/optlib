#block[
#block[
学习笔记 · Mathlib / Lean
= Mathlib 有限维拓扑向量空间理论完全指南
<mathlib-有限维拓扑向量空间理论完全指南>
这份笔记整理了 `Mathlib.Topology.Algebra.Module.FiniteDimension`
的核心思想：在完备非平凡赋范域上，有限维 Hausdorff
拓扑向量空间的拓扑由线性结构唯一决定，因此线性映射连续性、闭子空间、范数等价等结论可以自动获得。

#block[
有限维 Hausdorff TVS 完备非平凡赋范域 自动连续性 Lean 证明模式
]
]
#block[
== 一、文件概览与核心定位
<一文件概览与核心定位>
#block[
#block[
=== 1.1 基本信息
<基本信息>
#strong[文件路径：]`Mathlib/Topology/Algebra/Module/FiniteDimension.lean`

#strong[核心定位：]连接纯代数有限维线性代数与拓扑分析的关键枢纽。

]
#block[
=== 核心依赖
<核心依赖>
- `LinearAlgebra.FiniteDimensional.Lemmas`：纯代数有限维理论
- `Topology.Algebra.Module.ModuleTopology`：拓扑模基本结构
- `Analysis.Normed.Module.Basic`：赋范模基础

]
]
=== 1.2 标准研究设定
<标准研究设定>
#block[
统一前提
`𝕜` 是完备、非平凡赋范域；`E` 是 `𝕜` 上的 Hausdorff 拓扑向量空间；并且
`[FiniteDimensional 𝕜 E]`。

]
] <overview>
#block[
== 二、核心概念详解
<二核心概念详解>
=== 2.1 拓扑向量空间（TVS）
<拓扑向量空间tvs>
#strong[定义：]域 `𝕜` 上的向量空间
`E`，同时装备拓扑结构，并满足加法和数乘连续。

#block[
E × E → E, ~ (x, y) ↦ x + y
]
#block[
𝕜 × E → E, ~ (λ, x) ↦ λx
]
#block[
直觉
TVS
的本质是：线性运算与拓扑结构兼容。也就是说，"点之间的邻近性"在加法和数乘下不会被破坏。

]
=== 2.2 Hausdorff 分离性
<hausdorff-分离性>
#strong[公理：]对任意两个不同点 `x ≠ y`，存在互不相交的开邻域
`U, V`，使得 `x ∈ U` 且 `y ∈ V`。

#strong[TVS 中的等价条件：]原点所有邻域的交集只有原点本身。

#block[
⋂#sub[U ∋ 0，U 为开邻域] U = {0}
]
#block[
#block[
==== 核心推论
<核心推论>
- 极限唯一。
- 单点集 `{x}` 是闭集。
- 不同点在拓扑上可区分。

]
#block[
==== 关键洞见
<关键洞见>
Hausdorff 公理是拓扑意义上的"正定性"。非 Hausdorff
空间的问题在于可能存在拓扑不可区分的点，导致极限不唯一。

]
]
=== 2.3 完备非平凡赋范域
<完备非平凡赋范域>
==== 2.3.1 赋范域
<赋范域>
域 `𝕜` 上装备范数函数 `‖·‖ : 𝕜 → ℝ≥0`，满足：

+ 正定性：`‖a‖ = 0 ↔ a = 0`。
+ 齐次性：`‖ab‖ = ‖a‖ ‖b‖`。
+ 三角不等式：`‖a + b‖ ≤ ‖a‖ + ‖b‖`。

==== 2.3.2 非平凡性
<非平凡性>
非平凡性用于排除平凡范数，即排除所有非零元素范数都等于 1
的情况。它保证域中存在真正有分析意义的收敛结构。

==== 2.3.3 完备性
<完备性>
完备性要求域中所有柯西列都收敛到域内的点。

#block[
为什么完备性重要？
如果域不完备，例如 `ℚ`，有限维 Hausdorff TVS
的拓扑可能不唯一，线性映射也可能不连续，许多有限维核心定理都会失效。

]
#block[
反例提示
`ℚ` 上的二维空间 `E = ℚ(√2)` 可以装备两种不同的 Hausdorff TVS
拓扑：一种来自 `ℚ × ℚ` 的乘积拓扑，另一种来自作为 `ℝ` 子集的子空间拓扑。

]
] <concepts>
#block[
== 三、核心定理：拓扑唯一性
<三核心定理拓扑唯一性>
=== 3.1 定理陈述
<定理陈述>
#block[
核心定理
完备非平凡赋范域上的有限维 Hausdorff TVS，拓扑是唯一的。

换句话说，无论用什么基、什么方式装备拓扑，只要满足 Hausdorff TVS
公理，其拓扑必然等于标准乘积拓扑。

]
=== 3.2 证明直觉
<证明直觉>
+ 任意选择一组基，得到坐标映射，把 `E` 映射到 `𝕜ⁿ`。
+ 坐标映射是线性映射，在有限维 Hausdorff TVS 上自动连续。
+ 坐标映射的逆也是线性映射，因此也自动连续。
+ 所以坐标映射是同胚，所有基诱导的拓扑相同。

=== 3.3 本质含义
<本质含义>
在完备域上，有限维向量空间的线性结构已经完全决定了它的拓扑结构。我们不需要额外选择范数或基；只要知道维数，拓扑就唯一确定。

] <uniqueness>
#block[
== 四、核心结论大全
<四核心结论大全>
=== 4.1 最常用定理
<最常用定理>
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([定理], [Lean 代码], [核心结论],),
    table.hline(),
    [线性映射自动连续], [`LinearMap.continuous_of_finiteDimensional f`], [从有限维
    Hausdorff TVS 到任意 TVS 的线性映射必然连续。],
    [有限维子空间必闭], [`Submodule.closed_of_finiteDimensional S`], [有限维线性子空间是闭集。],
    [连续线性同构判据], [`FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq`], [两个有限维
    Hausdorff TVS 连续线性同构当且仅当维数相等。],
    [所有范数等价], [`FiniteDimensional.norm_equivalent`], [有限维空间上任意两个范数彼此等价，诱导同一拓扑。],
    [线性泛函连续判据], [`LinearMap.continuous_iff_isClosed_ker f`], [线性泛函连续当且仅当其核是闭集。],
  )]
  , kind: table
  )

=== 4.2 基础拓扑性质
<基础拓扑性质>
#block[
#block[
==== 极限与同胚
<极限与同胚>
- 极限唯一。
- 平移映射 `x ↦ x + a` 是同胚。
- 非零数乘映射是同胚。

]
#block[
==== 开映射性质
<开映射性质>
- 加法是开映射。
- 开集的平移仍是开集。

]
]
=== 4.3 子空间与商空间
<子空间与商空间>
- 子空间继承 Hausdorff 性。
- 商空间 `E/S` 是 Hausdorff 的当且仅当 `S` 是闭集。
- 有限维子空间的商空间自动是 Hausdorff 的。

=== 4.4 赋范空间额外结论
<赋范空间额外结论>
- Heine-Borel 定理：有限维赋范空间中，紧集等价于有界闭集。
- 有限维赋范空间自动完备，因此是 Banach 空间。
- Riesz 引理刻画有限维与无限维空间的本质区别。

] <conclusions>
#block[
== 五、拓扑的本质
<五拓扑的本质>
=== 5.1 拓扑不是什么
<拓扑不是什么>
- 拓扑不是距离；距离只是诱导拓扑的一种方式。
- 拓扑不是形状；它不直接关心大小、角度、长度。
- 拓扑也不只是"开集的集合"；开集只是描述拓扑的工具。

=== 5.2 拓扑的本质
<拓扑的本质>
#block[
核心理解
拓扑是给集合中的点定义"邻近性"的数学结构。

]
#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([拓扑概念], [围绕"邻近性"的解释],),
    table.hline(),
    [邻域], [与某点足够近的所有点的集合。],
    [连续], [保持邻近性的映射。],
    [极限], [序列最终与某点任意邻近。],
    [Hausdorff 性], [不同点不可能任意邻近。],
  )]
  , kind: table
  )

=== 5.3 有限维与无限维的根本区别
<有限维与无限维的根本区别>
#block[
#block[
==== 有限维
<有限维>
线性结构完全决定邻近性结构，因此拓扑唯一。

]
#block[
==== 无限维
<无限维>
线性结构不足以决定邻近性结构，可以有无数种不同的拓扑。

]
]
] <essence>
#block[
== 六、典型使用场景与证明模式
<六典型使用场景与证明模式>
=== 6.1 最高频使用场景
<最高频使用场景>
==== 模式 1：一键证明线性映射连续
<模式-1一键证明线性映射连续>
```
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- ℝ³ 到 ℝ² 的任意线性映射自动连续
example (f : ℝ³ →ₗ[ℝ] ℝ²) : Continuous f :=
  LinearMap.continuous_of_finiteDimensional f

-- 矩阵对应的线性算子自动连续
example (A : Matrix (Fin 3) (Fin 2) ℝ) :
    Continuous (fun x : ℝ³ => A *ᵥ x) :=
  LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin A)
```

==== 模式 2：证明有限维子空间是闭集
<模式-2证明有限维子空间是闭集>
```
-- ℝ⁵ 中任何 2 维子空间都是闭集
example (S : Submodule ℝ ℝ⁵) [FiniteDimensional ℝ S] :
    IsClosed (S : Set ℝ⁵) :=
  Submodule.closed_of_finiteDimensional S

-- 有限秩线性映射的核是闭集
example (f : ℝ⁴ →ₗ[ℝ] ℝ³) :
    IsClosed (f.ker : Set ℝ⁴) :=
  Submodule.closed_of_finiteDimensional f.ker
```

==== 模式 3：证明商空间是 Hausdorff 的
<模式-3证明商空间是-hausdorff-的>
```
example (S : Submodule ℝ ℝ⁴) [FiniteDimensional ℝ S] :
    Hausdorff (ℝ⁴ ⧸ S) := by
  have h1 : IsClosed (S : Set ℝ⁴) :=
    Submodule.closed_of_finiteDimensional S
  exact QuotientModule.hausdorff_iff_submodule_isClosed.mpr h1
```

=== 6.2 核心应用领域
<核心应用领域>
#block[
#block[
==== 多变量微积分
<多变量微积分>
导数是线性映射，自动连续；用于隐函数定理和反函数定理。

]
#block[
==== 微分几何
<微分几何>
切空间是有限维 Hausdorff TVS，切映射自动连续。

]
#block[
==== 泛函分析
<泛函分析>
有限维 Banach 空间理论、紧算子理论。

]
#block[
==== 数值分析
<数值分析>
范数等价性保证误差分析不依赖范数选择。

]
#block[
==== 代数拓扑与表示论
<代数拓扑与表示论>
有限维表示的连续性，上同调群的拓扑性质。

]
]
=== 6.3 Mathlib 内部依赖链
<mathlib-内部依赖链>
```dependency-tree
Mathlib.Topology.Algebra.Module.FiniteDimension
├─ Mathlib.Analysis.Normed.Module.FiniteDimension
│  └─ Mathlib.Analysis.Normed.Operator.Basic
│     └─ Mathlib.Analysis.Calculus.FDeriv.Basic
│        └─ Mathlib.DifferentialGeometry.Manifold.Basic
├─ Mathlib.Topology.Algebra.Module.Dual
├─ Mathlib.Topology.Algebra.Module.Quotient
└─ Mathlib.LinearAlgebra.Matrix.FiniteDimensional
```

] <patterns>
#block[
== 七、快速参考表
<七快速参考表>
#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([条件组合], [自动成立的结论],),
    table.hline(),
    [有限维 + Hausdorff TVS], [所有线性映射自动连续。],
    [有限维 + Hausdorff TVS], [有限维子空间必闭。],
    [有限维 + Hausdorff TVS], [同构当且仅当维数相等。],
    [有限维 + 赋范空间], [所有范数等价。],
    [有限维 + 赋范空间], [紧集 ⇔ 有界闭集。],
    [任意 Hausdorff TVS], [商空间 Hausdorff ⇔ 子空间闭。],
    [任意 Hausdorff TVS], [线性泛函连续 ⇔ 核闭。],
  )]
  , kind: table
  )

] <reference>
#block[
== 八、总结
<八总结>
`Mathlib.Topology.Algebra.Module.FiniteDimension`
模块的核心价值在于：它将纯代数的有限维线性代数结论无缝升级到了拓扑分析层面。

#block[
一句话总结
在完备非平凡赋范域上，有限维 Hausdorff TVS
的拓扑是唯一的；因此我们可以放心地在有限维空间上进行分析学研究，而不必担心拓扑选择造成歧义。

]
只要证明涉及"有限维向量空间 + 连续性 / 拓扑 /
极限"的组合，这个模块通常都能帮助你省去大量繁琐的连续性证明，把注意力集中在问题的核心逻辑上。

] <summary>
] <top>
