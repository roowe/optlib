== 目录
<目录>
- #link(<inner-product-basic>)[1. InnerProductSpace.Basic]
- #link(<inner-product-concept>)[2. 什么是内积]
- #link(<basis-defs>)[3. Basis.Defs]
- #link(<basis-basic>)[4. Basis.Basic]
- #link(<comparison>)[5. 导入文件对比]

#block[
== 总览
<总览>
#block[
#block[
=== `InnerProductSpace.Basic`
<innerproductspace.basic>
提供内积空间的基本
API：内积线性规则、范数关系、Cauchy--Schwarz、不等式与极化恒等式等。

]
#block[
=== 内积
<内积>
内积是把两个向量变成一个数的运算，用来描述长度、夹角与正交。

]
#block[
=== `Basis.Defs`
<basis.defs>
定义 `Basis ι R M`，即由指标类型 `ι` 索引的 `R`-模 `M` 的一组基。

]
#block[
=== `Basis.Basic`
<basis.basic>
在 `Basis.Defs` 之上补充线性无关、张成、构造基等常用定理。

]
]
] <overview>
#block[
== 1. `import Mathlib.Analysis.InnerProductSpace.Basic`
<import-mathlib.analysis.innerproductspace.basic>
这个导入用于加载实数或复数内积空间的基础性质。它适合用于证明与内积、范数、正交、Cauchy--Schwarz
不等式、平行四边形恒等式等有关的命题。

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
```

=== 常见对象与定理
<常见对象与定理>
```lean
#check inner_conj_symm
#check real_inner_comm
#check inner_add_left
#check inner_add_right
#check inner_smul_left
#check inner_smul_right
#check inner_self_eq_zero
#check inner_self_eq_norm_sq
#check norm_inner_le_norm
#check parallelogram_law
#check inner_eq_sum_norm_sq_div_four
#check norm_inner_eq_norm_iff
```

=== Mathlib 中的约定
<mathlib-中的约定>
在 Mathlib 中，内积对第一个变量是共轭线性的，对第二个变量是线性的。

#block[
inner 𝕜 (r • x) y = star r \* inner 𝕜 x y \ inner 𝕜 x (r • y) = r \*
inner 𝕜 x y
]
=== 典型用法
<典型用法>
```lean
import Mathlib.Analysis.InnerProductSpace.Basic

variable {𝕜 E : Type*}
variable [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

example (x y z : E) :
    inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z := by
  exact inner_add_left x y z

example (x y : E) :
    ‖inner 𝕜 x y‖ ≤ ‖x‖ * ‖y‖ := by
  exact norm_inner_le_norm x y
```

#block[
#strong[使用场景：]只要证明里出现
`inner 𝕜 x y`、`⟪x, y⟫_𝕜`、范数平方、正交性或
Cauchy--Schwarz，通常都可以从这个文件开始。
]
] <inner-product-basic>
#block[
== 2. 什么是内积
<什么是内积>
内积可以理解为"带有角度信息的乘法"。它把两个向量变成一个数，用来描述两个向量之间的长度、夹角和正交关系。

=== 实向量空间中的点积
<实向量空间中的点积>
#block[
x = (x₁, x₂, \..., xₙ) \ y = (y₁, y₂, \..., yₙ) \ \ ⟪x, y⟫ = x₁y₁ + x₂y₂
\+ \... + xₙyₙ
]
例如：

#block[
x = (1, 2, 3), y = (4, 5, 6) \ ⟪x, y⟫ = 1·4 + 2·5 + 3·6 = 32
]
=== 内积的三个核心用途
<内积的三个核心用途>
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([用途], [公式], [解释],),
    table.hline(),
    [定义长度], [`‖x‖ = sqrt(⟪x, x⟫)`], [向量与自身的内积给出长度的平方。],
    [定义夹角], [`⟪x, y⟫ = ‖x‖ ‖y‖ cos θ`], [内积越大，两个向量方向越接近。],
    [定义正交], [`⟪x, y⟫ = 0`], [表示两个向量垂直。],
  )]
  , kind: table
  )

=== 实内积的基本性质
<实内积的基本性质>
```
⟪x, x⟫ ≥ 0
⟪x, x⟫ = 0 当且仅当 x = 0
⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
⟪a x, y⟫ = a ⟪x, y⟫
⟪x, y⟫ = ⟪y, x⟫
```

=== 复内积中的共轭
<复内积中的共轭>
如果是复向量空间，内积满足共轭对称性：

```
⟪x, y⟫ = conjugate(⟪y, x⟫)
```

在 Lean / Mathlib 中，常用写法是：

```lean
inner 𝕜 x y
⟪x, y⟫_𝕜
```

] <inner-product-concept>
#block[
== 3. `import Mathlib.LinearAlgebra.Basis.Defs`
<import-mathlib.linearalgebra.basis.defs>
`Basis.Defs` 是基的定义层文件。它提供 `Basis ι R M`
这个核心类型，以及坐标表示、重编号、映射等基础 API。

```lean
import Mathlib.LinearAlgebra.Basis.Defs
```

=== 核心类型
<核心类型>
```lean
Basis ι R M
```

含义是：`M` 作为 `R`-模的一组由 `ι` 索引的基。

内部上，它可以理解为一个线性等价：

```lean
M ≃ₗ[R] ι →₀ R
```

也就是说，每个向量都唯一对应一组有限支撑的坐标。

=== 典型模板
<典型模板>
```lean
import Mathlib.LinearAlgebra.Basis.Defs

variable {ι R M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)
variable (i : ι)
variable (x : M)

#check b i        -- 第 i 个基向量
#check b.repr     -- 把向量写成坐标的线性等价
#check b.repr x   -- x 在基 b 下的坐标，类型是 ι →₀ R
#check b.coord i  -- 第 i 个坐标函数
```

=== 重要概念：`b.repr`
<重要概念b.repr>
如果 `x : M`，那么：

```lean
b.repr x : ι →₀ R
```

表示 `x` 在基 `b` 下的坐标。反过来，`b.repr.symm` 会把坐标还原成向量。

=== 常见定理
<常见定理>
```lean
#check Basis.repr_self
#check Basis.repr_self_apply
#check Basis.repr_symm_single
#check Basis.linearCombination_repr
#check Basis.repr_linearCombination
#check Basis.ext
#check Basis.ext_elem
#check Basis.reindex
#check Basis.map
#check Basis.constr
#check Basis.coord
```

#figure(
  align(center)[#table(
    columns: 2,
    align: (auto,auto,),
    table.header([定理], [直观含义],),
    table.hline(),
    [`Basis.repr_self`], [第 `i` 个基向量的坐标是
    `Finsupp.single i 1`。],
    [`Basis.linearCombination_repr`], [先取坐标，再按基线性组合回来，得到原向量。],
    [`Basis.ext`], [两个线性映射如果在所有基向量上相等，那么它们整体相等。],
  )]
  , kind: table
  )

#block[
#strong[注意：]`Basis.Defs`
偏向定义层。如果需要"基向量线性无关""基张成整个空间""由线性无关且张成构造基"等结果，通常应导入
`Basis.Basic`。
]
] <basis-defs>
#block[
== 4. `import Mathlib.LinearAlgebra.Basis.Basic`
<import-mathlib.linearalgebra.basis.basic>
`Basis.Basic` 是 `Basis.Defs` 的升级版：它不只是定义
`Basis`，还证明基与"线性无关 + 张成全空间"的等价关系。

```lean
import Mathlib.LinearAlgebra.Basis.Basic
```

=== 它导入了什么
<它导入了什么>
```lean
Mathlib.LinearAlgebra.Basis.Defs
Mathlib.LinearAlgebra.LinearIndependent.Basic
Mathlib.LinearAlgebra.Span.Basic
```

=== 核心结果
<核心结果>
```lean
#check Basis.linearIndependent
#check Basis.span_eq
#check Basis.mk
```

#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([结果], [含义], [Lean 形式],),
    table.hline(),
    [`Basis.linearIndependent`], [一组基向量一定线性无关。], [`LinearIndependent R b`],
    [`Basis.span_eq`], [一组基向量张成整个空间。], [`Submodule.span R (Set.range b) = ⊤`],
    [`Basis.mk`], [线性无关且张成全空间的向量族可以构造为基。], [`Basis.mk hli hsp`],
  )]
  , kind: table
  )

=== 典型用法
<典型用法-1>
```lean
import Mathlib.LinearAlgebra.Basis.Basic

variable {ι R M : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

example : LinearIndependent R b := by
  exact b.linearIndependent

example : Submodule.span R (Set.range b) = ⊤ := by
  exact b.span_eq
```

=== 由线性无关和张成构造基
<由线性无关和张成构造基>
```lean
variable (v : ι → M)
variable (hli : LinearIndependent R v)
variable (hsp : ⊤ ≤ Submodule.span R (Set.range v))

noncomputable def myBasis : Basis ι R M :=
  Basis.mk hli hsp
```

=== 其他常用辅助结论
<其他常用辅助结论>
```lean
#check Basis.mem_span
#check Basis.mem_span_image
#check Basis.repr_support_subset_of_mem_span
#check Basis.ne_zero
#check Basis.span
#check Basis.maximal
#check Basis.singleton
#check Basis.empty
```

#block[
#strong[特别常用：]`Basis.span hli` 表示如果 `v : ι → M`
线性无关，那么它可以作为其自身张成子模的基。
]
] <basis-basic>
#block[
== 5. 导入文件对比
<导入文件对比>
#figure(
  align(center)[#table(
    columns: 3,
    align: (auto,auto,auto,),
    table.header([导入文件], [主要作用], [适合场景],),
    table.hline(),
    [`Mathlib.Analysis.InnerProductSpace.Basic`], [内积空间的基本性质与常用定理。], [证明内积、范数、正交、Cauchy--Schwarz、平行四边形恒等式等。],
    [`Mathlib.LinearAlgebra.Basis.Defs`], [定义
    `Basis`，提供坐标表示与基础 API。], [只需要使用基的定义、坐标
    `b.repr`、基向量 `b i` 时。],
    [`Mathlib.LinearAlgebra.Basis.Basic`], [补充线性无关、张成、构造基等常用结论。], [需要证明"基线性无关""基张成全空间"或从线性无关和张成构造基时。],
  )]
  , kind: table
  )

=== 推荐记忆
<推荐记忆>
```
InnerProductSpace.Basic：处理内积与范数。
Basis.Defs：给出基的定义和坐标表示。
Basis.Basic：给出基的主要性质和构造方法。
```

] <comparison>
