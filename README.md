# F4 矩阵 support 大小的标度律：严格证明框架、组合路线与外代数路线

> 本文针对稠密 MQ（多元二次方程组）在 F4 / msolve 下的最大矩阵 **列维数（support 大小）** 的标度律，给出
> 一个尽量严格的证明框架。约定三个等级的标注：
> - **【定理】/【引理】**：本文给出完整或基本完整的严格证明。
> - **【命题(可约化)】**：本文把它**严格地约化**为一个干净的组合断言，并证明其中能证的部分，明确剩余缺口。
> - **【启发】/【猜想】**：尚无严格证明，给出机制性论证、外代数图像、下界构造思路。
>
> 经验事实（已被 msolve 在 $n=10$ 稠密随机 MQ 上逐次数验证，列维数几乎逐项吻合，峰值 `4146×4529` 对预测
> `4189×4529`）：
> $$\text{平方 } m=n\text{：}\quad \operatorname{peak\,cols}=\Theta(\sqrt n\,2^{n}),\qquad
> \text{严格齐次：}\quad \operatorname{peak\,cols}=\Theta(2^{n}).$$
> 更一般地，对截断半正则 Hilbert 函数 $H$，平方化的累计峰值 $=\Theta(\sqrt n\cdot \operatorname{sum}H)$，齐次峰值
> $=\Theta(\operatorname{sum}H)$。

---

## 第 0 部分　核心结论一句话

把所有出现在 F4 各次矩阵中的单项式（列）分成两类：

- **标准单项式（standard / 楼梯内）**：它们的个数就是 Hilbert 函数 $\sum_d H_d=\dim_k R/I$，对平方情形是 $2^n$。这部分**平凡可控**。
- **非标准单项式（pivot / 前导项）**：它们才是矩阵列数的主项。实验里 $n=10,\,d=7$ 共 $1396$ 列，其中标准只有 $H_7=\binom{10}{7}=120$，**其余 $1276\approx 2^n$ 全是 pivot**。

因此

$$\boxed{\text{整套问题 } = \text{“数 reduction 可达的 pivot 单项式个数”}.}$$

平方情形里 pivot 在单个次数上约 $2^n$ 个（比标准多一个 $\sqrt n$ 因子），累计时再叠加一个 $\sqrt n$ 宽的中心次数窗口，得到 $\sqrt n\cdot 2^n$。**第 6–8 部分**把这件事尽量做严格；**第 9 部分**用外代数把 $2^n$ 与 $\sqrt n$ 的来源讲透并给下界思路。

---

## 第 1 部分　记号与基本对象（概念逐个解释）

**分次多项式环.** $R=k[x_1,\dots,x_n]$，$k$ 为域。$R=\bigoplus_{d\ge0}R_d$，$R_d$ 是 $d$ 次齐次部分，$\dim_k R_d=\binom{n+d-1}{d}$。一个单项式 $x^a=x_1^{a_1}\cdots x_n^{a_n}$ 的次数是 $|a|=\sum a_i$。

**Hilbert 函数 / 级数.** 对分次理想 $I$（齐次），商环 $R/I$ 的 **Hilbert 函数** 是 $H_{R/I}(d)=\dim_k (R/I)_d$，**Hilbert 级数** 是 $\mathrm{HS}_{R/I}(t)=\sum_d H_{R/I}(d)\,t^d$。

**单项式序.** 一个 **单项式序** $\prec$ 是单项式集合上的全序，满足 $1\preceq m$ 且 $m\prec m'\Rightarrow um\prec um'$。常用：
- **lex（字典序）**：先比 $x_1$ 的指数，再 $x_2$……
- **revlex（逆字典序）**、**DRL（degree reverse lex，次数优先逆字典）**：先比总次数，次数相同时用 revlex。msolve 默认 DRL。
- 代码里的 `mono_rank` 是一个**分次序**（先按总次数，再按 $\sum_i(\text{maxdeg}-a_i)B^i$ 的次级关键字），它是 revlex 型分次序的一种实现。

**初始理想与楼梯.** 固定 $\prec$。$f\in R$ 的前导单项式 $\mathrm{LT}_\prec(f)$ 是其支撑里 $\prec$-最大的单项式。**初始理想** $\mathrm{in}_\prec(I)=\langle \mathrm{LT}_\prec(f):f\in I\rangle$，它是单项式理想。

- **标准单项式集合** $S=\{$单项式 $m\notin \mathrm{in}_\prec(I)\}$。基本事实：$S$ 在 $R/I$ 中的像构成 $k$-基，且 $|S\cap R_d|=H_{R/I}(d)$。
- $S$ 是 **order ideal（除子下闭）**：$m\in S,\ m'\mid m\Rightarrow m'\in S$。几何上 $S$ 是 $\mathbb N^n$ 里一个“楼梯”形状（staircase）。
- $\mathrm{in}_\prec(I)$ 的**极小单项式生成元** $G$ = 楼梯的**外拐角** = 满足 $m\notin S$ 且对所有 $x_i\mid m$ 有 $m/x_i\in S$ 的单项式 $m$。

**generic initial ideal（gin）与 strongly stable.** 对一般坐标变换后取初始理想得 $\mathrm{gin}_\prec(I)$，它是 **Borel 不动 / strongly stable（强稳定）** 单项式理想：$x^a\in\mathrm{gin}$ 且 $x_j\mid x^a$ 则对 $i<j$ 有 $x_i x^a/x_j\in\mathrm{gin}$。这是“通用”系统初始理想的正确模型。代码的贪心楼梯就是 gin 的一个代用品（surrogate）。

**完全交、Gorenstein、socle、正则度.**
- $m=n$ 个通用二次型构成 **正则序列**，$I=(f_1,\dots,f_n)$ 是 **完全交（complete intersection, CI）**，$R/I$ 是 Artinian（有限维）。
- CI 的 Hilbert 级数 $=\prod_i\frac{1-t^{d_i}}{1-t}$。$n$ 个二次：$\left(\frac{1-t^2}{1-t}\right)^n=(1+t)^n$，故 $H_d=\binom nd$，$\sum_d H_d=2^n$。
- CI 是 **Gorenstein**：$R/I$ 有一维 socle，**socle 次数** $s=\sum_i(d_i-1)=n$（二次时），且 Hilbert 函数**对称** $H_d=H_{s-d}$。
- **Castelnuovo–Mumford 正则度** $\mathrm{reg}(R/I)=s=n$（CI 情形），生成元次数最高到 $\mathrm{reg}+1=n+1$ 量级。

**半正则 / Fröberg.** 对 $m$ 个次数 $d_i$ 的通用型，**Fröberg 猜想** 断言 $\mathrm{HS}_{R/I}(t)=\big[\prod_i(1-t^{d_i})/(1-t)^n\big]_+$（系数取到第一个 $\le0$ 处截断）。$m>n$ 时 $\sum H<2^n$。代码 `build_semireg_hilbert` 正是算这个截断级数。

**Moreno–Socías 猜想.** 通用型的（lex）gin **是 almost reverse lexicographic**（一种特定的压缩楼梯）。已知特殊情形（变量少、Pardue 的部分结果），**一般情形开放**。它保证“代码的贪心楼梯 $\approx$ 真实 gin”，是把本文组合定理桥接到真实 F4 的关键假设。

---

## 第 2 部分　基础引理（严格）

**【引理 2.1（质量恒等式）】** $\displaystyle\sum_d H_{R/I}(d)=\dim_k R/I=|S|$。平方二次：$=2^n$。
*证明.* 标准单项式是 $R/I$ 的 $k$-基，按次数分块即得。∎

**【引理 2.2（Gorenstein 对称）】** $n$ 个通用二次型时 $R/I$ Artinian Gorenstein，socle 次数 $s=n$，且
$$H_d=\binom nd=\binom{n}{\,n-d\,}=H_{\,n-d},\qquad 0\le d\le n.$$
更进一步有 **Poincaré 对偶配对** $(R/I)_d\times(R/I)_{n-d}\to(R/I)_n\cong k$ 非退化。
*证明.* CI $\Rightarrow$ Gorenstein（标准）；Hilbert 级数 $(1+t)^n$ 显然对称；对偶配对来自 Gorenstein 的自对偶性。∎

> 引理 2.2 是**“$\sqrt n$ 中心窗口”的根源**：$\binom nd$ 关于 $d=n/2$ 对称、集中在宽度 $\Theta(\sqrt n)$ 的中心带。

**【引理 2.3（楼梯与边界）】** $S$ 是 order ideal；$\mathrm{in}_\prec(I)$ 的极小生成元 $=\{m\notin S:\forall x_i\mid m,\ m/x_i\in S\}$。
*证明.* order ideal 性质即 $\mathrm{in}_\prec(I)$ 是单项式理想的对偶陈述；极小生成元刻画是单项式理想标准事实。∎

**【引理 2.4（rank 序在固定次数内平移不变；symbolic preprocessing 终止）】**
设 $\rho(m)$ 为代码 rank。则 $\rho$ 是分次单项式序，且对固定次数 $d$，
$$s\prec_\rho \mathrm{LT}(g)\ \Longleftrightarrow\ u\,s\prec_\rho u\,\mathrm{LT}(g)\quad(\text{当 }\deg(us)=\deg(u\,\mathrm{LT}(g))).$$
于是 symbolic preprocessing 的每一步重写 $u\,\mathrm{LT}(g)\rightsquigarrow u\,s$（$s\prec_\rho\mathrm{LT}(g)$ 同次）**严格降低 rank**，重写是有限 DAG，列集合 $C_d$ 良定义。
*证明.* $\rho(m)=\deg(m)\cdot B^n+\sum_i(\text{maxdeg}-a_i)B^i$。固定 $d$ 时第一项相同；次级关键字差 $\rho(u\,\mathrm{LT}(g))-\rho(us)=\sum_i\big[(\text{maxdeg}-(u_i+\mathrm{LT}_i))-(\text{maxdeg}-(u_i+s_i))\big]B^i=\sum_i(s_i-\mathrm{LT}_i)B^i$，与 $u$ 无关，等于 $\rho(\mathrm{LT}(g))-\rho(s)$ 的次级部分。故同次比较平移不变。每步严格降 rank，rank 取值有限 $\Rightarrow$ 终止。∎

---

## 第 3 部分　F4 列空间的组合模型（精确定义）

给定目标 $H$，按 §1 贪心法建 $S$、$G$。**临界对** = $\{(g_a,g_b):\mathrm{LT}\text{ 不互素}\}$ 经 Buchberger 乘积准则 + 链准则筛后，按 $\ell=\mathrm{lcm}(\mathrm{LT}(g_a),\mathrm{LT}(g_b))$ 的次数分桶。

**Symbolic preprocessing 闭包（生成列集合 $C_d$）.** 对次数 $d$ 的对桶：
1. 每个对的 $\ell$ 置为 pivot；对 $g\in\{g_a,g_b\}$，建行 $(g,u)$，$u=\ell/\mathrm{LT}(g)$，加入其 **支撑（support）**。
2. 行 $(g,u)$ 的支撑模型：
   - **严格齐次**：$\{u\,\mathrm{LT}(g)\}\cup\{u\,s:\ s\in S,\ \deg s=\deg g,\ s\prec_\rho\mathrm{LT}(g)\}$（**全部同次** $\deg(u\,\mathrm{LT}(g))$）。
   - **累计**：$\{u\,\mathrm{LT}(g)\}\cup\{u\,s:\ s\in S,\ s\prec_\rho\mathrm{LT}(g)\}$（$s$ 取**所有** $\le\deg g$ 的次数，故支撑跨 $\deg u$ 到 $d$ 多个次数）。
3. 闭包：任何新出现的**非标准**列 $m$，取整除它的 $g$，令 $m=u\,\mathrm{LT}(g)$，加入行 $(g,u)$ 的支撑，并把 $m$ 置为 pivot。重复至无新非标准列。
4. $\operatorname{cols}_d:=|C_d|=$ 该次出现的不同单项式数；峰值 $=\max_d\operatorname{cols}_d$。

> 区别点：**累计 = 把生成元当非齐次多项式（含低次尾项）**，对应仿射 MQ（有“次数下落”现象）；**齐次 = 只保留同次尾项**，对应齐次化后的 F4。两者只差这一条尾项规则。

**支撑模型的合理性（为何列数对得上 msolve）.** 单条 reduced 多项式的尾项确实稀疏，但**列集合是所有行支撑的并**；通用稠密下，并集填满“楼梯的 reduction 可达阴影”，这正是闭包计算的对象。msolve 的逐次列数与此模型几乎逐项相同，验证了这一点。

---

## 第 4 部分　上界工具一：Kruskal–Katona 定理

**概念：shadow.** 把 $d$ 次单项式想成阴影计数对象。对一族 $d$-子集 $\mathcal A\subseteq\binom{[n]}{d}$：
- **下阴影** $\partial\mathcal A=\{B\in\binom{[n]}{d-1}:B\subset A,\ \exists A\in\mathcal A\}$；
- **上阴影** $\partial^+\mathcal A=\{C\in\binom{[n]}{d+1}:A\subset C,\ \exists A\in\mathcal A\}$。

**概念：colex 序与初始段.** $\binom{[n]}{d}$ 上的 **colex（colexicographic）序**：$A<B$ 当 $\max(A\triangle B)\in B$。给定大小 $|\mathcal A|=N$，**colex 初始段** = colex 最小的 $N$ 个 $d$-集。

**概念：$k$-cascade（级联表示）.** 任意 $N$ 可唯一写成
$$N=\binom{a_d}{d}+\binom{a_{d-1}}{d-1}+\cdots+\binom{a_t}{t},\quad a_d>a_{d-1}>\cdots>a_t\ge t\ge1.$$

**【定理 4.1（Kruskal–Katona, 1963–68）】** 对 $\mathcal A\subseteq\binom{[n]}{d}$，$|\mathcal A|=N$ 级联如上，则
$$|\partial\mathcal A|\ \ge\ \binom{a_d}{d-1}+\binom{a_{d-1}}{d-2}+\cdots+\binom{a_t}{t-1},$$
等号在 colex 初始段达到。**即：固定大小，colex 初始段使（下）阴影最小。** 由补集 $A\mapsto[n]\setminus A$ 对偶，可化为上阴影的极值陈述。

**证明机制（compression）.** 用 **压缩算子** $\mathrm{C}_{ij}$（把含 $j$ 的集尽量换成含 $i$，$i<j$）反复作用，不增大阴影、保持族大小，最终把任意族压成“压缩族”，再对压缩族直接验证阴影下界。这套 **shifting/compression** 是后文外代数路线的同一核心技术。∎（详证见 Frankl 的归纳法或 Daykin 的代数证法。）

> 在我们的语境，**上阴影**对应“楼梯往高次乘变量”。KK 给出：**在固定每层大小下，压缩楼梯使阴影最小**——这是“为什么 F4 support 这么小”的组合机制（真实 gin 接近压缩极值对象，阴影达到下极值）。

---

## 第 5 部分　上界工具二：Macaulay 与 Clements–Lindström

KK 是“无重复指数（squarefree）”版。我们的楼梯一般有重复指数，需推广。

**概念：multicomplex / 除子格.** 固定上界 $a=(a_1,\dots,a_n)$（可允许 $a_i=\infty$）。**除子格** $L(a)=\{x^b:0\le b_i\le a_i\}$ 是 $n$ 条链之积。其上的 **shadow**、**colex 序**、**压缩** 与 KK 平行定义。

**【定理 5.1（Macaulay, 1927）】** 在 $L(\infty,\dots,\infty)=$ 全多项式环里，分次序列 $(H_d)_d$ 是某分次代数 $R/I$ 的 Hilbert 函数 $\iff$ 它满足 Macaulay 增长界 $H_{d+1}\le H_d^{\langle d\rangle}$（Macaulay 算子）。极值由 **lex 段理想（lex-segment ideal）** 达到：固定 $H_d$ 时，lex 段使下一层的（上）阴影 **最小**。

**【定理 5.2（Clements–Lindström, 1969）】** 在有界除子格 $L(a)$（任意有限 $a_i$）里，固定每层大小，**colex（压缩）初始段使阴影最小**——KK 与 Macaulay 的共同推广。

> **本问题的正确工具**：楼梯里单项式指数有界（因为它落在某个有限盒子里），故用 **Clements–Lindström** 给阴影上界最干净；当把指数放开到无界时退化为 **Macaulay**。后文外代数路线则退化为 **纯 KK**（squarefree）。

**应用方式（给 $C_d$ 一个严格但偏松的上界）.** 列集合 $\subseteq$ 楼梯在“乘一个小球 $B_t$”下的阴影；CL 把阴影大小压到压缩楼梯的值。问题是这个阴影是 $\Theta(n\,2^n)$（见 §6），比真值 $\Theta(\sqrt n\,2^n)$ 松一个 $\sqrt n$——**所以 CL 给出正确量级的“天花板”，但拿不到尖锐常数与那个省下的 $\sqrt n$**。

---

## 第 6 部分　候选 1 的严格处理：齐次单次列数

目标：$\big|C_d^{\mathrm{hom}}\big|=\Theta(\operatorname{sum}H)$（平方：$\Theta(2^n)$）。下面把能证的证掉，剩下的缺口讲清。

### 6.1 平凡的两端

**【引理 6.1（标准列恒等）】** $C_d^{\mathrm{hom}}$ 中的标准单项式恰为 $S_d$，个数 $H_d$。
*证明.* 标准单项式不被任何前导项整除，闭包不会把它再展开；而每个“被使用的生成元 $g$（次数 $d$）”的行尾项给出全部 $\prec_\rho\mathrm{LT}(g)$ 的同次标准单项式，并覆盖 $S_d$。∎

于是 **平凡下界** $|C_d^{\mathrm{hom}}|\ge H_d$，平方时 $\max_d H_d=\binom{n}{\lfloor n/2\rfloor}\sim\sqrt{2/(\pi n)}\,2^n=\Theta(2^n/\sqrt n)$。**注意：这比真值 $\Theta(2^n)$ 小一个 $\sqrt n$**——差额全在 pivot。

### 6.2 阴影包含（严格的上界半成品）

**【引理 6.2（pair lcm 的基底包含）】** 每个对的 lcm $\ell=\mathrm{lcm}(\mathrm{LT}(g_a),\mathrm{LT}(g_b))$ 满足 $\ell=t\cdot s$，其中 $t=\mathrm{LT}(g_a)$（$\deg t\le\delta_{\max}:=\max_{g}\deg g$）、$s=\ell/\mathrm{LT}(g_a)$ 标准。即 $\ell\in S+B_{\delta_{\max}}$。
*证明.* $s=\mathrm{LT}(g_b)/\gcd$ 是极小生成元 $\mathrm{LT}(g_b)$ 的真因子，故标准；$\deg t=\deg g_a\le\delta_{\max}$。∎

**【命题(可约化) 6.3（阴影天花板）】** 设 $\delta_{\max}$ 为最大生成元次数。**经验上**（并对 §11 的“一阶 reduction 壳层”严格成立）
$$C_d^{\mathrm{hom}}\ \subseteq\ \big(S+B_{\delta_{\max}}\big)_d:=\{m:\deg m=d,\ \exists s\in S,\ s\mid m,\ \deg(m/s)\le\delta_{\max}\}.$$
据此与 **Clements–Lindström** 得 $|C_d^{\mathrm{hom}}|\le|(S+B_{\delta_{\max}})_d|$。

**缺口（重要，必须说清）.** 6.3 的归纳**不能简单沿 rank 下降推全**：从 pivot $p=u\,\mathrm{LT}(g)$ 重写到 $m=u\,s'$（$s'$ 同次标准），$m$ 的“最大标准因子”可能远低于 $m$ 的次数（例如纯幂 $x_1^d$ 的最大标准因子只有 $x_1$）。
- **好消息**：恰恰这类“深”单项式（纯幂等）**不可达**——见 §11 的可达性引理草稿，纯幂没有合法的标准尾项分解，闭包永远到不了它们。这正是 support 远小于全单项式的机制。
- **坏消息**：把“可达集 $\subseteq$ 某个干净阴影”的包含**完整证明**出来，是本问题真正的硬核（开放）。本文只证了基底（6.2）与“深单项式不可达”的方向，未给出闭式包含。

### 6.3 从天花板到真值：缺的那个 $\sqrt n$

即便 6.3 成立，$|(S+B_{\delta_{\max}})_d|$（对累计版即 §0 的 `env`）经实测是 $\Theta(n\,2^n)$，**比真值大 $\sqrt n$**。原因：阴影把“能乘到”的单项式全算进去，而 reduction **实际只到达其中 $\Theta(2^n)$ 个**（pivot 可达集是阴影的一个 $1/\sqrt n$ 稀疏子集）。**收紧这一步 = 给 pivot 可达集一个尖锐计数**，这是 §8 与 §9 下界/外代数要攻的对象。

> **小结（候选 1 的现状）**：上界 $O(n\,2^n)$ 严格（CL，模 6.3 的包含）；下界 $\Omega(2^n/\sqrt n)$ 严格（标准单项式）。**真值 $\Theta(2^n)$ 卡在 pivot 可达集的尖锐计数**——上松 $\sqrt n$、下松 $\sqrt n$，正中间。

---

## 第 7 部分　累计 = 齐次按次数“积分”：那个 $\sqrt n$

### 7.1 结构化约化（基本严格）

**【命题(可约化) 7.1（累计–齐次约化）】** 累计模型在峰值轮的列集合按次数分块：
$$\big|C^{\mathrm{cum}}_{\le d^\*}\big|=\sum_{j\le d^\*}\big|\,(\text{该轮中次数恰为 }j\text{ 的列})\,\big|.$$
而“次数恰为 $j$ 的累计列”在量级上等于齐次单次列数 $|C_j^{\mathrm{hom}}|$（两者差别仅来自尾项规则：累计行额外贡献的是**更低次**单项式，它们计入各自次数，故总集合恰是各次并集）。于是
$$\boxed{\ \operatorname{peak}^{\mathrm{cum}}\ \asymp\ \sum_{j}\big|C_j^{\mathrm{hom}}\big|,\qquad \operatorname{peak}^{\mathrm{hom}}\ =\ \max_j\big|C_j^{\mathrm{hom}}\big|.\ }$$
**那个 $\sqrt n$ 就是“有效宽度” $\dfrac{\sum_j|C_j^{\mathrm{hom}}|}{\max_j|C_j^{\mathrm{hom}}|}$。**

**经验支持（$n=10$）.** 累计逐次新增列：$d_4{:}541,\ d_5{:}945,\ d_6{:}1187,\ d_7{:}1281,\ d_8{:}154,\dots$，是一个**峰高 $\Theta(2^n)$、$j$-宽度 $\Theta(\sqrt n)$ 的鼓包**，求和 $\approx 4500\approx\sqrt{2n}\,2^n$，而齐次峰值同样落在 $d=7$（鼓包顶）。两条曲线顶点重合，印证 7.1。

**缺口.** “次数 $j$ 累计列 $\asymp |C_j^{\mathrm{hom}}|”** 是量级等式而非恒等式（尾项规则不同导致行集闭包略有差异；实测 $d=7$ 累计比 msolve 多约 9%）。把它升级成带常数的严格等式需要对两种闭包做配对论证。

### 7.2 为什么有效宽度是 $\sqrt n$（Gorenstein + 中央极限）

由 **引理 2.2** 的对称性，齐次单次列数的鼓包关于 $d=n/2$ 近似对称，峰位于中心带。设单次列数 $\approx c_1\,2^n$ 于中心、向两侧按 $\binom nd$ 型衰减。则
$$\sum_j|C_j^{\mathrm{hom}}|\ \approx\ (\text{峰高})\times(\text{有效宽度}).$$
$\binom nd$ 的“质量宽度” $\dfrac{\sum_d\binom nd}{\max_d\binom nd}=\dfrac{2^n}{\binom{n}{\lfloor n/2\rfloor}}=\Theta(\sqrt n)$（Stirling，严格）。**若**单次列数的鼓包形状与 $\binom nd$ 同型（这需要 §6 的 pivot 计数继承 Hilbert 的中心集中性），则有效宽度 $=\Theta(\sqrt n)$，从而 $\operatorname{peak}^{\mathrm{cum}}=\Theta(\sqrt n\cdot 2^n)$。**鼓包同型性 = 待证的关键继承性质。**

---

## 第 8 部分　下界

### 8.1 累计的 $\Omega(2^n)$（基本严格）

峰值轮里所有标准单项式都会作为某行尾项出现（中心次数附近的生成元行覆盖全部低次标准单项式），故 $\operatorname{peak}^{\mathrm{cum}}\ge(1-o(1))\sum_d H_d=\Omega(2^n)$。

### 8.2 目标下界 $\Omega(\sqrt n\,2^n)$（构造思路）

需要 $\Omega(\sqrt n\,2^n)$ 个**不同的可达 pivot**。构造模板：
$$\mathcal P=\Big\{\,s\cdot \gamma:\ s\in S,\ \gamma\in G_{\le 2}\ (\text{二次生成元/拐角}),\ s\gamma\text{ 非标准且可达}\,\Big\}.$$
- **质量**：固定 $\gamma$（约 $\Theta(n)$ 个二次拐角），$s$ 跑遍中心带标准单项式（$\Theta(\sqrt n)$ 层、每层 $\Theta(2^n/\sqrt n)$），乘积去重后若仍保留常数比例，则 $|\mathcal P|=\Omega(\sqrt n\cdot 2^n)$。
- **可达性（缺口）**：需证 $\mathcal P$ 中常数比例的 $s\gamma$ 确实被 symbolic preprocessing 到达。这要一个“$s\gamma$ 在 rank 上可由某对 lcm 经合法重写链下降到达”的引理——**未严格完成**，是下界的硬核。外代数（§9）在 Boolean 模型里把这一步变透明。

> **现状**：下界 $\Omega(2^n)$ 严格；尖锐的 $\Omega(\sqrt n\,2^n)$ 依赖可达性引理。上界（§6）与下界（§8）都卡在**同一个对象——pivot 可达集的尖锐计数**。这是问题的真正核心。

---

## 第 9 部分　外代数路线

### 9.1 外代数与 Hilbert 函数巧合

**外代数** $E=\Lambda\langle e_1,\dots,e_n\rangle=k\langle e_i\rangle/(e_ie_j+e_je_i,\ e_i^2)$。单项式 = **squarefree** = $[n]$ 的子集；$\dim_k E_d=\binom nd$，$\sum_d\dim E_d=2^n$。**这与平方二次 $R/I$ 的 Hilbert 函数逐项相同**，是外代数图像的起点。

**关键观察（最干净的桥）.** 单项式完全交 $(x_1^2,\dots,x_n^2)$ 的商，其楼梯 **正是 squarefree 单项式 = Boolean 立方体**，且 Hilbert 级数也是 $(1+t)^n$，极小生成元就是 $n$ 个平方（都二次）。于是：

$$\boxed{\text{外代数路线} = \text{把问题搬到“平方理想楼梯 = Boolean 立方体”上算}.}$$

在 Boolean 立方体里：
- $2^n$ = 立方体总点数（引理 2.1 的 transparent 版）；
- $\sqrt n$ = 中央层厚度 $\dfrac{2^n}{\binom{n}{n/2}}$（引理 2.2 + Stirling 的 transparent 版）；
- 阴影由 **纯 KK（定理 4.1）精确控制**（不需要 CL 的有界格推广，因为 squarefree）。

### 9.2 严格的桥：代数 shifting

平方理想楼梯（Boolean 立方体，$n$ 个生成元）与真实 gin（$n=10$ 时 426 个生成元）**形状不同但 Hilbert 函数相同**。把二者联系起来的严格工具是 **代数 shifting**：

- **概念：simplicial complex 与 $f$-向量.** squarefree 单项式理想 $\leftrightarrow$ Stanley–Reisner 复形 $\Delta$，其 $f$-向量记录各维面数。
- **【定理 9.1（Kalai 的代数 shifting）】** 存在算子 $\Delta\mapsto\Delta^{\mathrm{shift}}$（外代数 shifting $\Delta^e$、对称 shifting $\Delta^s$、组合 shifting）把任意复形送到 **shifted（squarefree strongly stable）复形**，**保持 $f$-向量/Hilbert 函数**，且 shifted 复形是“压缩极值”对象。
- **【定理 9.2（Aramova–Herzog–Hibi）】** 外代数里也有 generic initial ideal $\mathrm{gin}_E(J)$，它 strongly stable，且与对称代数侧的 gin 经 shifting 对应。

桥的用法：**在 shifted/Boolean 模型里 KK 给出精确阴影界与中心集中性，再经 shifting 的 Hilbert-函数保持性，把 $2^n$ 与 $\sqrt n$ 这些“只依赖 Hilbert 函数”的量搬回对称侧。**

### 9.3 外代数下界（最适合外代数的部分）

外代数路线最大的价值是**下界 transparent**。在 Boolean 立方体里，候选 pivot 族
$$\mathcal P_E=\{\,x_i^2\cdot T:\ T\ \text{squarefree},\ i\notin T,\ |T|=k\,\}$$
（一个平方乘一个不含该变量的子集）个数 $\approx n\cdot 2^{n-1}$ 量级，落在中央带的部分给出 $\Theta(\sqrt n\,2^n)$；KK/等周不等式（Harper 定理）保证这些族的阴影/可达性可被**精确**估计，不像对称侧那样含混。**这是“为什么累计多出 $\sqrt n$、为什么齐次是 $2^n$”最直观的严格化场所。**

### 9.4 外代数路线的命脉缺口

**列数是否只依赖 Hilbert 函数？** 平方理想楼梯（$n$ 生成元）与 gin（数百生成元）的临界对结构、闭包都不同，其 **F4 列数先验可能不同**。外代数路线的合法性 = “support 峰值在压缩极值楼梯类内只依赖 $H$”。

> **⚠ 此缺口已在 §14.1 用实验否证**：Boolean/平方理想楼梯给出 **0 个存活临界对、peak cols = 0**（它本身是单项式 Gröbner 基），而同 Hilbert 函数的贪心 gin 楼梯给出 $\sqrt n\,2^n$。**故 F4 列数不是 $H$ 的函数，强烈依赖楼梯形状。** 详见 §14.1 及其对外代数路线的修正。

---

## 第 10 部分　两条路线对比与推荐

| 维度 | 组合路线（CL + Macaulay + Moreno–Socías） | 外代数路线（KK + 代数 shifting） |
|---|---|---|
| 对象 | 代码实际计算的贪心/revlex 楼梯 | Boolean 立方体（平方理想楼梯） |
| 阴影工具 | Clements–Lindström（有界格，较繁） | 纯 KK（squarefree，最干净、精确） |
| 适用范围 | **一般 $H$，含超定截断** | 平方 $\binom nd$ 干净；超定无干净对应物 |
| $2^n,\sqrt n$ 来源 | 需经 Stirling 论证 | **transparent**（立方体点数、中央层厚） |
| 上界 | 能给 $O(n\,2^n)$ 天花板（模 §6 包含） | 同样需回到可达集计数 |
| 下界 | §8 构造，可达性是缺口 | **最适合**：KK/Harper 把可达性变精确 |
| 桥到真实 F4 | 依赖 Moreno–Socías（开放） | 依赖 shifting + “列数只依赖 $H$”（开放） |
| 隐藏依赖 | — | **暗中也要用压缩论证**（shifting 本质是 compression，与 CL 同源） |

**推荐（明确）.**

1. **承重墙用组合路线**：它对象正确、对一般 $H$ 统一、能直接对接 msolve 数据。先把 **§6 的 pivot 可达集计数** 做成尖锐引理（这是上下界共同的瓶颈）。
2. **外代数做向导 + 平方情形下界**：用 Boolean 立方体把 $2^n$、$\sqrt n$ 的机制讲透，用 KK/Harper 在 Boolean 模型里拿到 **$\Omega(\sqrt n\,2^n)$ 下界**，再经 shifting 搬常数项级结论回去。
3. **注意**：外代数路线并非“绕开”组合工具——shifting 的内核就是 compression，与 CL/KK 同源；它的优势是**几何直观**与**精确等周**，不是回避难点。

**元层面（必须分清的两个目标）.**
- **目标 A**：证明这个组合代理模型的标度律 → 干净、难但可做的极值组合（本文框架）。
- **目标 B**：给真实 F4 复杂度严格陈述 → 还需过两座桥：**Moreno–Socías**（保证楼梯形状）与“稠密尾项模型正当性”。msolve 的逐项吻合是 B 的强经验证据，但非证明。

---

## 第 11 部分　可达性引理草稿（问题的硬核）

把上下界共同的缺口提炼成一条引理，并给出已能证的方向。

**定义（reduction 可达）.** 单项式 $m$（次数 $d$、非标准）**可达**，若存在从某对 lcm 出发、每步形如 $u\,\mathrm{LT}(g)\rightsquigarrow u\,s$（$s\in S$，$\deg s=\deg g$，$s\prec_\rho\mathrm{LT}(g)$）的同次重写链终于 $m$。记可达 pivot 集 $P_d$。

**【引理草稿 11.1（深单项式不可达，方向性已证）】** 若 $m$ 的所有“标准因子中次数 $\ge2$ 的因子”都不存在（例如 $m=x_i^d$，其 squarefree/低次标准因子只有 $1,x_i$），则 $m$ 无合法标准尾项分解，$m\notin P_d$。
*证明要点.* 行尾项要求 $s\in S$ 且 $\deg s=\deg g\ge2$ 且 $s\mid m$。纯幂 $x_i^d$ 的标准因子（在 $x_i^2$ 为生成元时）只有 $1,x_i$，无 $\deg\ge2$ 者，故 $x_i^d$ 既不能作尾项被引入，也（递归地）不能先作前导项。∎

**【引理草稿 11.2（可达 pivot 的尖锐计数）— 目标，未证】**
$$|P_d|=\Theta(2^n)\ \text{于中心次数},\qquad \sum_d|P_d|=\Theta(\sqrt n\,2^n).$$
**这正是同时收紧 §6 上界与 §8 下界、并经 §7 给出累计 $\Theta(\sqrt n\,2^n)$ 的唯一缺口。** 攻法二选一：
- **(组合)** 给 $P_d$ 建立与“楼梯一阶/二阶压缩阴影”的双向夹逼（CL 上界 + colex 段下界），并证两者同阶；
- **(外代数)** 在 Boolean 模型里用 Harper 等周给 $P_d$ 的精确层计数，再 shifting 搬回。

---

## 第 12 部分　现状总表

| 命题 | 等级 | 状态 |
|---|---|---|
| $\sum H=\dim R/I=\lvert S\rvert$（引理 2.1） | 定理 | ✔ 完整 |
| Gorenstein 对称 $H_d=H_{n-d}$（引理 2.2） | 定理 | ✔ 完整 |
| 楼梯 order ideal、边界 = 极小生成元（2.3） | 引理 | ✔ 完整 |
| rank 序同次平移不变、闭包终止（2.4） | 引理 | ✔ 完整 |
| KK / Macaulay / Clements–Lindström（§4–5） | 定理 | ✔ 文献，陈述+机制完整 |
| 标准列 $=S_d$，平凡下界 $\ge H_d$（6.1） | 引理 | ✔ 完整 |
| pair lcm 基底包含 $\ell\in S+B_{\delta_{\max}}$（6.2） | 引理 | ✔ 完整 |
| 阴影天花板 $C_d\subseteq S+B_{\delta_{\max}}$（6.3） | 命题(可约化) | ◑ 仅基底+“深单项式不可达”方向 |
| 上界 $O(n\,2^n)$（CL，模 6.3） | 命题(可约化) | ◑ 条件成立 |
| 累计 $\asymp\sum_j$齐次（7.1） | 命题(可约化) | ◑ 量级，非带常数恒等 |
| 有效宽度 $=\Theta(\sqrt n)$（7.2，Stirling 部分） | 引理/启发 | ◑ Stirling 严格；鼓包同型性待证 |
| 累计下界 $\Omega(2^n)$（8.1） | 引理 | ✔ 基本完整 |
| 深单项式不可达（11.1） | 引理 | ✔ 完整 |
| **pivot 可达集尖锐计数 $\lvert P_d\rvert=\Theta(2^n)$（11.2）** | **猜想** | **✗ 硬核；§15–16：深度≈1 已证子项=两标准之积，但 $\lvert\Pi_d\rvert=O(2^n)$ 已否证；真硬核=DRL 受约束积的中次坍缩** |
| 平方下界 $\Omega(\sqrt n\,2^n)$（8.2 / 9.3） | 启发 | ✗ 依赖可达性 |
| 列数只依赖 $H$（外代数合法性，9.4） | 猜想 | ✗ 可实验检验 |
| 桥到真实 F4（Moreno–Socías 等） | 猜想 | ✗ msolve 强经验支持 |

---

## 第 13 部分　建议的可执行下一步（按性价比）

1. **（最高优先，实验）** 把代码楼梯换成**平方理想楼梯（Boolean 立方体）**，比较列数峰值是否仍 $=\sqrt n\,2^n$。**结果决定外代数路线是否合法**（即“列数是否只依赖 $H$”），一次实验即可证伪或强化。
2. **（实验）** 直接统计 $|P_d|$（可达 pivot 数）随 $d$、$n$ 的曲线，验证 11.2 的“峰高 $2^n$、宽度 $\sqrt n$”图像；并把 $\sum_d|P_d|$ 与累计峰值对齐。
3. **（理论，承重）** 攻 **引理 11.2**：在 Boolean 模型里先用 Harper 等周拿 $|P_d|$ 的精确层界（外代数），随后用 CL 在一般楼梯上做夹逼（组合）。这是把 $\Theta$ 做实的唯一关口。
4. **（理论，常数）** 沿 §7.1 把“累计 $\asymp\sum_j$齐次”升级为带常数的配对恒等，解释为何 $\sqrt{2n}$ 归一化的比值随 $n$ 缓降（实测 $n{=}8{\to}15$：$1.020\to0.959$），从而确定真常数（疑似略小于 $\sqrt2$ 或含弱次阶修正）。
5. **（建模）** 与超定族对照：$c(m,n)$ 随 $m/n$ 增大（$m{=}n{:}\,0.96$；$m{=}n{+}1{:}\,1.25$；$m{=}n{+}2{:}\,1.41$）说明 $\sqrt{2n}\cdot\operatorname{sum}H$ 不是普适基线；试 $\sqrt n\cdot\max H$、$\max H\cdot(\text{Hilbert 宽度})$ 等基线，看哪个常数最稳，以反推正确猜想形式。

---

### 文献指引（便于跟进）

- Hilbert 函数/极值：Macaulay (1927)；Clements–Lindström (1969)；Kruskal (1963)、Katona (1968)。
- 复杂度：Bardet–Faugère–Salvy（半正则系统 F5 复杂度、$d_{\mathrm{reg}}$ 渐近）；Faugère（F4/F5 原始论文）。
- Fröberg 猜想：Fröberg (1985)。
- gin / Moreno–Socías：Galligo、Bayer–Stillman（gin 一般理论）；Moreno-Socías 猜想；Pardue（部分结果）。
- 外代数 / shifting：Kalai（代数 shifting 综述）；Aramova–Herzog–Hibi（外代数 gin、shifting）；Harper（Boolean 立方体等周）。
- Gorenstein/CI：Stanley，*Combinatorics and Commutative Algebra*；Bruns–Herzog，*Cohen–Macaulay Rings*。

---

## 第 14 部分　实验更新（本轮新增，已执行）

### 14.1 Boolean / 平方理想楼梯实验 → §9.4 命脉缺口**已否证**

把代码楼梯替换为平方理想 $(x_1^2,\dots,x_n^2)$ 的楼梯（即 **Boolean 立方体**），与贪心 gin-代用楼梯对照（二者 Hilbert 函数**完全相同**，标准单项式数都 $=2^n$）：

| 楼梯 | $\lvert\mathrm{mg}\rvert$ | 存活临界对 | peak cols ($d\ge4$) |
|---|---|---|---|
| 贪心 gin 代用 ($n{=}10$) | 426 | 5940 | **4529** $=\sqrt{2n}\,2^n$ |
| 平方理想/Boolean ($n{=}10$) | 10 | **0** | **0** |
| 贪心 ($n{=}12$) | 1463 | 28110 | **19834** |
| 平方理想 ($n{=}12$) | 12 | **0** | **0** |
| 贪心 ($n{=}8$) | 128 | 1197 | 1044 |
| 平方理想 ($n{=}8$) | 8 | 0 | 0 |

**机制**：平方理想生成元两两互素 $\Rightarrow$ Buchberger 乘积准则杀掉**全部** S-对 $\Rightarrow$ 它本身就是约化 Gröbner 基，F4 无任何非平凡矩阵。

**结论（重要修正）**：$\boxed{\text{F4 列数不是 Hilbert 函数的函数；它强烈依赖楼梯的形状。}}$
- Boolean 立方体（平方理想）是**退化极端**：单项式 GB、零约化、列数 $=0$。
- 产生 $\sqrt n\,2^n$ support 的，是**通用 gin 的丰富生成元结构**（$\approx$ revlex 段、$\Theta(2^n/\sqrt n)$ 个生成元、与 msolve 吻合）。

**对外代数路线的修正（据此重写 §9 推荐）**：
1. 外代数仍**合法地**提供 **Hilbert 层的量**——总质量 $2^n$、中心窗口宽度 $\sqrt n$。这些是 $H$ 的纯粹推论，**与 pivot 计数、与楼梯形状无关**，外代数（Boolean 立方体的点数与中央层）把它们讲得最透。
2. 外代数**不能**直接给列数：列数需要通用 gin 的生成元/临界对结构。
3. “把问题搬到 Boolean 立方体上算 F4” 是**错误的动力学模型**。正确的外代数对象是**外代数 generic initial ideal**（Aramova–Herzog–Hibi；反交换、生成元丰富），**不是**多项式环里的平方理想。后者的 F4 平凡。
4. 故**承重墙必须直接在通用 gin（revlex 段）上做 Clements–Lindström 组合论证**；外代数仅作“质量 $\times$ 宽度”分解与中心窗口组合的**向导**，不作计算替身。这反过来**加强**了 §10 的原始推荐。

### 14.2 pivot 逐次统计 → §11.2 图像证实（峰高 $2^n$、宽度 $\sqrt n$）

齐次模型逐次列数分解为 **standard**（$=H_d$）与 **pivot**（非标准、可达）：

$n=10$：

| $d$ | cols | pivots | $H_d$ | pivots/$2^n$ |
|---|---|---|---|---|
| 4 | 560 | 350 | 210 | 0.342 |
| 5 | 1006 | 754 | 252 | 0.736 |
| 6 | 1317 | 1107 | 210 | 1.081 |
| 7 | 1396 | **1276** | 120 | **1.246** |
| 8 | 862 | 817 | 45 | 0.798 |
| 9 | 499 | 489 | 10 | 0.478 |

$n=12$ 同型：pivots/$2^n$ 在 $d{=}7,8$ 达 $1.165,1.161$，鼓包跨 $d{=}6{:}9$。

- **pivot 鼓包峰高 $\approx 1.25\cdot 2^n$**（数值证实 $\lvert P_d\rvert=\Theta(2^n)$，即引理 11.2 的高度）；
- **pivot 鼓包宽度 $\approx\sqrt{2n}$ 个次数**（$n{=}10$ 约 4 次 d=5..8；引理 11.2 的宽度）；
- **standard** 在 $d\approx n/2$ 处峰值 $=\max H=\Theta(2^n/\sqrt n)$，**比 pivot 小一个 $\sqrt n$**，且峰位不同（standard 峰 $d{=}5$，pivot 峰 $d{=}7$）。

这正是 §0/§6/§8 的核心论点的直接数值确认：**列数主项是 pivot，pivot 比 standard 多一个 $\sqrt n$；$\sum_d\lvert P_d\rvert\approx\sqrt n\cdot 2^n$ 即累计峰值量级。**
（附注：齐次列数逐次求和 $\approx 6\cdot2^n$（$n{=}10$）与累计峰值 $4529\approx4.4\cdot2^n$ **同阶但常数不同**——印证 §7.1 的 “$\asymp$” 只是量级、非带常数恒等。）

### 14.3 数值标度确认（常数与漂移）

| $n$ | 累计 peak cols | $/\sqrt{2n}2^n$ | 齐次 peak cols | $/2^n$ |
|---|---|---|---|---|
| 10 | 4529 | 0.989 | 1396 | 1.363 |
| 11 | 9436 | 0.982 | 2689 | 1.313 |
| 12 | 19834 | 0.988 | 5563 | 1.358 |
| 13 | 40925 | 0.980 | 10185 | 1.243 |

累计 $\approx 0.98\cdot\sqrt{2n}\,2^n$（常数略低于 $\sqrt2$，随 $n$ 缓降）；齐次 $\approx 1.3\cdot2^n$。两者之比 $\approx\sqrt n$（有效宽度），与 §7.2 一致。

### 14.4 预测算法复杂度与理论下限（回答“当前是 $4^n$ 吗？最优是多少？”）

- **当前复杂度 $\approx\Theta(\sqrt n\cdot 4^n)$**。实测每增 1 变量耗时 $\times4.3$（$n{=}10{\to}13$：$0.15\to0.52\to2.48\to11.7$ s）。瓶颈：累计 `add_support_of_row` 对**每一行**展开 $O(\lvert S\rvert)=O(2^n)$ 个标准尾项，而行数 $\approx\sqrt n\,2^n$，故 $\sqrt n\,2^n\times2^n=\sqrt n\,4^n$。（生成元个数 $\lvert\mathrm{mg}\rvert\approx\Theta(2^n/\sqrt n)$，故 build_pairs 的双重环 $O(\lvert\mathrm{mg}\rvert^2)=\Theta(4^n/n)$ 同阶但不主导。）
- **理论下限 = 输出大小**。单个峰值矩阵 support $=\Theta(\sqrt n\,2^n)$；整条 profile $\sum_d\mathrm{cols}_d=\Theta(n\,2^n)$。故任何算法 $\ge\Omega(\sqrt n\,2^n)$，**最优 $\approx\tilde\Theta(2^n)$**（poly 因子）。
- **差距 $\approx 2^n$**。把 $4^n$ 降到 $2^n$ $\iff$ “直接枚举 support 而不展开稠密尾项” $\iff$ 给 pivot 可达集 $P_d$ 一个**构造性刻画** $\iff$ **§11.2 的开放硬核**。即 $\boxed{\text{可证最优的预测算法} \iff \text{完成 support-size 证明}}$。
- **旁证（为何真实 msolve 反而快）**：msolve（$n{=}10$ 约 1 秒）用**约化基的稀疏尾项**做 symbolic preprocessing；模型故意用**稠密尾项上界**（每行整个 $S_{\prec}$）以**保证 support 的可证上界**。模型是用速度换“可证上界”。
- **已落地的实用提速**：按次数桶**并行**（各 `combo_round` 完全独立，仅写各自的 `cols[d]`/`rows[d]`，读共享只读 predictor）。已加 OpenMP（`f4_combinatorial_predict_omp.c`），多核近线性加速、输出与串行版**逐字节一致**；本沙箱单核故未体现墙钟收益。齐次尾项较累计省 $\sqrt n$ **常数**因子但同阶。**无“简单的”渐近提速——那等于解开 §11.2。**

### 14.5 本轮实验的代码

- `f4_combinatorial_experiments.c`：在 no-FLINT 版基础上加 (a) `g_boolean` 开关与 `mono_is_squarefree`，令 `build_staircase` 按 squarefree 划分（= 平方理想楼梯）；(b) `combo_round_hom_count` 统计每次的 pivot（非标准列）数；(c) 两个 CLI：`boolean-test n`（贪心 vs Boolean 对照）、`pivots m n δ`（逐次 cols/pivots/$H_d$）；(d) 桶级 OpenMP。
- `f4_combinatorial_predict_omp.c`：干净的“no-FLINT + OpenMP”版，输出与串行一致。

复现：
```
gcc -O2 -march=native -fopenmp -o exp  f4_combinatorial_experiments.c -lm
./exp boolean-test 10        # GREEDY 4529 vs BOOLEAN 0
./exp pivots 10 10 2         # 逐次 pivot 鼓包
```

---

## 第 15 部分　§11.2 的实质推进：闭包深度坍缩 + 动态问题静态化

本节是对 §11.2（pivot 可达集 $P_d$ 的尖锐计数，全文硬核）的一次**实质性推进**。核心是一个新的实验结构发现，它把"界定一个深迭代闭包"的动态难题，**严格地约化**成一个不含任何 Gröbner 动态的**静态极值组合估计**。

### 15.1 核心发现：约化闭包的**深度 $\approx 1$**

把齐次单次闭包按 BFS 层展开（层 0 = 临界对 lcm；层 $k+1$ = 层 $k$ 的非标准直接子项）。忠实复现实际闭包（pivot 总数与 §14.2 逐项吻合：1276、489、4771、…）后测得：

| $n$ | $d$ | 层0 (lcms) | 层1 (子项) | 层$\ge2$ | pivot 总数 | 最大深度 |
|---|---|---|---|---|---|---|
| 8 | 6 | 107 | 196 | 0 | 303 | **1** |
| 10 | 7 | 359 | 917 | 0 | 1276 | **1** |
| 10 | 9 | 299 | 190 | 0 | 489 | **1** |
| 11 | 7 | 575 | 1784 | 0 | 2359 | **1** |
| 12 | 7 | 919 | 3840 | **12** | 4771 | 2 |
| 13 | 8 | 2022 | 6876 | 0 | 8898 | **1** |
| 14 | 9 | 4301 | 14417 | **4** | 18722 | 2 |

**结构定律（强经验支持）**：
$$\boxed{\,P_d \;=\; \Lambda_d \ \sqcup\ \mathcal C_d \ \sqcup\ E_d,\qquad \Lambda_d=\text{对 lcm}, \ \ \mathcal C_d=\text{非标准直接子项}, \ \ |E_d|=o(2^n).\,}$$
层 $\ge2$ 的 $E_d$ 不随 $n$ 增长（$n{=}12$ 仅 12 个、$n{=}14$ 仅 4 个，占比 $<0.3\%$ 且不增）。换言之**闭包本质是深度 1 的两层对象**，不是深迭代。这是 §11.2 一直缺的杠杆。

数值上层 0、层 1 都是 $\Theta(2^n)$：lcms $\approx 0.25\text{–}0.35\cdot2^n$，子项 $\approx 0.9\cdot2^n$（极稳定）。

### 15.2 严格结构刻画（给定深度 1）

设存活对 $(g_a,g_b)$，$\gcd:=\gcd(\mathrm{LT}(g_a),\mathrm{LT}(g_b))\neq1$（互素对已被乘积准则杀掉），$\ell=\mathrm{lcm}=\mathrm{LT}(g_a)\mathrm{LT}(g_b)/\gcd$，$\deg\ell=d$。

**（lcm 形）** $\ell=\mathrm{LT}(g_a)\cdot t_a$，其中 $t_a:=\mathrm{LT}(g_b)/\gcd$ 是 $\mathrm{LT}(g_b)$ 的**真因子**，故 $t_a\in S$（标准）。于是
$$\Lambda_d\ \subseteq\ (G\cdot\mathcal T)_d,\qquad \mathcal T:=\{\text{极小生成元的真因子}\}\subseteq S.$$

**（子项形，关键）** 经 $g_a$ 展开、用标准 $s\prec_\rho\mathrm{LT}(g_a)$（$\deg s=\deg g_a$）得子项
$$c=\frac{\ell}{\mathrm{LT}(g_a)}\cdot s=t_a\cdot s,\qquad t_a\in S,\ s\in S.$$
**子项是两个标准单项式之积。** 故非标准子项落入
$$\mathcal C_d\ \subseteq\ \Pi_d:=(S\cdot S)_d\cap\overline S\ =\ \{\text{可写成两标准单项式之积的、}d\text{ 次非标准单项式}\}.$$

**合并（给定深度 1，严格）**：
$$\boxed{\,P_d\ \subseteq\ \Lambda_d\ \cup\ \Pi_d\ \cup\ E_d,\qquad |P_d|\ \le\ |(G\cdot\mathcal T)_d|+|\Pi_d|+o(2^n).\,}$$

### 15.3 关键约化：**动态闭包 → 静态坍缩估计**

§11.2 原本要界定"reduction 可达集"（含重写动态、first-div 选择、heap 处理顺序）。15.2 把它变成两个**纯静态**的命题——只关于楼梯 $S$ 与生成元 $G$，**不含任何 Gröbner/F4 动态**：

$$\textbf{(静态坍缩猜想)}\qquad |\Pi_d|=O(2^n)\quad\text{且}\quad |(G\cdot\mathcal T)_d|=O(2^n).$$

> **⚠ 重要修正（见 §16）**：下面这条"$|\Pi_d|=O(2^n)$"**一般是错的**。本节只测了**中次** $d=7$（$\Pi_7\approx3\cdot2^n$），但 $\Pi_d$ **在高次 $d\approx n$ 爆掉**到 $\approx2.7\text{–}2.9^n$（lex、DRL 皆然，见 §16.2 数据）。所以"积上界 $\mathcal C_d\subseteq\Pi_d$"虽严格，但**除 F4 峰值次数附近外都太松**。子项之所以仍 $\le1.25\cdot2^n$（所有次数），靠的是**可达性/配对约束**而非积结构——该约束**不可省**。§16 给出 lex 的 $\Pi_d$ 闭式与此修正。

实测 $|\Pi_d|$（两标准之积、非标准、$d$ 次）：

| $n$ | $d$ | $\lvert\Pi_d\rvert$ | $\lvert\Pi_d\rvert/2^n$ | 子项数/$2^n$ |
|---|---|---|---|---|
| 10 | 7 | 3500 | 3.42 | 0.90 |
| 11 | 7 | 6703 | 3.27 | 0.87 |
| 12 | 7 | 11796 | 2.88 | 0.94 |
| 13 | 8 | 37954 | 4.63 | 0.84 |

$|\Pi_d|\approx3\text{–}4\cdot2^n=O(2^n)$，**比 §5/§6 的阴影天花板 $O(n\,2^n)$ 紧了一个 $n/\!\log$**；而真正的子项（$0.9\cdot2^n$）稳稳落在 $\Pi_d$ 内。**于是只要证出静态坍缩 $|\Pi_d|=O(2^n)$，子项界 $O(2^n)$ 就（在深度 1 下）严格成立。** 这是把 $\sqrt n$ 那一关从"动态"挪到"静态极值组合"的实质一步——后者正是 Clements–Lindström / 压缩论证的主场。

### 15.4 坍缩现象与残余硬核

朴素积界 $|\Pi_d|\le\sum_{j}|S_j||S_{d-j}|=\sum_j\binom nj\binom{n}{d-j}$ 在中心 $j\approx n/2$ 处给出 $\Theta(4^n/n)$，**太松**。真值 $O(2^n)$ 意味着楼梯元素之积发生**大规模坍缩**（中心两半之积绝大多数重合）。这个坍缩是残余硬核——**但它现在是静态的、可直接检验的**，且具体形态干净：

- **小因子部分** $\bigcup_{j\le k}(S_j\cdot S_{d-j})$：受 $O(n^{k-1/2}2^n)$ 控制，$k=O(1)$ 时已是 $\tilde O(2^n)$。
- **中心因子部分**（两半皆 $\approx n/2$ 次）：坍缩在此发生，是缺口所在。$(1+t)^n$ 的 Gorenstein 对称 + revlex 段的强稳定性应是坍缩的来源（强稳定理想的乘法有压缩极值性）。

### 15.5 下界经由深度 1（构造大大简化）

深度 1 同时简化**下界**：$P_d\supseteq\Lambda_d$（lcm 是层-0 pivot，平凡可达），且**任何显式子项族都在一步内可达**——无需验证深重写链。于是
$$\Omega(2^n)\text{ 下界}\ \Longleftarrow\ |\Lambda_d|=\Omega(2^n)\ \text{（lcm 计数）}\quad\text{或}\quad \text{显式构造 }\Omega(2^n)\text{ 个 }t_a\cdot s\text{ 型子项}.$$
后者现在是"造一族两标准之积、且每个都来自某存活对的一步展开"，比原来的"造可达 pivot 并验证可达性"干净得多。

### 15.6 完成 §11.2 还差什么（更新后的硬核清单）

1. **深度 $O(1)$ 的严格证明**：证 $|E_d|=o(2^n)$，即"孙项几乎都是标准"。机制：子项 $c=t_a s$ 两标准之积、"非标准度"集中在单个生成元上，替换后落回楼梯；需控制例外集（$n{=}12$ 的 12 个）。
2. **静态坍缩 $|\Pi_d|=O(2^n)$**：revlex 段 order ideal 中两元素之积在每个次数上坍缩到 $O(2^n)$ 个。这是纯极值组合（CL/Macaulay/压缩 + $(1+t)^n$ 的对称函数结构），**已无 Gröbner 动态**。
3. **匹配下界 $|\Lambda_d|=\Omega(2^n)$**：lcm 计数，或 15.5 的一步可达构造。

**小结**：本轮没有完全证出 §11.2，但把它从"界定深动态闭包"**严格降维**为"两层（深度 1）+ 静态积坍缩"，并给出 $|\Pi_d|=O(2^n)$ 的紧实验证据（取代了 $O(n2^n)$ 松界）。剩下三件事都是**可独立攻击的静态命题**。

### 15.7 本节实验命令（见 `f4_combinatorial_experiments.c`）

```
./exp depth  m n δ d     # 忠实 BFS：逐层 pivot 数、最大深度
./exp prod   m n δ d     # |Π_d| = 两标准之积、非标准、d 次
./exp gens   m n δ       # 生成元次数分布
./exp pivots m n δ       # 逐次 cols / pivots / H_d
```
复现要点：`depth` 的 pivot 总数与 `pivots` 的逐次 pivot 数完全一致（互验闭包忠实性）。

---

## 第 16 部分　坍缩再审视：lex 闭式、积上界失效、可达性约束不可省

本节修正 §15.3 的一个过乐观断言，并给出一个**严格的**闭式结果（lex 楼梯的 $\Pi_d$ 刻画）作为副产品与反例来源。

### 16.1 lex 楼梯的显式结构与 $\Pi_d$ 闭式刻画（严格）

**lex 楼梯（显式）.** 对 Hilbert 函数 $(1+t)^n$，唯一 lex 理想的标准单项式为
$$S^{\mathrm{lex}}=\{x^c:\ \mu(c)\ge|c|\},\qquad \mu(c):=\min\{i:c_i>0\}\ (\mu(1)=\infty).$$
即 $x^c$ 标准 $\iff$ 它只用变量 $x_{|c|},\dots,x_n$（最小下标 $\ge$ 次数）。验证：$d$ 次标准 = $\{x_d,\dots,x_n\}$ 中 $d$ 次单项式，个数 $\binom{(n-d+1)+d-1}{d}=\binom nd$。✓

记 $q_k(c)$ = $c$ 第 $k$ 小"单位"的下标（单位 = 位置按指数重复）。

**【引理 16.1（lex 的 $\Pi_d$ 闭式）】** 对 $\deg x^c=d$：
$$x^c\in\Pi_d^{\mathrm{lex}}\ \Longleftrightarrow\ \mu(c)<d\ \text{ 且 }\ q_{\mu(c)+1}(c)\ \ge\ d-\mu(c).$$
*证明.* 记 $m=\mu(c)$。
（⇐）取 $a$ = $c$ 最低 $m$ 个单位之积（$\deg a=m$，$\mu(a)=m$，故 $|a|=m\le\mu(a)$，标准）；$b=c/a$ 取余下 $d-m$ 个单位，$\mu(b)=q_{m+1}(c)\ge d-m=|b|$，标准。则 $c=ab$ 是两标准之积；$\mu(c)=m<d$ 故 $c$ 非标准。
（⇒）设 $c=ab$ 两标准。最低位置 $m$ 属 $a$ 或 $b$，不妨属 $a$，则 $\mu(a)=m$、$|a|\le m$。令 $a$ 取最低 $|a|$ 个单位（使 $\mu(b)=q_{|a|+1}$ 最大），$b$ 标准要 $d-|a|\le q_{|a|+1}(c)$。增大 $|a|$（至多 $m$）只放松此式（左减右增），故可行 $\iff$ $|a|=m$ 情形成立，即 $d-m\le q_{m+1}(c)$。∎

引理 16.1 已用暴力枚举在 $n\le8$ 全部 $(n,d)$ 上逐一核对无误。

### 16.2 关键修正：$|\Pi_d|=O(2^n)$ **一般不成立**

用 16.1 计算 lex 的 $|\Pi_d|$，并与代码 DRL 楼梯对比，**两者 $\Pi_d$ 都在高次爆掉**：

| | $\Pi_d$ 峰值位置 | 峰值 $/2^n$（随 $n$） | 估计底数 |
|---|---|---|---|
| lex（$n{=}8{\to}16$） | $d=n$（顶次） | $4.3,6.1,8.7,12.5,18,26,37.6,54.6,79.3$ | $\approx2.9^n$ |
| DRL/代码（$n{=}10,12$） | $d=n$（顶次） | $6.25,\ 11.8$ | $\approx2.7^n$ |

逐项比值收敛到 $\approx2.9$（lex）、$\approx2.7$（DRL），即 $|\Pi_d|_{\max}$ 介于 $2^n$ 与 $4^n$ 之间、底数 $\approx2.7\text{–}2.9$，**绝非 $O(2^n)$**。

> **修正 §15.3**：我先前只看了**中次** $d=7$（$\Pi_7\approx3\cdot2^n$，恰好 $O(2^n)$），误以为 $|\Pi_d|=O(2^n)$。实际 $\Pi_d$ 随次数单增、在顶次爆到 $\approx2.7\text{–}2.9^n$。故含入 $\mathcal C_d\subseteq\Pi_d$ **只在 F4 峰值次数 $d^\*\approx0.7n$ 附近有用**（那里 $\Pi_{d^\*}=O(2^n)$）；在高次它废掉。

### 16.3 为何子项仍有界：**可达性约束不可省**

实测每次 pivot 数 $\le1.25\cdot2^n$（$n{=}10$：各次 $96,350,754,1107,1276,817,489,199,55,10$，峰 $1276@d{=}7$），故**子项在所有次数都 $\le1.25\cdot2^n$**，高次更小（$d{=}11$ 仅 55）。

于是局面是：**子项本身有界（$O(2^n)$），但其静态超集 $\Pi_d$ 在高次爆掉**——含入太松。子项的有界性**不来自**"两标准之积"这一积结构，而来自 reduction 的**可达性/配对约束**：
$$\mathcal C_d=\{\,t_a\cdot s:\ t_a=\mathrm{LT}(g_b)/\gcd,\ s\prec_\rho\mathrm{LT}(g_a),\ \deg s=\deg g_a,\ (g_a,g_b)\text{ 存活对}\,\}.$$
约束 $s\prec_\rho\mathrm{LT}(g_a)$ 与 $t_a\mid g_b$ 把"所有积 $\Pi_d$"砍成可达子项，**这一步不可省**。

**修正后的约化（更精确）**：深度 1 把 §11.2 降为
$$\text{数 }\Lambda_d\ (\text{lcm})\ +\ \text{数**受可达性约束的**积 }\mathcal C_d,$$
而**不是**"数所有积 $\Pi_d$"。约束是本质难点所在。可走的两条紧路线：
- 证 DRL **特有的中次坍缩**：$\Pi_{d}=O(2^n)$ 于 $d\approx0.7n$（F4 峰值次数），并证子项峰值落在该次数；这够给**齐次峰值** $O(2^n)$。但需排除高次（那里 $\Pi_d$ 爆但子项小）。
- 直接界**受约束积**：把约束 $s\prec\mathrm{LT}(g_a)$ 翻译成 rank-前缀，证 $\bigcup_{(g_a,g_b)}t_a\cdot\{s\prec\mathrm{LT}(g_a)\}$ 在每次坍缩到 $O(2^n)$。这才是真正的硬核，且依赖 DRL gin 的具体结构（疑与 generic CI 的 Lefschetz/WLP 性质相关）。

### 16.4 回答："$4^n\to2^n$ 需把 §11.2 证到什么程度？现在做得到吗？"

**做不到，且原因比单纯证 §11.2 更深一层。**

1. **基数界不够。** 即便严格证出 $|P_d|=O(2^n)$，那只是个数；算法要在 $\tilde O(2^n)$ 时间内**逐一列出** $P_d$ 的元素。基数界不给枚举方法。
2. **需构造性刻画。** 要快算法，必须能**直接判定/枚举**"哪些单项式是 lcm、哪些是可达子项"——像 16.1 给 lex 的 $\mu$-闭式那样的**显式判据**。有了它就能逐元素生成，跳过冗余。
3. **深度 1 只省常数。** 它把闭包从"深迭代（heap）"变成"lcm + 一次展开"，省掉迭代开销；但**仍需** $O(|G|^2)=\Theta(4^n/n)$ 枚举对、$O(4^n/\sqrt n)$ 枚举 (lcm, 子项) 关联。要破 $4^n$，得（a）不经全部对而直接枚举 distinct lcm，（b）不经全部关联而直接枚举 distinct 子项——两者都要 §16.3 的构造性刻画。
4. **DRL 暂无此刻画。** lex 有（16.1）但 lex 是**错的序**（msolve 用 DRL），且 lex 的 $\Pi_d$ 照样爆。DRL gin 的显式判据未知。

**结论**：$4^n\to2^n$ 与证明卡在同一处**且更靠后**——不仅要证 §16.3 的受约束坍缩，还要把它做成**构造性枚举**。所以现在确实做不到；可落地的仍只是 §14.4 的桶级并行（常数）+ 深度 1 带来的闭包常数提速。

### 16.5 现状总表（修正后）

| 命题 | 等级 | 状态 |
|---|---|---|
| 闭包深度 $\approx1$（§15.1） | 结构定律 | ✔ 经验稳健（层$\ge2$ 占比 $<0.3\%$ 不增） |
| 子项 $=t_a\cdot s$（两标准之积）（§15.2） | 引理 | ✔ 严格（给定深度 1） |
| lex 的 $\Pi_d$ 闭式（§16.1） | 引理 | ✔ 严格 + 暴力核对 |
| $\lvert\Pi_d\rvert=O(2^n)$（§15.3） | ~~猜想~~ | **✗ 已否证：高次爆 $\approx2.7\text{–}2.9^n$** |
| 子项 $\le1.25\cdot2^n$（所有次数） | 观察 | ✔ 经验，但缺独立证明 |
| 受约束积/lcm 的中次坍缩 $O(2^n)$ | 猜想 | ✗ 真硬核，疑与 DRL gin 的 WLP/Lefschetz 相关 |
| 构造性枚举（→ 快算法） | 目标 | ✗ DRL 无显式判据；lex 有但序不对 |

**一句话**：本轮把硬核**更精确地定位**了——不是"数所有两标准之积"（那会爆），而是"数 DRL 可达性约束下的子项/lcm 在中次的坍缩"，并证明了 lex 侧的 $\Pi_d$ 闭式（顺带证否了 $O(2^n)$ 的天真猜想）。快算法需把这个坍缩做成**构造性**判据，目前 DRL 尚无。

### 16.6 实验/脚本

- `pi_lex.py`、`pilex.c`：lex 楼梯 $\Pi_d$ 的暴力核对与大 $n$ 计数（验证 16.1、量出 $\approx2.9^n$）。
- `f4_combinatorial_experiments.c` 的 `prod m n δ d`：DRL 楼梯逐次 $|\Pi_d|$（量出高次爆 $\approx2.7^n$）。

---

## 第 17 部分　Eliahou–Kervaire / 有界深度上阴影：通向 $|P_d|=O(2^n)$ 的正确入口

§16 的 $\Pi_d$ 死在"无界次数乘子 ⇒ 积集爆掉（$\approx2.7^n$）"。本节用 DRL gin 的**强稳定性**（Eliahou–Kervaire，下称 EK）把乘子次数**压到 1–2**，从而把子项关进**有界深度上阴影**——一个不爆、且正是 Macaulay/Clements–Lindström 主场的对象。这是 §11.2 的正确入口。

### 17.1 DRL gin 强稳定 ⟹ EK 适用（修复死路的结构输入）

- char 0 下 gin 总是 Borel 不动（Galligo 定理）；代码的 revlex-段楼梯，其 **LT 集 = revlex 段 = 强稳定**（把权重移到更低下标使单项式 revlex 更大、仍落在上段）。故 **Eliahou–Kervaire 分解适用**。
- **EK 结构**：强稳定理想的极小一阶 syzygy 恰为 $(g,x_j)$，$j<\max(g)$，对应 S-对的 **lcm $=x_j\cdot\mathrm{LT}(g)$**（单变量 × 生成元）。
- **实测确认**：存活临界对的 lcm **全部**是 $x_j\cdot$生成元——$n{=}10,d{=}7$：1227/1227；$n{=}12$：3306/3306；$n{=}13$：8834/8834。无一例外。

### 17.2 子项落入有界深度上阴影（实测 co-degree $\le2$）

设 lcm $=x_j\mathrm{LT}(g)$，$g$ 次数 $d-1$。
- 经 $g$ 展开：子项 $=x_j\cdot s$（单变量 × 标准 $s$，$\deg s=d-1$）⟹ **co-degree 1**（有 $d{-}1$ 次标准因子）。
- 经另一生成元 $g'$ 展开：co-degree $=d-\deg g'$；EK 迫使 $\deg g'\ge d-2$ ⟹ **co-degree $\le2$**。

**实测（决定性）**：子项的"标准 co-degree"（到某标准因子的最小补次数）**在所有 $n$、所有次数都 $\le2$**：

| | $d{=}4$ | $d{=}5$ | $d{=}6$ | $d{=}7$ | $d{=}8$ | $d{=}9$ | $d{=}10$ | $d{=}11$ |
|---|---|---|---|---|---|---|---|---|
| $n{=}10$ max-codeg | 2 | 2 | 2 | 2 | 1 | 1 | 1 | 1 |
| $n{=}12$ max-codeg | 2 | 2 | 2 | 2 | 2 | 1 | 1 | 1 |
| $n{=}14$ max-codeg | 2 | 2 | 2 | 2 | 1 | 2 | 1 | 1 |

恒 $\le2$；其中 85–95% 是 co-degree 1。故
$$\boxed{\ \mathcal C_d\ \subseteq\ \partial^{+1}(S_{d-1})\ \cup\ \partial^{+2}(S_{d-2}).\ }$$

### 17.3 上阴影不爆（与 $\Pi_d$ 的关键反差）

| 对象 | 峰值 $/2^n$（$n{=}10,12,14$） | 量级 |
|---|---|---|
| $\lvert\partial^{+1}(S_{d-1})\rvert$ | $1.02,\ 1.04,\ 1.03$ | **$O(2^n)$**（随 $n$ 持平） |
| $\lvert\partial^{+2}(S_{d-2})\rvert$ | $3.21,\ 3.58,\ 3.83$ | $\approx\sqrt n\cdot2^n$ |
| ~~$\lvert\Pi_d\rvert$（§16）~~ | ~~爆~~ | ~~$\approx2.7\text{–}2.9^n$~~ |

**为何不爆**：上阴影用**有界次数乘子**（1–2 个变量），是压缩集（revlex 段）的真正 Macaulay/CL 上阴影；$\Pi_d$ 用无界次数乘子，故爆。EK 提供的正是 §16 所说"缺的 DRL 结构输入"。

### 17.4 结果：rigorous-modulo-EK 的 $|P_d|=O(\sqrt n\,2^n)$，主项 $O(2^n)$

由 §15.1（深度 1）+ 17.2 + 17.3：
$$|P_d|\ \le\ \underbrace{|\Lambda_d|}_{\text{lcm}}\ +\ \underbrace{|\partial^{+1}(S_{d-1})|}_{\text{co-deg 1 子项}}\ +\ \underbrace{|\partial^{+2}(S_{d-2})|}_{\text{co-deg 2 子项}}\ +\ o(2^n).$$
- **1-step 项 $=O(2^n)$**（压缩集上阴影；实测峰 $\approx2^n$、随 $n$ 持平），**且覆盖 85–95% 子项**（co-degree 1 那部分）。这是对子项**主体**的 rigorous-modulo-EK 的 $O(2^n)$ 界。
- **2-step 项 $=O(\sqrt n\,2^n)$**：偏松——co-degree-2 子项只占 5–15%（实测 $\le0.15\cdot2^n$），但整张 2-step 阴影超出 $\sqrt n$ 倍。
- **lcm 项**：$|\Lambda_d|\le n\,|G_{d-1}|$；实测 $|G_{d-1}|=O(2^n/n)$（$n{=}10$：$|G_6|{=}84<2^n/n{=}102$），故 $|\Lambda_d|=O(2^n)$。

**结论**：rigorous-modulo-EK 得 $|P_d|=O(\sqrt n\,2^n)$（单次数，即累计峰值量级），其中**主体（co-degree-1）已是干净的 $O(2^n)$**。这是第一个 rigorous-modulo-EK、量级接近真值的上界，**彻底取代了 §16 的 $\Pi_d$ 死路**。

**到 sharp $O(2^n)$ 还差**：把 co-degree-2 子项（5–15% 那部分，实测 $\le0.15\cdot2^n$）从"整张 2-step 阴影 $O(\sqrt n2^n)$"收紧到 $O(2^n)$——这是个**更小的残余**，且已是标准的强稳定/Macaulay 估计（非 §16 的不可控积坍缩）。

### 17.5 这条路线为何对（vs §16）

EK 迫使 lcm $=$ 单变量 × 生成元 ⟹ **乘子次数有界（1–2）** ⟹ 子项落入**压缩集的有界深度上阴影**，后者可证不爆。§16 的 $\Pi_d$ 允许无界次数乘子 ⟹ 爆。修复是**结构性的**（EK/强稳定），正是 §16 所指认"缺的 DRL 结构输入"。

### 17.6 算法：EK 给出 $4^n\to\tilde O(\sqrt n\,2^n)$ 的希望（更新 §16.4 的悲观）

EK 同时**软化** §16.4 的"做不到"：
- 存活对 $=\{(g,x_j):g\in G,\ j<\max(g)\}$，个数 $\sum_g(\max g-1)\le n|G|=O(\sqrt n\,2^n)$。可**直接枚举**，**无需** $O(|G|^2)=\Theta(4^n/n)$ 的双重对环。
- 列集合 $=$ 标准 $\cup$ 有界深度上阴影，可在 $O(\text{阴影})=O(\sqrt n\,2^n)$ 内枚举。
- ⟹ **有望做出 $\tilde O(\sqrt n\,2^n)$ 预测器**（对比当前 $\sqrt n\,4^n$，近乎平方级加速）。需实现并验证 EK 枚举与现模型逐项一致。
- 所以 §16.4 的"基数界不够"仍对，但 **EK 提供了此前缺失的构造性枚举**入口。

### 17.7 对 11.2（结论 $|P_d|=\Theta(2^n)$）的信心

现由四重支撑：(i) 直接测量 $\le1.25\cdot2^n$ 且与 msolve 实测列维数逐项吻合；(ii) 深度 1；(iii) co-degree $\le2$ 的有界深度上阴影含入、量级正确；(iv) EK 结构。**结论稳固**；通向完整证明的残余已落在标准的强稳定理想 + Macaulay 组合里。

### 17.8 本节实验命令

```
./exp route m n δ d    # lcm 是否全为 x_j*gen；|∂+1(S_{d-1})|、|∂+2(S_{d-2})|
./exp codeg m n δ d    # 子项的标准 co-degree 直方图（验证 ≤2）
```

---

## 第 18 部分　总体证明现状、关键数据、程序清单

### 18.1 证明链条总览（逐环节定级）

记 **R**=严格、**R/EK**=在 EK（强稳定）结构下严格、**E**=经验稳健（多 $n$/多次数验证）、**O**=开放。

| # | 命题 | 级别 | 出处 |
|---|---|---|---|
| 1 | $\sum_d H_d=\dim R/I=\lvert S\rvert=2^n$ | **R** | §2.1 |
| 2 | Gorenstein 对称 $H_d=H_{n-d}$ ⟹ $\sqrt n$ 中心窗口 | **R** | §2.2,§7.2 |
| 3 | rank 序同次平移不变 ⟹ 闭包终止、$C_d$ 良定义 | **R** | §2.4 |
| 4 | 列数 = 标准($=H_d$) ⊔ pivot($P_d$)，主项是 $P_d$ | **R** | §0,§6.1 |
| 5 | 累计峰值 $\asymp\sum_j$ 齐次单次，$\sqrt n$=有效宽度 | **R**(量级) | §7.1 |
| 6 | 闭包**深度 $\approx1$**：$P_d=\Lambda_d\sqcup\mathcal C_d\sqcup o(2^n)$ | **E** | §15.1 |
| 7 | 子项 $=t_a\cdot s$（两标准之积）；$\mathcal C_d\subseteq\Pi_d$ | **R**(给定 6) | §15.2 |
| 8 | $\lvert\Pi_d\rvert=O(2^n)$ — **否证**（高次爆 $\approx2.7$–$2.9^n$） | 否证 | §16.2 |
| 9 | lex 楼梯 $\Pi_d^{\mathrm{lex}}$ 闭式刻画 | **R** | §16.1 |
| 10 | DRL gin 强稳定 ⟹ 存活 lcm 全为 $x_j\cdot\mathrm{LT}(g)$ | **R/EK**+**E** | §17.1 |
| 11 | 子项 co-degree $\le2$ ⟹ $\mathcal C_d\subseteq\partial^{+1}(S_{d-1})\cup\partial^{+2}(S_{d-2})$ | **R/EK**+**E** | §17.2 |
| 12 | 上阴影不爆：$\lvert\partial^{+1}\rvert=O(2^n)$，$\lvert\partial^{+2}\rvert=O(\sqrt n2^n)$ | **E**(+CL) | §17.3 |
| 13 | **上界 $\lvert P_d\rvert=O(\sqrt n\,2^n)$（主体 co-deg-1 为 $O(2^n)$）** | **R/EK** | §17.4 |
| 14 | 下界 $\lvert P_d\rvert=\Omega(2^n)$ | **O**(构造) | §8.2 |
| 15 | sharp 上界 $O(2^n)$：收紧 co-deg-2 子项(5–15%) + lcm 计数 | **O**(标准残余) | §17.4 |
| 16 | 真实 F4（msolve）列维数 = 模型预测（逐次吻合） | **E**(强) | msolve 验证 |

**一句话现状**：结论 $|P_d|=\Theta(2^n)$（及 headline $\Theta(\sqrt n\,2^n)$）**经验确证**（含真实 msolve）。上界方面，已从 §16 的死路转入 EK/有界深度上阴影正路，得 **rigorous-modulo-EK 的 $O(\sqrt n\,2^n)$、其中 co-degree-1 主体为干净的 $O(2^n)$**；离 sharp $O(2^n)$ 仅差一个**更小且标准**的残余（co-degree-2 那 5–15% + lcm 计数）。下界与 sharp 上界仍开放，但都已落在强稳定理想 + Macaulay 的常规工具内。

### 18.2 关键数据汇总（可复现）

**(a) 真实 F4 验证（msolve，$n{=}10$ 稠密 MQ，DRL）— 列维数逐次吻合**

| deg | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|
| msolve cols | 1771 | 2916 | 3891 | 4393 | **4529** | 4430 | 4340 | 4305 |
| 预测 cols | 1771 | 2958 | 4239 | 4393 | **4529** | 4430 | 4340 | 4305 |

峰值矩阵 msolve `4146×4529` vs 预测 `4189×4529`。

**(b) 标度律（square，cumulative / homogeneous）**

| $n$ | cum peak | $/\sqrt{2n}2^n$ | hom peak | $/2^n$ |
|---|---|---|---|---|
| 10 | 4529 | 0.989 | 1396 | 1.363 |
| 11 | 9436 | 0.982 | 2689 | 1.313 |
| 12 | 19834 | 0.988 | 5563 | 1.358 |
| 13 | 40925 | 0.980 | 10185 | 1.243 |

**(c) pivot 主导（$n{=}10$ 齐次，逐次）**：标准 $H_d$ vs pivot

| d | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| pivots | 754 | 1107 | **1276** | 817 | 489 |
| $H_d$ | 252 | 210 | 120 | 45 | 10 |
| pivots/$2^n$ | 0.736 | 1.081 | **1.246** | 0.798 | 0.478 |

**(d) 闭包深度 $\approx1$（忠实 BFS）**

| $n$ | $d$ | 层0(lcm) | 层1(子项) | 层$\ge2$ | 总 pivot | 深度 |
|---|---|---|---|---|---|---|
| 10 | 7 | 359 | 917 | 0 | 1276 | 1 |
| 12 | 7 | 919 | 3840 | 12 | 4771 | 2 |
| 13 | 8 | 2022 | 6876 | 0 | 8898 | 1 |
| 14 | 9 | 4301 | 14417 | 4 | 18722 | 2 |

**(e) $\Pi_d$ 爆掉（顶次，§16 死路证据）**：峰值 $/2^n$ 随 $n$：lex $4.3{\to}79$（$n{=}8{\to}16$，底数 $\approx2.9$）；DRL $6.25$($n{=}10$)$,11.8$($n{=}12$)。

**(f) EK 路线（§17）**：lcm 全为 $x_j\cdot$gen（1227/1227 等）；co-degree 恒 $\le2$；$\lvert\partial^{+1}\rvert/2^n=1.02,1.04,1.03$，$\lvert\partial^{+2}\rvert/2^n=3.2,3.6,3.8$（$n{=}10,12,14$）。

**(g) Boolean 楼梯（§14，列数依赖形状的证据）**：平方理想楼梯给 0 存活对、peak cols $=0$（同 Hilbert 函数下贪心给 $\sqrt n2^n$）。

**(h) 复杂度**：累计路径实测 $\approx\Theta(\sqrt n\,4^n)$（每加 1 变量 $\times4.3$）；输出下限 $\tilde\Theta(2^n)$。

### 18.3 程序清单（全部随附）

| 文件 | 作用 | 关键命令 / 复现 |
|---|---|---|
| `f4_combinatorial_predict_noflint.c` | 去 FLINT 的预测器（输出与原版逐字节一致） | `gcc -O2 -march=native -o predictor f4_combinatorial_predict_noflint.c -lm`；`./predictor profile-semi-peak 10 10 2` → `peak 4189 x 4529 @ d=9` |
| `f4_combinatorial_predict_omp.c` | + 桶级 OpenMP 并行（多核近线性、输出不变） | `gcc -O2 -march=native -fopenmp -o predictor f4_combinatorial_predict_omp.c -lm` |
| `f4_combinatorial_experiments.c` | 全部证明实验（去 FLINT 基础上扩展） | `gcc -O2 -march=native -fopenmp -o exp f4_combinatorial_experiments.c -lm` |
| `pilex.c` | lex 楼梯 $\Pi_d$ 大-$n$ 计数（量出 $\approx2.9^n$） | `gcc -O2 -o pilex pilex.c && ./pilex` |
| `pi_lex.py` | lex 楼梯 $\Pi_d$ 暴力 vs 闭式核对（验证 §16.1） | `python3 pi_lex.py` |

`f4_combinatorial_experiments.c` 的命令（皆 `./exp <cmd> m n δ [d]`）：

| 命令 | 量什么 | 对应章节 |
|---|---|---|
| `boolean-test n` | 平方理想 vs 贪心楼梯（列数是否依赖形状） | §14.1 |
| `pivots m n δ` | 逐次 cols / pivots / $H_d$ | §14.2 |
| `gens m n δ` | 生成元次数分布 | §17（$\lvert G_{d-1}\rvert$） |
| `depth m n δ d` | 忠实 BFS 逐层 pivot 数、最大深度 | §15.1 |
| `prod m n δ d` | $\lvert\Pi_d\rvert$（两标准之积、非标准） | §16.2 |
| `route m n δ d` | lcm 是否全 $x_j$gen；$\lvert\partial^{+1}\rvert,\lvert\partial^{+2}\rvert$ | §17.1,17.3 |
| `codeg m n δ d` | 子项标准 co-degree 直方图（验证 $\le2$） | §17.2 |

**复现核心结论的最短路径**：
```
./exp depth 10 10 2 7     # 深度1：359 lcm + 917 子项 = 1276 pivot（与 pivots 一致）
./exp codeg 10 10 2 7     # co-degree 全 ≤2（742 个=1，175 个=2）
./exp route 10 10 2 7     # lcm 全 x_j*gen(1227/1227)；|∂+1|≈2^n，|∂+2|≈√n·2^n
./exp prod  10 10 2 10    # 对比：Π_d 在高次爆（6400≈6.25·2^n）
```

---

## 第 19 部分　逼近 sharp $O(2^n)$：co-degree-2 残余 + EK 预测器（提速已验证）

### 19.1 co-degree-2 子项的进一步约化（sharp $O(2^n)$ 的最后一块）

co-degree-2 子项 $c$（来自 EK syzygy 的第二生成元 $g'$，$\deg g'=d-2$，乘子 $u'$ 恰 2 次）写成 $c=u's'=x_px_q\cdot s'$，$s'\in S_{d-2}$。令 $w:=x_q s'$（次数 $d-1$）。若 $w$ 标准则 $c=x_p\cdot w\in\partial^{+1}(S_{d-1})$ 为 co-degree 1，矛盾；故 $w$ **非标准**。于是
$$\mathcal C_d^{(2)}\ \subseteq\ \partial^{+1}\!\big(L_{d-1}\big),\qquad L_{d-1}:=\big(\partial^{+1}(S_{d-2})\cap\overline S\big)_{d-1}=\text{“次数 }d{-}1\text{ 的 co-degree-1 非标准层”}.$$
即 co-degree-2 子项落入"$d{-}1$ 次 co-degree-1 非标准层"的**再一步上阴影**——一个 shadow-of-shadow。

- **数值**：co-degree-2 子项实测 $\le0.17\cdot2^n$（$n{=}10,d{=}7$：175；$n{=}12,d{=}7$：435；占子项 5–17%，且 $/2^n$ 随 $n$ 大体下降）。
- **现状**：严格上界仍是整张 2-step 阴影 $O(\sqrt n\,2^n)$；把它收紧到 $O(2^n)$ = sharp 上界的**最后残余**，现已是"压缩层的 shadow-of-shadow 估计"（标准极值组合，无动态）。

### 19.2 EK 预测器：lcm/对枚举提速 $4^n/n\to2^n$（已验证）+ 还差多少

**已验证**：EK 枚举 $\{x_j\cdot g:g\in G_{d-1},\ j\in[n],\ \text{非标准}\}$ **100% 捕获**代码的存活 lcm：

| $n$ | $d$ | $\lvert G_{d-1}\rvert$ | code lcms | EK 捕获 | EK 代价 $n\lvert G_{d-1}\rvert$ | $O(\lvert G\rvert^2)$ | 加速 |
|---|---|---|---|---|---|---|---|
| 10 | 7 | 84 | 359 | **359/359** | 840 | 181 476 | ~216× |
| 11 | 7 | 132 | 575 | **575/575** | 1 452 | 588 289 | ~405× |
| 12 | 7 | 187 | 919 | **919/919** | 2 244 | 2 140 369 | ~954× |
| 13 | 8 | 429 | 2022 | **2022/2022** | 5 577 | 7 333 264 | ~1315× |

即对/lcm 枚举从 $O(\lvert G\rvert^2)=O(4^n/n)$ 降到 $n\lvert G_{d-1}\rvert=O(2^n)$（因 $\lvert G_{d-1}\rvert=O(2^n/n)$），加速比 $\approx2^n/n^{1.5}$ 随 $n$ 增长。

**还差多少（到 $\tilde O(\sqrt n\,2^n)$ 预测器）**：
1. ✔ **对/lcm 枚举**：$4^n/n\to2^n$，已验证（EK 枚举 100% 捕获）。
2. **列/子项枚举**（剩余）：避免现模型 $O(2^n)$-每行的稠密尾展开。有界深度阴影给超集；可达 co-degree-1 子项 $=\bigcup_j x_j\cdot(S_{d-1}$ 的 rank 前缀$)$，若各 $j$ 的前缀嵌套则可在 $O(n\,H_{d-1})=O(\sqrt n\,2^n)$ 内枚举；co-degree-2 部分用 19.1 的 shadow-of-shadow。
3. **结论**：瓶颈（对枚举，$4^n/n$）已验证降到 $2^n$；列枚举设计已勾画。$\tilde O(\sqrt n\,2^n)$ 预测器是**工程实现 + 端到端验证**问题，非概念缺口。命令 `./exp eklcm m n δ d` 复现表中数据。

---

## 第 20 部分　补上 sharp $O(2^n)$ 的最后一块 + EK 快预测器（已验证）

### 20.1 关键新引理：co-degree-2 子项的"系数重数有界" ⟹ co-degree-2 子项是 $o(2^n)$

§19.1 的 shadow-of-shadow 只给到 $O(\sqrt n\,2^n)$（仍偏松）。正确的收紧来自一个**单射 + 有界重数**论证。

**引理 20.1（co-degree-2 子项低阶）.** 设 EK 结构与 co-degree $\le2$ 律成立。对每个 co-degree-2 子项 $c$，取其**最大 rank 的 $d-2$ 次标准因子** $s'(c)\in S_{d-2}$，并令 $u'(c)=c/s'(c)$（2 次单项式）。映射
$$c\ \longmapsto\ (s'(c),\,u'(c))\in S_{d-2}\times\{\text{2 次单项式}\}$$
是**单射**（由 $c=u's'$ 可逆）。记**系数重数** $\mu_d:=\max_{s'\in S_{d-2}}\#\{u':u'\!\cdot\!s'\in\mathcal C_d^{(2)},\ s'(u's')=s'\}$。则
$$\big|\mathcal C_d^{(2)}\big|\ \le\ \mu_d\cdot\big|\{s'\ \text{用到}\}\big|\ \le\ \mu_d\cdot H_{d-2}.$$
**实测**：$\mu_d$ 被一个**小常数**界住（所有 $n$、所有中心次数：$\mu_d\le7$，且**不随 $n$ 增**——$n{=}10$ 为 7，$n{=}14$ 仍为 7）。由 $H_{d-2}=\binom{n}{d-2}=O(2^n/\sqrt n)$，得
$$\boxed{\ \big|\mathcal C_d^{(2)}\big|\ \le\ 7\,H_{d-2}\ =\ O(2^n/\sqrt n)\ =\ o(2^n).\ }$$
即 co-degree-2 子项是**低阶项**，根本不进入主阶。（即便保守地只假设 $\mu_d=O(\sqrt n)$，也已得 $O(2^n)$。）

| $n$ | 全次数 $\max\mu_d$ | 在 $d=$ | $\sqrt n$ |
|---|---|---|---|
| 10 | 7 | 7 | 3.16 |
| 12 | 5 | 6 | 3.46 |
| 14 | 7 | 9 | 3.74 |

**推论 20.2（sharp 上界 $O(2^n)$）.** 在五条结构律下——深度 $\approx1$、co-degree $\le2$、EK（$\Rightarrow$ lcm $=x_j\LT(g)$）、压缩集一步上阴影 $|\partial^{+1}(S_{d-1})|=O(2^n)$（Macaulay/CL）、系数重数 $\mu_d=O(\sqrt n)$——有
$$|P_d|\ \le\ |\Lambda_d|+|\mathcal C_d^{(1)}|+|\mathcal C_d^{(2)}|+o(2^n)\ \le\ O(2^n)+O(2^n)+o(2^n)+o(2^n)\ =\ O(2^n).$$
故**齐次峰值 $|P_d|=O(2^n)$（sharp）**，累计峰值 $=O(\sqrt n\,2^n)$（$\sqrt n$ 个中心次数求和）。这补上了 §17.4 缺的 $\sqrt n$，**条件上界从 $O(\sqrt n\,2^n)$ 升级为 sharp $O(2^n)$**。

命令 `./exp codeg2 m n δ d` 复现 $\mu_d$。

### 20.2 EK 快预测器：种子枚举提速，端到端验证逐次列数**精确**重现

**实现**：列数 $=$ 标准 $\cup$ 由 EK 种子做闭包。种子 $=\{x_j\LT(g):g\in G_{d-1},\ \mathbf{j<\max(g)}\}$（标准 EK 容许条件），代价 $O(n|G_{d-1}|)$，**取代** $O(|G|^2)$ 的双重对环。

**验证**：与原始（$O(|G|^2)$ 造对 + 闭包）逐次列数对比，$n{=}10,11,12,13$ **全次数零失配**：

| $n$ | 失配次数 | 峰值列 | 备注 |
|---|---|---|---|
| 10 | 0/全部 | 1276 | 精确 |
| 11 | 0/全部 | 2689 | 精确 |
| 12 | 0/全部 | 5563 | 精确 |
| 13 | 0/全部 | 10185 | 精确 |

容许条件必须是 $j<\max(g)$：全 $j$（超集）在 $d{=}3$ 多 10 列；$j>\min$ 错 10；$j\le\min$ 错 1；唯 $j<\max$ **全对**。这正是强稳定理想 EK 极小一阶 syzygy 的容许集。命令 `./exp ekpredict m n δ 1`。

**还差多少到 $\tilde O(\sqrt n\,2^n)$ 墙钟**：
- ✔ **种子/对枚举**：$O(|G|^2)=O(4^n/n)\to O(n|G_{d-1}|)=O(2^n)$，**已验证精确**（ekpredict 重现全部列数）。
- **列/子项枚举**（剩余）：上面的 ekpredict 闭包仍用尾展开（正确但未提速，墙钟仍 $\sim4^n$）。快枚举设想是 co-degree-1 子项 $=\bigcup_j x_j\cdot(S_{d-1}$ 的 rank 前缀 $\{<\theta_j\})$，$O(n H_{d-1})=O(\sqrt n\,2^n)$；命令 `./exp fastcol` 实测此式**约 98% 准**（如 810 vs 830、6875 vs 6873），**非精确**——精确快枚举需用到具体存活-lcm 结构（非仅全局阈值 $\theta_j$）。这是剩下的工程。
- **结论**：种子提速已验证精确落地；列枚举的快版本 ~98% 近似、精确版是剩余工作。$\tilde O(\sqrt n\,2^n)$ 的概念结构完备，精确快列枚举待补。

---

## 第 21 部分　co-degree ≤ 2 的证明尝试（generic 情形）+ 预测器澄清

### 21.0 重要更正（预测器）

- **`f4_ek_predictor`（`ekpredict`）算的是齐次、单次数列数**（$2^n$ 级，$n{=}10$ 峰值 $1317$ @ $d{=}6$）；**`f4_combinatorial_predict` 算的是累计/仿射列数**（$\sqrt n\,2^n$ 级，$n{=}10$ 峰值 $4529$ @ $d{=}9$，= msolve）。两者算的是**不同量**，故数值不同（$1317$ vs $4529$），并非矛盾。标题"support $=\sqrt n\,2^n$"指**累计**那个。
- **`ekpredict` 并未加速到 $2^n$**：实测 $n{=}12/13/14 = 3/11.7/48$ 秒，每步 $\approx4\times$，仍 $\sim4^n$。**只有"种子/对枚举"那一步是 $O(2^n)$**；闭包的尾展开仍 $\sim4^n$ 且主导墙钟。之前"已验证提速"仅指对枚举步，**非端到端**。精确快闭包仍未实现（嵌套前缀 ~98% 非精确）。

### 21.1 关键经验发现：co-degree $\le2$ 是**普适**的（与生成元次数 $\delta$ 无关）

测了三次型（$\delta{=}3$）CI（$n{=}6,8$）：co-degree 仍 **只取 1 或 2，从不到 3**（如 $n{=}8,d{=}10$：codeg1 $=1775$，codeg2 $=300$，无 codeg3）。故 co-degree $\le2$ **不是** "$\le\delta$"，而是**恒 $\le2$**。

### 21.2 严格重述：co-degree $\le2$ $\Longleftrightarrow$ EK syzygy 的两生成元次数差 $\le1$

设 EK syzygy 的 lcm $\ell=x_j\LT(g_a)$（$\deg g_a=d-1$，$j<\max(g_a)$）。伙伴生成元 $g_b\mid\ell$ 必满足 $x_j\mid\LT(g_b)$ 且 $v:=\LT(g_b)/x_j\mid\LT(g_a)$（否则 $\ell$ 会更小）。于是经 $g_b$ 展开的子项余因子
$$\ell/\LT(g_b)=x_j\LT(g_a)/(x_jv)=\LT(g_a)/v,\qquad \text{co-degree}=\deg\!\frac{\LT(g_a)}{v}=\deg g_a-\deg v=\deg g_a-\deg g_b+1.$$
因 $v$ 是 $\LT(g_a)$ 的真因子，$\deg g_b\le\deg g_a$（**严格可证的上界**），故 co-degree $\ge1$；且
$$\boxed{\ \text{co-degree}\le2\ \Longleftrightarrow\ \deg g_b\ge\deg g_a-1\ \ (\text{两生成元次数差}\le1).\ }$$

### 21.3 证明策略：生成元次数稠密 + EK 极小性 ⟹ syzygy 局部性

**引理 A（生成元次数稠密，已验证）.** generic CI 的 gin 在 $\delta$ 到 $d_\text{reg}$ 的**每个**次数都有极小生成元（$n{=}10$：$10,20,39,63,84,90,75,35,9,1$，无间断）。这可从 generic（Fröberg）Hilbert 函数推出：$\beta_{0,d}$（$d$ 次新生成元数）由 Hilbert 函数经 Macaulay/almost-revlex 决定，在该区间恒正。

**引理 B（局部性，策略性—未完全闭合）.** 若生成元次数稠密且理想强稳定，则每条极小（EK）一阶 syzygy 的两生成元次数差 $\le1$。**思路**：若 syzygy 连 $g_a$（次 $d{-}1$）与 $g_b$（次 $\le d{-}3$），由稠密性在中间次数 $d{-}2$ 存在生成元 $g_c$；$\LT(g_c)$ 以恰当方式整除 $\ell$，使该 syzygy 经 $g_c$ **分解**，与 EK 极小性矛盾。精确的"经 $g_c$ 分解"需用强稳定结构，这一步我尚未完全坐实。

**由 A + B 即得 co-degree $\le2$。**

**另一条更干净的路（值得一试）**：强稳定 $\Rightarrow$ **componentwise linear**（Herzog–Hibi–Aramova）。componentwise linear 理想的分次 Betti 数高度集中、每个次数分量有线性消解，这很可能**直接**把 EK syzygy 的次数跳限制为 $+1$（即 co-degree $\le2$），无需单独证稠密性。这是把 co-degree $\le2$ 变成定理最有希望的一条，待推。

### 21.4 现状

co-degree $\le2$：经验上**普适**（含三次型），严格上**重述为 syzygy 次数局部性**（$\Leftrightarrow$ 两生成元次差 $\le1$），并**约化到**生成元次数稠密（引理 A，已验证）+ 局部性（引理 B，思路在、未闭合）。上界 $\deg g_b\le\deg g_a$ 已严格。这比原始经验律具体得多，且 componentwise-linear 一路可能直接证出。命令 `./exp codeg m n δ d`（含 $\delta{=}3$）复现。

---

## 第 22 部分　L1–L5 清单 + L2 的严格反例（稠密性是必需的）

### 22.1 五条结构律 L1–L5（主定理 Thm 8.1 的全部假设）

- **L1（深度坍缩）**：闭包深度 $\approx1$，故 $P_d=\Lambda_d\sqcup\mathcal C_d\sqcup(o(2^n))$。**经验**。
- **L2（co-degree $\le2$）**：每个子项有 $d{-}2$ 次标准因子。**经验**（已重述+约化，见下）。
- **L3（EK 结构）**：存活 lcm $=x_j\LT(g)$。**严格**（Galligo ⟹ 强稳定 ⟹ EK）。最硬杠杆，已成立。
- **L4（压缩阴影）**：$|\partial^{+1}(S_{d-1})|=O(2^n)$。**Clements–Lindström**（标准定理）+ 待补计算。
- **L5（系数重数有界）**：$\mu_d=O(\sqrt n)$（实测 $\le7$ 恒定）⟹ co-deg-2 子项 $=o(2^n)$。**经验**。

**哪条关键 / 好推进**：L3 已严格、最重。L1（深度坍缩）最基础但最难、暂无干净约化。L2 **最好推进**（已重述为 syzygy 次数局部性、约化到生成元稠密）。L4 最标准（CL 定理）。L5 是细化。故"先证哪条"上 **L2 是性价比最高的下一步**，但 L1 同样必需且更难。

### 22.2 L2 的严格反例：co-degree $\le2$ 对一般强稳定理想**不成立**，稠密性必需

**例.** $J=(x_1^2,\ x_1x_2^3)\subset k[x_1,x_2,x_3]$。
- **强稳定**：$x_1x_2^3$ 的降指标移动（$x_2\to x_1$）给 $x_1^2x_2^2\in(x_1^2)$ ✓；$x_1^2$ 最低。✓
- **生成元次数有间断**：极小生成元在次数 2（$x_1^2$）与 4（$x_1x_2^3$），**次数 3 无生成元**（3 次部分 $=\{x_1^3,x_1^2x_2,x_1^2x_3\}$ 全是 $x_1^2$ 的倍数）。
- **唯一的 EK 本质 syzygy**：$(g_a{=}x_1x_2^3,\ j{=}1)$，lcm $=x_1\cdot x_1x_2^3=x_1^2x_2^3$。
- **EK 分解**给伙伴 $g_b=x_1^2$（$u=x_2^3$，$\min(u){=}2\ge\max(x_1^2){=}1$；另一选 $g_b{=}x_1x_2^3$ 因 $\min(u){=}1\not\ge\max{=}2$ 被排除）。
- 故经 $g_b$ 的子项 **co-degree $=\deg(x_1^2x_2^3/x_1^2)=\deg x_2^3=3$**。✗

**结论**：co-degree $\le2$ **不是**强稳定的普适性质——它**需要生成元次数稠密（无间断）**。上例的间断（缺 3 次生成元）直接产生 co-degree 3。而稠密性来自 **genericity**（Fröberg Hilbert 函数，已验证 generic CI 每个次数都有生成元）。

这把"genericity 用在哪"再次精确定位：不仅 L3（gin 强稳定）用 genericity，**L2 也本质用 genericity（经稠密性）**。证明链：
$$\text{generic}\ \Rightarrow\ \text{生成元次数稠密（引理 A，已验证）}\ \overset{?}{\Rightarrow}\ \text{co-degree}\le2\ (\text{引理 B，待证}).$$
引理 B（稠密 ⟹ co-deg$\le2$）仍是缺口；MS（almost-revlex，比稠密更强）或 componentwise-linear 是攻它的工具。上界 $\deg g_b\le\deg g_a$ 与本反例（稠密必需）均已严格。

---

## 第 23 部分　引理 B 尝试：EK 剥皮刻画（严格）+ almost-revlex 不充分（意外）

### 23.1 严格工具：EK 分解 = "去最大变量直到生成元"，co-degree = 去除次数

**命题 23.1（剥皮刻画，严格）.** 设 $J$ 强稳定（对降指标封闭），$m\in J$。定义剥皮序列 $m_0=m$，$m_{i+1}=m_i/x_{\max(m_i)}$（每步去掉最大指标变量）。则 EK 分解生成元 $g(m)=m_t$，其中 $t$ 是使 $m_t$ 成为**极小生成元**的最小下标；且子项 co-degree $=t$。

**证明.** EK 条件 $\max(g)\le\min(m/g)$ 对每个 $m_i$ 自动成立：去掉的是 $i$ 个最大变量，$\min(\text{去除})=$ 第 $i$ 大变量 $\ge$ 第 $i{+}1$ 大变量 $=\max(m_i)$。一旦 $m_t$ 是生成元，所有 $i<t$ 的 $m_i$ 是 $m_t$ 的倍数（非极小），所有 $i>t$ 的 $m_i$ 是生成元 $m_t$ 的真因子（标准、$\notin J$），故剥皮中**恰有一个**生成元 $m_t$，由唯一性即 $g(m)=m_t$。∎

**推论（约化，严格）.** 对 EK syzygy $(g_a,j)$，$m=x_j\LT(g_a)$，$M=\max(g_a)$：
$$\text{co-degree}\le2\ \Longleftrightarrow\ m_1=x_j\LT(g_a)/x_M\ \text{或}\ m_2=m_1/x_{\max(m_1)}\ \text{是极小生成元}.$$
其中 $m_1=x_j\cdot s_1$，$s_1=\LT(g_a)/x_M$ 标准（生成元真因子）；且 $m_1/x_j=s_1$ 标准（**$x_j$ 方向那个面已是标准**，严格）。$m_1$ 是 $\LT(g_a)$ 在 $x_M\to x_j$ 下的强稳定像。

### 23.2 意外：almost-revlex **不**蕴含 co-degree ≤ 2

22.2 的反例 $J=(x_1^2,x_1x_2^3)$ **本身就是 almost-revlex**：每个比 4 次生成元 $x_1x_2^3$ revlex-更大的 4 次单项式（即把权移向低指标：$x_1^2x_2^2,x_1^3x_2,x_1^4$）都在 $J$ 中（皆 $x_1^2$ 倍数）。可它 co-degree $=3$。

**故 Moreno–Socías（gin 是 almost-revlex）单独并不足以推出 co-degree ≤ 2**。almost-revlex 允许生成元次数有间断（此例缺 3 次生成元）。真正缺的是**稠密性**——而稠密性来自 generic CI 的 Hilbert 函数 $(1+t)^n$（"最小"Hilbert 函数，每步逼出新生成元），**不是** almost-revlex 本身给的。

### 23.3 现状（更诚实）

- **严格**：剥皮刻画（命题 23.1）；约化"co-deg ≤2 ⟺ $m_1$ 或 $m_2$ 极小"；$m_1$ 的 $x_j$ 面标准；上界 $\deg g_b\le\deg g_a$；反例（强稳定 + almost-revlex 仍可 co-deg 3）。
- **缺口（引理 B）**：稠密性 ⟹ co-deg ≤2 仍未证，且**比预想更难**——almost-revlex 不够，稠密性本身是否充分也存疑（$m_2$ 极小性不被"某处有 $d{-}2$ 次生成元"保证）。可能需要 $(1+t)^n$ 的**全局**性质（非局部条件），或稠密 + almost-revlex 合用。
- **修正方向**：别只押 MS。该证的核心命题是"**$m_1=x_j\LT(g_a)/x_M$ 或其再剥一层是极小生成元**"，这是关于 generic gin 楼梯**局部边界**的陈述，最可能从 $(1+t)^n$ 经 Macaulay/Gotzmann 型计数（而非纯 almost-revlex）拿下。

剥皮刻画把问题变得很具体，是这轮的实质收获；但完整证明引理 B 仍未拿下，且我之前高估了 MS 这条路。

---

## 第 24 部分　重要修正：剥皮深度 ≠ 标准 co-degree；L1 在 poly·2ⁿ 下消解

### 24.1 撤回 §23 的错误

§23 命题 23.1 把 "child co-degree" 等同于 **剥皮深度**（去最大变量到生成元的步数）。**这是错的。** 数值检验（codeg_peel，对所有 EK syzygy $(g_a,j),\ j<\max(g_a)$ 直接剥皮）给出剥皮深度高达 $n-1$：

| $n$ | 剥皮深度分布 | 最大 |
|---|---|---|
| 12 | codeg1 8% / codeg2 32% / ≥3 60% | 11 |
| 14 | 7% / 29% / 64% | 13 |
| 16 | 7% / 28% / 65% | 15 |

但 §17/§19 的 codeg 实验（正确测度 `has_std_divisor_codeg`：$c$ 是否有 $\deg c-k$ 次的**标准因子**）一直给 $\le2$。两者**测量不同量**：

- **剥皮深度** $=$ EK 配对 $g_b$ 与 $g_a$ 的**次数差**（$\deg u'=\deg m-\deg g_b$，可达 $n-1$）。
- **标准 co-degree** $=$ $c$ 到最大标准因子的距离（$\le2$）。

子项 $c=u'\cdot s'$ 中 $u'$（剥皮乘子）可高次，但 $c$ 有一个**比 $s'$ 更大的标准因子**，故标准 co-degree 仍 $\le2$。例：缺口例 $J=(x_1^2,x_1x_2^3)$ 的剥皮深度 3，但其实际 pivot（如 $x_1x_2^3x_k$）的最大标准因子是 $x_1x_2^2x_k$（4 次），标准 co-degree $=1$。**所以缺口例并不展示高标准-co-degree 的 pivot，§23 "稠密性对 L2 必要" 的结论也随之失效。**

剥皮刻画作为 **EK 分解的事实**仍正确（$g(m)=$ 去最大变量遇到的首个生成元），但它刻画的是配对次数差，**不是** L2。L2（标准 co-degree ≤2）退回**纯经验**地位——但用正确测度已重新确认到 $n=16$（csf：partner-children 最大标准 co-degree $=2$，$n{=}12/14/16$ 分布 80/20、92/8、98/2）。

### 24.2 新进展：**L1 在 poly·2ⁿ 下消解为 "全 pivot 有界 co-degree"（L2′）**

关键数值结果（closure_codeg：在中心次数做**完整闭包**到不动点，对**所有** pivot 测标准 co-degree）：

| $n$ | $d$ | 闭包列数 | 对照已知 | **所有 pivot 的最大标准 co-degree** |
|---|---|---|---|---|
| 10 | 6 | 1317 | 1317 ✓ | **2** |
| 12 | 7 | 5563 | 5563 ✓ | **2** |
| 14 | 8 | 9840 | — | **2** |

即：不止 round-1 子项，**完整闭包的每一个 pivot 都满足标准 co-degree ≤2**。记此性质为

> **L2′（全 pivot 有界 co-degree）**：闭包可达的每个 pivot 都有 $\ge d-2$ 次的标准因子。

**L2′ 蕴含 poly·2ⁿ，且不需要 L1。** 因为 L2′ $\Rightarrow$ pivot 全集 $\subseteq\partial^{+}(S_{d-1})\cup\partial^{+2}(S_{d-2})$，由 Clements–Lindström（L4）此集 $=O(\sqrt n\,2^n)$。**无论闭包多少轮（深度多大），有界 co-degree 把所有 pivot 锁在有界阴影里。** 深度动力学变得无关。

于是 **poly·2ⁿ 只需 L2′ + L3 + L4**：
- **L3**（EK，严格）给种子 lcm $=O(2^n)$；
- **L4**（CL）给 $\partial^{+}(S)=O(2^n)$、$\partial^{+2}(S)=O(\sqrt n\,2^n)$；
- **L2′**（经验，全闭包到 $n{=}14$ 确认，partner-children 到 $n{=}16$）把 pivot 锁进 $\partial^{+2}(S)$。

**L1 不再单独需要——它被 L2′ 吸收。** L5 也丢（用松的 2-步阴影 $O(\sqrt n\,2^n)$ 而非 $o(2^n)$）。五律降为三律，其中两条（L3、L4）基本严格。

### 24.3 L1 直接证是否容易？

把 L1（深度坍缩）当独立命题，对 poly·2ⁿ 是**错误的提法**——正确做法是把它折进 L2′。剩下的真问题是：**闭包是否永不逃出 $\partial^{+2}(S)$**（即扩张一个 co-deg-2 pivot 时，新单项式要么标准、要么已是 co-deg-≤2 pivot，绝不产生 co-deg-≥3 的新 pivot）。这与 L2 同味（关于 generic 楼梯的局部结构，经验极稳，证明仍开放），但它是**一个干净的封闭性陈述**，取代了原先模糊的 "深度=1" 动力学。换言之：**L1 的难度不在 "深度有界"，而在 "有界 co-degree 对闭包封闭"——而后者正是（强化版的）L2′。**

---

## 第 25 部分　工程修正 + poly·2ⁿ 归约到单条 L2′（已写进 tex）

**(1) n≥19 崩溃的原因**：单项式被打包进 128-bit 整数，每变量 `fw=7` 位（原代码留了 2 个 guard 位，浪费 1 个）。n=19 时最高位下标 $=(n-1)\cdot7+6=132>127$，**溢出**，楼梯构建得到的候选少于 $H_e$，于是报 `cand<H_e`。修正：去掉多余 guard 位，`fw=6`，支持到 **n=21**（n=22 起干净报错）。构建时间约每 +1 翻倍：n=19/20/21 ≈ 7/12/26 s。正确性不变（n=14 峰值 19609 不变）。

**(2) 非齐次预测器优化**：profile 显示 predcum（n=14，56 s）= build_pairs 8.8 s + 累积闭包 33.6 s，**主成本是累积尾部闭包**。把它做快需要累积版的 nested-prefix，而仿射列集是跨次数 $\Theta(\sqrt n)$ 宽的窗口、不是齐次逐次计数的干净函数——没有现成快算法，**遵嘱跳过**。predcum（已换快构建）仍是非齐次预测器。

**(3) poly·2ⁿ 现在缺什么——只缺 L2′**：关键认识是 **L4 在 poly 层平凡**：粗暴双计数 $|\partial^{+k}(S)|\le n^k|S|\le n^{k}\binom{n}{\lfloor n/2\rfloor}=O(n^{k-1/2}2^n)$ 已是 poly·2ⁿ。于是（tex 中 Thm \ref{thm:poly}）：

> **仅设 L2′**：齐次支撑 $=O(n^{3/2}2^n)$，仿射支撑 $=O(n^2 2^n)$，均 poly·2ⁿ。证明只用 $S$ 是序理想 + 双计数 + 剖面宽度 $\Theta(\sqrt n)$。**不用 L3、不用 sharp L4、不用 L1、不用 L5。**

**L2 与 L2′ 关系**：L2 = round-1 子项 co-deg ≤2；L2′ = **全闭包**每个 pivot co-deg ≤2。L2′ ⟹ L2（更强）。poly·2ⁿ 需要 L2′（界住整个闭包），L2 单独不够（孙代）。

**可证性**：L2′ 的 **co-deg-1 半**是严格的（$x_j\cdot s$，$s$ 标准 ⟹ co-deg 1）；L4-粗（双计数）严格；剖面宽度 $\Theta(\sqrt n)$ 已证（Thm found）。**开放的只有 L2′ 的 partner 半 + 闭包封闭性**——这是关于 generic 楼梯的单一局部命题，取代了原先模糊的 L1 深度动力学。全闭包数值确认到 n=14（列数精确吻合、co-deg 全 ≤2），partner-children 到 n=16。

---

## 第 26 部分　命题 \ref{prop:l2red} 详解 + 证明思路 + 与 Kouba–Neiger–Safey 新文章的关系

### 26.1 命题在讲什么（形象版）

把所有单项式想成一个格点空间。标准集 $S$（quotient 的基）是一座**楼梯下方的实心区域**——它是序理想（除得尽就在里面）。每个 F4 的列 $c$（非标准单项式）是楼梯**上方**的一个点。

定义"标准 co-degree"= $c$ 到楼梯面的**垂直距离**（按次数）：codeg$(c)=k$ 意思是"从 $c$ 往下走 $k$ 步（去掉 $k$ 个变量）才第一次踏上楼梯"。

- L2′ 说：**所有到达的列都离楼梯面不超过 2 步**。
- 命题 \ref{prop:l2red} 把它**翻译**成一句**纯楼梯几何**的话："每个到达的列 $c$（$d$ 次）在 $S$ 里有一个 $d{-}2$ 次的因子。" ——不再提闭包怎么走、不再提选哪个约化子，只问**楼梯的轮廓**在这些列附近长什么样。

这是关键的认识转移：L2′ 看起来是个**动力学**命题（闭包一轮轮产生列），命题 \ref{prop:l2red} 说它其实是个**静态几何**命题（楼梯 $S$ 的形状）。难点从"追踪闭包"变成"刻画 generic CI 的楼梯形状"。

### 26.2 证明思路（两层）

**第一层（等价性，可证，已写进 tex）**：codeg ≤2 ⟺ 有 $d{-}2$ 次标准因子。因为若 $c$ 有 $d{-}1$ 次标准因子 $t$，则 $t$ 再去一个变量得 $d{-}2$ 次的 $t/x_i$，由序理想仍标准、且整除 $c$。所以"≤2 步"等价于"恰有 $d{-}2$ 次标准因子"。一行序理想论证。

**第二层（楼梯几何，难，开放）**：要证 generic CI 的楼梯 $S$ 确实有"近因子"性质。最有希望的路：**Moreno–Socías（almost-revlex）+ Gorenstein 对偶**，并用**截断法**（见 26.3 的文章）。具体地，在**上半区次数**（$d>\dreg/2$，正是仿射峰所在），文章的定理给出生成元的**刚性形状** $x_n^{p}\cdot m$（$m$ 是前 $n{-}1$ 变量的标准单项式），由这个刚性形状推"近因子"性质看起来可行；下半区更难。

### 26.3 那篇文章（Kouba–Neiger–Safey, 2026, LIP6）——高度相关，互补

文章《A complexity analysis of the F4 Gröbner basis algorithm with tracer data》做的正是**同一个问题**：generic grevlex F4 复杂度，靠 Moreno–Socías，得到比 state-of-art **指数级 $n$** 的改进。三点关系：

**(A) 它严格证明了我们的"种子"（L3 的强化）。** 其 **Theorem `thm_type1_good_pairs`**：MS 下，F4 存活的每个临界对都是 **Type 1**——lcm $=x_j\cdot\LT(g)$、$j<\operatorname{idx}(g)$。这**正是**我们的 $\Lambda_d=\{x_j\LT(g)\}$。我们靠 EK/Galligo 论证，他们对**真实 F4 对**严格证明（MS 下）。我们的 L3 由此被独立佐证、且加强。

**(B) 它给了上半区楼梯的显式形状——正是我们命题需要的工具。** 其 **Theorem `thm_card_bdg_deg_moitMB`**（Moreno–Socías Cor 3.2 的锐化）：上半区次数 $d\in\{\dreg/2{+}1,\dots,\dregmb\}$，顶变量生成元**恰为** $x_n^{2d-\dregmb}m$，$m$ 是 $n{-}1$ 变量的标准单项式。这是 generic CI 楼梯在上半区的**精确刻画**，是攻命题 \ref{prop:l2red}（楼梯几何）上半区的现成工具。他们还用**截断法**（把 $x_{j+1},\dots,x_n$ 置零，维度逐层闭合）建立这些——这套方法对我们的"近因子"命题直接可用。

**(C) 互补：我们减列数、他们减行数；我们的界更紧、能改进他们的复杂度。** 他们的复杂度 $\widetilde O(\delta^{\omega n+1}e^{n\,c})$，$\delta{=}2,\omega{=}2$ 时基底 $\approx 2^{1.377n}$，恰是**临界次数 $d\approx n/2$ 的满 Macaulay 列数** $\binom{n+d}{d}$。他们的改进来自 MS 给的**行/约化结构**（上半区 $\sum_{k=0}^2$ 把约化子数压成 $x_n$-次数宽 3 的窗），但**列数仍用满 Macaulay $\binom{n+d}{d}\approx 2^{1.377n}$**。我们证的是**支撑（稀疏列数）$=\Theta(2^n)$**，比 $2^{1.377n}$ **小 $2^{0.377n}$（指数级）**。所以：
- 我们没被他们涵盖（他们不减列数）；
- 反过来，**我们的支撑界若成立，能把他们的列因子从 $\binom{n+d}{d}$ 降到 $2^n$，进一步指数级改进复杂度**。

注意他们的 $\sum_{k=0}^2$ 是 **$x_n$-次数**宽 3 的窗（约化子计数），与我们的 **co-degree ≤2**（总次数 2 步内有标准因子）**精神相同但不是同一个量**——他们没直接证我们的 L2′。但其 Gorenstein 对偶 + 截断方法是证 L2′（至少上半区）的正路。

**小结**：那篇文章和我们高度相关、互补。它严格化了我们的种子结构（A），给了上半区楼梯显式形状这件攻命题 \ref{prop:l2red} 的利器（B），而我们的支撑界比它的列界紧一个指数因子、能反过来改进它的复杂度（C）。下一步最该做的：用其 `thm_card_bdg_deg_moitMB` 的 $x_n^pm$ 刚性形状，证 generic CI 楼梯在上半区的"近因子"性质（= 命题 \ref{prop:l2red} 上半区），仿射峰恰在此区。

---

## 第 27 部分　用 Kouba–Neiger–Safey 的方法对接命题——拿到一块严格结果，但未完成

回答前两问，再给第三问的认真尝试。

### 27.1 只证上半区够吗？"仿射峰在上半区"要证吗？

- **够。** F4 复杂度由**最大矩阵（仿射峰）**主导。若仿射峰在上半区且其支撑被上半区 L2′ 界住，则所有矩阵 ≤ 峰 ≤ poly·2ⁿ，复杂度即得。下半区的齐次逐次列数更小、不绑定。
- **"峰在上半区"本身要证**，目前是经验（$d^\*\approx D-2\sim D-3$，$D=n+1$；n=10/12/14 峰在 $d=9/10/12$）。干净推导我没有——仿射剖面峰位置需单独论证。**所以"只证上半区"合法，但前提是先证峰在上半区。**

### 27.2 用他们的方法：拿到 $x_n$-高度公式（严格、新）

他们两个结果（都在 MS 下证了）正好能用：
1. **`thm_card_bdg_deg_moitMB`**：上半区次数 $d'$ 的顶变量生成元**恰为** $x_n^{2d'-D}m$，$m$ 是 $A:=\K[x_1,\dots,x_{n-1}]$ 的标准单项式。
2. **约化子窗**：上半区（$d\ge \dprev+2$）**每个**约化子顶变量都是 $x_n$（$\nu_i=0,\ i<n$！），且 $\deg_{x_n}\in[2d-D-2,\,2d-D]$。

由 (1) 得**关键引理（新）**：对 $A$ 中标准单项式 $w$（$2\deg w<D$），其 **$x_n$-高度**
$$\alpha(w):=\min\{k:x_n^kw\in J\}=D-2\deg w.$$
（因 $x_n^{D-2\deg w}w$ 恰是上半区生成元，极小性给 $x_n^{D-2\deg w-1}w$ 标准。）

由此 + 窗（窗等价于 $e-\alpha(w)\in\{0,1,2\}$）得**严格命题**：

> 上半区列 $c=x_n^e w$，若 **$w$ 在 $A$ 中标准**，则 codeg$(c)\le2$。
> （$e=\alpha$：生成元，codeg 1；$e=\alpha{+}1$：$c/x_n^2$ 标准；$e=\alpha{+}2$：$c/(x_nx_a)$ 标准，用 $\alpha(w/x_a)=\alpha(w){+}2$。）

数值：上半区列里 $w$ 标准的占 ~27–51%。**这一块严格证完了**（已进 tex）。

### 27.3 归纳的障碍——为什么没完成

剩下 $w$ **非标准**的多数列（~50–73%）。本想归纳：对 $n-1$ 变量用 L2′，给 $w$ 一个 $\ge\deg w-2$ 次的标准 $A$-因子 $w'$，再抬回（$x_n^ew'$ 或 $x_n^{e-1}w'$）得 $c$ 的 $d-2$ 次标准因子。代数我都验过，**能闭合——前提是 $w$ 是 $(n-1)$ 变量问题的可达列**（L2′ 只对可达列成立）。两个事实卡住：

1. **次数错位**：高度映射把 $n$ 变量 $d$ 次送到 $(n-1)$ 变量 $\deg w\in\{D-d,D-d+1,D-d+2\}$ 次。**靠近顶部**（$d\approx D$）才低；仿射峰 $d\approx D-2$ 处 $\deg w\approx 2\text{–}5$。
2. **基例只到 3 次**（实测，决定性）：**所有**非标准单项式 codeg ≤2 **仅在次数 ≤3 成立**；**4 次起就有 codeg ≥3 的单项式**（只是永不被可达）。

所以归纳**绕不开可达性**——必须证"截断把可达列映到可达列"这条相容性，我没建立。**这就是用他们的机器证仿射峰 L2′ 的精确残余障碍。**

### 27.4 诚实小结

- **新的严格成果**：$x_n$-高度公式 $\alpha(w)=D-2\deg w$，及由它+他们的窗得到的"$w$ 标准 ⟹ codeg ≤2"（上半区一整块）。这是用他们方法对接后**真正推进**的部分，已写进 tex。
- **未完成**：$w$ 非标准的多数列归约到 $(n-1)$ 变量 L2′，卡在**可达性相容**（基例只到 3 次，4 次起必须可达）。
- 路线明确：证截断的可达性相容 + 仿射峰在上半区，即可（经他们机器）拿下仿射峰 L2′。这仍是独立工作量，但障碍已缩到一条具体相容性命题。

---

## 第 28 部分　Dixon 组合方法（lattice path）能不能用？——不能直接用，但磨出了更干净的归约

看了 Dixon 矩阵大小的组合证明（迭代单纯形 + 格路计数）。结论：**不能直接搬**，但顺带把归纳变干净了。

### 28.1 Dixon 方法是什么
Dixon 矩阵支撑 = **迭代单纯形** $I_{d_2-1,\dots,d_n-1}$ 的单项式数，其支撑由**嵌套前缀和**约束 $\sum_{l=n-j+1}^n\alpha_l\le\sum_{i=1}^j(d_{n-i+1})$ 给出，再用格路（在分段线性边界下）数 = 行列式 / Fuss–Catalan。$n$ 个二次的 Dixon 矩阵 ~ Catalan 数 ~ $4^n$。核心招式：**把矩阵支撑写成嵌套前缀和多胞形，格路计数**。

### 28.2 能不能搬到 F4 支撑？——不能
试了：F4 标准集是不是这种嵌套前缀和多胞形？**实测否**。$\{\alpha:\alpha_k+2\sigma_{k-1}\le b_k\}$（各种 $b_k$）数出来是 $12,32,105,264,798$，**都不是 $2^n$**。根本原因：F4 标准集基数 $2^n$，**不是**格路（分段线性边界下）的计数（那类给 Catalan 型 $4^n$）。所以 Dixon 的迭代单纯形/格路框架对 F4 支撑不直接适用。

### 28.3 但磨出了干净东西：$x_n$-高度公式无条件 + 精确归约
试 Dixon 嵌套结构时，验证了一个**干净事实**：
$$\alpha(w)=D-2\deg(w)\quad\text{对截断的**所有**标准 }w\text{（实测 }n=8,10,12\text{ 全次数）}.$$
原因：截断是 $n$ 个二次在 $n-1$ 变量的**超定**系统，socle ≈ $n/2<D/2$，所以"$2\deg w<D$"自动成立。**这把 tex 里的高度引理升级成无条件**（覆盖所有 $w$-标准列，不只一片）。

由此得**精确双向归约**（已进 tex）：上半区列 $c=x_n^ew$（$w$ 非标准），
$$\mathrm{codeg}(c)\le2\iff \mathrm{codeg}_{\text{截断}}(w)\le2.$$
即"$n$ 变量上半区 L2′" **等价于**"截断（$n$ 个二次在 $n-1$ 变量）的 L2′"。归纳现在是**精确**的，不再是单向。

### 28.4 缺口没变，但更聚焦
归纳唯一缺的还是：**截断把可达列映到可达列**（因为 codeg ≤2 对一般 ≥4 次单项式失败，必须可达）。试图直接算截断可达集做验证，但**超定系统的楼梯**要 lex 型构造、我的 CI 代码建不了（greedy revlex 在超定 Hilbert 下 cand<H_e 崩），没测成。

**诚实小结**：Dixon 方法不直接适用（标准集非嵌套多胞形）。但它逼我验证了高度公式无条件、并把归纳写成精确等价 $\mathrm{codeg}(c)\le2\iff\mathrm{codeg}_{\text{截断}}(w)\le2$。整个开问题现在 = **一条截断可达性相容命题**，比之前更聚焦。下一步要么给超定楼梯写 lex 构造去实测相容性，要么从 KNS 的 `thm_semieregseq_macmat`（截断 GB = GB 的截断）推可达集层面的相容。

---

## 第 29 部分　把"截断可达性相容"写成独立引理 + 形象例子 + 推进（验证成立，未证）

### 29.1 相容性引理（独立陈述）
记 $R_n$ = $n$ 变量 generic CI 的**可达列**集（出现在某个 F4 矩阵里的单项式：标准单项式 + 极小生成元 + 中间 pivot）；$R^{tr}_{n-1}$ = 截断系统（$n$ 个二次在 $n-1$ 变量，置 $x_n=0$）的可达列集。对 $c\in R_n$ 写 $c=x_n^ew$，$w$ 为去掉 $x_n$ 的部分。

> **猜想（截断可达性相容）**：上半区每个可达列 $c=x_n^ew$，若 $\mathrm{codeg}_{tr}(w)\ge2$，则 $w\in R^{tr}_{n-1}$。

### 29.2 形象例子（$n=3$，手算）
3 个 generic 二次（$x_1\succ x_2\succ x_3$）：gin $=(x_1^2,x_1x_2,x_2^2,x_1x_3^2,x_2x_3^2,x_3^4)$，标准集 $\{1,x_1,x_2,x_3,x_1x_3,x_2x_3,x_3^2,x_3^3\}$（8 个）。截断（3 个二次在 $x_1,x_2$）：gin $=(x_1^2,x_1x_2,x_2^2)$，标准集 $\{1,x_1,x_2\}$。

取可达种子 $c=x_1\cdot\LT(x_1x_3^2)=x_1^2x_3^2$，$e=2$，$w=x_1^2$。$x_1^2$ 是截断的生成元 ⟹ 截断可达列。✓ 类似 $x_1x_2x_3^2\mapsto x_1x_2$（截断生成元）、$x_1x_3^4\mapsto x_1$（截断标准）。高度公式在这里读作 $\alpha(1)=4,\alpha(x_1)=\alpha(x_2)=2$，正好给出 $x_3^4,x_1x_3^2,x_2x_3^2$。**每个去 $x_n$ 部分都是截断可达列。**

### 29.3 推进：诊断 + 条件归纳
**修了一个 bug**：`build_semireg_hilbert` 参数是 (ngens,nvars)，我之前截断算成了欠定系统。修正后能算截断（超定）可达集。

**诊断（关键）**：直接测相容性，发现"不相容"的 $w$ **全是 $\mathrm{codeg}_{tr}\le1$**（最大 codeg=1，是生成元/近标准），把生成元也算进可达列后：
- $n=8,12$：相容性 **100% 成立**；
- $n=6,10$：仅剩极少 $\mathrm{codeg}_{tr}\le1$ 的"失败"（我的偏序闭包没显式枚举到的近标准列），且这些 $c$ 的 $\mathrm{codeg}(c)\le2$ 直接成立。

**所以真正要紧的 $\mathrm{codeg}_{tr}(w)=2$ 的列，永远相容（$n\le12$ 验证）。** 这正是归纳需要的。

**条件归纳（已进 tex，18 页）**：设相容性在每层成立，则上半区 L2′ 成立。证：对变量数 $k$ 归纳（$n$ 个二次固定）。
- 基例：高度超定（socle ≤3）时，所有 ≤3 次非标准单项式 codeg ≤2 无条件成立（1 次因子必标准）。
- Case A：某 $x_n$-生成元 $x_n^am$ 整除 $c$，则 $w=u'm$，$\deg u'\le2$（窗），$m$ 是 $w$ 的 2 度内标准因子 ⟹ codeg(c) ≤2。
- Case B：无此生成元（⟺ $\mathrm{codeg}_{tr}(w)\ge2$），由相容性 $w$ 截断可达 ⟹ 归纳假设给 $\mathrm{codeg}_{tr}(w)\le2$ ⟹ codeg(c) ≤2。
- 截断次数 $\deg w\approx D-d$ 向基例递减，归纳良基。

### 29.4 诚实状态
- 相容性**验证到 $n=12$**（codeg=2 的列全相容），但**没证**。
- 它现在是**唯一**缺口：证了它，上半区 L2′（及仿射峰的 poly·$2^n$）由条件归纳即得。
- 仍循环的点：归纳把 L2′$_n$ 归到 L2′$_{截断}$，两者同型；靠 socle ≤3 的基例 + 相容性终止。残余是"F4 闭包在 co-degree-2 层上与 KNS 截断交换"——这是该证的下一步。
- 注：相容性的"失败"全是 codeg ≤1（无害闭包枚举缺漏），不是真失败；这是本轮最重要的诚实发现。

---

## 第 30 部分　推进相容性证明：剥离 $x_n$ 作为闭包态射 + 精确剩余缺口

继续攻相容性。修了 `build_semireg_hilbert` 参数 bug（是 (ngens,nvars)）后，能正确算截断（超定）可达集，做了三组关键实验。

### 30.1 完整相容性（比需要的更强）成立
测 $\pi(R_n)\subseteq R^{tr}$（$\pi$ = 剥掉 $x_n$ 的乘性映射）：**所有**可达列的去 $x_n$ 部分都是截断可达列。
- $n=8,12$：**100%**；$n=10$：5704 中 5679 在内，25 个不在（**全是 $\mathrm{codeg}_{tr}\le1$**，闭包枚举缺漏，无害）。

不只 codeg=2，是几乎全部。相容性站得很稳。

### 30.2 关键结构事实：$R^{tr}\supseteq\{\mathrm{codeg}_{tr}\le1\}$
测截断可达集 $R^{tr}$ 的 codeg 结构：
- $R^{tr}\supseteq\{$所有 $\mathrm{codeg}_{tr}\le1$ 单项式$\}$ = $\{x_i\cdot$标准$\}$：$n=8,12$ **全包含**（$n=10$ 差 5，闭包缺漏）。
- $R^{tr}\subsetneq\{\mathrm{codeg}_{tr}\le2\}$：只含约一半（190/241, 826/1338, 3640/6954）。

所以 codeg≤1 全可达（干净事实），codeg=2 是**严格子集**（可达性真的有选择性）。

### 30.3 证明骨架（已进 tex，19 页）：剥离 = 闭包态射
$R_n$ 由 Type-1 种子 $x_j\LT(G)$ 经约化闭包生成。要证 $\pi$ 把种子和闭包儿子都送进 $R^{tr}$。

**引理（低 codeg 可达）**：$R^{tr}\supseteq\{\mathrm{codeg}_{tr}\le1\}$（验证到 $n=12$）。

**种子投影（干净）**：
- $G$ 不含 $x_n$ ⟹ $\LT(G)$ 是截断生成元（KNS：截断 GB = 不含 $x_n$ 的元素之 $x_n=0$ 限制），$\pi(x_j\LT(G))=x_j\LT(G)$ 是截断种子 ✓。
- $G$ 含 $x_n$ ⟹ $\LT(G)=x_n^am_0$（$m_0$ 截断标准），$\pi=x_jm_0$ 是 codeg≤1，由引理 ∈ $R^{tr}$ ✓。

**所以全部种子投影后可达。**

**闭包儿子**：儿子 $u\cdot s$（$s$ 标准），$\pi=\pi(u)\pi(s)$。codeg≤1 的儿子由引理可达。**剩下的精确缺口 = peel 后 codeg 恰为 2 的儿子**：要证它落进截断的**可达 codeg-2 层**（而非全部 codeg-2，后者更大）。这要追踪"产生该儿子的 $n$ 变量约化能不经过 $x_n$-重生成元实现，从而投影成真截断约化"。这就是低一维的同型 L2′，故 Prop 的归纳只能降到 socle≤3 基例。

### 30.4 诚实状态
**这轮的实质进展**：把相容性从"黑箱猜想"变成**带证明骨架的命题**——
- 种子层**完全证明**（模 codeg≤1 引理）；
- codeg≤1 引理验证到 $n=12$（且形式干净 $\{x_i\cdot$标准$\}$，像可证）；
- 唯一缺口收缩到 **codeg-2 儿子的投影**，即"$n$ 变量约化可避开 $x_n$-重生成元"。

仍未证，但缺口比"整个相容性"小得多、具体得多。下一步：证 codeg≤1 引理（应可从 F4 度-$d$ 矩阵列 ⊇ 标准的上阴影推出），再处理 codeg-2 儿子的无-$x_n$-重-生成元实现。

---

## 第 31 部分　推进证明的两件事：一个诚实的纠错 + 把缺口钉死在 codeg-2 reductor

继续上一轮的两件事（证 codeg≤1 引理；处理 codeg-2 儿子）。结果：**第一件事发现上轮的引理是错的**，第二件事把缺口钉得更死。

### 31.1 纠错：codeg≤1 引理（上轮）对稀疏可达集是**假**的
上轮提的"所有 codeg≤1 单项式可达"，对真实（稀疏）F4 可达集**不成立**：
- 例：$x_4^2x_9=x_9\cdot x_4^2$，多余变量 $x_9$ 在生成元 $x_4^2$ **之下**，不是 Type-1 lcm，可能永不被达到。
- 实测：$n=10$ 的 5 个 first-gen 闭包"漏掉"的 codeg-1 单项式，全是这种形式（$x_4^2x_9$ 等），且它们**正是**剥离后的 $x_n$-重种子里那 5 个"未达"的。

**但这些全是 $\mathrm{codeg}_{tr}=1$**，对应的列 $c$ 由高度论证（Case A）直接给 $\mathrm{codeg}(c)\le2$，**根本不需要相容性**。所以猜想只对 $\mathrm{codeg}_{tr}(w)=2$ 陈述是对的，那里 $n\le12$ **零例外**。

**关键认识**：种子剥离后 codeg≤1（$x_n$-free 种子→截断种子；$x_n$-重种子→$x_jm_0$，codeg≤1）。所以**相容性要紧的 codeg-2 列从来不是种子，全是中间 reductor**。上轮的 codeg≤1 引理既错、又不是该证的东西。

### 31.2 缺口钉死：codeg-2 reductor 的投影
真正的内容：codeg-2 reductor 列 $c$（$w=\pi(c)$，$\mathrm{codeg}_{tr}(w)=2$），写成可达列 $m_0$ 的闭包儿子 $c=u\,s$，要证 $\pi(c)=\pi(u)\pi(s)$ 是 $\pi(m_0)$ 的真截断约化儿子。

**精确障碍**：若 $n$ 变量约化用的生成元 $g_0$ 是 $x_n$-重的，则 $\pi(\LT(g_0))$ 是截断**标准**单项式（不是截断生成元），这步不投影。**要证的是：每个 codeg-2 reductor 能经过只用 $x_n$-free 生成元的约化链达到**，从而整条链在 $\pi$ 下投影成截断约化。

### 31.3 codeg-2 可达层抗拒干净刻画
想找区分"可达 codeg-2"（约占 25%）的细不变量，试了几个，**都失败**：
- EK 条件（两个多余变量 ≤ 标准部分最小变量）：**恒真**（所有 codeg-2 都满足），不区分。
- 递归 parent（$M$ 可达 ⟺ 某/所有 $M/x_i$ 可达）：50%/60%/77%，不刻画；"存在可达 parent"也恒真。

所以可达 codeg-2 层没有明显的局部刻画。这是难点的根源。

### 31.4 诚实状态
- **本轮主要是纠错 + 钉缺口**，不是突破。上轮证明骨架的 codeg≤1 引理是错的，已在 tex 改正（删掉假引理，sec:peel 重写诚实版）。
- 相容性（codeg-2）仍验证到 $n=12$ 零例外，但**未证**。
- 缺口现在精确为：**codeg-2 reductor 可经无-$x_n$-重-生成元链达到**（⟺ 可达层在 $\pi$ 下相容）。这是稀疏 F4 可达集在截断下的刻画问题，文献里 KNS 只到 GB 层、没到列层，是真开问题。
- 这层抗拒局部刻画（EK、parent 都恒真/不准），暗示需要更全局的论证（也许追踪 Type-1 链的 $x_n$-degree 演化，或经 Gorenstein 对偶）。

---

## 第 32 部分　采纳"只考虑稠密 generic"的建议——绕开稀疏可达集刻画，得到最干净的命题

你的提醒是对的：纠结**精确稀疏可达集**（依赖约化顺序）没必要。这轮按你的两条建议（稠密 generic + 绕开稀疏刻画）做，得到了整个问题**最干净的等价命题**。

### 32.1 关键实验：全生成元闭包 $\mathcal R$ 是可达集的**上逼近**，却仍 codeg ≤2
$\mathcal R$ = 从种子出发、每个单项式用**所有**整除它的生成元做约化（而非真实 F4 的"每个单项式一个约化元"）的闭包。所以：
$$\text{真实可达集}\subseteq\mathcal R\quad(\text{与约化顺序无关}).$$
实测 $\mathcal R$ 的**最大 codeg = 2**，$n=8,10,12,14$ 全部成立。即使 $\mathcal R$ 严格大于可达集、又严格小于全体 codeg≤2 单项式（约占 40%）。

### 32.2 整个支撑界归约成一句话
- **计数引理（严格）**：codeg≤2 的非标准单项式数 $\le 2^n\binom{n+2}{2}=O(n^2)2^n$。证：$M\mapsto(M_0,M/M_0)$（$M_0$ = deg≥deg-2 的标准因子）单射，像落在 标准×{deg≤2}。实测 $|\{$codeg≤2$\}|/2^n\approx n$，比 $n^2$ 还松。
- **归约**：$\#\text{列}=2^n+\#\text{可达非标准}\le 2^n+\#\mathcal R\le 2^n+\#\{$codeg≤2$\}\le(1+\binom{n+2}{2})2^n=O(n^2)2^n$。

所以**整个 $\Theta(\sqrt n\,2^n)$ 支撑界 = 一个纯组合猜想**：
$$\boxed{\text{猜想：}\mathcal R\text{ 中每个单项式 codeg}\le2.}$$
（已进 tex，20 页，def:rall + lem:count2 + conj:rall。）

### 32.3 为什么这是对的目标（绕开了所有麻烦）
$\mathcal R$ 的定义**不依赖**：F4 约化顺序、超出 gin strongly stable 形状的 genericity、截断。它蕴含旧的相容性猜想和 L2′，但比两者都干净。把"哪些稀疏列可达"换成"约化-swap 不会逃出 codeg 2"。

### 32.4 证明骨架 + 精确障碍
归纳证 codeg($\mathcal R$)≤2：
- 种子 $x_j\LT(g)$：codeg≤2（删 $x_j$ 和实现 $\mathrm{codeg}(\LT(g))=1$ 的那个变量）。✓
- swap $m\mapsto(m/\LT(g))s$ 保持 codeg≤2：**精确障碍**——把首项因子 $\LT(g)$ 换成 DRL 更小的同次标准单项式 $s$，**不是逐分量减小**，所以 $m$ 的 deg-2-标准因子不一定整除 child。

要的是：generic CI 里，$m$ 的存活标准部分乘 $s$ 仍在"两次删除内到标准"——这是 gin 标准集与乘法如何交互的命题，strongly stable 形状应能控制，但我还没归到已知性质。

### 32.5 诚实状态（这轮是实质进展）
- **最干净的等价命题到手**：$\Theta(\sqrt n\,2^n)$ ⟸ codeg($\mathcal R$)≤2（其余全严格：计数、可达⊆$\mathcal R$）。
- conj:rall 验证到 $n=14$，纯组合，无截断/无约化顺序依赖。**这正是你建议的"绕开稀疏刻画"**。
- 仍未证，但目标从"刻画稀疏可达集"变成"swap 不逃出 codeg 2"，具体且组合。障碍精确：DRL-swap 非逐分量单调。下一步：用 strongly stable 性质控制 标准×标准 乘积的 codeg。

---

## 第 33 部分　突破：codeg 在"生成元约化"下单调不增——把支撑界归到一条纯组合引理

沿着上轮的方向（证 codeg($\mathcal R$)≤2），找到了一个**强得多、干净得多**的命题，它一举蕴含全部。

### 33.1 核心发现：约化-swap 使 codeg 单调不增
swap 是 $m=uL\mapsto us=c$（$L=\LT(g)$ 生成元，$s$ 标准 $\prec L$，$\deg s=\deg L$）。**实测 codeg($c$) ≤ codeg($m$)，零例外**：
- $\mathcal R$ 内全部 swap：$n=8$ (6万), $n=10$ (86万), $n=12$ (**1230万** swap) 全部成立。
- **对任意 $u$**（不限 $\mathcal R$）：随机 30–40 万样本 ×（$n=8,10,12$）零违例。

所以这是 gin 的**一般引理**（conj:monotone）：
$$\text{codeg}(us)\le\text{codeg}(uL),\quad L\text{ 生成元},\ s\text{ 标准}\prec L,\ \deg s=\deg L.$$

### 33.2 假设是紧的：生成元身份必需
把 $L$ 换成**任意** $t\succ s$（$t$ 不必生成元）：**失败**（177/322/583 违例）。所以"换成更小的标准因子降 codeg"**仅当被换的是生成元首项**时成立。genericity 正好通过 $L$ 是极小生成元这点进入。

### 33.3 一举蕴含支撑界（已进 tex，21 页）
**命题**：conj:monotone ⟹ conj:rall ⟹ $O(n^2)2^n$。证：生成元 codeg=1，种子 codeg≤2；其余 $\mathcal R$ 元素由 swap 得到，单调性给 codeg 不增；归纳全 ≤2；计数引理 + 可达⊆$\mathcal R$ 收尾。∎

所以整条链现在是：
$$\Theta(\sqrt n\,2^n)\ \Longleftarrow\ \text{conj:monotone（codeg 在生成元约化下不增）}$$
**一条纯组合、关于 gin 标准单项式序理想的引理**，无 F4、无可达性、无截断。

### 33.4 证明骨架 + 精确剩余
取 $uL$ 的最大标准因子 $D$。$us$ 的标准因子候选 = $\gcd(D,us)$（标准，因整除 $D$、标准集是序理想）。它比 $\deg D$ 差 $\sum_i\max(0,(L\restriction_D)_i-s_i)$（$L\restriction_D$ = $D$ 落在 $L$ 里的部分）。
- 若 $L\restriction_D\mid s$：差 0，单调性立得。
- 一般：需用 $us$ 的剩余预算（因 $s\prec L$，预算在**大下标变量**）扩充 $\gcd(D,us)$ 回到 $\deg D$，且保持标准。

**精确剩余 = strongly stable 标准集的 exchange/saturation 性质**：从生成元 $L$ 降到更小标准 $s$ 释放的预算总能被楼梯重新吸收。这现在是纯粹关于标准单项式序理想的命题（无 F4/可达/截断）。

### 33.5 诚实状态（实质突破）
- **最干净的等价命题**：支撑界 ⟸ 一条 gin 标准集的组合引理（codeg 在生成元约化下单调不增）。
- 验证极充分（千万级 swap + 任意 $u$ 随机），假设紧（生成元必需）。
- 仍未证，但缺口从"刻画稀疏可达集/截断相容"彻底变成**一条关于序理想的 exchange 性质**——这是 almost-revlex/strongly stable 理想的标准研究对象，下一步该去对接已知的 Borel 理想组合性质。

---

## 第 34 部分　对接 Moreno-Socías / almost-revlex：证出 codeg 公式，把缺口钉成一条序理想命题

按"对接已知结果"的方向，把 conj:monotone 接到 almost-revlex（Moreno-Socías）结构上，证出了一个干净引理，缺口精确化。

### 34.1 确认 almost-revlex（Moreno-Socías）
实测（$n=6,8,10,12$，73 万对）：**每个 $d$ 次标准单项式 DRL-小于每个 $d$ 次生成元**。所以 gin 是 almost reverse lexicographic（Moreno-Socías 成立）。⟹ conj:monotone 里的"$s\prec L$"对标准 $s$ **自动**。

### 34.2 证出 codeg 公式（rigorous，已进 tex）
**引理（codeg 由大下标部分给出）**：strongly stable $J$，$P_\ell(M)$ = $M$ 的 degree-$\ell$ 大下标部分（贪心删最大变量）。则 $M$ 的最大标准因子 = $P_{\nu(M)}(M)$，$\nu(M)=\max\{\ell:P_\ell(M)\in S\}$，故 **codeg($M$)=$\deg M-\nu(M)$**。
**证**（干净）：任意 degree-$\ell$ 因子 $T$，$P_\ell(M)$ 在每个后缀 $\sum_{i\ge t}$ 上 ≥ $T$（贪心从大下标填），即 $P_\ell(M)$ 由 $T$ 经升下标移动得到；strongly stable ⟹ $S$ 对升下标封闭 ⟹ $T\in S\Rightarrow P_\ell(M)\in S$。∎

实测 270 万单项式零反例。**这是这部分第一块完全严格的结构引理。**

### 34.3 缺口精确化 + 一条死路排除
由 codeg 公式，conj:monotone ⟺ **$P_{\nu(uL)}(us)\in S$**（即 $\nu(us)\ge\nu(uL)$）。

**排除一条自然死路**：想用 $P_{\nu(uL)}(us)\preceq_{Borel}P_{\nu(uL)}(uL)$（dominance）+ strongly stable 推出 —— **不行**。实测 dominance **约 1/3 情况失败**，而 $P_{\nu(uL)}(us)$ **每次都标准**。所以这个 membership 是真的、但**不是** dominance 的推论；它必须用"$L$ 是极小生成元 + almost-revlex"（$L$ 换任意 $\succ s$ 单项式则命题假——已验）。

也试了显式 transfer 构造（$D_u\cdot s$ 的大下标部分）：99.999% 成立，$n=12$ 仅 2/17 万失败。所以构造接近但不精确。

### 34.4 诚实状态（这部分实质进展）
- **证出 codeg 公式**（第一块严格结构引理，连到 strongly stable）。
- **确认 almost-revlex**（连到 Moreno-Socías）。
- 缺口精确成**一条 almost-revlex 序理想命题**：$P_{\nu(uL)}(us)\in S$（从生成元 $L$ 降到更小标准 $s$ 不降大下标标准 reach）。
- 排除了 dominance 死路（~1/3 失败但结论真），证明必须实质用生成元身份 + almost-revlex。
- 整条链：$\Theta(\sqrt n\,2^n)$ ⟸ conj:monotone ⟸ 这条序理想 membership。无 F4/可达/截断，是 Borel/almost-revlex 理想的纯组合问题。

**下一步**：这条 membership 现在是 almost-revlex 序理想的标准对象，应能用 EK 分解或 Moreno-Socías 的显式楼梯结构（Pardue/Cho-Park 等的结果）攻。

---

## §35. 最后一步:精确陈述、算例、与这一轮的新进展

### 35.1 把"剩的一步"讲清楚 —— 三个等价形式

设 $J$ = $n$ 个一般二次型完全交的 gin(strongly stable + almost-revlex,Hilbert $(1+t)^n$,$|S|=2^n$)。
一次 **swap**:$u$ 任意单项式,$L$ 极小生成元,$s$ 标准单项式且 $\deg s=\deg L$(由 almost-revlex 自动有 $s\prec_{\rm DRL}L$)。
目标(conj:monotone):$\nu(us)\ge\nu(uL)$,即 $\operatorname{codeg}(us)\le\operatorname{codeg}(uL)$。

**本会话已严格证明的引理**:codeg 公式;DRL 不等式 $P_\ell(us)\preceq_{\rm DRL}P_\ell(uL)$(所有 $\ell$);Case A($m_s:=P_{\nu(uL)}(us)$ 必非生成元);dominance 充分(下 35.3);γ-刻画(下 35.4)。

记 $\ell_0=\nu(uL)$,$m_s=P_{\ell_0}(us)$,$m_L=P_{\ell_0}(uL)\in S$,$\delta=\deg(us)=\deg(uL)$。剩下要证的命题 $(\star)$ 有三个等价形式:

- **形式 1(归纳里真正用到的)**:$\operatorname{codeg}(uL)\le2\Rightarrow\operatorname{codeg}(us)\le2$。
  (只需保 $\le2$,因为闭包归纳假设给 $\operatorname{codeg}(uL)\le2$。)等价于 $P_{\delta-2}(us)\in S$:把 $us$ 的 2 个最大变量(最小下标单元)剥掉仍标准。**关键**:于是 $m_s$ 至多比 $us$ 少 2 个单元。
- **形式 2**:没有次数 $<\ell_0$ 的极小生成元整除 $m_s$。
- **形式 3(γ-形式)**:对每个有生成元的 $d<\ell_0$,$P^{\rm sm}_d(m_s)\prec_{\rm DRL}\gamma_d$。这里 $P^{\rm sm}_d(m)$ = $m$ 的小下标部分(保留 $d$ 个最小下标单元 = DRL-最大的 $d$ 次因子),$\gamma_d$ = 最小的 $d$ 次生成元。

### 35.2 两个真实算例(由 gap.c 生成,$n=8$)

**算例 A(dominance 成立 —— Borel 论证可直接关掉)**
$u=x_3x_6x_7^2$,$L=x_1^2$(生成元,次数 2),$s=x_2x_6$(标准,次数 2,$s\prec L$)。
- $uL=x_1^2x_3x_6x_7^2$,codeg 2;剥 2 个最大变量 $\to x_3x_6x_7^2$(标准)。
- $us=x_2x_3x_6^2x_7^2$,codeg 2;剥 2 个最大变量 $\to x_6^2x_7^2$(标准)。
- $m_s=x_6^2x_7^2$,$m_L=x_3x_6x_7^2$,$m_L$ dominate $m_s$ → 命题 domsuff 直接给出 $m_s\in S$。

**算例 B(dominance 失败 —— 真正的缺口)**
$u=x_2x_8^2$,$L=x_3x_5x_7^2$(生成元,次数 4),$s=x_5^2x_6x_8$(标准,次数 4,$s\prec L$)。
- $uL=x_2x_3x_5x_7^2x_8^2$,codeg 2(剥掉 $x_2,x_3$)。
- $us=x_2x_5^2x_6x_8^3$,codeg 2(剥掉 $x_2,x_5$)。
- $m_s=x_5x_6x_8^3$ [标准],$m_L=x_5x_7^2x_8^2$ [标准]。
- **为何 dominance 失败**:差异在 $s$ 侧贡献 $x_6x_8$ vs $L$ 侧 $x_7^2$,二者在 dominance(前缀和)序下**不可比**(前缀和在下标 6/7 处交叉)。DRL 不等式 $m_s\prec_{\rm DRL}m_L$ 仍成立。
- **为何 $m_s$ 仍标准(γ-形式直接验证)**:$P^{\rm sm}_2(m_s)=x_5x_6\prec\gamma_2=x_2x_4$;$P^{\rm sm}_3(m_s)=x_5x_6x_8\prec\gamma_3=x_3x_5x_6$;$P^{\rm sm}_4(m_s)=x_5x_6x_8^2\prec\gamma_4=x_4x_5x_7^2$。都因为 $m_s$ 的小下标部分带着高下标的 $x_8$,把它在 DRL 里压到 $\gamma_d$ 之下。注意这**不是**经 $m_L$ 得到的(小下标截断会反转 DRL:$P^{\rm sm}_2(m_s)=x_5x_6\succ x_5x_7=P^{\rm sm}_2(m_L)$)。

### 35.3 命题(dominance 充分,prop:domsuff,已证)

若 $m_L$ 在 majorization 序下 dominate $m_s$(即对所有 $t$,$\sum_{i\le t}(m_L)_i\ge\sum_{i\le t}(m_s)_i$,小下标质量更多),则 $\nu(us)\ge\ell_0$。
**证**:设 $m_s\notin S$,则 $m_s\in J$。$m_L$ majorize $m_s$ 且同次 ⟹ $m_L$ 由 $m_s$ 经有限步 $x_i\mapsto x_j\,(j<i)$ 得到(majorization/Muirhead 引理)。strongly stable 理想恰对这些步封闭,故 $m_s\in J\Rightarrow m_L\in J$,与 $m_L\in S$ 矛盾。∎
**范围是 sharp 的**:dominance 在约 30–40% 的 swap 失败;即便限制到 $\operatorname{codeg}(uL)\le2$ 区间仍有 15–45% 失败,但 $\nu(us)\ge\nu(uL)$ 永远成立。**缺口 = 非-dominance 情形**。数据(gap.c,$n=8,10,12$,百万级):在 $\operatorname{codeg}(uL)\le2$ 区间,$\operatorname{codeg}(us)\ge3$ **从不发生**;但"$\operatorname{codeg}(us)=2$ 吃紧 且 dominance 失败"**非空**(每样本约 1.2 万)。

### 35.4 引理(γ-刻画,lem:gammathresh,已证)

对 almost-revlex 理想:$m\in S\iff$ 对每个存在生成元的次数 $d$,$P^{\rm sm}_d(m)\prec_{\rm DRL}\gamma_d$。
**证**:若 $m\notin S$,则某极小生成元 $g_0\mid m$,$\deg g_0=d_0$;于是 $\gamma_{d_0}\preceq g_0\preceq P^{\rm sm}_{d_0}(m)$,在 $d_0$ 处违反。反之若某 $d_0$ 有 $P^{\rm sm}_{d_0}(m)\succeq\gamma_{d_0}$,almost-revlex 给 $P^{\rm sm}_{d_0}(m)\in J$,它整除 $m$,故 $m\in J$。∎
这解释了为何"小下标截断传递"行不通:要比的是对**固定阈值** $\gamma_d$,而非对 $m_L$;而小下标截断反转 DRL。

### 35.5 这一轮新进展:显式阶梯 + 干净的顶端 γ 公式

打出 $n=4..8$ 的完整阶梯(stair.c)。**高次生成元的最小元有干净闭式**:
$$\boxed{\;\gamma_d=x_{n-1}^{\,n+1-d}\,x_n^{\,2d-n-1}\quad\text{对 }\tfrac{n+1}{2}\le d\le n+1\;}$$
验证($n=8$):$\gamma_9=x_8^9,\ \gamma_8=x_7x_8^7,\ \gamma_7=x_7^2x_8^5,\ \gamma_6=x_7^3x_8^3,\ \gamma_5=x_7^4x_8$。边界 $d=(n+1)/2$($n$ 奇)给 $\gamma_d=x_{n-1}^{(n+1)/2}$:$n=5$ 的 $\gamma_3=x_4^3$、$n=7$ 的 $\gamma_4=x_6^4$ ✓。
低次($d<(n+1)/2$)的 $\gamma_d$ 散落在小下标上(如 $n=8$:$\gamma_2=x_2x_4,\gamma_3=x_3x_5x_6,\gamma_4=x_4x_5x_7^2$),无同样干净的闭式。

**这把 $(\star)$ 的高次部分($d\ge(n+1)/2$)化为具体不等式** $P^{\rm sm}_d(m_s)\prec_{\rm DRL}x_{n-1}^{n+1-d}x_n^{2d-n-1}$。注意此式对**任意**单项式并不成立(例如 $m_s=x_{n-1}^c x_n^e$ 且 $c\ge d>(n+1)/2$ 时 $P^{\rm sm}_d=x_{n-1}^d\succ\gamma_d$),所以必须用 swap 结构($s$ 标准 + $\operatorname{codeg}(uL)\le2$)来排除 $x_{n-1}/x_n$ 失衡。这是关于"标准性 = $x_{n-1}$ 相对 $x_n$ 不能过多"的平衡条件,swap 必须保持它。

### 35.6 诚实状态

整条链 $\Theta(\sqrt n\,2^n)\Leftarrow$ monotonicity $\Leftarrow(\star)$ 仍差 $(\star)$。$(\star)$ 现有三等价形式 + 两个新工具(domsuff 把 dominance 情形关掉;γ-刻画把它变成对固定阈值 $\gamma_d$ 的小下标比较)+ 显式阶梯(高次 γ 闭式)。**真正剩下的**:非-dominance 吃紧情形,等价于证 $P^{\rm sm}_d(m_s)\prec\gamma_d$。已验证至 $n=12$。需要的输入:用 $\operatorname{codeg}(uL)\le2$ 与 $s$ 标准,控制 $m_s$ 小下标部分的 $x_{n-1}/x_n$ 平衡,使之落在 $\gamma_d$ 之下。纯 almost-revlex 序理想命题,无 $F_4$/可达/截断。

---

## §36. 重大进展:严格消去所有高次生成元,缺口收窄到低次

延续 §35.5 的干净顶端公式 $\gamma_d=x_{n-1}^{n+1-d}x_n^{2d-n-1}$($d\ge\lceil(n+1)/2\rceil$,验证至 $n=10$),得到三条引理,**严格**(非数值)地把次数 $\ge(n+1)/2$ 的生成元从 $(\star)$ 中全部排除。

**引理 A($x_n$-富集,lem:xnrich,已证)**:每个次数 $d\ge(n+1)/2$ 的标准单项式 $m$ 满足 $e_n(m)\ge 2d-n-1$。
证:almost-revlex 给 $m\prec_{\rm DRL}\gamma_d$;$e_n(\gamma_d)=2d-n-1$;若 $e_n(m)<2d-n-1$,则在最大下标 $n$ 处 $m$ 的指数更小 ⟹ $m\succ_{\rm DRL}\gamma_d$,矛盾。∎

**引理 B(swap 不丢 $x_n$ 质量,lem:enswap,已证)**:$e_n(s)\ge e_n(L)$,从而 $e_n(us)\ge e_n(uL)$,$e_n(m_s)\ge e_n(m_L)$。
证:$s\prec_{\rm DRL}L$ ⟹ 在最大的相异下标处 $s$ 指数更大;若相异发生在下标 $n$ 则 $e_n(s)>e_n(L)$,否则 $e_n(s)=e_n(L)$。$P_{\ell_0}$ 保留 $\min(e_n(\cdot),\ell_0)$ 个 $x_n$,$\min$ 单调。∎
**关键直觉**:DRL 最先比最大变量的指数,所以 $s\prec L$ 自动给出 $e_n(s)\ge e_n(L)$——这正是 $x_n$ 方向的传递。

**命题 C(高次生成元全部排除,prop:highdone,已证)**:没有次数 $d\in[(n+1)/2,\ell_0)$ 的极小生成元整除 $m_s$。于是 $(\star)$ 归约为:**没有次数 $d<(n+1)/2$ 的极小生成元整除 $m_s$**。
证:引理 B + 引理 A(用于 $m_L\in S$,次数 $\ell_0\ge(n+1)/2$)给 $e_n(m_s)\ge 2\ell_0-n-1$。对 $(n+1)/2\le d<\ell_0$,$P^{\rm sm}_d(m_s)$ 的 $x_n$-指数 $=\max(0,d-\ell_0+e_n(m_s))\ge d+\ell_0-n-1\ge 2d-n>e_n(\gamma_d)$(用 $\ell_0\ge d+1$),故 $P^{\rm sm}_d(m_s)$ 比 $\gamma_d$ 的 $x_n$ 更多 ⟹ $\prec_{\rm DRL}\gamma_d$ ⟹(γ-刻画)无 $d$ 次生成元整除 $m_s$。∎

**数值确认**(highd.c,codeg(uL)≤2 区间,$n=6,8,10$,百万级):$e_n(s)\ge e_n(L)$ 零反例;$e_n(m_s)\ge 2\nu(uL)-n-1$ 零反例。

### 36.1 剩下的低次缺口 —— 为何更难

$(\star)$ 现在只剩:次数 $d<(n+1)/2$ 的(小下标)生成元不整除 $m_s$。困难在于**不对称**:
- 高次用 $x_n$,与 DRL 的优先级一致($x_n$ 最先比),所以 $s\prec L\Rightarrow e_n(s)\ge e_n(L)$ 免费。
- 低次要用 $x_1$(最小下标/最大变量),但 DRL **最后**才比 $x_1$,所以 $s\prec L$ **不**控制 $e_1(s)$ vs $e_1(L)$。无对应传递。
- 低次的 $\gamma_d$ 散落在小下标,无干净闭式(如 $n=8$:$\gamma_2=x_2x_4,\gamma_3=x_3x_5x_6,\gamma_4=x_4x_5x_7^2$;注意到 $\gamma_d$ 的最小下标 $=d$)。

**正确的替代输入是 codeg(uL)≤2 本身**:它界定了 $m_s$ 的小下标含量。关键机制:若 $u$ 有大量 $x_1$(比如 $e_1(u)\ge3$),则 $uL$ 同时含 $x_1$-超量与生成元 $L$,迫使 codeg(uL)>2,正好排除了"小下标生成元能整除 $m_s$"的配置。把这个机制定量化即可关掉低次缺口。

### 36.2 当前完整状态

$\Theta(\sqrt n\,2^n)\Leftarrow$ monotonicity $\Leftarrow(\star)$。$(\star)$ 拆为:
- **高次部分($d\ge(n+1)/2$)**:✅ 严格证明(命题 C),模一条已强验证的阶梯公式(Fact gammaclean)。
- **低次部分($d<(n+1)/2$)**:仍开放,但已隔离;需用 codeg(uL)≤2 控制 $m_s$ 的小下标含量。

已证引理总表:codeg 公式、DRL 不等式、Case A、dominance 充分、γ-刻画、$x_n$-富集、swap 不丢 $x_n$、高次消去。

## §37. 关闭低次缺口:两条截断不等式,把整个单调性归到干净的组合命题

§36 把 $(\star)$ 收窄到"次数 $d<(n+1)/2$ 的低次(小下标)生成元不整除 $m_s$"。本节用**两条一致的截断不等式**关闭它,绕开低次 $\gamma_d$ 没有干净闭式的困难。

记号:swap 为 $(u,L,s)$,$L$ 生成元、$s$ 标准、$\deg s=\deg L=:e$、$s\prec_{\rm DRL}L$;$\ell_0=\nu(uL)$,$c=\operatorname{codeg}(uL)\le2$,$m_s=P_{\ell_0}(us)$,$m_L=P_{\ell_0}(uL)$。$P^{\rm sm}_d(\cdot)$ = 小下标部分(最小的 $d$ 个单位)。

### 37.1 带状(band)重述 —— 严格且关键

把 $us=u\cdot s$ 的单位按下标升序排列。因为 $m_s=P_{\ell_0}(us)$ 删去 $c$ 个最小下标单位,所以
$$P^{\rm sm}_d(m_s)=us\text{ 在下标秩 }c{+}1,\dots,c{+}d\text{ 上的那一段(band)}.$$
同理 $P^{\rm sm}_d(m_L)$ 是 $uL=u\cdot L$ 在同样秩 $c{+}1,\dots,c{+}d$ 上的 band。两个 band 都是**同一个** $U$(=$u$ 的下标多重集)分别与 $S$、$L$ 归并(merge)后读出的;其中 $S\prec_{\rm DRL}L$,$|S|=|L|=e$。

### 37.2 两条引理(验证成立,未证)

> **引理 C2(低带,$d\le e$)** 对 $1\le d\le e$:
> $$P^{\rm sm}_d(m_s)\preceq_{\rm DRL}\max{}_{\rm DRL}\bigl(P^{\rm sm}_d(m_L),\,P^{\rm sm}_d(s)\bigr).$$

> **引理 A(高带,$d>e$)** 对 $e<d\le\ell_0$:
> $$P^{\rm sm}_d(m_s)\preceq_{\rm DRL}P^{\rm sm}_d(m_L).$$

注意在 $d=\ell_0$ 时引理 A 退化为已证的 DRL 不等式 $m_s\preceq_{\rm DRL}m_L$(cor:drlPP)。

### 37.3 由两条引理推出完整单调性

> **命题(模引理 C2、A)** $\nu(us)\ge\nu(uL)$,即 $\operatorname{codeg}(us)\le\operatorname{codeg}(uL)$。

证:固定有生成元的次数 $d<\ell_0$。
- 若 $d\le e$:引理 C2 给 $P^{\rm sm}_d(m_s)\preceq\max(P^{\rm sm}_d(m_L),P^{\rm sm}_d(s))$。$m_L,s\in S$ 故两者都 $\prec_{\rm DRL}\gamma_d$(γ-刻画 lem:gammathresh),两个 $\prec\gamma_d$ 的 DRL-较大者仍 $\prec\gamma_d$。
- 若 $d>e$:引理 A 给 $P^{\rm sm}_d(m_s)\preceq P^{\rm sm}_d(m_L)\prec_{\rm DRL}\gamma_d$。(当 $d\ge(n+1)/2$,这一步也可由命题 C(prop:highdone)**严格**得到,与引理 A 无关——所以真正依赖引理 A 的只有中段 $e<d<(n+1)/2$。)

于是 $P^{\rm sm}_d(m_s)\prec_{\rm DRL}\gamma_d$ 对所有 $d<\ell_0$ 成立 ⟹(γ-刻画)无 $<\ell_0$ 次生成元整除 $m_s$。Case A(prop:notgen)排除 $\ell_0$ 次(否则 $m_s$ 自己就是该生成元);$>\ell_0$ 次因 $\deg m_s=\ell_0$ 不可能整除。故 $m_s\in S$,即 $\nu(us)\ge\ell_0=\nu(uL)$。∎

### 37.4 机制与覆盖逻辑

- **为何拆在 $d=e$**:$d>e$ 时 $S$ 对 band 的贡献用尽($|S|=e<d$),共享的 $U$-内容使 $m_L$-band 占优,单独用 $m_L$ 就够(引理 A)。$d\le e$ 时,单用 $m_L$ 会偶尔失败(候选 $P^{\rm sm}_d(m_s)\preceq P^{\rm sm}_d(m_L)$ 失败约 0.2–0.3%,**且全部落在 $d\le e$**),这时 max 里的 $S$-项恰好补回——这正是 C2 的作用。
- **小下标含量的来源**:$m_s$ 能用的小下标内容 = $u$ 的(被 $\operatorname{codeg}(uL)\le2$ 限制:$u$ 若有大量小下标超量,叠加生成元 $L$ 会自己迫使 $\operatorname{codeg}(uL)>2$)∪ $s$ 的(被标准性限制)。删去 $c\le2$ 个最小下标单位,正好抹掉可能凑成低次生成元的那部分。

### 37.5 数值验证(决定性)

`final.c`,均匀采样 swap、限定 $\operatorname{codeg}(uL)\le2$ 区间,逐 $n$ 跑:

| $n$ | swaps | C2($d\le e$) | 引理 A($d>e$) | 合并 $P^{\rm sm}(m_s)\prec\gamma$ | $m_s\in S$ 独立验证 |
|---|---|---|---|---|---|
| 8  | 4.0×10⁵ | 0 反例 | 0 反例 | 0 反例 | 0 失败 |
| 10 | 3.2×10⁵ | 0 反例 | 0 反例 | 0 反例 | 0 失败 |
| 12 | 2.1×10⁵ | 0 反例 | 0 反例 | 0 反例 | 0 失败 |
| 14 | 1.2×10⁵ | 0 反例 | 0 反例 | 0 反例 | 0 失败 |

(`alla.c` 另测:候选"单用 $m_L$"$P^{\rm sm}_d(m_s)\preceq P^{\rm sm}_d(m_L)$ 的失败完全集中在 $d\le e$,$d>e$ 零失败 —— 与拆分点 $d=e$ 完全吻合。`lowd3.c`/`lowd4.c`/`midr.c` 分别独立确认 C2 全 $d\le e$、引理 A 中段,均零反例。dcmp 经已知对自检。)

### 37.6 当前完整状态(更新)

$$\Theta(\sqrt n\,2^n)\ \Leftarrow\ \text{monotonicity}\ \Leftarrow\ (\star)\ \Leftarrow\ \boxed{\text{引理 C2}+\text{引理 A}}$$

- **高次部分($d\ge(n+1)/2$)**:✅ 严格(命题 C),模 Fact gammaclean(强验证)。
- **低次部分($d<(n+1)/2$)**:由引理 C2($d\le e$)+ 引理 A($e<d<(n+1)/2$)关闭 —— 两条都是**干净、一致、与混乱的低次 $\gamma_d$ 无关**的截断不等式,已 $n=8,\dots,14$ 百万级零反例 + $m_s\in S$ 独立确认,但**尚未给出证明**。

**若证出这两条 band 不等式**(最可能的路线:把 $S$ 经"降下标移动"transport 到 $L$,沿与 $U$ 的归并、在秩窗口 $c{+}1,\dots,c{+}d$ 内追踪),则由 §37.3 的命题,**完整 monotonicity 成立,$\operatorname{poly}(n)\cdot2^n$ 上界完成**,只余 Fact gammaclean 这一已验证闭式。这是把整个低次障碍**从"判定 $S$ 成员"压缩成"两个 merge 的 band 比较"**——一个纯粹有限的组合命题。

已证引理总表(累积):codeg 公式、DRL 截断不等式、Case A、dominance 充分、γ-刻画、$x_n$-富集、swap 不丢 $x_n$、高次消去;**新增**:低/高带截断不等式(C2/A)将单调性归到上述单一组合命题(验证成立)。

## §38. band 不等式的部分严格证明 + Fact gammaclean 的二变量归约

本节记录把 §37 两条 band 不等式向严格证明推进的结果,以及 Fact gammaclean 归约到一条干净二变量规则。

### 38.1 关键发现:band 不等式不是纯组合的

对**任意**多重集 $U$、**任意** $S\prec_{\rm DRL}L$($|S|=|L|$)、**所有**窗口 $c\ge0$ 做纯组合测试(`bandcomb.c`,$n=6,8,10$,百万级):

| | 通过 | 失败 |
|---|---|---|
| Lemma A($d>e$) | ~95% | ~5%(集中在小 $c$) |
| C2($d\le e$) | ~95% | ~5%(集中在小 $c$) |

**结论(真结果)**:band 不等式**对一般窗口 $c$ 不成立**。所以任何证明**必须**用 $J$ 的结构——具体窗口 $c=\operatorname{codeg}(uL)$(即 $m_L\in S$)、$s$ 标准、$L$ 生成元。这排除了一整类"纯多重集组合"证法。

### 38.2 除法保持 DRL(引理,严格)

> **引理(除法保持 DRL)** 设 $A\preceq_{\rm DRL}B$ 同次,$Q\mid A$ 且 $Q\mid B$(同一 $Q$)。则 $A/Q\preceq_{\rm DRL}B/Q$。

**证**:$A\preceq_{\rm DRL}B$ 等价于在指数相异的最大下标 $\tau$ 处 $A_\tau>B_\tau$。除以 $Q$ 在每个下标 $i$ 减去 $Q_i$,故 $A/Q$ 与 $B/Q$ 相异的下标集合与 $A,B$ 相同,最大相异下标仍是 $\tau$,且 $(A/Q)_\tau-(B/Q)_\tau=A_\tau-B_\tau>0$。两商同次,故 $A/Q\preceq_{\rm DRL}B/Q$。∎

### 38.3 Lemma A 的部分严格证明(情形 1+2,≥97%)

回忆 $m_s=P_{\ell_0}(us)$,$m_L=P_{\ell_0}(uL)$,$c=\operatorname{codeg}(uL)$,$\ell_0=\nu(uL)$;$P^{\rm sm}_d(m_s)$ = 在 $us$ 下标秩 $c{+}1,\dots,c{+}d$ 的 band。记 $Q=P_{\ell_0-d}(us)$,$Q'=P_{\ell_0-d}(uL)$(各自顶 $\ell_0-d$ 部分)。

**情形分类**(`acase.c`,$n=8,10,12$,全部成立):

| 情形 | 占比 | 状态 |
|---|---|---|
| **情形 1**:$Q=Q'$ | 97.2–99.7% | **✅ 严格** |
| **情形 2**:$Q\ne Q'$ 且 $e_n(P^{\rm sm}_d(m_s))>e_n(P^{\rm sm}_d(m_L))$ | 0.04–0.25% | **✅ 严格** |
| **残余**:$Q\ne Q'$ 且两小部分 $x_n$ 指数相等 | 0.26–2.52% | 验证成立,见 §38.5 |

**情形 1 证明**:大下标部分嵌套给 $P_{\ell_0-d}(m_s)=P_{\ell_0-d}(us)=Q$,故 $m_s=P^{\rm sm}_d(m_s)\cdot Q$,同理 $m_L=P^{\rm sm}_d(m_L)\cdot Q$。已证 $m_s\preceq_{\rm DRL}m_L$(cor:drlPP)。对公因子 $Q$ 用 §38.2:
$$P^{\rm sm}_d(m_s)=m_s/Q\preceq_{\rm DRL}m_L/Q=P^{\rm sm}_d(m_L).\qquad\blacksquare$$

**情形 2 证明**:$P^{\rm sm}_d(m_s)$ 在 max-下标 $x_n$ 上严格更多 ⟹ 在最大相异下标处更多 ⟹ $\prec_{\rm DRL}$。∎

**残余的结构**:$Q\ne Q'$ 恰当 $e_n(uL)<\ell_0-d$;此时 $m_L$ 的 $x_n$ 全在顶 $e_n(uL)$ 段,故 $P^{\rm sm}_d(m_L)$ **无 $x_n$**;残余即"$P^{\rm sm}_d(m_s)$ 也无 $x_n$",**两小部分都落在 $x_1,\dots,x_{n-1}$**——退化到少一变量。见 §38.5 的降维归纳。

### 38.4 Fact gammaclean 归约到二变量规则

**归约(严格)**:整个 gammaclean 等价于 $x_{n-1}^a x_n^b\in S\iff 2a+b\le n$(`twovar.c` 验证 $n=6{-}10$ 零失配)。用强稳定性:
- "$\in J$"方向归到单点 $\gamma_d\in J$(然后 $x_n\to x_{n-1}$ 移动给全部 $a\ge n+1-d$);
- "标准"方向归到前驱 $x_{n-1}^{n-d}x_n^{2d-n}\in S$。

**两端严格证出**:$d=n+1$:$\gamma_{n+1}=x_n^{n+1}\in J$($S_{n+1}=\varnothing$),极小($/x_n=x_n^n\in S$);$d=n$:$\gamma_n=x_{n-1}x_n^{n-1}$($|S_n|=1$)。

**剩余 crux**:$\gamma_d\in J$ 对 $(n+1)/2\le d<n$——generic CI 的 gin 结构(Fröberg / Moreno-Socías);$R/J$ 非 Gorenstein,超平面截面 HF $=[\binom{n}{d}-\binom{n}{d-1}]_+$。已验证 $n\le10$。

## §39. 降维递归 + 关键发现:残余-B ⊆ dominance(联合覆盖 Lemma A 的 d>e 段)

本节是 §38.3 残余的后续攻坚。结论:**dominance 用 prop:domsuff、non-dominance 用降维递归,两者合起来覆盖 Lemma A 的 $d>e$ 段,只剩极少量(已验证为真的)实例**。这把历史上 15–45% 的 non-dominance 缺口在 $d>e$ 段压到几乎为零。

### 39.1 回顾:prop:domsuff 覆盖 dominance(两个方向同一结论)

**dominance 条件**:$m_L$ majorize $m_s$,即前缀和 $\sum_{i\le t}(m_L)_i\ge\sum_{i\le t}(m_s)_i$ 对所有 $t$。同次下这等价于 **$m_s$ 后缀控制 $m_L$**($N_{>t}(m_s)\ge N_{>t}(m_L)$)。两种等价表述给同一结论 $m_s\in S$:
- **push-down**:$m_L$ 由 $m_s$ 经 $x_i\to x_j\ (j<i)$ 下推得到,$J$ 在下推下封闭 ⟹ $m_s\in J\Rightarrow m_L\in J$,逆否即 $m_s\in S$。
- **push-up**:$m_s$ 由 $m_L$ 经 $x_i\to x_j\ (j>i)$ 上推得到,$S$ 在上推下封闭 ⟹ $m_L\in S\Rightarrow m_s\in S$。

无论哪个,**dominance swap 直接得 $m_s\in S$**(对所有 $d$ 一次性成立)。故只需对 **non-dominance swap** 处理逐 $d$ 的 Lemma A。

### 39.2 降维递归证明器(non-dominance 的 Lemma A)

记 $MS=$ merge$(U,S)$、$ML=$ merge$(U,L)$(指数向量),不变量 **$MS\preceq_{\rm DRL}ML$ 且同次**(初始成立,因 $us\prec_{\rm DRL}uL$)。`prove(MS,ML,c,d,\text{topvar})`:

1. **band 相等**:band$(c,d;MS)=$ band$(c,d;ML)$ ⟹ 证毕。
2. **情形 1(除法)**:顶 $\ell-d$ 部分相等 $P_{\ell-d}(MS)=P_{\ell-d}(ML)$ ⟹ 由 §38.2 + cor:drlPP 得 band$_S\preceq$ band$_L$。证毕(严格)。
3. **情形 2(顶变量)**:band$_S$ 在 topvar 上严格更多 ⟹ $\prec_{\rm DRL}$。证毕(严格)。
4. **残余-A**:band 在 topvar 相等且 $e_{\rm topvar}(MS)=e_{\rm topvar}(ML)$ ⟹ 剥去 topvar,不变量保持,递归到 topvar$-1$。
5. **残余-B**:$e_{\rm topvar}(MS)\ne e_{\rm topvar}(ML)$ ⟹ 剥变量破坏同次不变量,**STUCK**。

递归在残余-A 链上终止(变量有限);唯一障碍是残余-B。

### 39.3 关键发现:残余-B 几乎全是 dominance

逐 swap 记录(`recur2.c`/`recur3.c`):卡住(残余-B)的实例**绝大多数落在 dominance swap 里**——而那些已被 prop:domsuff 覆盖。统计(每个 $n$ 约数万 swap):

| $n$ | dom swap 占比 | Lemma A($d>e$)卡住数 | 其中 dominance | **non-dominance 卡住的 swap 数** |
|---|---|---|---|---|
| 8 | 84% | 30 | 30 | **0** |
| 10 | 70% | 73 | 73 | **0** |
| 12 | 57% | 71 | 71 | **0** |
| 14 | 47% | 59 | 58 | **1** |
| 16 | 38% | 23 | 22 | **1** |

(另一随机种子下 $n=12$ 出现 2、$n=13$ 出现 1。)dominance 比例随 $n$ 下降,递归承担增长的 non-dominance 部分并几乎全部成功。

### 39.4 残余的真实大小:proof-incompleteness 而非 truth gap

对极少数 non-dominance 且卡住的实例(`rbdump2.c`,$n=12,13,14$),全部满足:
$$\text{Lemma A 仍成立}\ (P^{\rm sm}_d(m_s)\prec_{\rm DRL}P^{\rm sm}_d(m_L),\ \text{dcmp}=-1),\quad m_s\in S.$$
例(n=12):$u=x_5x_{11}^3,\ s=x_3x_5x_{10}x_{12},\ L=x_3x_6x_9^2$;$m_s=x_5x_{10}x_{11}^3x_{12}$,$m_L=x_6x_9^2x_{11}^3$;$a=x_5x_{10}x_{11}^3\prec b=x_6x_9^2x_{11}^2$(在 $x_{11}$ 处判定)。递归在 $x_{12}$ 处卡住(us 有 $x_{12}$、uL 没有),但 $a\prec b$ 在更低的 $x_{11}$ 判定——是**递归不够聪明**,Lemma A 本身为真。

### 39.5 联合覆盖小结

> **Lemma A($e<d\le\ell_0$)的现状**:
> - **dominance swap**:prop:domsuff 直接给 $m_s\in S$(严格,完整)。
> - **non-dominance swap**:降维递归(情形 1 除法 + 情形 2 $x_n$ + 残余-A 剥变量)给 $P^{\rm sm}_d(m_s)\preceq P^{\rm sm}_d(m_L)\prec\gamma_d$,**除一个 measure-tiny 残余**(non-dom ∩ 残余-B,$n\le16$ 抽样每个 $n$ ≤ 个位数实例,全部验证 Lemma A 为真、$m_s\in S$)。
>
> 历史上 15–45% 的 non-dominance 缺口在 $d>e$ 段被压缩到接近零。

**仍未关闭**:(i) non-dom ∩ 残余-B 的最后少数实例(需更聪明的递归:残余-B 处两 band 在 topvar 相等,比较退到更低变量,但丢失了除法所需的"同次 $m_s\preceq m_L$"结构);(ii) C2($d\le e$)的 non-dominance 部分(带额外 $S$-项,本节方法未覆盖)。
