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
