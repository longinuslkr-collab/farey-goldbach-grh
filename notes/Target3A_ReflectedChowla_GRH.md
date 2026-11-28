# Dirichlet GRH 下素数反射 Möbius 相关的减号总装

固定任意奇素数 \(r_1<r_2\)。所有估计均可依赖这对素数。令 \(p\) 为趋于无穷的素数，\(\Delta=r_2-r_1\)，\(L=\log p\)，\(e(x)=\exp(2\pi i x)\)。第 1–7 节给出物理配对、历史矩和小弧估计。第 8 节核对同一弧核及局部投影下的主弧估计，第 9 节推回反射相关。Lean 证书验证代数、参数和条件推论。

## 1. 物理范围和单一弧核

写 \(u_0=p-r_1s_0\)、\(v_0=p-r_2s_0\)，则 \(r_2u_0-\Delta p=r_1v_0\)。对 \(u_0\) 的 Type II 分解取 \(u_0=m(n/r_2)\)，把 \(r_2\) 放进第二系数。模 \(r_1\) 分块后，固定 \(i\in\mathbb F_{r_1}^{\times}\) 并要求
\[
m,r\equiv i,\qquad n,s\equiv r_2p\,i^{-1}\pmod{r_1},\qquad n,s\equiv0\pmod{r_2}. \tag{1}
\]
采用 \((M,2M]\)、\((N,2N]\) 的盒，\(X=MN\)，\(M,N\ge p^\delta\)，\(X\ll_{r_1,r_2}p\)。只处理原物理正值范围非空的盒，因此 \(4X\ge\Delta p\) 且 \(X\asymp_{r_1,r_2}p\)。盒内权为 \(\alpha_m,\beta_n\)，大小均 \(\ll L^C\)，其中 \(\alpha_m\) 仅支撑于 \(z\)-粗数，\(z=\exp(L^\zeta)\)，\(\beta<\zeta<1\)。\(z\)-粗表示无素因子 \(\le z\)，\(\beta\) 作为指数时与带下标的系数区分。

设 \(\mathcal P_i=(e^{\lambda_i},e^{2\lambda_i}]\cap\mathbb P\) 为 \(k\) 个分离素数区间，\(\lambda_1\ge L^\alpha\)，\(\lambda_k\ll L^\beta\)，\(\lambda_{i+1}\ge8\lambda_i\)。设 \(\mathcal A\) 为每区间取一个素数所得乘积集，\(V_i=\sum_{\ell\in\mathcal P_i}\ell^{-1}\asymp1\)，\(V=\prod_i V_i\)。取 Lichtman §6 的固定平滑母函数 \(\eta\in C_c^\infty([1,4])\) 并令 \(\eta_Y(t)=\eta(t/Y)\) 为支撑于 \([Y,4Y]\) 的有界非负平滑分割权（从而具有一致全变差界），\(Y\) 为二进尺度。活跃素数均大于 \(r_1,r_2,\Delta\) 且小于 \(p\)。非空尺度满足 \(\lambda_1-O(1)\le\log Y\ll_k L^\beta\)，故 \(Y=p^{o(1)}\)、\(Y=o(z)\)。

在提取 \(v_0\) 的活跃素因子后，令
\[
S_Y(Q_0)=\sum_{\substack{a\in\mathcal A,\ m,n\\mn-\Delta p=a r_1 Q_0}}
\eta_Y(a)\alpha_m\beta_n.
\]
原和在此尺度为 \((-1)^k\sum_{Q_0>0}c(Q_0)S_Y(Q_0)\)，\(|c(Q_0)|\le1\)。正余因子的个数为 \(O(X/Y)\)。Cauchy–Schwarz 给出
\[
|T_Y|^2\ll \frac XY\sum_{Q_0>0}|S_Y(Q_0)|^2
\le \frac XY\sum_{Q_0\in\mathbb Z}|S_Y(Q_0)|^2 . \tag{2}
\]
第二步使用平方项非负。记扩大后的归一化平方和为 \(Q^{\rm raw}_{Y,p}=V^{-2}\sum_{\mathbb Z}|S_Y(Q_0)|^2\)。其展开保留共同的整数 \(Q_0\)。整数余因子等价式只用于这一扩大后的和。

两条余因子等式模 \(r_2\) 分别给出 \(a r_1Q_0\equiv-\Delta p\equiv r_1p\) 及 \(b r_1Q_0\equiv r_1p\)。由于 \(p,r_1\) 是模 \(r_2\) 的单位，\(Q_0,a,b\) 均为单位，并且
\[
a\equiv b\equiv p\,Q_0^{-1}\pmod{r_2}. \tag{3}
\]
从此在所有弧和物理算子中都实施 (1) 和 \(a\equiv b\bmod r_2\)。在扩大后的原始项上，这个附加投影由 (3) 自动满足。

置 \(t=bmn-ars\)、\(Z=\Delta Y\)、\(B=L^{A_0}\)。取固定偶函数 \(\psi\in C_c^\infty(\mathbb R)\)，\(0\le\psi\le1\)，在 \([-3,3]\) 恒为 1，支撑于 \([-4,4]\)。对 \(p\mid t\) 的项令 \(u=t/p\) 并定义
\[
K_{\mathcal I}(u;a,b)=\psi(u/Z)\int_{\mathcal I}e\big(\theta[u-\Delta(b-a)]\big)\,d\theta ,
\quad \mathcal I\in\{\mathbb T,\mathfrak M,\mathfrak m\}. \tag{4}
\]
其中 \(\mathfrak M=\bigcup_{q\le B,(h,q)=1}\{\|\theta-h/q\|\le 2B/Z\}\)，\(\mathfrak m=\mathbb T\setminus\mathfrak M\)，Haar 测度归一为 1。对 \(p\nmid t\) 直接跳过该项。分别以 \(K_{\rm raw},K_{\rm maj},K_{\rm min}\) 表示三个核。有 \(K_{\rm raw}=K_{\rm maj}+K_{\rm min}\)，\(|K_{\rm maj}|\ll B^3/Z\)，三个核均支撑于 \(|u|\le4Z\)。整周正交性给 \(K_{\rm raw}=\mathbf1_{u=\Delta(b-a)}\)，因为 \(a,b\in[Y,4Y]\)。当 \((a,b)=1\) 时，这正是原证书中 \(\texttt{correctedCofactorEquiv}\) 在 (1) 的块上给出的共同整数余因子条件。令 \(Q^{\rm maj}_{Y,p}\) 为以 (4) 的主弧核取代共同余因子所得的归一化六重和，所有局部投影仍在其中。定义 \(Q^{\rm min}_{Y,p}=Q^{\rm raw}_{Y,p}-Q^{\rm maj}_{Y,p}\)。共享素因子的原始项继续按共同余因子定义。[Lichtman，v1 §6](https://arxiv.org/html/2611.28392v1#S6)


## 2. 共享素因子与端点删除

令 \(K_0=mn\)、\(K_1=rs\)。固定 \(a,b\in[Y,4Y]\)。在弧核支撑上，固定 \(K_0\) 后 \(K_1\) 落在模 \(p\) 的一个剩余类内，并落在长度 \(O(pZ/a)=O_\Delta(p)\) 的区间与 \([1,4X]\) 的交内。反向也一样。因此两边纤维数均为 \(O_\Delta(1+X/p)=O_{r_1,r_2}(1)\)。令 \(\tau_j\) 表示 \(j\) 重除数函数，\(\tau=\tau_2\)。用 \(\sum_{h\le T}\tau(h)^2\ll T(\log(2T))^3\) 和 Cauchy–Schwarz，得到弧核支撑上的绝对因子计数
\[
\sum_{K_0,K_1}\tau(K_0)\tau(K_1)\ll XL^3,\qquad
\sum_{K_0,K_1:\,\ell\mid K_1}\tau(K_0)\tau(K_1)\ll XL^3\ell^{-1/2}. \tag{5}
\]
第二式使用 \(\sum_{h\le4X/\ell}\tau(\ell h)^2\le4\sum_{h\le4X/\ell}\tau(h)^2\)。\(\ell\mid K_0\) 时同理。两式的每个求和都有 \(p\mid bK_0-aK_1\)。

在共同余因子上，还需固定 \(a\) 的进程二阶矩。对 \(K=a r_1 Q_0+\Delta p\in[X,4X]\)，\((a r_1,\Delta p)=1\)。由 \(\tau(K)^2\le\tau_4(K)\le4\sum_{e\mid K,\ e\le(4X)^{3/4}}\tau_3(e)\)，若 \(e\mid K\) 有解，则 \(Q_0\) 是模 \(e\) 的一个类。故
\[
\sum_{Q_0}\tau(a r_1Q_0+\Delta p)^2
\ll (X/Y)L^3+X^{3/4}L^2\ll (X/Y)L^3. \tag{6}
\]
这里用了 \(\sum_{e\le U}\tau_3(e)\ll U\log^2(2U)\)、\(\sum_{e\le U}\tau_3(e)/e\ll\log^3(2U)\)。若同时要求 \(\ell\mid K\) 且 \(\ell\nmid a r_1\)，先把 \(Q_0\) 限在模 \(\ell\) 的唯一类。然后 \(K/\ell\) 仍是步长 \(a r_1\) 的互素进程，因为它的截距乘以 \(\ell\) 模 \(a r_1\) 同余 \(\Delta p\)。用 \(\tau(\ell h)\le2\tau(h)\) 再做同一估计，右边变为 \(\ll (X/(Y\ell))L^3\)。误差 \((X/\ell)^{3/4}L^2\) 被吸收，因为 \(Y,\ell=p^{o(1)}\)。

**(a) 共享活跃素数。** 共享的 \((a,b)\) 数目至多 \(\sum_{\ell\ge e^{\lambda_1}}\lfloor4Y/\ell\rfloor^2\ll Y^2 e^{-\lambda_1}\)。原始项固定 \((a,b)\) 后用 (6) 两次和 Cauchy–Schwarz，得到 \((X/Y)L^{4C+3}\)。主弧项用 (5) 和 \(B^3/Z\)，得到同一界乘 \(O(B^3)\)。于是这类删除误差是 \(O_E(XY L^{-E})\)，对每个固定 \(E\) 成立。这一证明包含 \(a=b\)。

**(b) 物理及辅助端点碰撞。** 若 \((a,b)=1\) 且 \(\ell\mid(b,s)\)，原始行列式等式模 \(\ell\) 给出 \(\ell\mid\Delta p a\)，矛盾。\(\ell\mid(a,n)\) 同理。主弧应用 (5) 的第二式，对每个固定 \((a,b)\) 和每个这样的 \(\ell\)，贡献 \(\ll (B^3/Z)XL^{4C+3}\ell^{-1/2}\)。每对至多有 \(2k\) 个候选素数，故总计 \(O_E(XY L^{-E})\)。当 \(t=0\)、\((a,b)=1\) 时，\(b\mid rs\)，由 \(r\) 粗得 \(b\mid s\)，也已删除。

另抽取辅助素数时，若固定的辅助 \(\ell\nmid ab\) 又整除 \(s\) 或 \(n\)，主弧仍用 (5)。原始项对相应乘积用 (6) 的模 \(\ell\) 版本，另一乘积用 (6) 本身，Cauchy–Schwarz 给出 \((X/Y)L^{4C+3}\ell^{-1/2}\)。固定 \(a,b\) 和一个抽样槽，对其 \(\ell\) 的概率按 \((\ell V_i)^{-1}\) 求和不超过 1。乘 \(kJ\) 个槽及 \(O(Y^2)\) 对 \((a,b)\) 后，合计 \(\ll XY L^{4C+3}(1+B^3) kJ e^{-\lambda_1/2}\)。

删除后，绝对原始和及绝对主弧和分别 \(\ll XY L^{4C+3}\)、\(\ll XY L^{4C+3}B^3\)。这是 (6) 和 (5) 在全部 \(O(Y^2)\) 对上的直接求和。上述迁移对应 Lemmas 6.2、9.2。[Lichtman，v1 §§6、9](https://arxiv.org/html/2611.28392v1#S9)

## 3. 与物理算子的精确配对

令 \(J=\lfloor L^\jmath\rfloor\)。每区间独立有放回抽 \(J\) 个有序辅助素数，每槽按 \((\ell V_i)^{-1}\) 抽样。乘积 \(d\) 的有序样本权为 \(1/(dV^J)\)，总质量 1。选 \(D\le d<2D\) 为唯一二进范围，只保留 \(d\) 无平方因子且 \((d,abns)=1\) 的样本。重复或撞 \(ab\) 的失重至多 \(O_k((J+1)^2 e^{-\lambda_1})\)，由槽对并集界和最大原子 \(\max_{i,\ell}(\ell V_i)^{-1}\ll e^{-\lambda_1}\) 得到。乘上节绝对和后为 \(O_E(XY L^{-E})\)。撞 \(ns\) 已由 (b) 的按槽估计覆盖。

设 \(A_{\rm box}=DYM,\ B_0=N\)，盒为 \(\mathcal B_D=[A_{\rm box},16A_{\rm box}]\times[B_0,2B_0]\)。状态由 \((\mathbf v,c)\) 组成，\(\mathbf v=(x,y)^{\mathsf T}\in\mathcal B_D\cap\mathbb Z^2\) 本原，\(c\mid x\) 是每区间 \(J+1\) 个不同素数之积。状态满足
\[
x\equiv ic,\quad y\equiv r_2p\,i^{-1}\pmod{r_1},\qquad y\equiv0\pmod{r_2}. \tag{7}
\]
状态测度为常数 \(\kappa_J=((J+1)!)^kV^{-(J+1)}\)。置 \(f_D(\mathbf v,c)=\overline{\alpha_{x/c}}\beta_y\)，超出原系数支撑处为零。若 \(f_D\ne0\)，粗性使 \(c\) 必含 \(x\) 的所有活跃素因子且各只出现一次。因此同一 \(\mathbf v\) 上若有非零值，则只有该状态可存在，且存在函数 \(f_D^\circ(\mathbf v)\) 使 \(f_D(\mathbf v,c)=f_D^\circ(\mathbf v)\) 在全部状态上成立。

物理转移 \(T_D\) 从 \((\mathbf v,c)\) 均匀选 \(b\mid c\)、\(b\in\mathcal A\)（分母 \((J+1)^k\)），令 \(d=c/b\)，要求 \(D\le d<2D\)。再以因子 \(V^{-1}\) 对 \((a,c)=1\)、\(a\in\mathcal A\) 求和。目标为 \((\mathbf v',ad)\)。边要求 \(p\mid\det(\mathbf v,\mathbf v')\) 和 \(c\equiv ad\bmod r_2\)，并赋因子
\[
\frac Dd\,\eta_Y(a)\eta_Y(b)\,
K_{\rm min}\!\left(\frac{\det(\mathbf v,\mathbf v')}{dp};a,b\right). \tag{8}
\]
因为 \(d\mid x,x'\) 且 \(p\nmid d\)，(8) 的参数是整数。由于 \(d\) 模 \(r_2\) 可逆，边同余正是 \(a\equiv b\bmod r_2\)。两个状态的测度相同，反向替换交换 \(a,b\)，保持 \(d\) 和全部投影。弧集关于 0 对称，\(\psi\) 为偶，故 \(K_{\rm min}(-u;b,a)=\overline{K_{\rm min}(u;a,b)}\)，\(T_D\) 自伴。

逐条边的正向还原为
\[
\mathbf v=(bdm,s)^{\mathsf T},\quad \mathbf v'=(adr,n)^{\mathsf T},\quad
c=bd,\quad c'=ad,\qquad \det(\mathbf v,\mathbf v')=d(bmn-ars). \tag{9}
\]
这些向量已本原。若素数 \(q\mid(bdm,s)\)，端点删项和 \((d,s)=1\) 强制 \(q\mid m\)，所以 \(q>z\)。又 \(2M<p\)，故 \(q\ne p\)，且 \(q\mid u\)，与 \(0<|u|\le4Z=o(z)\) 矛盾。目标向量同理。反向由 \(m=x/c,\ r=x'/c',\ s=y,\ n=y'\) 还原；本原性保证 \((b,s)=(a,n)=1\)、\((d,ns)=1\)，换槽条件保证 \((a,b)=1\) 和 \((d,ab)=1\)。

内积取 \(\langle f,g\rangle=\kappa_J\sum\overline f g\)。由 (9)，端点乘积是 \(\alpha_m\overline{\alpha_r}\beta_n\overline{\beta_s}\)。每条边在 \(D^{-1}\langle f_D,T_D f_D\rangle\) 中的公共系数严格等于
\[
\frac1D\ \frac{((J+1)!)^k}{V^{J+1}}\ \frac1{(J+1)^k}\ \frac1V\ \frac Dd
=\frac{(J!)^k}{dV^{J+2}} . \tag{10}
\]
固定无平方因子乘积 \(d\) 恰有 \((J!)^k\) 个有序代表。于是 \(\sum_DD^{-1}\langle f_D,T_D f_D\rangle\) 逐项等于删除 (a)、(b) 后的六重小弧和，其中每项额外乘 \(\sum_{\text{合格有序样本}}1/(dV^J)\)。由前述删项界，
\[
Q^{\rm min}_{Y,p}=\sum_DD^{-1}\langle f_D,T_D f_D\rangle+O_E(XY L^{-E}). \tag{11}
\]
这给出 (9.11)–(9.13) 的模 \(p\) 版本。[Lichtman，v1 §§9.1–9.2](https://arxiv.org/html/2611.28392v1#S9.SS1)

对任意矩阵核 \(K\)，若 \(P_\gamma,P'_\gamma\) 分别为源、目标按 \(c\bmod r_2\) 的单位类分出的正交投影，则
\[
\left\|\sum_{\gamma\in\mathbb F_{r_2}^{\times}}P'_\gamma KP_\gamma h\right\|^2
=\sum_\gamma\|P'_\gamma KP_\gamma h\|^2
\le \|K\|^2\sum_\gamma\|P_\gamma h\|^2\le\|K\|^2\|h\|^2 . \tag{12}
\]
同余配对压缩因此保持范数上界。两弧、(8) 和每一步历史转移均保留 (7) 的物理坐标投影和 (12)。


## 4. 指数 \(p\) 格、交换坐标与坏根点

沿每条物理边有 \(p\mid\det(\mathbf v,\mathbf v')\)。盒内 \(0<x,y<p\) 对充分大的 \(p\) 成立，因为 \(M,N\ge p^\delta\)、\(DY=p^{o(1)}\) 且 \(X\asymp p\)。各点模 \(p\) 非零，故一条路径全在根点的同一条模 \(p\) 直线上。对本原根 \((x,y)\)，取 \(0\le x_0<x\) 使 \(yx_0\equiv p\bmod x\)，令 \(y_0=(yx_0-p)/x,\ \rho=x_0/x\)。有
\[
G_p=\begin{pmatrix}x&x_0\\ y&y_0\end{pmatrix},\qquad
\det G_p=-p,\qquad
G_p\mathbf w=\binom{x\tau_\rho(\mathbf w)}{y\tau_\rho(\mathbf w)-pw_2/x},
\quad \tau_\rho(\mathbf w)=w_1+\rho w_2. \tag{13}
\]
两列模 \(p\) 都在根直线上，像格的指数为 \(|\det G_p|=p\)，与该直线原像的指数相同。因此两格相等。从 \(\mathbf w\) 到 \(G_p\mathbf w\) 时，伴随矩阵恒等式表明本原向量新出现的公素因子只能是 \(p\)，而盒内 \(0<x_{\mathbf w}<p\) 排除它。反向若 \(\mathbf w\) 不本原，其公因子也整除 \(G_p\mathbf w\)。这两个断言在原 Lean 证书中已形式化。若 \(d\) 为该边共享乘积，则
\[
\frac{\det(\mathbf v,\mathbf v')}{dp}=-\frac{\det(\mathbf w,\mathbf w')}{d}. \tag{14}
\]
根点 \(y\equiv0\bmod r_2\) 时，\(xy_0\equiv-p\bmod r_2\) 使 \(y_0\) 为单位，故原物理投影 \(y_{\mathbf w}\equiv0\bmod r_2\) 严格等于 \(w_2\equiv0\bmod r_2\)。模 \(r_1\) 仍按 \(G_p\mathbf w\) 的两行执行 (7)。

为应用以短边为第一坐标的根点计数，考虑 \(B_0<A_{\rm box}\)。因 \(A_{\rm box}B_0=DYX,\ 4X\ge\Delta p\)，
\[
0<\epsilon=\frac{p}{xy}\le\frac4{DY\Delta}<1
\]
对充分大的 \(p\) 成立。令 \(j=\lceil\rho-\epsilon\rceil\in\{0,1\}\)、\(\rho'=j-\rho+\epsilon\in[0,1)\)，\(P=\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)\)、\(R_j=\bigl(\begin{smallmatrix}1&j\\0&-1\end{smallmatrix}\bigr)\)。交换后的归一化完成矩阵恰为 \(G_p'=PG_pR_j\)，其第二列是 \((jy-y_0,jx-x_0)^{\mathsf T}\)，行列式仍为 \(-p\)。又 \(\lceil\rho'-\epsilon\rceil=\lceil j-\rho\rceil=j\)，且 \(R_j^2=1\)，故各分支双射。对任意模 \(T\) 的完成矩阵类 \(C\)，分支严格对应为
\[
C'=PCR_j\bmod T,\qquad C'_{11}=C_{21},\quad \det C'=\det C. \tag{15}
\]
顶点同时换成 \(\mathbf w'=R_j\mathbf w\)，于是 \(G_p'\mathbf w'=PG_p\mathbf w\)。这把原物理行投影送到交换后的同一物理行，把根限制 \(C_{21}\equiv0\bmod r_2\) 送到 \(C'_{11}\equiv0\bmod r_2\)。每个实变量分支的 Jacobian 绝对值为 1。分界 \(\rho=\epsilon\) 在归一化坐标中有有界斜率。

对一个状态定义 \(\rho_{\mathbf v}\) 为它的行列式 \(-p\) 完成参数模 1。好状态同时满足下述两项。

1. 对所有允许的 \(d=c/b\in[D,2D)\)，及整数 \(1\le h\le Y^{1/5}\)，有 \(\|h d \rho_{\mathbf v}\|>Y^{-7/10}\)。
2. 对非空区间指标集 \(I\)，令 \(i_*=\max I\)，令 \(P_<\) 从 \(I\setminus\{i_*\}\) 每区间取一个素数之积。按 \(\prod_{i\notin I}(\ell_i V_i)^{-1}\) 抽出乘积 \(T_f=\prod_{i\notin I}\ell_i\)。除总质量至多 \(e^{-\lambda_{i_*}/4}\) 的 \(T_f\) 外，任意两个不同 \(d P_<\) 给出的 \(\Delta d P_< T_f\rho_{\mathbf v}\bmod1\) 相距至少 \(100e^{-\lambda_{i_*}}\)。

固定 \(c\) 时，第一项失败的 Haar 测度至多 \(2(J+1)^kY^{-1/2}\)。第二项中候选 \(dP_<\) 至多 \((J+1)^k\exp(2\lambda_{i_*}/7)\)。每一对的非零整数乘子保持 Haar 测度，因此对固定 \(T_f\) 的失败测度至多 \(200(J+1)^{2k}\exp[-(1-4/7)\lambda_{i_*}]\)。对 \(T_f\) 取平均再用 Markov 不等式，失败的参数测度 \(\ll_k e^{-c_1L^\alpha}\)，其中 \(c_1>0\) 可固定。令 \(\mathsf G\) 为好状态投影，\(A_D=\mathsf G T_D\mathsf G\)。它同样自伴。

以下明确根点计数在单边和整矩中如何使用。固定一条长度 \(h\le 2H\) 的相对路径配置，\(H=\lceil L^\varrho/2\rceil\)。每边有 \(|\det(\mathbf v_j,\mathbf v_{j+1})|\ll pDZ\)。用
\[
\frac{y_{j+1}}{x_{j+1}}-\frac{y_j}{x_j}
=\frac{\det(\mathbf v_j,\mathbf v_{j+1})}{x_jx_{j+1}}
\]
和盒内各 \(x_j\asymp A_{\rm box}\)，得
\[
|w_{j,2}|=|\det(\mathbf v_0,\mathbf v_j)|/p\ll HDZ,\qquad
1/16\le\tau_\rho(\mathbf w_j)\le16,\qquad |\mathbf w_j|\ll HDZ. \tag{16}
\]
固定路径的模数取 \(T=r_1r_2\prod_{\ell\ {\rm 出现在路径}}\ell\)，每个活跃 \(\ell\) 只取一次。模 \(T\) 的完成矩阵类别固定后，所有活跃除法、(7)、(12) 均已决定。由 (14)，核只依赖相对行列式和素数选择。几何支撑仍保留 (13) 的第二坐标修正项。所有配置的绝对权总量（加 1）为 \(W\)，粗计数给
\[
\log T+\log W\ll_k H\bigl(\log(HDZ)+(J+1)L^\beta+(J+1)\log(J+1)\bigr)
=o(L). \tag{17}
\]
此计数允许每个顶点独立取 \(\ll (HDZ)^2\) 个相对格点及每个槽独立取 \(\exp(O(L^\beta))\) 个素数，也覆盖系数、阶乘和弧核的绝对上界。最后一步用 \(\varrho+\beta+\jmath<1\)。

采用题设根点 Kloosterman 计数的矩形版本。每个均匀的 \(\det C=-p\bmod T\) 类占标准归一化体积的 \(1/(\zeta(2)|\mathrm{SL}_2(\mathbb Z/T\mathbb Z)|)\)，归一化盒误差为 \(p^{-\delta/1000+o(1)}\) 或更小。这里可直接看出该归一化。短边为 \(x\) 时固定 \(x\equiv C_{11}\bmod T\)，置 \(T_1=(x,T)\)，\(T_2=T/T_1\)。完成方程为 \(yx_0\equiv p+x C_{22}\bmod xT_1\)，模 \(T_2\) 条件已由各坐标剩余类保证。\(T_1\) 各素因子处 \(y,x_0\) 为单位。把 \(y,x_0\) 在指定模 \(T\) 类中参数化，模 \(x\) 对两个参数做区间 Fourier 展开。零频的允许剩余对数为 \(x\prod_{\ell\mid x,\ell\nmid T}(1-1/\ell)\)。非零频由模 \(xT_1\) 的 Weil–Kloosterman 界给 \(x^{1/2+o(1)}T^{O(1)}(1+B_0/x)\) 的误差。具体地，限制 \(y\bmod T_1\) 用加法字符投影，频率公因子上界为 \(T_1\gcd(m,n,x)\)。区间 Fourier 系数除以周期后有界于 \(O((1+|m|)^{-1})\)，对非零频按 \(d\mid(m,x)\) 分组吸收该公因子的平方根。长 \(y\) 区间可按周期切分，给出上式的 \(1+B_0/x\)。最后对 \(x\) 进程求和，展开 \(\prod_{\ell\mid x,\ell\nmid T}(1-1/\ell)=\sum_{d\mid x,(d,T)=1}\mu(d)/d\)。主项常数为 \(T^{-3}\prod_{\ell\nmid T}(1-\ell^{-2})\)，等于所述常数。非零频归一化误差为 \(A_{\rm box}^{-1/2}p^{o(1)}\)；若 \(B_0<A_{\rm box}\)，先用 (15) 把矩形分支送入交换后的坐标。对像区域使用边长 \(p^{-\delta/1000}\) 的网格，分支和矩形边界的有界横截斜率给同量级的边界体积误差。短边计数的 \(p^{-\delta/2+o(1)}\) 在至多 \(p^{3\delta/1000}\) 个网格盒上求和后仍足够。由分支的 Jacobian 和矩阵类双射得到回到原坐标的同一常数。此处 \(p\) 不在 \(T\) 中，且 \(T=p^{o(1)}\)。

取三维网格边长 \(p^{-\delta/8000}\)。位置边界在 \(x/A_{\rm box}\) 或 \(y/B_0\) 方向的横截导数是 \(\tau_\rho(\mathbf w)\)，在支撑上介于 \(1/16\) 与 16。对于 \(\det(\mathbf w,\widehat{\mathbf w})=1\) 的整数完成，运输后的 \(\rho_{G_p\mathbf w}\) 是 \(\tau_\rho(\widehat{\mathbf w})/\tau_\rho(\mathbf w)\bmod1\)，其对 \(\rho\) 的未取模导数为 \(\tau_\rho(\mathbf w)^{-2}\)。枚举好点测试中出现的整数乘子、整数平移和素数选择，再加上交换分界，可把有关边界分成 \(p^{o(1)}\) 个片段，斜率为 \(p^{o(1)}\)。好点第二项的加权判定在各单项测试边界之间恒定。网格边界总体积为 \(p^{-\delta/8000+o(1)}\)，计数误差为 \(p^{3\delta/8000-\delta/1000+o(1)}\)。乘 (17) 的绝对配置权及模类数后，归一化总误差仍为 \(p^{-\delta/8000+o(1)}=O_E(L^{-2EH})\) 对每个固定 \(E\) 成立。单边也适用该估计，此时不要求返回根。计数迁移与 Lichtman Proposition 10.2 的网格论证对应。[Lichtman，v1 §10](https://arxiv.org/html/2611.28392v1#S10)


**(c) 坏点的单边删除。** §3 已证明出现于配对的两端本原。历经多个顶点时，再由 (13) 的盒内本原性逐点执行同一个投影。好点测试的删除使用
\[
\langle f_D,T_D f_D\rangle-\langle f_D,A_D f_D\rangle
=\langle(1-\mathsf G)f_D,T_D f_D\rangle+\langle\mathsf Gf_D,T_D(1-\mathsf G)f_D\rangle .
\]
对第一项把两端系数乘积以 \(O(L^{4C})\) 控制，分别按原始核和主弧核取绝对值。根的相对向量为 \((1,0)^{\mathsf T}\)。原始核把目标的 \(w_2\) 固定为 \(\Delta d(a-b)\)。主弧允许 \(w_2/d\) 为 \(O(Z)\) 个整数，每个核 \(\ll B^3/Z\)。每个 \(w_2\) 至多 \(O(1)\) 个 \(w_1\)，由 \(1/16\le\tau_\rho(\mathbf w)\le16\) 得到。故固定素数选择时，目标总质量 \(\ll 1+B^3\)。

在均匀的完成矩阵类中，对模每个活跃 \(\ell\)，第一行的核是一条均匀的射影直线。理由是行列式 \(-p\) 为单位，固定任一非零第一行恰有 \(\ell\) 个第二行可选择，每条核直线有 \(\ell-1\) 个这样的第一行。CRT 给出这些直线彼此独立，且独立于 \(r_1,r_2\) 的固定矩阵类。每个不同的活跃素数在单边有一次 Haar 因子 \((\ell+1)^{-1}\)，条件是所有要求该素数的相对顶点落在同一直线。此前本原性保证这些相对向量模 \(\ell\) 非零。结合 (10) 后的配对权但未除以 \(D\)，去掉几何因子 \(D/d\le1\)，把 \(d\) 改回有序抽样，可得正规化素数总质量至多
\[
V^{-(J+2)}\prod_i\left(\sum_{\ell\in\mathcal P_i}\frac1{\ell+1}\right)^{J+2}\le1.
\]
物理局部投影留在积项中，取绝对上界时以 1 控制。坏根测试的 \(\rho\)-测度为 \(\ll e^{-c_1 L^\alpha}\)。加上网格误差，每条单边归一化删除界为
\[
(DYX)^{-1}|\langle(1-\mathsf G)f_D,T_Df_D\rangle|
\ll L^{4C}(1+B^3)e^{-c_1 L^\alpha}+p^{-\delta/8000+o(1)}.
\]
反向并用自伴性得到坏目标同界。由于 \(\log d\ll_k L^{\beta+\jmath}\) 且 \(\beta+\jmath<1\)，二进 \(D\) 范围数最终 \(\le L\)。于是对任意固定 \(E>0\)
\[
Q^{\rm min}_{Y,p}=\sum_D D^{-1}\langle f_D,A_Df_D\rangle+O_E(XY L^{-E}). \tag{18}
\]
这一步给出对应 Lichtman Lemma 9.4 的物理算子公式。[Lichtman，v1 §§9.3–10](https://arxiv.org/html/2611.28392v1#S9.SS3)

## 5. 路径矩与空记忆边界

设 \(u_{\mathbf v}\) 为所有在物理点 \(\mathbf v\) 上状态的指示函数。定义
\[
\mathcal T_H=\sum_{\mathbf v}\langle u_{\mathbf v},A_D^{2H}u_{\mathbf v}\rangle
=\sum_{\mathbf v}\|A_D^H u_{\mathbf v}\|^2.
\]
在通常矩阵表示下，每根一项精确等于
\[
\kappa_J
\sum_{\substack{c_0:(\mathbf v,c_0)\ {\rm 为状态}\\c_{2H}:(\mathbf v,c_{2H})\ {\rm 为状态}}}
(A_D^{2H})_{(\mathbf v,c_0),(\mathbf v,c_{2H})}.
\tag{19}
\]
初末活跃积独立求和，只在起点出现一次 \(\kappa_J\)。矩阵乘法展开后逐条边应用 (13)–(16)，相对路径从 \((1,0)^{\mathsf T}\) 出发并回到 \((1,0)^{\mathsf T}\)。路径支撑仍是原指数 \(p\) 格。按 §4 网格平均并展开 CRT，得
\[
\frac{\mathcal T_H}{DYX}
=\frac1{\zeta(2)}\int_{1}^{16}\int_{1}^{2}\int_0^1
\mathbb E_{C_{r_1},C_{r_2}}\mathcal M_H(A_{\rm box}\sigma,B_0\upsilon,\rho;C_{r_1},C_{r_2})
\,d\rho\,d\upsilon\,d\sigma+O_E(L^{-2EH}). \tag{20}
\]
这里 \(\mathcal M_H\) 是 (19) 的相对闭路和，每个出现过的活跃素数取一条统一的 Haar 直线。固定 \(\ell\) 后，因子恰为
\[
\frac1{\ell+1}\sum_{L_\ell\in\mathbb P^1(\mathbb F_\ell)}
\prod_{j:\ell\mid c_j}\mathbf1_{\overline{\mathbf w}_j\in L_\ell}.
\tag{21}
\]
其中 \(C_{r_1}, C_{r_2}\) 分别在行列式为 \(-p\) 的类中均匀取值，(7)、(12) 一直是投影。式 (20) 的根点误差已经包括全部配置绝对权。

令 \(\nu_i(\ell)=1/((\ell+1)V_i)\)，记 \(a_*=\max_{i,\ell}\nu_i(\ell)\ll e^{-\lambda_1}\)，\(\sum_\ell\nu_i(\ell)\le1\)。在固定 (20) 的实参数和局部矩阵类后，历史状态记录相对位置、活跃积 \(c\) 和每区间无序的暂离二元组集合 \((\ell,L_\ell)\)。同一时刻所有活跃与暂离素数互异，暂离总量上限 \(M_0=\lceil L^2\rceil\)。状态测度为活跃权 \(\prod_i((J+1)!\prod_{\ell\mid c,\ \ell\in\mathcal P_i}\nu_i(\ell))\) 乘暂离各对的 \(\nu_i(\ell)\)，射影线用计数测度。它等于对称有序暂离槽采用 \(1/m_i!\) 的测度。

取每步的出槽区间集 \(S\) 和回归区间集 \(I\)。离场素数在 \(S\) 上存入其当前直线，其余死亡。进场素数在 \(I\) 上从源暂离集合取出并检验目标直线，权 \(V_i^{-1}\)。其余为新出生，权 \(\nu_i(\ell)\)。本步刚存入的槽不参与本步回归。保留 (7)、(12)、好点和位置投影、同一步的 \((a,c)=1\)，以及共享 \(d\) 的同线条件和 \(D/d\) 因子。相对核按 (14) 算，删槽仍除以 \((J+1)^k\)。把所有 \(S,I\) 和选择求和得历史转移 \(\mathsf E_j\)，取与 (19) 一致的核方向。用 \(b_0\) 指示初、末的相对根位置和空暂离记忆，活跃积任取，局部及好点条件在各边端点施加。其平方范数 \(\le\prod_i(\sum_\ell \nu_i(\ell))^{J+1}\le1\)。

**(d) 空记忆对接和全局碰撞。** 一条 (19) 的路径唯一决定记忆选择。一项离场当且仅当同一素数之后再进场时进入暂离槽，否则死亡。到末端仍活跃的素数无需离场，全部暂离槽此时已空。每个曾出现的素数只出生一次，因而反过来，初、末空记忆且全程出生值互异的历史恰好重建这条路径。共享 \(d\) 的连续顶点用同线条件，离开后再返回时用记忆中的原线，实现 (21) 的全部检查。一个素数若有 \(h_\ell\) 个连续活跃区段，其总权是首次 \(\nu_i(\ell)\) 乘随后 \(h_\ell-1\) 次 \(V_i^{-1}\)，即 \(V_i^{-h_\ell}/(\ell+1)\)。初始阶乘正来自 \(\kappa_J\)，出槽分母和 \(D/d\) 在每步各出现一次。因此在固定实参数上逐历史有
\[
\mathcal M_H=\langle b_0,\mathsf E_0 \mathsf E_1\cdots \mathsf E_{2H-1} b_0\rangle_{\text{全程出生值互异}}.
\tag{22}
\]
至多 \(2kH<M_0\) 个暂离素数，故容量截断不改变空记忆配对。在只要求同时活跃或暂离的素数互异时，已经死亡的素数仍可再次出生。下节估计这个全局限制，保留长矩所需的符号消去。[Lichtman，v1 §11，(11.5)–(11.6)](https://arxiv.org/html/2611.28392v1#S11)


## 6. 单步历史算子和截断产生的频率平移

给定相对源点 \(\mathbf w\)，取 \(\det(\mathbf w,\widehat{\mathbf w})=1\) 的整数完成。目标写成 \(j_0\mathbf w+j_1\widehat{\mathbf w}\)。在位置支撑上，\(\tau_\rho(\mathbf w')/\tau_\rho(\mathbf w)\in[1/16,16]\)，每个 \(j_1\) 至多 \(O(1)\) 个 \(j_0\)。原始核指定 \(j_1\)，主弧核允许 \(O(Z)\) 个 \(j_1/d\)，故固定素数的绝对目标总量仍 \(\ll1+B^3\)。回归可选暂离槽至多 \(M_0^k\)，出生的 \(\nu_i\) 总质量至多 1，删槽权均值为 1。于是行和 \(\ll_k M_0^k(1+B^3)\)。若指定 \(s\) 个出生槽值，此行界多一个 \(a_*^s\)。

列界可在同一测度上逐边反向。给原边的进场出生素数乘 \(\nu_i\)，给反边出生的离场死亡素数乘 \(\nu_i\)。源测度乘前者与目标测度乘后者相等，因为共同存活素数各保留一次 \(\nu_i\)，每个活跃区间的阶乘也不变。正向回归权 \(\prod_{i\in I}V_i^{-1}\) 与反向回归权 \(\prod_{i\in S}V_i^{-1}\) 的比值为 \(\prod_{i\in S}V_i/\prod_{i\in I}V_i\asymp_k1\)。反向的线检验对应相同活跃位置。例如取粗权指数 \(c_*=2k+3A_0+10\)，可使充分大的 \(p\) 上绝对算子的行、列和及 Schur 范数 \(\le L^{c_*}\)。附加出生标志和单位圆相位也满足该粗界。

**无回归或存储的边。** 先允许进场与离场素数同值。按 \(w_2/\tau_\rho(\mathbf w)\) 切成宽 \(DZ\) 的带，按共享 \(d\) 的直线分块。行列式支撑保证带之间只有有界邻接。任取一个有贡献的邻带对和同线格，取一个好本原参考点 \(\mathbf w_*\)，该格写成 \(h\mathbf w_*+j d\widehat{\mathbf w}_*\)。恒等式
\[
\frac{w_2}{\tau_\rho(\mathbf w)}-\frac{w_{*,2}}{\tau_\rho(\mathbf w_*)}
=\frac{\det(\mathbf w_*,\mathbf w)}{\tau_\rho(\mathbf w_*)\tau_\rho(\mathbf w)}
\]
给 \(|j|\ll Z\)，且 \(h+j d\rho_*\) 有界，其中 \(\rho_*=\tau_\rho(\widehat{\mathbf w}_*)/\tau_\rho(\mathbf w_*)\)。格 \((j/Z,h+jd\rho_*)\) 的余面积为 \(1/Z\)。好点第一测试给最短非零向量长度 \(\gg_\Delta Z^{-4/5}\)：若 \(|j|>Y^{1/5}\) 用第一坐标，否则用第二坐标的 \(Y^{-7/10}\) 界，\(j=0\) 时用 \(|h|\ge1\)。二维约化基的夹角正弦有固定正下界，故基长之积 \(\asymp Z^{-1}\)，所得整数坐标盒两边 \(A',B'\) 满足 \(A'B'\asymp Z\) 和 \(Z^{1/10}\le A',B'\le Z^{9/10}\)。取原格正向基 \(\mathcal B_d\)，则 \(\det\mathcal B_d=d\)，\(\det(\mathbf w,\mathbf w')/d=\det(\mathbf k,\mathbf l)\)。这一格盒步骤对应 Lü–Wang–Wu (4.42)–(4.46)。[Lü–Wang–Wu，v1 §4.4](https://arxiv.org/html/2610.20242v1#S4.SS4)

固定 \(d\) 和暂离元组，换为计数测度后，未共享标签端点因子为 \(\eta_Y(a)\sqrt{m(a)}\)、\(\eta_Y(b)\sqrt{m(b)}\)，其中 \(m(a)=\prod_{\ell\mid a}\nu_i(\ell)\ll_k1/Y\)；此式来自源目标状态测度之平方根比与出生权的乘积。其余位置、好点、活跃及暂离互异、模 \(r_1,r_2\) 顶点条件全是端点乘子，类匹配用 (12)。现在把 (4) 代入 (14)，并用弧集关于 0 对称反转 \(\theta\)。几何相位为 \(e(\theta\det(\mathbf k,\mathbf l))\)，标签相位为 \(e(-\theta\Delta(a-b))\)。对标签作 Fourier 零延拓到 \(\Delta\mathbb Z\)。对每个输入 \(F\)，Parseval 给
\[
\int_{\mathbb T}\sum_{\mathbf k}
\left|\sum_b\eta_Y(b)\sqrt{m(b)}F(\mathbf k,b)e(\pm\Delta b\theta)\right|^2d\theta
\ll Y^{-1}\|F\|^2 .
\tag{23}
\]
输出同理。因此用 Cauchy–Schwarz，对每个截断 Fourier 变量 \(v\)，积分算子范数 \(\ll Y^{-1}\sup_{\theta\in\mathfrak m}\|\mathsf U_{\theta+v/Z}\|\)，\(\mathsf U_\xi(\mathbf k,\mathbf l)=e(\xi\det(\mathbf k,\mathbf l))\)。这里 \(\psi(\det/Z)=\int\widehat\psi(v)e(v\det/Z)\,dv\)，频移只作用于几何相位。

若 \(|v|\le B=L^{A_0}\) 且 \(\theta\in\mathfrak m\)，对所有 \(q\le B\) 的既约 \(h/q\) 有
\[
\|\theta+v/Z-h/q\|> 2B/Z-|v|/Z\ge B/Z .
\]
用 Dirichlet 取 \(Q=\lceil Z/B\rceil\)，得到既约 \(h/q\) 满足距离 \(\le1/(qQ)\le\min(B/Z,q^{-2})\)。必有 \(B<q\le Q\ll Z/B\)，所以窄主弧确已避开。

张量积把 \(\mathsf U_\xi\) 分成 \(e(\xi k_1l_2)\) 与其换向共轭。其范数为一个一维矩形 Fourier 矩阵的范数平方。Gram 行和至多 \(\sum_{|h|\ll A'}\min(B',O(\|h\xi\|^{-1}))\)。按长度 \(q\) 分块，在每个 \(1/q\) 小区间有 \(O(1)\) 个 \(h\xi\) 像，因为在一块内与 \(h h_0/q\) 的相对偏差至多 \(1/q\)（\(h_0/q\) 为所取既约逼近）。故行和 \(\ll (A'/q+1)(B'+q\log(2q))\)。除以 \(Z\) 得
\[
Z^{-1}\|\mathsf U_\xi\|
\ll q^{-1}+Z^{-1/10}\log(2Z)+q\log(2q)/Z.
\tag{24}
\]
于是小 \(v\) 部分 \(\ll L^{\beta-A_0}+Z^{-1/10}\log(2Z)\)。若 \(|v|>B\)，平凡矩阵范数 \(\|\mathsf U_\xi\|\ll Z\) 与 (23) 的 \(Y^{-1}\) 抵消到固定常数，Schwartz 尾贡献 \(\ll_{\psi,N}B^{1-N}\) 对每个 \(N>1\) 成立。恢复 \((a,c)=1\) 时，\(a\cap d=\varnothing\) 已由目标积无平方因子保证，需扣除进、离场标签共享素数的边。指定一个出生值使行、列和 \(\ll_k(1+B^3)a_*\)。按 \(d\) 的分块合并使用归一化复制 \(F\mapsto((J+1)^{-k/2}F|_{d\mid c,\ c/d\in\mathcal A})_d\)，它是压缩，因为每状态至多 \((J+1)^k\) 份。对各带求和时，把输出按目标带分组并用 Cauchy–Schwarz。每个源带和目标带都只涉及有界多个相邻带，故同一界控制无链接子算子整体。

**有存储或回归的边。** 若 \(I\ne\varnothing\)，固定最高区间 \(i_*=\max I\) 的回归对 \((\ell,L_\ell)\)，以及新出生的乘积 \(T_f\)。写 \(c'=ad=\ell U\)、\(U=dP_<T_f\)，\(\rho_*=\tau_\rho(\widehat{\mathbf w})/\tau_\rho(\mathbf w)\)。原始相对行列式由 (14) 给 \(j_1=\Delta(\ell U-c)\equiv-\Delta c\ne0\bmod\ell\)。于是目标的模 \(\ell\) 轨迹是一条不经过原点的仿射直线，和 \(L_\ell\) 相交至多一点，强制 \(j_0\equiv j_*\bmod\ell\)，其中 \(j_*\) 与 \(U\) 无关。由位置限制，
\[
\Delta U\rho_*\bmod1
\ \in\ \frac{[1/16,16]+\Delta c\rho_*-j_*}{\ell}\pmod1 .
\]
该弧长 \(<16e^{-\lambda_{i_*}}\)。好点第二测试使非异常 \(T_f\) 至多有一个 \(U\)。再用 \(d=(c,U)\) 唯一还原 \(d,b,P_<\)，各返回槽由素数值唯一决定。固定回归对的删槽均值省 \((J+1)^{-k}\)，再乘至多 \(M_0\) 个最高回归槽。异常 \(T_f\) 用 \(M_0^k\) 的粗计数，质量至多 \(e^{-\lambda_{i_*}/4}\)，因为 \(\nu_i(\ell)\le(\ell V_i)^{-1}\)。原始核的该方向行界为 \(O_k(M_0(J+1)^{-k}+M_0^k e^{-\lambda_1/4})\)。没有回归的一侧原始行界为 \(O_k(1)\)。若 \(I=\varnothing\)、\(S\ne\varnothing\)，反向交换两者。Schur 范数 \(\ll_k L^{1-\jmath k/2}+O_N(L^{-N})\)。

有链接的主弧核中，固定一个回归 \(\ell\) 后 \(\ell\nmid d\)，故同一格盒基模 \(\ell\) 可逆。目标的非平凡线条件在盒内至多允许 \(O(Z(\ell^{-1}+Z^{-1/10}))\) 个点，固定一个坐标后另一坐标在一个剩余类即可看出。乘 \(B^3/Z\)、\(M_0^k\) 及出生质量，并用反向行界和 Schur，得到任意对数幂节省。以上分解按 \(K_{\rm min}=K_{\rm raw}-K_{\rm maj}\) 使用原始、主弧核，两者共有同一投影与截断。取 \(A_0>G+\beta+2,\ \jmath k/2>G+2\)，上述子算子求和后，对所有充分大的 \(p\) 有 \(\|\mathsf E_j\|\le L^{-G}\)。[Lichtman，v1 §11，(11.7)–(11.15)](https://arxiv.org/html/2611.28392v1#S11)


## 7. 碰撞秩与谱 Hölder

把 \(N_* =k(J+1)+2kH\) 个可能出生槽按时间排列。初始每区间的 \(J+1\) 项暂且有序，使用独立的 \(\nu_i\) 权再限互异。对恢复成无序活跃积，每个积恰好有 \((J+1)!\) 个顺序，故与初始状态测度严格一致。未出生的槽赋彼此不同、且与素数值不交的哑值。

对这些槽的一个分拆 \(\pi\)，令 \(r(\pi)=N_*-\#\pi\)，\(\mu(\pi)=\prod_{P\in\pi}(-1)^{|P|-1}(|P|-1)!\)。出生值全异指标等于
\[
\sum_\pi\mu(\pi)\prod_{P\in\pi}\mathbf1_{\text{该块各槽值相同}} .
\tag{25}
\]
固定一条历史，只有其相等类的细分可贡献。每个相等类内求和是该类置换的符号和，因为一块的 \((|P|-1)!\) 是可能轮换的数目。大小至少 2 的类符号和为 0，单元素类为 1。秩 \(l\) 的绝对系数和等于有 \(N_*-l\) 个轮换的置换数，为 \(\prod_{j=0}^{N_*-1}(1+jt)\) 的 \(t^l\) 系数，因此至多 \(N_*^{2l}\)。

**高秩。** 在每个非单元素块中，除最早槽外，每个槽出生时必须取该最早值。如果任何必要槽未出生或等式跨不同活跃区间，该项为零。一条边在每个区间最多只有一个出生槽，因此后续强制值来自此前的边或初始槽。顺序暴露初始和后来各出生槽时，每个被指定的值带一个最大原子 \(a_*\)，总数恰为 \(l\)。用 §6 固定出生值后的绝对行界逐步求和，连同初始有序权，得到每个秩 \(l\) 分拆的绝对量 \(\le L^{2Hc_*} a_*^l\)。令
\[
l_0=\left\lceil C_0\,\frac{2H\log L}{\lambda_1}\right\rceil .
\]
由于 \(N_*=L^{O_k(1)}\) 和 \(a_*\ll_k e^{-\lambda_1}\)，充分大时 \(N_*^2 a_*\le e^{-\lambda_1/2}\)。高秩 \(l\ge l_0\) 总量
\[
\le 2L^{2Hc_*} e^{-\lambda_1 l_0/2}
\le 2L^{-2H(C_0/2-c_*)}.
\tag{26}
\]

**低秩。** 对每块用树连接其槽，用 \(\int_{\mathbb T}e(\theta(v-v'))\,d\theta\) 实现各相等条件。每个所涉槽须是真出生，因而可在它出现的转移步骤加出生标志和单位相位。初始槽的相位在所有顺序上取平均，形成范数 \(\le1\) 的初端乘子。终端仍为同一个空记忆指示。非单元素块涉及至多 \(2l\) 个槽，故至多 \(2l\) 个步骤被改造。对这些步骤用 \(L^{c_*}\) 的绝对 Schur 界，其余步骤保留 \(L^{-G}\) 范数。逐分拆对相位积分并求和得
\[
\left|\text{低秩总量}\right|
\le L^{-2HG} \sum_{l<l_0}N_*^{2l}L^{2l(G+c_*)}
= L^{-2HG}\exp(o(H)).
\tag{27}
\]
最后因为 \(l_0\log L=O(H(\log L)^2/L^\alpha+\log L)=o(H)\)。这也证明了带全程出生互异的 (22) 的矩控制。式 (25)–(27) 完成 (d) 的记忆槽碰撞账本，分别保留高秩原子节省和低秩的未改造边节省。[Lichtman，v1 §11，(11.16)–(11.18)](https://arxiv.org/html/2611.28392v1#S11)

若 \(G>E_0+3\)、\(C_0/2>c_*+E_0+3\)，则 (26)、(27) 均 \(\ll L^{-2H(E_0+2)}\)。将 (20) 的误差精度取为 \(E>E_0+2\) 得
\[
0\le \mathcal T_H\ll DYX L^{-2HE_0}.
\tag{28}
\]

**插值中的端点数。** \( \|f_D\|_\infty\ll L^{2C}\)，且 \(\|f_D\|^2\ll DYX L^{4C}\)。后者由固定 \(c\) 的盒内点数 \(O(DYX/c)\) 和 \(\kappa_J\sum_c c^{-1}\le1\) 得到。若 \((A_D^{2H})\) 连接两个端点，(16) 给 \(p\mid\det(\mathbf v,\mathbf v')\) 且 \(|\det(\mathbf v,\mathbf v')|\ll HpDZ\)。整数 \(\det(\mathbf v,\mathbf v')/p\) 只有 \(O(HDZ)\) 个候选。对每个固定值，解 \(\mathbf v'\) 两两相差整数倍的 \(\mathbf v\)，因为根本原。由 \(x'\in[A_{\rm box},16A_{\rm box}]\)、\(x\ge A_{\rm box}\)，每层只有 \(O(1)\) 个候选。因此每根可及的端点总数 \(O(HDZ)\)。

置 \(g_{\mathbf v}=\|A_D^H u_{\mathbf v}\|\)。展开 \(f_D=\sum_{\mathbf v}f_D^\circ(\mathbf v)u_{\mathbf v}\) 后，只有上述可及端点对在 \(\|A_D^H f_D\|^2\) 中出现。Cauchy–Schwarz 给内积界 \(g_{\mathbf v}g_{\mathbf v'}\le (g_{\mathbf v}^2+g_{\mathbf v'}^2)/2\)。所以
\[
\|A_D^H f_D\|^2\ll L^{4C} HDZ\,\mathcal T_H .
\]
\(A_D\) 自伴，对 \(f_D\) 的谱测度应用 Hölder 得
\[
|\langle f_D,A_D f_D\rangle|
\le \|f_D\|^{2-1/H}\|A_D^H f_D\|^{1/H}.
\]
代入 (28) 和端点范数，
\[
D^{-1}|\langle f_D,A_D f_D\rangle|
\ll XY L^{4C-E_0}(HDZ)^{1/(2H)} .
\tag{29}
\]
因为 \(\log(HDZ)\ll_k \log L+L^{\beta+\jmath}\) 且 \(\beta+\jmath<\varrho\)，末因子为 \(O(1)\)。式 (18) 至多有 \(L\) 个尺度，因此在 \(E_0>A+4C+2\) 时得
\[
|Q^{\rm min}_{Y,p}|\ll_A XY L^{-A}.
\tag{30}
\]
这正是 \(p\mid\det\) 在插值中带来的尺度。端点自由度始终按 \(\det/p\) 计数。[Lichtman，v1 Lemma 9.5](https://arxiv.org/html/2611.28392v1#S9.SS4)

## 8. 对同一弧核的主弧估计

在用于原相关和的盒内，\(\alpha_m=\mu(m)R_z(m)m^{i t_0}w_m(m)\)，\(|t_0|\le p^{O(1)}\)，\(w_m\) 是一致有界变差权。此节维持 (1) 与 \(a\equiv b\bmod r_2\)。对给定的单位类 \(\gamma\bmod r_2\)，将 \(a,b\) 分别限在 \(\gamma\)。令 \(\theta=h/q+\xi\)，\(|\xi|\le2B/Z\)。全部因子 \(a,b,m,n,r,s<p\)，故 \(p\mid t\) 的指标是 \((p-1)^{-1}\sum_{\chi\bmod p}\chi(bmn)\overline{\chi(ars)}\)。在该指标上 \(e(h t/(pq))=e(h\bar p\,t/q)\)。这给出可在全和使用的模 \(q\) 相位与乘法特征展开。

为分开连续权，设 \(S_0=XY\)、\(x_1=bmn,x_2=ars\)，\(s_j=\log(x_j/S_0)\)，\(\lambda=S_0/(pZ)=O_{r_1,r_2}(1)\)。乘两个在盒上恒为 1 的固定紧支撑光滑函数 \(W_1,W_2\)，在 \((s_1,s_2)\) 中反演
\[
F(s_1,s_2)=W_1(s_1)W_2(s_2)
\psi\bigl(\lambda(e^{s_1}-e^{s_2})\bigr)
e\bigl(\xi Z\lambda(e^{s_1}-e^{s_2})\bigr).
\]
积分分出的权是 \((x_1/S_0)^{2\pi i t_1}(x_2/S_0)^{2\pi i t_2}\)，系数是 \(\widehat F(t_1,t_2)\)。紧支撑和 \(j\) 阶导数 \(O_j((1+B)^j)\) 给 \(\|\widehat F\|_1\ll L^{O(1)}\)，并且截在 \(\max(|t_1|,|t_2|)\le L^{A_0+K_1}\) 时可取 \(K_1\) 及足够多次分部积分，使尾的 \(L^1\) 范数 \(\ll_T L^{-T}\)。截断前的模 \(p\) 平均可用下述乘积二阶矩和 \(|A_\chi|\ll Y\) 控制，因此该尾在所需尺度上任意小。剩余标签慢相位 \(e(-\xi\Delta(b-a))\) 直接分到两个标签。

对模 \(q\) 的相位，\(bm,ar\) 都是单位。在一端可写
\[
e(h\bar p\,bmn/q)=\sum_{\xi_1\bmod q}\xi_1(bm)\,
\frac1{\varphi(q)}\sum_{u\bmod q}^{*}\overline{\xi_1(u)}e(h\bar p\,un/q).
\]
内归一化和的模至多 1，允许 \(n\) 为非单位。另一端同样。标签有理相位及 \(r_1,r_2\) 的单位类可用小模乘法特征分开，非单位的 \(n,s\) 条件继续放在第二系数里。故只需对对数幂个分离项估计两端的 \(\chi\)-平均。每个端点含一个标签多项式 \(A_\chi\) 及一个乘积多项式 \(U_\chi=\sum_{h\le4X}u_h\chi(h)\)，\(|u_h|\ll L^{2C}\tau(h)\)。正交性及每个模 \(p\) 类至多 \(O(1+X/p)\) 个乘积给
\[
\frac1{p-1}\sum_{\chi\bmod p}|U_\chi|^2
\ll (1+X/p)XL^{4C+3}.
\]
两端 \(U_\chi\) 分别满足此界。

若 \(\chi\ne\chi_0\)，则它与任一小模特征相乘仍非主。固定标签其余 \(k-1\) 个素数的积 \(b'\)，最后一个素数落在 \([Y/b',4Y/b']\) 和自己的活跃区间的交。Dirichlet GRH 显式公式在 \(\sum_{n\le x}\Lambda(n)\chi(n)\) 中给 \(O(\sqrt{x}\log^2(2pqr_2x))\) 的界，去除素数幂后再用 Abel 求和处理有界变差为 \(L^{O(1)}\) 的平滑、乘法扭转和慢相位，给该素数和 \(\ll (Y/b')^{1/2}L^{O(1)}\)。由于每个非空 \(Y/b'\gg e^{\lambda_1}\) 且 \(\sum_{b'}1/b'\ll_k1\)，有 \(|A_\chi|\ll_k Y L^{O(1)}e^{-\lambda_1/2}\)。于是两端 Cauchy–Schwarz 后，非主贡献在乘主弧测度前为 \(\ll XY^2 L^{O(1)} e^{-\lambda_1}\)。[Dirichlet 显式公式，Lemmas 1–2](https://link.springer.com/article/10.1007/s00208-026-03383-y)

主特征在所有盒内因子上恒为 1。此时 \(m\) 的字符只剩模数为 \(L^{O(1)}\) 的小模字符，扭转高度仍 \(\le p^{O(1)}\)。Lichtman Proposition 8.1 给 \(\ll_D M L^{-D}\) 的粗 Möbius 和。其余变量用平凡界，故主特征项乘 \(1/(p-1)\) 后为 \(\ll_D X^2Y^2 p^{-1} L^{-D+O(1)}\)。两部分再乘主弧测度 \(\ll B^3/Z\)，得到 \(|Q^{\rm maj}_{Y,p}|\ll_D XY L^{-D}\)，因为 \(X/p\asymp1\)、\(Z/Y=\Delta\) 固定。主特征的 \(1/(p-1)\) 在这里补偿乘积计数尺度，对数节省由粗 Möbius 估计给出。[Lichtman，v1 §8](https://arxiv.org/html/2611.28392v1#S8)


## 9. Type I、区间权及 Kátai 推论

固定 \(s_0\) 的任意求和子区间并要求 \(1\le s_0<p/r_2\)。此时 \(u_0\in[(1-r_1/r_2)p,p]\)，\(v_0>0\)。只需使 \(v_0\) 典型。以 \(\lambda_j=2^{j-1}L^\alpha\) 取 \(B_{\rm pat}=\lfloor(\beta-\alpha)\log L/\log 2\rfloor\) 个区间。典型表示命中至少 \(3k\) 个区间，模式由最早命中的 \(3k\) 个区间决定。取其中第 \(1,4,\ldots,3k-2\) 个为活跃区间，余下条件为被动因子 \(\phi^-\)，它在乘入任意活跃素数时不变。

若 \(v_0\) 非典型，除至多 \(3k-1\) 个区间外其余区间均无小素数整除。对任一豁免区间集合，沿 \(s_0\) 筛。对相关的无平方因子筛模 \(d\)，\(d\mid v_0\) 是一个模 \(d\) 类，计数为区间长度除以 \(d\)，误差 \(O(1)\)。Bonferroni 截在 \(R=\lceil C_R\log L\rceil\) 个素因子，余项倒数和至多 \((\sum_{\ell}1/\ell)^{R+1}/(R+1)!\)，取 \(C_R\) 大即可任意对数节省。每个截断筛模至多 \(\exp(O(R L^\beta))=p^{o(1)}\)，总计数舍入误差为 \(p^{o(1)}\)。每未豁免区间的密度因子是 \(1/2+O_T(L^{-T})\)，由定量素数定理（如经典无零点区域下的素数定理余项）取任意固定对数精度。因此异常总数
\[
\ll_k p\,2^{-B_{\rm pat}} B_{\rm pat}^{3k-1}+O_T(pL^{-T})
=o(p).
\]
典型模式数 \(O_k(B_{\rm pat}^{3k})=L^{o(1)}\)。[Lichtman，v1 §4](https://arxiv.org/html/2611.28392v1#S4)

对每个模式，沿 \(u_0\equiv p\bmod r_1\) 使用 Lichtman Proposition 5.2 的卷积等式，令 \(W=p^{1/100}\)，粗 Möbius 分界 \(W^2\)，平滑部截在 \(W\)。允许的外部乘子就是 \(\mu(v_0)\phi(v_0)\)、区间和 \(u_0\) 的同余，绝对值至多 1。卷积恒等式的额外低端项支撑于 \(u_0\le W^3\)，与 \(u_0\gg_{r_1,r_2}p\) 不交。大平滑部的总误差由原 Lemma 3.1 的倒数和给 \(O_T(p L^{-T})\)。因此 Type I 的 \(q\le W^5\) 且系数 \(\ll\tau(q)\)，Type II 的两因子 \(>W^2\) 且第二系数 \(\ll\tau(n/r_2)\)。把后者截成 \(L^C\) 的代价为 \(O(pL^{4-C})\)，故给定精度 \(T\) 时先取 \(C>T+10\)。该代价由 \(\sum_{d\le O(p)}\tau(d)^2/d\ll L^4\) 得到。[Lichtman，v1 §§3、5，尤其 Proposition 5.2](https://arxiv.org/html/2611.28392v1#S5)

Type I 中写 \(u_0=qh\)。按原 Proposition 5.5，将 \(R_z(h)\) 截位展开成 \(d_0\mid h\)，将模式截位展开成 \(d\mid v_0\)，每个截位均取 \(R=\lceil C_R\log L\rceil\)。计数余项中 \(h=d_0j\) 满足 \(d\mid v_0\) 时 \(j\) 的个数 \(\ll p/(qd_0d)+1\)。这是因为 \(d\) 的素因子为模式素数，若与 \(r_2qd_0\) 共享素因子则会整除 \(\Delta p\)，故有解时互素。原 (5.14) 的每区间倒数积求和给模式截位误差 \(\ll B_{\rm pat}\exp(B_{\rm pat})/(R+1)!\)。粗截位的倒数尾为 \((\sum_{\ell\le z}1/\ell)^{R+1}/(R+1)!\)。先截粗性时可用 \(|\phi|\le1\)。若一并展开模式，其系数的倒数质量也至多 \(\exp(B_{\rm pat})=L^{O(1)}\)。对模式截位误差再乘粗性展开的 \(\sum_{d_0}d_0^{-1}\ll\log z\)。两者均乘 \(\sum_{q\le W^5}\tau(q)/q\ll L^2\)，取 \(C_R\) 大即可达到任意指定的对数精度。计数中的 \(+1\) 总代价为 \(p^{1/20+o(1)}\)。

主项的等式 \(r_1v_0+\Delta p=r_2qd_0j\) 给 \(v_0\) 模 \(r_2qd_0\) 的一类，因为物理条件已排除 \(r_1\mid qd_0\)。再加 \(d\mid v_0\) 得一条模 \(r_2qd_0d\) 的进程。模数 \(\le p^{1/20+o(1)}\)，按 \(qd_0d\) 聚合的系数由 \(\tau_4(qd_0d)\) 控制。固定 \(r_2\) 后同样由 \(\tau_4(r_2qd_0d)\) 控制。用 Lichtman Lemma 5.4 对所有剩余类成立的带权 Möbius Bombieri–Vinogradov 界，Type I 为 \(O_T(pL^{-T})\)。[Lichtman，v1 §5，Lemma 5.4 与 Proposition 5.5](https://arxiv.org/html/2611.28392v1#S5)

Type II 将 \(r_2\) 放入第二变量并作 (1) 的分块。二进盒数 \(O(L^2)\)。对物理区间的 \(mn\) 限制，在半整数端点用高 \(p^3\) 的截断 Perron 积分。对每个盒，用横实部 \(1/L\) 并按 \(M,N\) 归一化后，只给两端加一致有界的实幂权及高至 \(p^3\) 的乘法扭转，积分 \(L^1\) 代价 \(O(L)\)。每项离半整数端点的相对距离 \(\gg p^{-1}\)，截断总误差 \(O(p^{-1}L^{O(C)})\)。物理 \(v_0>0\) 可由 \(Q_0>0\) 继续施加。若活跃 \(\ell^2\mid v_0\)，粗的 \(m\) 使 \(n\) 只取一个模 \(\ell^2\) 类，二进盒计数 \(\ll X/\ell^2\)，因为 \(\ell^2=p^{o(1)}\ll N\)。这部分绝对误差 \(\ll XL^{2C}\sum_{\ell\ge e^{\lambda_1}}\ell^{-2}\)。

在无活跃平方的部分，对 \(v_0=aQ_0\) 使用
\[
c(Q_0)=\frac{\mu(Q_0)\phi^-(Q_0)}
{\prod_i(\omega_{\mathcal P_i}(Q_0)+1)} .
\]
在每个区间按可选活跃素因子计数得到准确的 Ramaré 恒等式。对有活跃平方的部分，提取式绝对值仍 \(\le1\)，因为对每个被选 \(\ell\in\mathcal P_i\)，\(\omega_{\mathcal P_i}(v_0/\ell)+1\ge\omega_{\mathcal P_i}(v_0)\)，所以可重新允许前述小误差。现在 (2)、(30) 和 §8 给每尺度的 Type II 和 \(\ll_D XL^{-D}\)，将弧估计取为 \(2D\) 次精度即可。求和各尺度与盒，再乘 Perron 代价和模式数，仍可得到任意固定对数精度。于是
\[
\sup_{\mathcal I}\left|
\sum_{\substack{s_0\in\mathcal I\\1\le s_0<p/r_2}}
\mu(p-r_1s_0)\mu(p-r_2s_0)\right|=o(p),
\tag{31}
\]
其中 \(\mathcal I\) 对 \(p\) 可变。[Lichtman，v1 Lemma 6.1 与 §7](https://arxiv.org/html/2611.28392v1#S7)

令 \(F_p(n)=\mu(p-n)w(n/p)\) 于 \(1\le n<p\)，其余置零。固定奇素数 \(q_1<q_2\)，用 (31) 及分部求和可以处理共轭乘积权 \(w(q_1s/p)\overline{w(q_2s/p)}\)，其全变差与上界均由固定的 \(w\) 控制。故 \(\sum_{s\ge1}F_p(q_1s)\overline{F_p(q_2s)}=o(p)\)。取固定有限奇素数集 \(\mathcal P\)，\(\sigma=\sum_{q\in\mathcal P}1/q\)，\(\omega(n)=\sum_{q\in\mathcal P}\mathbf1_{q\mid n}\)。CRT 给 \(\sum_{1\le n<p}|\omega(n)-\sigma|^2\le p\sigma+O_{\mathcal P}(1)\)。因此 \(\sigma C_p\) 与 \(\sum_{q\in\mathcal P}\sum_{m\ge1}\mu(qm)F_p(qm)\) 的差为 \(O_w(p\sqrt{\sigma})+o_{\mathcal P,w}(p)\)。用 \(-\mu(m)\) 替换 \(\mu(qm)\)，只需对 \(q\mid m\) 付 \(\ll_w p\sum_{q\in\mathcal P}q^{-2}\)。再用 Cauchy–Schwarz，
\[
\left|\sum_m\mu(m)\sum_{q\in\mathcal P}F_p(qm)\right|^2
\le p\sum_m\left|\sum_{q\in\mathcal P}F_p(qm)\right|^2
\ll_w p^2\sigma+o_{\mathcal P,w}(p^2).
\]
对角项由有界性控制，非对角项用有限集逐对的 (31)。先令 \(p\to\infty\)，再扩大有限奇素数集使 \(\sigma\to\infty\)，得 \(C_p=o(p)\)。因此逐对结论的量词是“给定任意固定的一对”，Kátai 应用只对有限多个这样的结论求和。

## 10. 显式参数与 Lean 证书的范围

取
\[
\alpha=1/1000,\quad\beta=\jmath=1/100,\quad\varrho=1/4,\quad
E_0=A+4\max(0,C)+3,\quad G=E_0+4,\quad A_0=G+3,
\]
\[
k=\lceil200(G+3)\rceil,\qquad C_0=2(\max(0,c_*)+E_0+4).
\]
可取 \(\zeta=(1+\beta)/2\)。顺序为先取目标精度与权系数界，再取 \(E_0,G,A_0,k\)，由 §6 选择粗行列权指数 \(c_*\)，最后取碰撞秩阈值常数 \(C_0\)。这是因为 \(C_0\) 仅进入碰撞阈值。在 (17) 和 (29) 分别使用 \(\varrho+\beta+\jmath<1\) 及 \(\beta+\jmath<\varrho\)。其余参数不等式分别由 (24)、有链接 Schur 界及 (26)–(30) 使用。

Lean 使用同一个参数选择，验证模 \(r_2\) 约束、配对权恒等式、交换矩阵类、模 \(p\) 纤维间距，以及全部参数预算。解析接口的物理配对数据是 (18)，直接误差来自 (a)、(b)、(c)。历史矩数据在每个 \(D\) 上用 \((HDZ)\mathcal T_H/(DYX)\) 归一化，(20)、(25)–(27) 提供低秩主项、高秩碰撞项和网格误差，(29) 的谱不等式给配对接口。证书从这些具名输入推导实指数的任意对数幂节省。解析算子、网格、谱估计及 Kátai 论证是在本文中给出的数学证明，Lean 的内核检查范围由该接口的假设明确给定。
