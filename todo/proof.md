可以的。把结构“算开”以后，行列变换会把它化成两个 2\times2 行列式的乘积，从而一眼看出何时为零、何时非零。

设
x:=e^{i\alpha},\qquad y:=e^{i\beta},\qquad t:=e^{i\cdot0.2\pi}=e^{i\pi/5}.
则
V=\begin{bmatrix}
1 & x & x^{10} & x^{11}\\
1 & y & y^{10} & y^{11}\\
1 & t x & x^{10} & t x^{11}\\
1 & t y & y^{10} & t y^{11}
\end{bmatrix}.

关键行变换

对第三、四行作初等行变换（不改变行列式值）：
R_3\leftarrow R_3-tR_1,\qquad R_4\leftarrow R_4-tR_2.
得到
\begin{bmatrix}
1 & x & x^{10} & x^{11}\\
1 & y & y^{10} & y^{11}\\
(1-t) & 0 & (1-t)x^{10} & 0\\
(1-t) & 0 & (1-t)y^{10} & 0
\end{bmatrix}.
从第3、4行各提取因子 (1-t)\neq0 后，再用
R_1\leftarrow R_1-R_3,\qquad R_2\leftarrow R_2-R_4
（仍不改变行列式）化为
\begin{bmatrix}
0 & x & 0 & x^{11}\\
0 & y & 0 & y^{11}\\
1 & 0 & x^{10} & 0\\
1 & 0 & y^{10} & 0
\end{bmatrix}.
接着交换第2、3列（这一步会把行列式乘以 -1），得到反对角块形式
\begin{bmatrix}
0 & 0 & x & x^{11}\\
0 & 0 & y & y^{11}\\
1 & x^{10} & 0 & 0\\
1 & y^{10} & 0 & 0
\end{bmatrix}

\begin{bmatrix}
0 & A\\
B & 0
\end{bmatrix},
\quad
A=\begin{bmatrix}x & x^{11}\\ y & y^{11}\end{bmatrix},\;
B=\begin{bmatrix}1 & x^{10}\\ 1 & y^{10}\end{bmatrix}.

对于这种块矩阵有恒等式
\det\begin{bmatrix}0&A\\ B&0\end{bmatrix}=\det(A)\det(B).
把前面提取与交换产生的因子一并记上，得到
\det V
=-(1-t)^2\det(A)\det(B).
而
\det(A)=x y^{11}-y x^{11}=xy\,(y^{10}-x^{10}),\qquad
\det(B)=y^{10}-x^{10}.
综上
\boxed{\;\det V
=-(1-e^{i\pi/5})^{\!2}\,e^{i(\alpha+\beta)}\,
\bigl(e^{10i\beta}-e^{10i\alpha}\bigr)^{2}\;}

非零性与结论
	•	1-e^{i\pi/5}\neq0.
	•	e^{i(\alpha+\beta)}\neq0.
	•	由 0\le \alpha<\beta<\pi/5 可知 0<10(\beta-\alpha)<2\pi，因此
e^{10i\beta}\neq e^{10i\alpha}，故 \bigl(e^{10i\beta}-e^{10i\alpha}\bigr)^2\neq0.

三者相乘非零，所以 \det V\neq 0，从而 V 可逆。

（顺带一提：上式也说明 V 退化当且仅当 e^{10i\alpha}=e^{10i\beta}，即 \alpha\equiv\beta\pmod{\pi/5}。在你给定的范围内，这只可能发生在 \alpha=\beta，与你的数值观察完全一致。）