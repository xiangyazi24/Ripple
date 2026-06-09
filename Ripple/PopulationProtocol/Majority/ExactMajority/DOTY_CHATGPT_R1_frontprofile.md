[BRIDGE_WARNING] Likely truncated capture. The server rejected this text 4 times as intro-only or short (reasons: intro_preamble_short; last elapsed: 558s); the extension force-finalized at the kickback cap. The full ChatGPT answer is likely still visible in the browser tab — paste the actual reply back manually if you need the complete response.

---

Verdict
Your hwin_all hypothesis is not a faithful §6 invariant. In fact, as stated over every reachable FrontSync configuration, it is false.
Doty et al. do not keep the fixed penultimate minute cap−1 at O(log log n) agents. They keep a moving cumulative front profile small relative to the current bulk position. The fixed-cap feeder can absolutely fill while the cap is empty; in the paper that filling is not a bad event, it is exactly how the next minute starts.
The right replacement is a trajectory-level moving-frame invariant, not a feeder-only supermartingale:


$$\forall i,t,\quad n^{-0.4}\le c_{\ge i}(t)\le 0.1
\Longrightarrow
c_{\ge i+1}(t)<p\,c_{\ge i}(t)^2.$$


This is Theorem 6.5. It is self-contained for the clock, but any fixed-cap safety statement must be coupled to the bulk position through a statement like


$$c_{\ge u}(t)>0
\Longrightarrow
c_{\ge u-W}(t)\ge 0.1,
\qquad W=\Theta(\log\log n).$$


Equivalently,


$$c_{\ge u-W}(t)<0.1
\Longrightarrow
c_{\ge u}(t)=0.$$


That is the paper’s real “top cannot be far ahead of bulk” statement, coming from the first claim inside the proof of Theorem 6.5, not from a fixed feeder count bound. The paper proves that when the first agent reaches minute i, a 0.1 fraction is already within about 2 log log n minutes behind it. (arxiv.org)
Why the fixed-cap feeder invariant fails
Under FrontSync, cap is empty, and cap−1 has no upward outflow except the transition that breaks FrontSync. So the feeder is not a supermartingale. Worse, as a deterministic reachability statement, frontMinuteCount(cap−1) ≤ O(log log n) is false: once a single cap−1 agent exists, the epidemic rule can copy cap−1 into lower-minute agents one by one while avoiding cap−1, cap−1 interactions, leaving cap empty and making the feeder arbitrarily large. The clock rules in the paper are exactly: unequal clock minutes synchronize upward by max, and equal minutes drip upward while below the maximum minute. (arxiv.org)
So the obstruction you identified is real. The paper does not overcome it by finding a clever feeder potential. It avoids needing such an invariant.
A useful sanity check: the paper’s own early-drip allowance is much larger than O(log log n) in absolute count. It proves an early-drip fraction d_{\ge i+1}=O(n^{-0.85}), i.e. an absolute count O(n^{0.15}), not polylogarithmic. (arxiv.org)
The actual moving-frame object
The paper works with cumulative tails


$$c_{\ge i}(t)=\frac{|\{a:a.\mathrm{minute}\ge i\}|}{|C|}$$


and stopping times t⁺_{≥i}, t^{0.1}_{≥i}, and t^{0.9}_{≥i}. These are explicitly defined at the start of §6.1. (arxiv.org)
The right “potential-like” object is not the fixed feeder count. It is the excess front-tail quantity


$$Y_i(t)
=
c_{\ge i+1}(t)-d_{\ge i+1}(t),$$


compared against


$$0.9p\,c_{\ge i}(t)^2.$$


Lemma 6.3 proves, with very high probability,


$$c_{\ge i+1}(t)
\le
0.9p\,c_{\ge i}(t)^2+d_{\ge i+1}(t)$$


whenever $n^{-0.45}\le c_{\ge i}(t)\le 0.1$. The proof is a 0.1-time-window induction, not a supermartingale: it shows that in the previous 0.1 parallel time, the lower tail $x=c_{\ge i}$ grows enough by epidemic, while the upper tail $y=c_{\ge i+1}-d_{\ge i+1}$ can grow only by a bounded epidemic factor plus a drip source of order $p x^2$. (arxiv.org)
The key inequalities in Lemma 6.3 are:


$$x(t-0.1)<0.84x(t),$$


and


$$y(t)\le 1.23\bigl(y(t-0.1)+0.11p\,x(t)^2\bigr),$$


which close because


$$1.23\bigl(0.9p(0.84x(t))^2+0.11p x(t)^2\bigr)
<0.9p x(t)^2.$$


That is the “front slower than bulk” mechanism. The source term for the next level is quadratic in the current level, while the epidemic makes the current cumulative level grow by a constant factor in constant time. The front itself being sparse is not fatal: a sparse epidemic still has constant multiplicative growth time; what becomes harder is concentration, which is why the proof stops at thresholds like $n^{-0.45}$ and handles earlier drips separately. (arxiv.org)
How Theorem 6.5 is established
Theorem 6.5 is the main profile theorem:


$$n^{-0.4}\le c_{\ge i}(t)\le 0.1
\Longrightarrow
c_{\ge i+1}(t)<p\,c_{\ge i}(t)^2.$$


Its proof is an induction on the minute i. The inductive hypothesis has two parts:


$$t^{0.1}_{\ge i}-t^+_{\ge i}=O(\log\log n),$$


and


$$d_{\ge i+1}(t^{0.1}_{\ge i})=O(n^{-0.85}).$$


Then Lemma 6.3 gives


$$c_{\ge i+1}(t)
<
0.9p\,c_{\ge i}(t)^2+d_{\ge i+1}(t)
\le
p\,c_{\ge i}(t)^2,$$


because $c_{\ge i}(t)^2\ge n^{-0.8}$, making the $d$-term negligible. (arxiv.org)
The first inductive claim is the important moving-frame width statement. At the first time any agent reaches minute i, the paper proves that a 0.1 fraction is already at minute


$$j=i-2\log\log n$$


or beyond. In stopping-time form:


$$c_{\ge i}(t)>0
\Longrightarrow
c_{\ge i-2\log\log n}(t)\ge 0.1$$


on the good clock-profile event, up to the usual floors/constants. This is the source of the correct cap/bulk coupling. (arxiv.org)
How to “sum” the front tail
There is no separate sum over exact minute counts in the paper. The quantity $c_{\ge i}$ is already cumulative:


$$c_{\ge i}
=
\sum_{r\ge i} c_{=r}.$$


So if you want the total number of agents at or above a moving cutoff, the bound is simply


$$|C|\,c_{\ge i}.$$


If you define a moving bulk index, for example


$$b(t)=\max\{i:c_{\ge i}(t)\ge 0.1\},$$


then $c_{\ge b(t)+1}(t)<0.1$, and iterating Theorem 6.5 gives a doubly-exponential tail of the form


$$c_{\ge b(t)+1+r}(t)
\lesssim
p^{2^r-1}\,0.1^{2^r},$$


as long as the intermediate tails remain in the theorem’s density range. For the extreme top, where tails fall below the theorem’s $n^{-0.4}$ threshold, the paper switches to the first-arrival/width argument rather than continuing a clean recurrence all the way down to 1/n. (arxiv.org)
This is also why the statement “the number of agents within O(log log n) minutes of the maximum is O(log log n)” is not what the paper proves. The paper proves the width of the front tail is O(log log n) relative to the 0.1 bulk threshold. The count in that whole band can be a constant fraction of the population near the back end of the band.
The fixed-cap safety statement you actually want
For a fixed guard minute u, the faithful statement is:


$$t<t^{0.1}_{\ge u-W}
\Longrightarrow
c_{\ge u}(t)=0,
\qquad W=2\lceil\log\log n\rceil+O(1).$$


For your feeder:


$$t<t^{0.1}_{\ge (cap-1)-W}
\Longrightarrow
\mathrm{frontMinuteCount}(cap-1,t)=0.$$


Equivalently, at any time on the good profile event,


$$\mathrm{frontMinuteCount}(cap-1,t)>0
\Longrightarrow
c_{\ge cap-1-W}(t)\ge 0.1.$$


That is the precise coupling: a nonempty fixed feeder implies that the bulk is already within O(log log n) minutes of the feeder. This is the correct replacement for hwin_all.
So the Lean invariant should look like:
leanGoodWidth(path) :  ∀ t ≤ H, ∀ i,    rBeyond i (X t) > 0 →    rBeyond (i - W) (X t) ≥ 0.1 * cardC
and then a fixed-cap corollary:
leanNoGuardBeforeBulk(path) :  GoodWidth path →  (∀ t ≤ H, rBeyond (cap - W) (X t) < 0.1 * cardC) →  ∀ t ≤ H, rBeyond cap (X t) = 0
For the feeder:
leanNoFeederBeforeBulkBand(path) :  GoodWidth path →  rBeyond (cap - 1 - W) (X t) < 0.1 * cardC →  frontMinuteCount (cap - 1) (X t) = 0
This is joint with the bulk position. A fixed cap count is not separable from where the 0.1 quantile currently is.
Relation to completion and the paper’s finite cap
The paper’s actual clock minute field is finite, 0,…,kL, and when a Clock agent reaches the maximum minute kL, it starts a counter used to wait for the phase to settle. Reaching the top minute is not treated as a breach of a FrontSync invariant. (arxiv.org)
So if your capMinute = K(L+1) is an extra guard above the paper’s needed clock range, then you can prove “no cap before completion” only if the guard is at least $W=\Theta(\log\log n)$ minutes beyond the completion threshold. If the guard is only one constant-size hour beyond the bulk, then an empty-top statement is not asymptotically what the paper proves. The paper tolerates small fractions of agents being ahead; it does not require zero agents ahead.
At hour granularity, the paper defines


$$start_h=\min\{t: \text{fraction of Clock agents at hour }\ge h \ge 0.9\},$$


and


$$end_h=\min\{t: \text{fraction of Clock agents at hour }>h \le 0.001\}.$$


Then synchronous hour h is [start_h,end_h]. The proof of Theorem 6.9 uses Theorem 6.5 to show that two minutes before the next hour reaches 0.1, the fraction already beyond the next hour is below 0.001; this is the paper’s hour-level “front is not too far ahead” coupling. (arxiv.org)
What to change in the Lean architecture
Do not try to prove:
lean∀ reachable FrontSync c, frontMinuteCount (cap - 1) c ≤ O(log log n)
That is neither true nor used by the paper.
Use this structure instead:
lean-- trajectory-level, high-probability eventGoodFrontProfile :  ∀ t ≤ H, ∀ i,    n^(-0.4) ≤ c_ge i t ∧ c_ge i t ≤ 0.1 →    c_ge (i+1) t ≤ p * (c_ge i t)^2GoodFrontWidth :  ∀ t ≤ H, ∀ i,    c_ge i t > 0 →    c_ge (i - W) t ≥ 0.1-- deterministic consequence on the good eventNoFixedCapBeforeBulkBand :  GoodFrontWidth →  (∀ t ≤ H, c_ge (cap - W) t < 0.1) →  ∀ t ≤ H, c_ge cap t = 0
Then your probability decomposition should be:


$$\Pr[\text{bad cap event before completion}]
\le
\Pr[\neg GoodFrontWidth]
+
\Pr[\text{bad cap event before completion}\wedge GoodFrontWidth].$$


The second term should be zero if the guard is placed $W$ minutes beyond the completion bulk threshold. If the guard is not that far beyond completion, then a top-empty proof is stronger than the paper and likely false.
The only supermartingale potential in this part of §6 is later, in Lemma 6.10:


$$\Phi(t)=m_{>h}(t)-1.1c_{>h}(t),$$


which shows too-fast Clock agents do not drag too many Main/O agents above hour h. That potential is for Clock-to-Main coupling, not for controlling the clock front or the fixed-cap feeder. (arxiv.org)
So the minimal faithful invariant is:


$$\boxed{
\text{moving cumulative front profile}
+
\text{bulk-distance-to-guard stopping condition}
}$$


not a fixed cap−1 feeder.