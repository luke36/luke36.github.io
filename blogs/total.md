# 全函数和图灵完备

如果看过 The Little Typer, 应该都会对那段 "Why not?" "Because recursion is not an option." * n 的对话印象深刻. 不用 general recursion, 而是用类似 primitive recursion (称作 structural recursion) 的函数来代替, 保证计算一定终止, 第一次见肯定会感到新奇. 事实上, 许多类型系统包含 Dependent Type 的程序语言也有类似的特性 (因为 type 依赖于 value, 那么为了进行类型检查, 就得一边算, 要是算不出就没法查了), 只不过除了用 primitive recursion 来写递归函数外, 也可以正常写, 只要它强大的 totality checker 能检测出这个函数一定终止.

```coq
Check nat_rec.
nat_rec
     : forall P : nat -> Set,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n

(* nat_rec P base step O = base, *)
(* nat_rec P base step (S n) = step (nat_rec P base step n) *)
```

在 proof assistant 中, 保证 totality 已经习以为常, 正如在其它语言中写 general recursion 也已经习以为常. 如果在日常中也引入这样的习惯, 会有什么影响呢? 不能随手写递归虽然棘手, 但是也能增强对代码正确性的信心. 但是有些东西必须是不终止的(或是, 在你让它终止前, 不能终止的), 比如操作系统, 比如编辑器. 这也不是问题, 因为许多语言同时提供 coinductive datatype, 可以 encode 无限数据. 而且, 你也可以经常见到为了证明某无限递归的函数的某性质时给它加一个 counter, 每次减一, 以达到类似原函数的效果.

更严重的一个后果是, 凡是 total 的语言必定不是图灵完备的. 这不仅是在不能表达 partial function 的意义上, 也是在不能表达所有 total computable function 的意义上: 一个这样的函数是他自己的解释器 (在这门语言表达力足够的意义上), 证明是用对角化. 这看起来很严重! 好消息是, 即使只用 structural recursion (上文也提到, 一般不仅如此), 也能写出足够多的函数了 (哥德尔证明了: 从数据类型的公理出发, 能在一阶逻辑中被证明终止的所有函数能被表达). 算法的复杂性则仍然是一个开放问题. 论文作者认为可以用一系列表达能力逐步上升(然而安全性下降)的语言构建整个计算机体系. 就好比平时写高级语言, 有时不免写写汇编.

但是说这么多, 也只有偏完美主义者的人才会日常用 total programming language 吧... (￣y▽,￣)╭

## Reference

*Total Functional Programming*, D.A.Turner.

## 证明附

对于 total language $L$, 有图灵机 $i$, $[p](d) := i(p . d)$. 假设存在解释器 $p$, $i(p . (q . d)) = [p](q . d) = i(q . d)$, 那么考虑程序 $[s](r) := [p](r . r) + 1$, 有 $[p](s . s) = [s](s) = [p](s . s) + 1$, 矛盾. 这里假设 $L$ 可以表达 pair 和 +1.
