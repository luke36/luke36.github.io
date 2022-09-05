---
layout: post
title: "Tagless Final"
---

之前看魔理沙的[这篇文章](https://zhuanlan.zhihu.com/p/22231273), 虽然推导详尽令人信服, 但还是纯纯的看不懂. 并且认为这种技巧属于类型体操, 一辈子也不会用一次. 结果前两天试图把 ast 搞成 typed 的我搞 gadt 走火入魔, 去 OCaml 社区找讨论, 看见[这个串](https://discuss.ocaml.org/t/narrowing-variant-types-alternatives/3806/5), 又看到 Tagless Final, 遂学习 (<https://okmij.org/ftp/tagless-final/course/>). 看来这种做法不但优美, 实践上也确实有诸多好处, OCaml 虽然无 typeclass 也可用 module [模拟](https://okmij.org/ftp/tagless-final/course/final_mod.ml). 还是然而看完还是很多不懂, 魔理沙文章一开始 pretty print 等问题直接 abstract 成 typeclass 貌似就可以解决, 所以后面都是为了编译到 SKI ?? 算了, 我等凡夫俗子还是老老实实用 ADT 跟 assert false 吧...

其实一段时间, 脑子里在构思怎么存麻将对局信息, 想用 scheme 那种 S-exp 存, 要用了 (比如 pp 或者收集信息) 就先把 tag define 成函数, 再 load, 就可以达到数据变成表达式值的效果了, 其实就是 tagless final, 只不过在 untyped 的语言里还没有发挥出双重 extensibility 的威力.
