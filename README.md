Correctness proofs of distributed systems with Isabelle
=======================================================

This Gist accompanies a Talk by [Martin Kleppmann](https://martin.kleppmann.com/):

* [40-minute version given at Strange Loop 2019](https://www.youtube.com/watch?v=7w4KC6i9Yac) ([slides](https://speakerdeck.com/ept/correctness-proofs-of-distributed-systems-with-isabelle))
* [40-minute version given at Code Mesh LDN 2019](https://www.youtube.com/watch?v=NfdP6wwjsGk)
* [2-hour **extended version**](https://www.youtube.com/watch?v=Uav5jWHNghY), which I recorded at home

[Download Isabelle](http://isabelle.in.tum.de/) to play with the proofs. Have fun!

Abstract
--------

Testing systems is great, but tests can only explore a finite set of inputs and behaviors. Many real systems, especially distributed systems, have a potentially infinite state space. If you want to be sure that a program does the right thing in all possible situations, testing is not sufficient: you need proof. Only mathematical proof, e.g. by induction, can cover an infinite state space.

Pen-and-paper proofs are well established in mathematics, but they need to be laboriously checked by hand, and humans sometimes make mistakes. Automated theorem provers and computerized proof assistants can help here. This talk introduces Isabelle/HOL, an interactive proof assistant that can be used to formally prove the correctness of algorithms. It is somewhat like a programming language and REPL for proofs.

In this talk we will explore how Isabelle can be used to analyze algorithms for distributed systems, and prove them correct. We will work through some example problems in live demos, and prove real theorems about some simple algorithms. Proof assistants still have a pretty steep learning curve, and this talk won’t be able to teach you everything, but you will get a sense of the style of reasoning, and maybe you will be tempted to try it for yourself.