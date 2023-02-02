This document is an overview over the Haskell code implementing different parts of complexity of boolean functions. 

* `All.hs`
* `Memo.hs`
* `PolyCmp.hs`
* `Algor.hs`: step-by-step reconstruction of the algorithm generation.
* `BDD/Examples.hs`: some BDD examples of Boolean functions
* `BDD/Ordering.hs`: an ordering instance for BDDs

Older files (in TypeNatBased/)

* `Tuple.hs`: tuples, and boolean functions
* `Alg.hs`: algorithms (= decision trees) for Boolean functions, properAlg
* `Alg/Show.hs`: some old show functions for algorithms
* `BDD.hs`: contains Boolean Decision Diagrams and is the main file as of now. It contains a fairly efficient calculation of the best algorithms with corresponding costs for a Boolean function. It uses methods like memoization and interval root finding algorithms. Probably the content should be split into more files in the `BDD/` folder.
* `BDD/Fib.hs`: a memoized method of calculating the Fibonacci numbers as a stepping stone for general memoization
* `Examples.hs`: contains examples of Boolean functions and their algorithms, such as majority, all, AC, iterated majority, and graph connectivity
* `Expectation.hs`: computes level-p complexity for algorithms
* `Symbase.hs`: contains new symmetric polynomial representation that is useful for Boolean functions
* `GenAlg.hs`: a function for generating algorithms and some tests where we can see all algorithms generated for Boolean functions like majority, graphs and AC

The folder `misc` contains old files that are no longer used.

Helper modules:

* `FiniteEnum.hs`: brute-force enumeration of finite types
* `EmptyTypeNats.hs`: helper functions related to type level natural numbers
* `DSLsofMath`: folder with useful material regarding polynomials from the course [DSLsofMath](https://github.com/DSLsofMath/DSLsofMath) at Chalmers University of Technology

