# BoFunComplexity
Update 2023-12-12: The paper has now been published in Journal of Functional Programming: [Here is the link!](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/levelpcomplexity-of-boolean-functions-using-thinning-memoization-and-polynomials/58122B71C40F99E0D19ACD0FAFF867A9#article). A note on page 19, the sentence "The difference, illustrated in Figure 3, factors to exactly and we note that it is non-negative in the whole interval." should be "The difference, illustrated in Figure 3, factors
to exactly $p^2(1-p)^2(1-p+p^2)$ and we note that it is non-negative in the whole interval."

Associated code for the paper "Level-p-complexity of Boolean Functions using Thinning, Memoization, and Polynomials" (under submission to JFP) by Julia Jansson and Patrik Jansson.

A preprint is available as [arXiv:2302.02473](https://arxiv.org/abs/2302.02473) and the associated code is available as release [tag/v2023-02.pre-print](https://github.com/juliajansson/BoFunComplexity/releases/tag/v2023-02.pre-print) as the code continues to evolve.

The code was later extended by Christian Sattler.

(The first JFP submission 2023-02 received positive reviews leading to a resubmission 2023-08.)

# Piecewise polynomials (example results)

All polynomials are described by their list of coefficients starting from degree 0: [1,7,3] means 1 + 7x + 3x^2.

## 3-bit majority

maj3: 1 piece [2,2,-2]

cost(0.5) = 5/2 = 2.5

## 2-level iterated 3-bit majority:

maj3_2: piecewise polynomial in [0, 1]:
+  1 piece [4,4,6,9,-61,23,67,-64,16]

cost(0.5) = 393/64 = 6.140625

sqrt (cost(0.5)) ~= 2.478028450199876

## 2-level iterated 5-bit majority:

maj5_2: piecewise polynomial in [0, 1]:
+  1 piece [9,9,9,30,12,62,-14,816,-2143,-44004,169768,-291977,751873,-2494791,5464225,-8722210,13579067,-21830058,29475938,-29211477,20338155,-9697875,3027801,-559872,46656]

## 3-level iterated 3-bit majority:
We conjecture that this is the piecewise polynomial level-p-complexity function:

Piecewise polynomial in [0, 1]:
+  1 piece [8,8,12,14,61,36,102,-126,-10712,19365,17503,-77698,168601,-249980,-313643,1716199,-1770993,-1454571,5011281,-4174314,-399914,3794567,-3710286,1941192,-604912,106400,-8192]
  + separated by root of [0,0,0,0,0,0,0,0,-12,212,-673,226,2710,-6134,4136,5423,-15446,17254,-11248,4448,-992,96,0] between 1 % 16 and 1 % 8
+  2 piece [8,8,12,14,61,36,102,-126,-10700,19129,18600,-79246,165907,-236868,-331172,1713854,-1729723,-1517123,5050327,-4164943,-439980,3832237,-3730238,1947624,-606096,106496,-8192]
  + separated by root of [0,0,0,0,4,-14,1,-12,175,-161,-998,3551,-4928,555,9156,-14384,7125,5845,-11816,8727,-3526,772,-72,0] between 1 % 4 and 3 % 8
+  3 piece [8,8,12,14,61,44,58,-60,-10756,19529,17554,-80248,176679,-262924,-303248,1720090,-1794005,-1427025,5004749,-4197705,-363572,3766645,-3697136,1937340,-604264,106352,-8192]
  + separated by root of [0,1,-3,2,-21,71,-24,-135,-7,689,-1376,1433,-932,385,-93,10,0] between 25 % 64 and 101 % 256
+  4 piece [8,8,12,14,61,44,66,-97,-10708,19382,18285,-81106,174820,-258825,-298686,1697380,-1767324,-1425978,4961708,-4132148,-420508,3799684,-3710282,1940814,-604816,106392,-8192]
  + separated by root of [0,0,0,0,-4,14,-5,-22,52,-89,-46,394,-358,-409,1198,-1162,288,665,-938,582,-184,24,0] between 101 % 256 and 51 % 128
+  5 piece [8,8,12,14,61,52,14,21,-10786,19204,18897,-81904,174394,-255647,-302472,1695466,-1756074,-1441532,4971474,-4130334,-430714,3810502,-3716802,1943226,-605328,106440,-8192]
  + separated by root of [0,0,0,0,-4,14,-5,-22,10,54,-120,138,-96,37,-6,0] between 13 % 32 and 7 % 16
+  6 piece [8,8,12,14,61,52,34,-89,-10601,19034,19632,-83754,174889,-252057,-303907,1682551,-1729794,-1459317,4957064,-4082429,-489454,3855127,-3739252,1950536,-606728,106560,-8192]
  + separated by root of [0,1,-3,2,2,-3,-91,112,1343,-4490,3579,4875,-4827,-28207,88578,-134667,133272,-92987,46697,-16660,4026,-592,40,0] between 7 % 16 and 15 % 32
+  7 piece [8,8,12,14,62,49,36,-87,-10604,18943,19744,-82411,170399,-248478,-299032,1677724,-1758001,-1370739,4822397,-3949157,-582441,3901824,-3755912,1954562,-607320,106600,-8192]
  + separated by root of [0,0,0,0,-5,-3,65,-70,44,-360,266,1908,-5269,5797,558,-12659,19383,-10089,-7650,16435,-12413,5074,-1116,104,0] between 15 % 32 and 1 % 2
+  8 piece [8,8,12,14,67,42,-30,116,-10853,19461,18714,-83427,179218,-266721,-282727,1685702,-1803260,-1309225,4790486,-3970803,-529508,3855489,-3732235,1947152,-605996,106496,-8192]
  + separated by root of [0,1,-1,-12,33,3,-146,111,263,524,-2371,-1977,13919,-10938,-25427,65039,-59004,10590,30521,-35995,20529,-6834,1276,-104,0] between 1 % 2 and 17 % 32
+  9 piece [8,8,12,15,66,30,3,119,-10999,19572,18977,-82903,176847,-268698,-268808,1674764,-1828687,-1244186,4731482,-3960213,-498987,3819494,-3711706,1940318,-604720,106392,-8192]
  + separated by root of [0,0,0,0,-5,-3,60,-73,-6,129,-533,698,607,-2126,1193,1379,-2524,1421,337,-1140,834,-288,40,0] between 17 % 32 and 9 % 16
+ 10 piece [8,8,12,15,71,18,-51,376,-11395,19704,19842,-85593,180062,-267378,-277502,1683949,-1827731,-1256123,4744359,-3964849,-502831,3826041,-3716252,1942136,-605128,106432,-8192]
  + separated by root of [0,1,-3,2,-6,23,-17,-10,-53,233,-362,312,-161,47,-6,0] between 9 % 16 and 19 % 32
+ 11 piece [8,8,12,15,71,18,-11,151,-10970,19329,20737,-87768,180357,-263563,-271482,1648154,-1779126,-1256838,4655884,-3817044,-640476,3910596,-3751532,1951846,-606728,106552,-8192]
  + separated by root of [0,1,-3,2,2,-3,-31,40,432,-1498,1694,-518,2437,-12453,26624,-33910,28933,-17183,7080,-1942,320,-24,0] between 77 % 128 and 155 % 256
+ 12 piece [8,8,12,15,73,10,-1,151,-10980,19273,20879,-86984,176497,-257179,-275906,1654064,-1808906,-1178684,4534816,-3691358,-732708,3959122,-3769576,1956370,-607416,106600,-8192]
  + separated by root of [0,0,0,0,-5,-3,60,-73,-55,157,-78,-77,160,-133,57,-10,0] between 155 % 256 and 39 % 64
+ 13 piece [8,8,12,15,73,15,-8,90,-10824,19203,21198,-88564,177835,-253440,-284722,1658274,-1800465,-1194047,4543600,-3687109,-744967,3970623,-3775980,1958596,-607864,106640,-8192]
  + separated by root of [0,-1,1,12,-34,7,103,-142,-10,183,-1029,3533,-3797,-5515,20552,-24068,8927,9794,-15863,10553,-3946,812,-72,0] between 5 % 8 and 3 % 4
+ 14 piece [8,8,12,17,69,-7,84,8,-11016,19693,20934,-88950,180259,-262564,-270062,1661710,-1852599,-1104807,4477610,-3688843,-693653,3917791,-3746982,1949080,-606096,106496,-8192]
  + separated by root of [0,-1,8,-15,-19,101,-203,447,-422,-1733,6122,-6369,-4167,18583,-19895,3713,14304,-19078,12464,-4768,1024,-96,0] between 3 % 4 and 1 % 1
+ 15 piece [8,8,12,17,67,10,46,-15,-10795,19186,22031,-90241,177215,-248587,-288922,1659745,-1811266,-1163180,4504931,-3663948,-746113,3961797,-3768982,1955896,-607312,106592,-8192]

See also [the plot](plots/pw3_3.eps).

### More details

Name the polynomial pieces p1 .. p15 where pmid=p8 is the middle piece.
All p_i have value 8 at both endpoints and around 15 in the middle.

The value at 0.5 is exactly 15796051 % 1048576 (rounded to Double precision: 15.064288139343262).

  (15.064288139343262)**(1/3) = 2.4697303458263957

The pieces are very close: for example let pdiff = p8-p0, then

  pdiff = P [0,0,0,0,6,6,-132,242,-141,96,1211,-5729,10617,-16741,30916,-30497,-32267,145346,-220795,203511,-129594,60922,-21949,5960,-1084,96,0]

At 0.5 the difference is exactly (-10145) % 524288 ~= -0.01935, thus the relative difference is around 1/1000.

The difference varies between around +0.0139 (near 0.32) and around -0.0427 (near 0.68). The maximal relative difference is under 0.3% of the maximum of p8.

A [plot of pdiff](plots/maj3_3_p8-p0.png).

## Hints at asymptotic behaviour

To sum up, if a_k is the cost at p=0.5 of the k-level iterated 3-bit majority, we have

+ a_1 = 5/2 = 2.5
+ a_2 = 393/64 = 6.140625
+ a_3 = 15796051 % 1048576 ≃ 15.064288139343262

There is a proof in the literature that a_k^(1/k) will converge to some 2.25 <= L < 2.5 and that the limit is equal to (lim inf a_k^(1/k)). 

+ a_1^(1/1) = 2.5
+ a_2^(1/2) ≃ 2.478028450199876
+ a_3^(1/3) ≃ 2.4697303458263957

Thus, we can see that L < 2.47 - a very slight improvement on L < 2.5.

We can conjecture that a_4^(1/4) is close to 2.47, thus a_4 is close to 2.47^4 ≃ 37.2.

# Talks

* 2022-12: Patrik Jansson gave a talk at the 2012-12 online meeting of IFIP WG 2.1 on Algorithmic Languages and Calculi. The recording is available [on YouTube](https://www.youtube.com/watch?v=95rhCROOOdA) and the slides [here](talk/2022-12_Jansson_RandComplex.pdf).
* 2023-03: [Slides](talk/2023-03_Jansson_RandComplex.pdf), [YouTube recording](https://youtu.be/Z0cACMp8_hk)
