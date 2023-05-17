cardBoVec :: Integer -> Integer
cardBoVec = (2^)
cardBoFun :: Integer -> Integer
cardBoFun = (2^) . (2^)

factorial n = product [1..n]

foo n = factorial n * cardBoFun n
-- bar n = (factorial n)^(n-2) * cardBoFun n

cardFullDecTree :: Integer -> Integer
cardFullDecTree 0 = 2
cardFullDecTree n = n * (cardFullDecTree (n-1))^2
-- 
cardDecTree :: Integer -> Integer
cardDecTree 0 = 2
cardDecTree n =
       {-leaf-} 2
     + {-node-} n * (cardDecTree (n-1))^2

test1 :: Bool
test1 = take 6 (map cardBoFun [0..])
     == [2,4,16,  256,     65536,          4294967296]
--      [2,3, 6,   20,       168,                7581 monotone boolean functions
--   /= [2,6,74,16430,1079779602, 5829619944476392022]

test2 :: Bool
test2 = take 6 (map cardDecTree [0..])
    == [ 2
       , 6
       , 74
       , 16430
       , 1079779602
       , 5829619944476392022
       ]
