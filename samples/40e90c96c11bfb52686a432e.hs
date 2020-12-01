fact :: Integer -> Integer
fact n = factHelper n 1
    where factHelper 1 acc = acc
          factHelper n acc = factHelper (n-1) (acc*n)