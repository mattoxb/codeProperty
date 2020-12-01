fact :: Integer -> Integer
fact n = aux 1 n
    where aux acc 0 = acc
          aux acc n = aux (acc*n) (n-1)