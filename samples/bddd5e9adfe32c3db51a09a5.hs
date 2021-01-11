fact :: Integer -> Integer
fact n = aux 1 n
    where aux acc 1 = acc
          aux acc a = aux (acc * a) (a-1)