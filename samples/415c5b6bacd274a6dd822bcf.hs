fact :: Integer -> Integer
fact 0 = 1
fact 1 = 1
fact n = aux 1 n
     where aux acc 1 = acc
           aux acc n = aux (acc*n) (n-1)