fact :: Integer -> Integer
fact n = aux n 1
    where aux 0 ans = ans
          aux n ans = aux (n-1) (ans*n)