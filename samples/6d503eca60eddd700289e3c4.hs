fact :: Integer -> Integer
fact n = aux n 1
   where aux 1 a = a
         aux n a = n*(aux (n-1) a)