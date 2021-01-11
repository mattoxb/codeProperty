fact :: Integer -> Integer
fact x = aux x 1
   where aux 0 acc = acc
         aux x acc = aux (x-1) (acc*x)