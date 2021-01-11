factHelper :: Integer -> Integer -> Integer
factHelper x 1 = x
factHelper x n = factHelper (x*n) (n-1)

fact :: Integer -> Integer
fact n = factHelper n (n-1)