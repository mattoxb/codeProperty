fact :: Integer -> Integer
fact n = factorial n 1

factorial :: Integer -> Integer -> Integer
factorial 0 aux = aux
factorial n aux = factorial (n-1) (aux*n)