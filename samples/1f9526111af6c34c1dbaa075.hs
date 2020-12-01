fact :: Integer -> Integer
fact 1 = 1
fact n = facthelp 1 n
        where
            facthelp a 1 = a
            facthelp a b = facthelp (a*b) (b-1)