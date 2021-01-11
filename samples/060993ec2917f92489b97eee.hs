fact :: Integer -> Integer
fact a = aux 1 1 a
    where aux cur ac t
            | cur == t = ac
            | cur < t = aux (cur+1) (ac * (cur+1)) t