aux [] a = auxRev a []
aux (x:xs) a = aux xs ((x-1):a)

auxRev [] x = x
auxRev (x:xs) s = auxRev xs (x:s)

decList :: [Integer] -> [Integer]
decList x = aux x []
