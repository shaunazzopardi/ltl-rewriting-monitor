module LTL(rewriteWithOutput, propagateNot) where
    
    import Data.List
    import Data.Maybe

    data LTL 
        = T
        | F
        | In Int
        | Out Int
        | Or LTL LTL
        | And LTL LTL
        | Not LTL
        | Until LTL LTL
        | Release LTL LTL
        | Next LTL
        deriving(Eq, Show)

    rewriteWithOutput :: LTL -> [Int] -> (LTL, [[Int]])
    rewriteWithOutput T is = (T, [[]])
    rewriteWithOutput F is = (F, [])
    rewriteWithOutput (In i) is = if elem i is
                                    then (T, [[]])
                                    else (F, [])

    rewriteWithOutput (Out i) is = (T, [[i]])

    rewriteWithOutput (Or pi pi') is 
        = if reduce rpi == T
            then (T, out)
            else if reduce rpi == T
                then (T, out')
                else if reduce rpi == F && reduce rpi' == F
                        then (F, [])
                        else (reduce (Or (reduce rpi) (reduce rpi')), out ++ out')
        where 
            (rpi, out) = rewriteWithOutput pi is
            (rpi', out') = rewriteWithOutput pi' is

    rewriteWithOutput (And pi pi') is 
        = if reduce rpi == T && reduce rpi' == T
            then (T, out ++ out')
            else if reduce rpi == F 
                    then (F, out)
                    else if reduce rpi' == F
                            then (F, out')
                            else (reduce (And (reduce rpi) (reduce rpi')), out ++ out')
        where 
            (rpi, out) = rewriteWithOutput pi is
            (rpi', out') = rewriteWithOutput pi' is

    rewriteWithOutput (Not (Out i)) is = (T, [[]])

    rewriteWithOutput (Not (Not pi)) is
        = rewriteWithOutput pi is

    -- When we have Or (Not $ Out 1) (Out 2) [note how this is the definition of implication]
    -- then the program will do 2, but not doing anything is also an option
    -- note how not doing Out 1 satisfies the first conjunct, which is not captured here
    rewriteWithOutput (Not pi) is
        = if (Not pi) == propagated
            then if reduce rpi == T
                    then (F, [])
                    else if reduce rpi == F
                            then (T, out)
                            else (reduce $ Not (reduce rpi), out)
            else rewriteWithOutput propagated is
        where
            propagated = reduce $ propagateNot (Not pi)
            (rpi, out) = rewriteWithOutput pi is
            
    rewriteWithOutput (Until pi pi') is 
        = if reduce rpi == F
            then (reduce rpi', out')
            else if reduce rpi == T && reduce rpi' == T
                    then (reduce rpi', [is ++ is' | is <- out, is' <- out'])
                    else (reduce (Or ((Until (reduce pi) (reduce pi'))) (rpi')), out ++ out')
        where 
            (rpi, out) = rewriteWithOutput pi is
            (rpi', out') = rewriteWithOutput pi' is

    -- not working for  (Release (Not T) (Next (Out 2)))
    rewriteWithOutput (Release pi pi') is 
        = if reduce rpi' == F
            then (F, [])
            else if reduce rpi == T
                    then (reduce rpi', [is ++ is' | is <- out, is' <- out']) 
                    else if pi == rpi && pi' == rpi'
                            then (Release pi pi', [is ++ is' | is <- out, is' <- out'])
                            else if isOr final
                                    then (final, out ++ out')
                                    else (final, out') 
        where 
            (rpi, out) = rewriteWithOutput pi is
            (rpi', out') = rewriteWithOutput pi' is
            final = reduce (Or ((Release pi pi')) ( And ( rpi) ( rpi')))

    rewriteWithOutput (Next pi) is
        = (reduce pi, [])
    
    isOr :: LTL -> Bool
    isOr (Or _ _) = True
    isOr _ = False

    propagateNot :: LTL -> LTL
    propagateNot (Not (Next pi)) = Next (Not (propagateNot pi))
    propagateNot (Not (Release pi pi')) = Until (Not (propagateNot pi)) (Not (propagateNot pi'))
    propagateNot (Not (Until pi pi')) = Release ((propagateNot (Not pi))) (propagateNot (Not pi'))
    propagateNot pi = pi

    -- For an appropriate winning strategy I think we need the not operator to be
    -- directly attached to an output atom.
    -- not X o = X not o
    -- not(o U p) = (not o R not p)

    reduce :: LTL -> LTL
    reduce(Not(Not pi)) = reduce pi
    reduce(Not pi) = Not $ reduce pi
    reduce(And T pi) = reduce pi
    reduce(And pi T) = reduce pi
    reduce(And _ F) = F
    reduce(And F _) = F
    reduce(And pi pi') = reduce (And (reduce pi) (reduce pi'))
    reduce(Or _ T) = T
    reduce(Or T _) = T
    reduce(Or pi F) = reduce pi
    reduce(Or F pi) = reduce pi
    reduce(Or pi pi') = reduce (Or (reduce pi) (reduce pi'))
    reduce(Until pi pi') = Until (reduce pi) (reduce pi')
    reduce(Release pi pi') = Release (reduce pi) (reduce pi')
    reduce(pi) = pi
