Definition f (x:nat) (y: x = x) := y.

Goal (5 = 5).
    unshelve refine (let x := f _ _ in _).
    3: { 
        refine x. 
    }
Abort.