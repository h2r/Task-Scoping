(define (problem TAXINUMERIC-1)
(:domain multipasstaxi)
(:objects
	curly - passenger
    t0 - taxi
)
(:init
    (= (taxi-x t0) 0)
    (= (taxi-y t0) 0)
    (= (pass-x curly) 3)
    (= (pass-y curly) 3)
    (= (passenger-count t0) 0)
)
(:goal (and
    (= (pass-y curly) 5)
	(= (pass-x curly) 5)
    (not (in-taxi curly t0))
	
    )
    )
;(:metric  minimize (total-fuel-used) )

)