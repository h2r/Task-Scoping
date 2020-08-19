(define (problem UNITAXINUMERIC-1)
(:domain universal_multipasstaxi)
(:objects
	curly - passenger
    t0 - taxi
)
(:init
    (= (taxi-x t0) 0)
    (= (taxi-y t0) 0)
    (= (passenger-x curly) 3)
    (= (passenger-y curly) 3)
)
(:goal (and
    (= (passenger-y curly) 5)
	(= (passenger-x curly) 5)
    (not (passenger-in-taxi curly t0))	
    )
    )
;(:metric  minimize (total-fuel-used) )

)