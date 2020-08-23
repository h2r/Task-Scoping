(define (problem TAXINUMERIC-64)
(:domain universal_multipasstaxi)
(:objects
	curly smoov littman isbell - passenger
    t0 - taxi
)
(:init
    (= (taxi-x t0) 0)
    (= (taxi-y t0) 0)

    (not (passenger-in-taxi curly t0))
;    (not (passenger-in-taxi smoov t0))
    (= (passenger-x curly) 3329)
    (= (passenger-y curly) 3614)
;    (= (passenger-x smoov) 3459)
;    (= (passenger-y smoov) 1462)
)
(:goal (and
    (= (passenger-y curly) 10000)
	(= (passenger-x curly) 9000)
    (not (passenger-in-taxi curly t0))
	
    )
)

)