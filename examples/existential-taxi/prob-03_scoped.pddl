(define (problem TAXINUMERIC-03)
(:domain universal_multipasstaxi)
(:objects
	curly - passenger
    - taxi
)
(:init
;    (= (taxi-x t0) 0)
;    (= (taxi-y t0) 0)

;    (not (passenger-in-taxi curly t0))
;    (not (passenger-in-taxi smoov t0))
;    (not (passenger-in-taxi littman t0))

    (= (passenger-x curly) 3329)
    (= (passenger-y curly) 3615)

;    (= (passenger-x smoov) 3459)
;    (= (passenger-y smoov) 1262)

;    (= (passenger-x littman) 1291)
;    (= (passenger-y littman) 5037)

)
(:goal (and
    (= (passenger-y curly) 10000)
	(= (passenger-x curly) 9000)
;    (not (passenger-in-taxi curly t0))
	
    )
)

)